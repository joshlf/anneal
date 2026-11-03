// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end tests of the translator against the vendored MiniRust sources
//! and the checked-in generated output.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anneal_minirust_gen::pipeline::{self, Layout};
use anneal_minirust_gen::{lock, source};

fn minirust_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("minirust")
}

fn layout() -> Layout {
    Layout { root: minirust_dir() }
}

/// All files below `dir`, relative to `base`, with `/` separators.
fn files_below(base: &Path, dir: &Path, out: &mut Vec<String>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            files_below(base, &p, out);
        } else {
            let rel = p.strip_prefix(base).unwrap();
            out.push(rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect::<Vec<_>>().join("/"));
        }
    }
}

#[test]
fn generation_is_deterministic() {
    let a = pipeline::generate(&layout()).unwrap();
    let b = pipeline::generate(&layout()).unwrap();
    assert_eq!(a.files, b.files);
    assert_eq!(a.summary, b.summary);
}

/// The checked-in output is exactly what the generator produces: every
/// generated file matches byte for byte, and the generated directory contains
/// no other (stale or hand-written) files.
#[test]
fn checked_in_output_is_current() {
    let g = pipeline::generate(&layout()).unwrap();
    let root = minirust_dir();
    for (rel, text) in &g.files {
        let on_disk = std::fs::read_to_string(root.join(rel)).unwrap_or_else(|e| panic!("reading {rel}: {e}"));
        assert!(on_disk == *text, "{rel} is out of date; run `cargo run -p anneal-minirust-gen -- generate`");
    }
    let mut present = Vec::new();
    files_below(&root, &layout().generated_dir(), &mut present);
    for rel in present {
        assert!(g.files.contains_key(&rel), "{rel} is not produced by the generator");
    }
}

/// Counts every ```` ```rust ```` fence independently of the translator's own
/// Markdown scanner (opening fences of three or more backticks whose info
/// string starts with `rust`, closed by a fence at least as long).
fn count_rust_fences(md: &str) -> usize {
    let mut n = 0;
    let mut open: Option<usize> = None;
    for line in md.lines() {
        let t = line.trim_start();
        let ticks = t.chars().take_while(|&c| c == '`').count();
        match open {
            None if ticks >= 3 => {
                if t[ticks..].trim_start().starts_with("rust") {
                    n += 1;
                }
                open = Some(ticks);
            }
            Some(k) if ticks >= k && t[ticks..].trim().is_empty() => open = None,
            _ => {}
        }
    }
    n
}

/// Every Rust block of every vendored spec file is parsed, and every
/// top-level item of every block appears, in order and exactly once, in the
/// generated item list of its file.
#[test]
fn every_block_and_item_is_translated() {
    let l = layout();
    let lock = lock::parse(&std::fs::read_to_string(l.lock_path()).unwrap()).unwrap();
    let commit = lock.get("upstream", "commit").unwrap().to_string();
    let vroot = l.vendor_root(&commit);
    let g = pipeline::generate(&l).unwrap();
    let mut total_items = 0;
    let mut total_blocks = 0;
    for rel in lock.section("files").keys().filter(|p| p.starts_with("spec/") && p.ends_with(".md")) {
        let md = std::fs::read_to_string(vroot.join(rel)).unwrap();
        let sf = source::load_file(&vroot, rel).unwrap();
        assert_eq!(sf.rust_blocks, count_rust_fences(&md), "rust block count of {rel}");
        assert!(sf.skipped.iter().all(|b| !b.info.starts_with("rust")), "{rel}: a rust block was skipped");
        total_blocks += sf.rust_blocks;
        let module = format!("lean/MiniRustSpec/Generated/Items/{}.lean", sf.module_components().join("/"));
        let lean = g.files.get(&module).unwrap_or_else(|| panic!("no module {module} for {rel}"));
        // The `items` list at the end of the module, in order.
        let list = &lean[lean.rfind("def items : List SourceItem").expect("items list")..];
        let names: Vec<&str> = list
            .split("SourceItem.mk")
            .skip(1)
            .map(|s| s.trim_start().trim_start_matches('"').split('"').next().unwrap())
            .collect();
        let expected: Vec<&str> = sf.items.iter().map(|it| it.name.as_str()).collect();
        assert_eq!(names, expected, "item list of {rel}");
        for it in &sf.items {
            assert!(lean.contains(&format!("\ndef {} : Item :=", it.name)) || lean.contains(&format!("\ndef «{}» : Item :=", it.name)), "{rel}: no definition for {}", it.name);
        }
        total_items += sf.items.len();
    }
    let cov = &g.files["coverage.json"];
    assert!(cov.contains(&format!("\"rust_blocks\": {total_blocks}")), "coverage.json block total");
    assert!(total_items > 200, "suspiciously few items: {total_items}");
}

/// Generation refuses vendored sources that do not match the lock file.
#[test]
fn tampered_vendor_tree_is_rejected() {
    let l = layout();
    let lock = lock::parse(&std::fs::read_to_string(l.lock_path()).unwrap()).unwrap();
    pipeline::verify_vendor(&l, &lock).unwrap();
    let commit = lock.get("upstream", "commit").unwrap().to_string();

    let tmp = std::env::temp_dir().join(format!("anneal-minirust-gen-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    let mut files = Vec::new();
    files_below(&l.vendor_root(&commit), &l.vendor_root(&commit), &mut files);
    for rel in &files {
        let dst = tmp.join("vendor").join(&commit).join(rel);
        std::fs::create_dir_all(dst.parent().unwrap()).unwrap();
        std::fs::copy(l.vendor_root(&commit).join(rel), &dst).unwrap();
    }
    std::fs::copy(l.lock_path(), tmp.join("minirust.lock.toml")).unwrap();
    let t = Layout { root: tmp.clone() };
    pipeline::verify_vendor(&t, &lock).unwrap();

    // Flip one byte of one spec file.
    let victim = t.vendor_root(&commit).join("spec/lang/step/terminators.md");
    let mut bytes = std::fs::read(&victim).unwrap();
    bytes[100] ^= 1;
    std::fs::write(&victim, &bytes).unwrap();
    let err = pipeline::verify_vendor(&t, &lock).unwrap_err();
    assert!(err.contains("spec/lang/step/terminators.md"), "{err}");
    assert!(pipeline::generate(&t).is_err());

    // An extra file is rejected as well.
    std::fs::write(&victim, {
        bytes[100] ^= 1;
        &bytes
    })
    .unwrap();
    pipeline::verify_vendor(&t, &lock).unwrap();
    std::fs::write(t.vendor_root(&commit).join("spec/extra.md"), "```rust\nstruct X;\n```\n").unwrap();
    assert!(pipeline::verify_vendor(&t, &lock).unwrap_err().contains("extra"));

    let _ = std::fs::remove_dir_all(&tmp);
}

/// Extracts the contents of every ```` ```rust ```` fence (same rules as
/// `count_rust_fences`).
fn rust_fences(md: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut open: Option<(usize, bool)> = None;
    let mut cur = String::new();
    for line in md.lines() {
        let t = line.trim_start();
        let ticks = t.chars().take_while(|&c| c == '`').count();
        match open {
            None if ticks >= 3 => {
                open = Some((ticks, t[ticks..].trim_start().starts_with("rust")));
                cur.clear();
            }
            Some((k, is_rust)) if ticks >= k && t[ticks..].trim().is_empty() => {
                if is_rust {
                    out.push(std::mem::take(&mut cur));
                }
                open = None;
            }
            Some(_) => {
                cur.push_str(line);
                cur.push('\n');
            }
            None => {}
        }
    }
    out
}

fn coverage_number(cov: &str, key: &str) -> usize {
    let i = cov.find(&format!("\"{key}\": ")).unwrap_or_else(|| panic!("{key} in coverage.json"));
    cov[i + key.len() + 4..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().unwrap()
}

/// The per-kind item totals in `coverage.json` agree with an independent
/// `syn` parse of independently extracted blocks.
#[test]
fn item_kinds_match_independent_parse() {
    let l = layout();
    let lock = lock::parse(&std::fs::read_to_string(l.lock_path()).unwrap()).unwrap();
    let commit = lock.get("upstream", "commit").unwrap().to_string();
    let vroot = l.vendor_root(&commit);
    let mut kinds: BTreeMap<&'static str, usize> = BTreeMap::new();
    for rel in lock.section("files").keys().filter(|p| p.starts_with("spec/") && p.ends_with(".md")) {
        let md = std::fs::read_to_string(vroot.join(rel)).unwrap();
        for block in rust_fences(&md) {
            let file = syn::parse_file(&block).unwrap_or_else(|e| panic!("{rel}: {e}"));
            for item in &file.items {
                let k = match item {
                    syn::Item::Struct(_) => "struct",
                    syn::Item::Enum(_) => "enum",
                    syn::Item::Type(_) => "type",
                    syn::Item::Trait(_) => "trait",
                    syn::Item::Fn(_) => "fn",
                    syn::Item::Impl(_) => "impl",
                    syn::Item::Use(_) => "use",
                    syn::Item::Macro(_) => "macro",
                    _ => "other",
                };
                *kinds.entry(k).or_default() += 1;
            }
        }
    }
    let g = pipeline::generate(&l).unwrap();
    let cov = &g.files["coverage.json"];
    let section = &cov[cov.find("\"items_by_kind\"").unwrap()..];
    let section = &section[..section.find('}').unwrap()];
    for (k, n) in &kinds {
        assert_eq!(coverage_number(section, k), *n, "items of kind {k}");
    }
    assert!(!kinds.contains_key("other"), "unexpected item kinds: {kinds:?}");
}

/// Every opaque node reported in `coverage.json` is visible as an opaque
/// constructor in the generated Lean, and vice versa.
#[test]
fn opaque_nodes_are_reported() {
    let g = pipeline::generate(&layout()).unwrap();
    let cov = &g.files["coverage.json"];
    let section = &cov[cov.find("\"ast_nodes\"").unwrap()..];
    let opaque = coverage_number(section, "opaque");
    let mut opaque_in_lean = 0;
    for (rel, text) in &g.files {
        if rel.starts_with("lean/MiniRustSpec/Generated/Items/") {
            opaque_in_lean +=
                text.matches("AttrMeta.list").count() + text.matches("MacroBody.tokens").count() + text.matches(".verbatim").count();
        }
    }
    assert_eq!(opaque, opaque_in_lean, "opaque node count");
}
