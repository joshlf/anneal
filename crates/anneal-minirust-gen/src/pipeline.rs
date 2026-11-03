// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end generation: verify the vendored snapshot against the lock file,
//! translate every specification file, and write the Lean modules and the
//! coverage report.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::deep::{Coverage, Emitter, NodeCount};
use crate::lean::{Term, ident, string_lit};
use crate::lock::{self, Lock};
use crate::sha256::sha256_hex;
use crate::shallow::{self, ShallowStatus};
use crate::source::{self, SourceFile};

/// Lean namespace/module prefix of all generated declarations.
pub const GEN_MODULE: &str = "MiniRustSpec.Generated";
/// Namespace of shallowly embedded types.
pub const TYPES_NAMESPACE: &str = "MiniRustSpec.Gen";

const WIDTH: usize = 100;

fn lean_header(extra: &str) -> String {
    format!(
        "/-\nCopyright 2026 The Fuchsia Authors\n\nLicensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n\
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n\
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n\
This file may not be copied, modified, or distributed except according to\n\
those terms.\n\n\
GENERATED FILE -- DO NOT EDIT. Regenerate with\n\
`cargo run -p anneal-minirust-gen -- generate`.\n\
{extra}-/\n\n"
    )
}

/// Paths of the inputs and outputs, relative to the `minirust/` directory.
pub struct Layout {
    pub root: PathBuf,
}

impl Layout {
    pub fn lock_path(&self) -> PathBuf {
        self.root.join("minirust.lock.toml")
    }
    pub fn vendor_root(&self, commit: &str) -> PathBuf {
        self.root.join("vendor").join(commit)
    }
    pub fn generated_dir(&self) -> PathBuf {
        self.root.join("lean").join("MiniRustSpec").join("Generated")
    }
    pub fn generated_root_module(&self) -> PathBuf {
        self.root.join("lean").join("MiniRustSpec").join("Generated.lean")
    }
    pub fn coverage_path(&self) -> PathBuf {
        self.root.join("coverage.json")
    }
}

/// Checks that the vendored tree contains exactly the locked files with the
/// locked digests.
pub fn verify_vendor(layout: &Layout, lock: &Lock) -> Result<(), String> {
    let commit = lock.get("upstream", "commit")?;
    let vroot = layout.vendor_root(commit);
    let present = source::list_files(&vroot)?;
    let locked = lock.section("files");
    let locked_names: Vec<String> = locked.keys().cloned().collect();
    if present != locked_names {
        let extra: Vec<&String> = present.iter().filter(|p| !locked.contains_key(*p)).collect();
        let missing: Vec<&String> = locked_names.iter().filter(|p| !present.contains(p)).collect();
        return Err(format!("vendored tree does not match lock file: extra {extra:?}, missing {missing:?}"));
    }
    for (rel, want) in &locked {
        let got = sha256_hex(&std::fs::read(vroot.join(rel)).map_err(|e| format!("reading {rel}: {e}"))?);
        if &got != want {
            return Err(format!("vendored {rel} has sha256 {got}, lock file says {want}"));
        }
    }
    Ok(())
}

/// Everything produced by one generation run.
pub struct Generated {
    /// Output files: path relative to `minirust/` and contents.
    pub files: BTreeMap<String, String>,
    /// Human-readable coverage summary.
    pub summary: String,
}

struct FileReport {
    rel_path: String,
    module: String,
    sha256: String,
    rust_blocks: usize,
    skipped: Vec<(usize, String, String)>,
    items_by_kind: BTreeMap<&'static str, usize>,
    fn_count: usize,
    cov: Coverage,
}

fn item_kind(i: &syn::Item) -> &'static str {
    match i {
        syn::Item::Struct(_) => "struct",
        syn::Item::Enum(_) => "enum",
        syn::Item::Type(_) => "type",
        syn::Item::Trait(_) => "trait",
        syn::Item::Fn(_) => "fn",
        syn::Item::Impl(_) => "impl",
        syn::Item::Const(_) => "const",
        syn::Item::Use(_) => "use",
        syn::Item::Macro(_) => "macro",
        syn::Item::Static(_) => "static",
        syn::Item::Mod(_) => "mod",
        syn::Item::Union(_) => "union",
        _ => "other",
    }
}

fn count_fns(i: &syn::Item) -> usize {
    match i {
        syn::Item::Fn(_) => 1,
        syn::Item::Impl(im) => im.items.iter().filter(|x| matches!(x, syn::ImplItem::Fn(_))).count(),
        syn::Item::Trait(t) => t.items.iter().filter(|x| matches!(x, syn::TraitItem::Fn(_))).count(),
        _ => 0,
    }
}

fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn deep_module(file: &SourceFile, module: &str, cov: &mut Coverage, commit_short: &str) -> String {
    let mut em = Emitter::default();
    let mut out = lean_header(&format!(
        "\nDeep (syntax) embedding of every top-level item of upstream MiniRust\n\
`{}` (commit `{commit_short}`), one Lean definition per item, in source order.\n",
        file.rel_path
    ));
    out.push_str("import MiniRustSpec.Meta.Syntax\n\n");
    out.push_str("set_option maxRecDepth 100000\n\n");
    let ns = format!("MiniRustSpec.Gen.Items.{}", file.module_components().join("."));
    let _ = module;
    writeln!(out, "namespace {ns}\n").unwrap();
    out.push_str("open MiniRustSpec.Syntax\n\n");
    writeln!(out, "/-- Path of the upstream file these items were extracted from. -/").unwrap();
    writeln!(out, "def sourceFile : String := {}\n", string_lit(&file.rel_path)).unwrap();
    writeln!(out, "/-- SHA-256 of the upstream file. -/").unwrap();
    writeln!(out, "def sourceSha256 : String := {}\n", string_lit(&file.sha256)).unwrap();
    for it in &file.items {
        let term = em.item(&it.item);
        writeln!(out, "/-- `{}:{}` -/", file.rel_path, it.line).unwrap();
        writeln!(out, "def {} : Item :=\n  {}\n", ident(&it.name), term.render(2, WIDTH)).unwrap();
    }
    let entries: Vec<Term> = file
        .items
        .iter()
        .map(|it| {
            Term::app(
                "SourceItem.mk",
                vec![Term::str(&it.name), Term::nat(it.line as u128), Term::str(&it.token_sha256), Term::atom(ident(&it.name))],
            )
        })
        .collect();
    writeln!(out, "/-- All items of `{}`, in source order, with provenance. -/", file.rel_path).unwrap();
    writeln!(out, "def items : List SourceItem :=\n  {}\n", Term::List(entries).render(2, WIDTH)).unwrap();
    writeln!(out, "end {ns}").unwrap();
    cov.merge(&em.cov);
    out
}

/// Runs the translation in memory.
pub fn generate(layout: &Layout) -> Result<Generated, String> {
    let lock_text = std::fs::read_to_string(layout.lock_path()).map_err(|e| format!("reading lock file: {e}"))?;
    let lock = lock::parse(&lock_text)?;
    verify_vendor(layout, &lock)?;
    let commit = lock.get("upstream", "commit")?.to_string();
    let commit_short = &commit[..8.min(commit.len())];
    let vroot = layout.vendor_root(&commit);
    let spec_files: Vec<String> = lock
        .section("files")
        .keys()
        .filter(|p| p.starts_with("spec/") && p.ends_with(".md"))
        .cloned()
        .collect();
    let mut sources = Vec::new();
    for rel in &spec_files {
        sources.push(source::load_file(&vroot, rel)?);
    }
    // Module names must be unique after CamelCasing.
    let mut modules: BTreeMap<String, String> = BTreeMap::new();
    for s in &sources {
        let m = format!("{GEN_MODULE}.Items.{}", s.module_components().join("."));
        if let Some(prev) = modules.insert(m.clone(), s.rel_path.clone()) {
            return Err(format!("module name collision: {prev} and {} both map to {m}", s.rel_path));
        }
    }

    let mut files: BTreeMap<String, String> = BTreeMap::new();
    let mut reports = Vec::new();
    for s in &sources {
        let module = format!("{GEN_MODULE}.Items.{}", s.module_components().join("."));
        let mut cov = Coverage::default();
        let text = deep_module(s, &module, &mut cov, commit_short);
        let rel = format!("lean/{}.lean", module.replace('.', "/"));
        files.insert(rel, text);
        let mut items_by_kind = BTreeMap::new();
        let mut fn_count = 0;
        for it in &s.items {
            *items_by_kind.entry(item_kind(&it.item)).or_default() += 1;
            fn_count += count_fns(&it.item);
        }
        reports.push(FileReport {
            rel_path: s.rel_path.clone(),
            module,
            sha256: s.sha256.clone(),
            rust_blocks: s.rust_blocks,
            skipped: s.skipped.iter().map(|b| (b.line, b.info.clone(), b.reason.clone())).collect(),
            items_by_kind,
            fn_count,
            cov,
        });
    }

    // Shallow types.
    let sh = shallow::translate(&sources, commit_short);
    let mut types = lean_header(&format!(
        "\nShallow embedding of MiniRust data definitions (commit `{commit_short}`):\n\
every `struct`, `enum`, and `type` alias becomes a Lean `structure`, `inductive`,\n\
or `abbrev`; traits become classes of their associated types and trait impls\n\
the matching instances. See `crates/anneal-minirust-gen/src/shallow.rs` for the\n\
mapping rules and `minirust/coverage.json` for items that are not shallowly\n\
embedded (with reasons).\n"
    ));
    types.push_str("import MiniRustSpec.Meta.LibSpecr\n\n");
    writeln!(types, "namespace {TYPES_NAMESPACE}\n").unwrap();
    types.push_str("open MiniRustSpec\n\n");
    types.push_str(&sh.lean);
    writeln!(types, "end {TYPES_NAMESPACE}").unwrap();
    files.insert(format!("lean/{}.lean", format!("{GEN_MODULE}.Types").replace('.', "/")), types);

    // Manifest: pins and per-file digests as Lean data.
    let mut manifest = lean_header("\nPins and input digests of this generation run, as Lean data.\n");
    manifest.push_str("import MiniRustSpec.Meta.Syntax\n\n");
    writeln!(manifest, "namespace {GEN_MODULE}.Manifest\n").unwrap();
    for (section, key, lean_name) in [
        ("upstream", "repository", "upstreamRepository"),
        ("upstream", "commit", "upstreamCommit"),
        ("upstream", "tarball_sha256", "upstreamTarballSha256"),
        ("upstream", "upstream_rust_toolchain", "upstreamRustToolchain"),
        ("upstream", "upstream_libspecr", "upstreamLibspecr"),
        ("anneal", "rustc_dialect", "annealRustcDialect"),
        ("anneal", "rustc_version", "annealRustcVersion"),
        ("anneal", "lean_toolchain", "leanToolchain"),
    ] {
        writeln!(manifest, "def {lean_name} : String := {}\n", string_lit(lock.get(section, key)?)).unwrap();
    }
    let file_entries: Vec<Term> = lock
        .section("files")
        .iter()
        .map(|(k, v)| Term::app("Prod.mk", vec![Term::str(k), Term::str(v)]))
        .collect();
    writeln!(
        manifest,
        "/-- Every vendored upstream file and its SHA-256, as checked against\n`minirust/minirust.lock.toml` before generation. -/\ndef vendoredFiles : List (String × String) :=\n  {}\n",
        Term::List(file_entries).render(2, WIDTH)
    )
    .unwrap();
    writeln!(manifest, "end {GEN_MODULE}.Manifest").unwrap();
    files.insert(format!("lean/{}.lean", format!("{GEN_MODULE}.Manifest").replace('.', "/")), manifest);

    // Root module.
    let mut root = lean_header("\nRoot of the generated MiniRust model.\n");
    writeln!(root, "import {GEN_MODULE}.Manifest").unwrap();
    writeln!(root, "import {GEN_MODULE}.Types").unwrap();
    for r in &reports {
        writeln!(root, "import {}", r.module).unwrap();
    }
    root.push('\n');
    writeln!(root, "namespace {GEN_MODULE}\n").unwrap();
    root.push_str("open MiniRustSpec.Syntax\n\n");
    let all: Vec<Term> = reports
        .iter()
        .map(|r| {
            let ns = format!("MiniRustSpec.Gen.Items.{}", r.module.trim_start_matches(&format!("{GEN_MODULE}.Items.")));
            Term::app("Prod.mk", vec![Term::str(&r.rel_path), Term::atom(format!("{ns}.items"))])
        })
        .collect();
    writeln!(
        root,
        "/-- Every translated upstream specification file with its items. -/\ndef allFiles : List (String × List SourceItem) :=\n  {}\n",
        Term::List(all).render(2, WIDTH)
    )
    .unwrap();
    writeln!(root, "end {GEN_MODULE}").unwrap();
    files.insert("lean/MiniRustSpec/Generated.lean".to_string(), root);

    // Coverage report.
    let (json, summary) = coverage(&lock, &reports, &sh.statuses);
    files.insert("coverage.json".to_string(), json);
    Ok(Generated { files, summary })
}

fn coverage(lock: &Lock, reports: &[FileReport], statuses: &[ShallowStatus]) -> (String, String) {
    let mut total = Coverage::default();
    for r in reports {
        total.merge(&r.cov);
    }
    let t: NodeCount = total.totals();
    let mut kinds_total: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut fns = 0;
    let mut blocks = 0;
    for r in reports {
        for (k, v) in &r.items_by_kind {
            *kinds_total.entry(k).or_default() += v;
        }
        fns += r.fn_count;
        blocks += r.rust_blocks;
    }
    let shallow_ok = statuses.iter().filter(|s| s.skipped.is_none()).count();
    let shallow_total = statuses.len();

    let mut j = String::from("{\n");
    writeln!(j, "  \"upstream_commit\": {},", json_str(lock.get("upstream", "commit").unwrap_or(""))).unwrap();
    writeln!(j, "  \"anneal_rustc_dialect\": {},", json_str(lock.get("anneal", "rustc_dialect").unwrap_or(""))).unwrap();
    writeln!(j, "  \"spec_files\": {},", reports.len()).unwrap();
    writeln!(j, "  \"rust_blocks\": {blocks},").unwrap();
    writeln!(j, "  \"items_by_kind\": {{{}}},", kinds_total.iter().map(|(k, v)| format!("{}: {v}", json_str(k))).collect::<Vec<_>>().join(", ")).unwrap();
    writeln!(j, "  \"functions_and_methods\": {fns},").unwrap();
    writeln!(j, "  \"ast_nodes\": {{\"structural\": {}, \"opaque\": {}}},", t.structural, t.opaque).unwrap();
    writeln!(j, "  \"ast_node_kinds\": {{").unwrap();
    let kinds: Vec<String> = total
        .kinds
        .iter()
        .map(|(k, v)| format!("    {}: {{\"structural\": {}, \"opaque\": {}}}", json_str(k), v.structural, v.opaque))
        .collect();
    writeln!(j, "{}", kinds.join(",\n")).unwrap();
    writeln!(j, "  }},").unwrap();
    writeln!(j, "  \"shallow_types\": {{\"translated\": {shallow_ok}, \"candidates\": {shallow_total}, \"items\": [").unwrap();
    let st: Vec<String> = statuses
        .iter()
        .map(|s| {
            format!(
                "    {{\"file\": {}, \"line\": {}, \"item\": {}, \"kind\": {}, \"status\": {}}}",
                json_str(&s.file),
                s.line,
                json_str(&s.item),
                json_str(s.kind),
                match &s.skipped {
                    None => json_str("translated"),
                    Some(r) => json_str(&format!("not translated: {r}")),
                }
            )
        })
        .collect();
    writeln!(j, "{}", st.join(",\n")).unwrap();
    writeln!(j, "  ]}},").unwrap();
    writeln!(j, "  \"files\": [").unwrap();
    let fs: Vec<String> = reports
        .iter()
        .map(|r| {
            let c = r.cov.totals();
            format!(
                "    {{\"path\": {}, \"sha256\": {}, \"lean_module\": {}, \"rust_blocks\": {}, \"skipped_blocks\": [{}], \"items_by_kind\": {{{}}}, \"functions_and_methods\": {}, \"ast_nodes\": {{\"structural\": {}, \"opaque\": {}}}}}",
                json_str(&r.rel_path),
                json_str(&r.sha256),
                json_str(&r.module),
                r.rust_blocks,
                r.skipped.iter().map(|(l, i, why)| format!("{{\"line\": {l}, \"info\": {}, \"reason\": {}}}", json_str(i), json_str(why))).collect::<Vec<_>>().join(", "),
                r.items_by_kind.iter().map(|(k, v)| format!("{}: {v}", json_str(k))).collect::<Vec<_>>().join(", "),
                r.fn_count,
                c.structural,
                c.opaque
            )
        })
        .collect();
    writeln!(j, "{}", fs.join(",\n")).unwrap();
    writeln!(j, "  ]").unwrap();
    j.push_str("}\n");

    let mut s = String::new();
    writeln!(s, "MiniRust -> Lean mechanical translation coverage").unwrap();
    writeln!(s, "  upstream commit      : {}", lock.get("upstream", "commit").unwrap_or("?")).unwrap();
    writeln!(s, "  spec files consumed  : {} ({} `rust` blocks, {} non-`rust` blocks reported)", reports.len(), blocks, reports.iter().map(|r| r.skipped.len()).sum::<usize>()).unwrap();
    writeln!(s, "  top-level items      : {} ({})", kinds_total.values().sum::<usize>(), kinds_total.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join(", ")).unwrap();
    writeln!(s, "  fns + methods        : {fns} (all deep-embedded)").unwrap();
    let pct = if t.structural + t.opaque == 0 { 100.0 } else { 100.0 * t.structural as f64 / (t.structural + t.opaque) as f64 };
    writeln!(s, "  AST nodes            : {} structural, {} opaque ({pct:.3}% structural)", t.structural, t.opaque).unwrap();
    for (k, v) in &total.kinds {
        if v.opaque > 0 {
            writeln!(s, "    opaque {k:<28}: {}", v.opaque).unwrap();
        }
    }
    writeln!(s, "  shallow data types   : {shallow_ok}/{shallow_total} candidates translated").unwrap();
    for st in statuses.iter().filter(|s| s.skipped.is_some()) {
        writeln!(s, "    not shallow: {}:{} {} `{}`: {}", st.file, st.line, st.kind, st.item, st.skipped.as_ref().unwrap()).unwrap();
    }
    writeln!(s, "  per file (path: blocks, items, fns, structural/opaque nodes):").unwrap();
    for r in reports {
        let c = r.cov.totals();
        writeln!(s, "    {}: {}, {}, {}, {}/{}", r.rel_path, r.rust_blocks, r.items_by_kind.values().sum::<usize>(), r.fn_count, c.structural, c.opaque).unwrap();
    }
    (j, s)
}

/// Writes generated files under `layout.root`, first deleting every file in
/// the generated Lean directory so that stale modules cannot survive.
pub fn write(layout: &Layout, g: &Generated) -> Result<(), String> {
    let gen_dir = layout.generated_dir();
    if gen_dir.exists() {
        std::fs::remove_dir_all(&gen_dir).map_err(|e| format!("removing {}: {e}", gen_dir.display()))?;
    }
    for (rel, text) in &g.files {
        let p = layout.root.join(rel);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).map_err(|e| format!("creating {}: {e}", parent.display()))?;
        }
        std::fs::write(&p, text).map_err(|e| format!("writing {}: {e}", p.display()))?;
    }
    Ok(())
}

/// Copies the pinned subset of an upstream tarball into `vendor/<commit>/`
/// and writes the lock file.
pub fn vendor(
    layout: &Layout,
    tarball: &Path,
    meta: &BTreeMap<String, String>,
) -> Result<String, String> {
    let commit = meta.get("commit").ok_or("missing --commit")?.clone();
    let bytes = std::fs::read(tarball).map_err(|e| format!("reading tarball: {e}"))?;
    let tar_sha = sha256_hex(&bytes);
    let tmp = std::env::temp_dir().join(format!("anneal-minirust-gen-{}-{}", commit, std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).map_err(|e| e.to_string())?;
    let status = std::process::Command::new("tar")
        .arg("-xzf")
        .arg(tarball)
        .arg("-C")
        .arg(&tmp)
        .status()
        .map_err(|e| format!("running tar: {e}"))?;
    if !status.success() {
        return Err("tar failed".into());
    }
    let tar_root = tmp.join(format!("minirust-{commit}"));
    if !tar_root.is_dir() {
        return Err(format!("tarball does not contain minirust-{commit}/"));
    }
    let all = source::list_files(&tar_root)?;
    // `spec/` is the translator's input. `tooling/minimize/src/` is vendored
    // (but not translated) because the Lean correspondence transcribes and
    // quotes MiniRust's MIR-to-MiniRust translator, and the quotation test
    // (`tests/quotes.rs`) checks those quotes against it.
    let keep = |p: &str| -> bool {
        p.starts_with("spec/")
            || p.starts_with("tooling/minimize/src/")
            || matches!(p, "LICENSE-APACHE" | "LICENSE-MIT" | "README.md" | "specr.toml" | "rust-toolchain.toml" | "tooling/Cargo.lock")
    };
    let vroot = layout.vendor_root(&commit);
    if vroot.exists() {
        std::fs::remove_dir_all(&vroot).map_err(|e| e.to_string())?;
    }
    let mut file_hashes = Vec::new();
    for rel in all.iter().filter(|p| keep(p)) {
        let src = tar_root.join(rel);
        let dst = vroot.join(rel);
        std::fs::create_dir_all(dst.parent().unwrap()).map_err(|e| e.to_string())?;
        let data = std::fs::read(&src).map_err(|e| e.to_string())?;
        std::fs::write(&dst, &data).map_err(|e| e.to_string())?;
        file_hashes.push((rel.clone(), sha256_hex(&data)));
    }
    let toolchain = std::fs::read_to_string(tar_root.join("rust-toolchain.toml")).unwrap_or_default();
    let channel = toolchain
        .lines()
        .find_map(|l| l.trim().strip_prefix("channel").map(|r| r.trim().trim_start_matches('=').trim().trim_matches('"').to_string()))
        .unwrap_or_default();
    let cargo_lock = std::fs::read_to_string(tar_root.join("tooling/Cargo.lock")).unwrap_or_default();
    let mut libspecr = String::new();
    let mut lines = cargo_lock.lines();
    while let Some(l) = lines.next() {
        if l.trim() == "name = \"libspecr\"" {
            if let Some(v) = lines.next() {
                libspecr = v.trim().trim_start_matches("version = ").trim_matches('"').to_string();
            }
        }
    }
    let _ = std::fs::remove_dir_all(&tmp);
    let get = |k: &str| meta.get(k).cloned().unwrap_or_default();
    let upstream = vec![
        ("repository".to_string(), "https://github.com/minirust/minirust".to_string()),
        ("commit".to_string(), commit.clone()),
        ("commit_date".to_string(), get("commit_date")),
        ("commit_subject".to_string(), get("commit_subject")),
        ("tarball_url".to_string(), format!("https://codeload.github.com/minirust/minirust/tar.gz/{commit}")),
        ("tarball_sha256".to_string(), tar_sha),
        ("upstream_rust_toolchain".to_string(), channel),
        ("upstream_libspecr".to_string(), libspecr),
    ];
    let anneal = vec![
        ("rustc_dialect".to_string(), "V2026_06_01".to_string()),
        ("rustc_version".to_string(), "rustc 1.98.0-nightly (14210df0e 2026-05-31)".to_string()),
        ("rustc_commit".to_string(), "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65".to_string()),
        ("rust_toolchain".to_string(), "nightly-2026-06-01".to_string()),
        ("lean_toolchain".to_string(), "leanprover/lean4:v4.34.1".to_string()),
    ];
    let header = "Pinned upstream MiniRust snapshot consumed by `crates/anneal-minirust-gen`.\n\n\
Written by `cargo run -p anneal-minirust-gen -- vendor`; `generate` refuses to\n\
run unless `vendor/<commit>/` matches the `[files]` digests exactly.\n\n\
`[upstream]` pins the MiniRust commit and the tarball it was extracted from.\n\
`[anneal]` pins the `rustc` dialect of Anneal's MIR model\n\
(`Trusted.Rustc.V2026_06_01`) that the correspondence theorem targets. The\n\
upstream MiniRust tooling (`upstream_rust_toolchain`) targets a different\n\
nightly than Anneal's dialect; see `minirust/README.md` for the consequences.";
    let text = lock::render(header, &[("upstream", upstream), ("anneal", anneal), ("files", file_hashes)]);
    std::fs::write(layout.lock_path(), &text).map_err(|e| e.to_string())?;
    Ok(text)
}

/// Re-extracts `tarball` and checks that it hashes to the locked digest and
/// that every vendored file is byte-identical to the tarball's copy.
pub fn verify_tarball(layout: &Layout, tarball: &Path) -> Result<String, String> {
    let lock = lock::parse(&std::fs::read_to_string(layout.lock_path()).map_err(|e| e.to_string())?)?;
    let commit = lock.get("upstream", "commit")?;
    let bytes = std::fs::read(tarball).map_err(|e| format!("reading tarball: {e}"))?;
    let got = sha256_hex(&bytes);
    let want = lock.get("upstream", "tarball_sha256")?;
    if got != want {
        return Err(format!("tarball sha256 {got} != locked {want}"));
    }
    let tmp = std::env::temp_dir().join(format!("anneal-minirust-verify-{}-{}", commit, std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).map_err(|e| e.to_string())?;
    let status = std::process::Command::new("tar").arg("-xzf").arg(tarball).arg("-C").arg(&tmp).status().map_err(|e| e.to_string())?;
    if !status.success() {
        return Err("tar failed".into());
    }
    let tar_root = tmp.join(format!("minirust-{commit}"));
    let vroot = layout.vendor_root(commit);
    let mut n = 0;
    for (rel, _) in lock.section("files") {
        let a = std::fs::read(tar_root.join(&rel)).map_err(|e| format!("tarball lacks {rel}: {e}"))?;
        let b = std::fs::read(vroot.join(&rel)).map_err(|e| format!("vendor lacks {rel}: {e}"))?;
        if a != b {
            return Err(format!("{rel} differs between tarball and vendor/"));
        }
        n += 1;
    }
    let _ = std::fs::remove_dir_all(&tmp);
    Ok(format!("tarball sha256 {got} matches lock; {n} vendored files byte-identical to tarball minirust-{commit}/"))
}
