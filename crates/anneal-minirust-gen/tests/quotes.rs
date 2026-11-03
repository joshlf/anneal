// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The hand-written Lean development (`minirust/lean/`, outside the generated
//! modules) justifies its definitions by quoting upstream MiniRust code in
//! doc-comment block quotes (`> "..."`). This test checks every such quote
//! against the vendored upstream sources (`spec/**/*.md`,
//! `tooling/minimize/src/**/*.rs`, `README.md`), so that a transcription
//! cannot cite code that upstream does not contain.
//!
//! Comparison rules, chosen to tolerate only formatting: `//` comments are
//! dropped on both sides, all whitespace is ignored, `\"` in a quote stands
//! for `"`, and `..` in a quote elides upstream code (the pieces between
//! elisions must occur in order).

use std::path::{Path, PathBuf};

fn minirust_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("minirust")
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            walk(&p, out);
        } else {
            out.push(p);
        }
    }
}

/// Drops `//` comments that do not start inside a string literal.
fn strip_line_comments(text: &str) -> String {
    let mut out = String::new();
    for line in text.lines() {
        let bytes = line.as_bytes();
        let mut in_str = false;
        let mut cut = bytes.len();
        let mut i = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'\\' if in_str => i += 1,
                b'"' => in_str = !in_str,
                b'/' if !in_str && bytes.get(i + 1) == Some(&b'/') => {
                    cut = i;
                    break;
                }
                _ => {}
            }
            i += 1;
        }
        out.push_str(&line[..cut]);
        out.push('\n');
    }
    out
}

fn squash(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

fn corpus() -> String {
    let lock = anneal_minirust_gen::lock::parse(&std::fs::read_to_string(minirust_dir().join("minirust.lock.toml")).unwrap()).unwrap();
    let commit = lock.get("upstream", "commit").unwrap().to_string();
    let vroot = minirust_dir().join("vendor").join(commit);
    let mut files = Vec::new();
    walk(&vroot.join("spec"), &mut files);
    walk(&vroot.join("tooling").join("minimize").join("src"), &mut files);
    files.push(vroot.join("README.md"));
    let mut text = String::new();
    for f in files {
        text.push_str(&std::fs::read_to_string(&f).unwrap());
        text.push('\n');
    }
    squash(&strip_line_comments(&text))
}

/// Every block quote of `lean`: its first line number and the quoted text.
fn quotes(lean: &str) -> Vec<(usize, String)> {
    let mut blocks: Vec<(usize, String)> = Vec::new();
    let mut cur: Option<(usize, String)> = None;
    for (i, line) in lean.lines().enumerate() {
        match line.trim_start().strip_prefix('>') {
            Some(rest) => {
                let c = cur.get_or_insert((i + 1, String::new()));
                c.1.push_str(rest);
                c.1.push('\n');
            }
            None => blocks.extend(cur.take()),
        }
    }
    blocks.extend(cur.take());
    blocks
        .into_iter()
        .filter_map(|(line, b)| {
            let start = b.find('"')?;
            let bytes = b.as_bytes();
            let end = (start + 1..bytes.len()).rev().find(|&i| bytes[i] == b'"' && bytes[i - 1] != b'\\')?;
            Some((line, b[start + 1..end].replace("\\\"", "\"")))
        })
        .collect()
}

/// The first piece of `quote` that does not occur (in order) in `corpus`.
fn missing_piece(corpus: &str, quote: &str) -> Option<String> {
    let mut pos = 0;
    for piece in strip_line_comments(quote).split("..") {
        let piece = squash(piece);
        if piece.chars().count() < 4 {
            continue;
        }
        match corpus[pos..].find(&piece) {
            Some(j) => pos += j + piece.len(),
            None => return Some(piece),
        }
    }
    None
}

#[test]
fn quotations_occur_upstream() {
    let corpus = corpus();
    let lean_root = minirust_dir().join("lean");
    let mut files = Vec::new();
    walk(&lean_root, &mut files);
    let generated = lean_root.join("MiniRustSpec").join("Generated");
    let mut total = 0;
    let mut failures = Vec::new();
    for f in files {
        if f.starts_with(&generated) || f.file_name().unwrap() == "Generated.lean" || f.extension().unwrap_or_default() != "lean" {
            continue;
        }
        let text = std::fs::read_to_string(&f).unwrap();
        for (line, q) in quotes(&text) {
            total += 1;
            if let Some(piece) = missing_piece(&corpus, &q) {
                failures.push(format!("{}:{line}: not found upstream: {piece}", f.display()));
            }
        }
    }
    assert!(failures.is_empty(), "{} of {total} quotations do not occur upstream:\n{}", failures.len(), failures.join("\n"));
    // The interpretation and the translation quote dozens of upstream items;
    // a sudden drop means the extraction above broke.
    assert!(total >= 40, "only {total} quotations found");
}

#[test]
fn fabricated_quotations_are_rejected() {
    let corpus = corpus();
    // Genuine, with an elision.
    assert_eq!(missing_piece(&corpus, "Add => left + right, .. Sub => left - right,"), None);
    // Altered operator.
    assert!(missing_piece(&corpus, "Add => left - right,").is_some());
    // Reordered pieces (each occurs exactly once upstream, `Goto` first).
    assert_eq!(
        missing_piece(
            &corpus,
            "fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult .. \
             fn eval_terminator(&mut self, Terminator::Return: Terminator) -> NdResult"
        ),
        None
    );
    assert!(missing_piece(
        &corpus,
        "fn eval_terminator(&mut self, Terminator::Return: Terminator) -> NdResult .. \
         fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult"
    )
    .is_some());
}
