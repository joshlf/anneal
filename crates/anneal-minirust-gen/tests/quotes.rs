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

fn corpus() -> Vec<(String, String)> {
    let lock = anneal_minirust_gen::lock::parse(&std::fs::read_to_string(minirust_dir().join("minirust.lock.toml")).unwrap()).unwrap();
    let commit = lock.get("upstream", "commit").unwrap().to_string();
    let vroot = minirust_dir().join("vendor").join(commit);
    let mut files = Vec::new();
    walk(&vroot.join("spec"), &mut files);
    walk(&vroot.join("tooling").join("minimize").join("src"), &mut files);
    files.push(vroot.join("README.md"));
    files
        .into_iter()
        .map(|f| {
            let rel = f.strip_prefix(&vroot).unwrap().to_string_lossy().replace('\\', "/");
            let text = std::fs::read_to_string(&f).unwrap();
            (rel, squash(&strip_line_comments(&text)))
        })
        .collect()
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

/// Checks that `quote` occurs in order within at least one single vendored file.
/// If no single vendored file matches all pieces of `quote` in order, returns
/// the first unmatched piece from the file that matched the longest prefix.
fn missing_piece(corpus: &[(String, String)], quote: &str) -> Option<String> {
    let pieces: Vec<String> = strip_line_comments(quote)
        .split("..")
        .map(squash)
        .filter(|p| !p.is_empty())
        .collect();
    if pieces.is_empty() {
        return Some("<empty quote>".to_string());
    }
    let mut best_matched = 0usize;
    let mut best_missing: Option<String> = None;
    for (_path, file_text) in corpus {
        let mut pos = 0;
        let mut matched = 0;
        let mut failed = None;
        for piece in &pieces {
            match file_text[pos..].find(piece.as_str()) {
                Some(j) => {
                    pos += j + piece.len();
                    matched += 1;
                }
                None => {
                    failed = Some(piece.clone());
                    break;
                }
            }
        }
        if failed.is_none() {
            return None;
        }
        if matched >= best_matched {
            best_matched = matched;
            best_missing = failed;
        }
    }
    best_missing.or_else(|| pieces.into_iter().next())
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
    // Fabricated short token (< 4 chars) between elisions.
    assert!(missing_piece(&corpus, "Add => left + right, .. ??? .. Sub => left - right,").is_some());
    // Cross-file splice (operators.md followed by terminators.md).
    assert!(missing_piece(
        &corpus,
        "Add => left + right, .. fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult"
    )
    .is_some());
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
