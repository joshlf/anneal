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
//! against the vendored upstream file(s) cited by its enclosing doc comment or
//! section header (`spec/**/*.md`, `tooling/minimize/src/**/*.rs`, `README.md`),
//! so that a transcription can neither cite code that upstream does not contain
//! nor attribute code from one vendored file to another.
//!
//! Comparison rules, chosen to tolerate only formatting: `//` comments are
//! dropped on both sides, all whitespace is ignored, `\"` and `\\` in a quote
//! unescape to `"` and `\`, and `..` in a quote elides upstream code (the
//! pieces between elisions must occur in order within a single cited file).

use std::collections::BTreeSet;
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

/// If `text[i..]` begins a Rust/Lean character literal (`'c'`, `'α'`, `'\n'`,
/// `'\x22'`, `'\u{22}'`, etc., as opposed to a Rust lifetime `'a`), returns the
/// byte index strictly past the closing `'`.
fn skip_char_literal(text: &str, i: usize) -> Option<usize> {
    let rest = text.get(i..)?.strip_prefix('\'')?;
    let mut chars = rest.char_indices();
    let (_, first) = chars.next()?;
    match first {
        '\n' | '\r' | '\'' => None,
        '\\' => {
            let (_, esc) = chars.next()?;
            if esc == '\n' || esc == '\r' {
                return None;
            }
            for (step, (off, ch)) in chars.enumerate() {
                if step > 12 || ch == '\n' || ch == '\r' {
                    return None;
                }
                if ch == '\'' {
                    return Some(i + 1 + off + 1);
                }
            }
            None
        }
        _ => match chars.next() {
            Some((off, '\'')) => Some(i + 1 + off + 1),
            _ => None,
        },
    }
}

/// Drops `//` comments that do not start inside a string or character literal.
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
                b'\'' if !in_str => {
                    if let Some(next_i) = skip_char_literal(line, i) {
                        i = next_i;
                        continue;
                    }
                }
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
    let lock = anneal_minirust_gen::lock::parse(
        &std::fs::read_to_string(minirust_dir().join("minirust.lock.toml")).unwrap(),
    )
    .unwrap();
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

#[derive(Debug)]
struct DocComment {
    start_line: usize,
    is_module_doc: bool,
    body: String,
}

/// Extracts all Lean doc comments (`/-! ... -/` and `/-- ... -/`), respecting
/// nested `/- ... -/` block comments, `--` line comments, character literals,
/// and string literals.
fn doc_comments(lean: &str) -> Vec<DocComment> {
    let bytes = lean.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    let mut line = 1usize;
    while i < bytes.len() {
        match bytes[i] {
            b'\n' => {
                line += 1;
                i += 1;
            }
            b'\'' => {
                if let Some(next_i) = skip_char_literal(lean, i) {
                    i = next_i;
                } else {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\n' {
                        line += 1;
                    }
                    if bytes[i] == b'\\' {
                        if bytes.get(i + 1) == Some(&b'\n') {
                            line += 1;
                        }
                        i += 2;
                        continue;
                    }
                    if bytes[i] == b'"' {
                        i += 1;
                        break;
                    }
                    i += 1;
                }
            }
            b'-' if bytes.get(i + 1) == Some(&b'-') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if bytes.get(i + 1) == Some(&b'-') => {
                let start_line = line;
                let third = bytes.get(i + 2).copied();
                let is_doc = matches!(third, Some(b'!' | b'-')) && bytes.get(i + 3) != Some(&b'/');
                let is_module_doc = third == Some(b'!');
                let body_start = if is_doc { i + 3 } else { i + 2 };
                i = body_start;
                let mut depth = 1usize;
                let mut body_end = bytes.len();
                while i < bytes.len() && depth > 0 {
                    if bytes[i] == b'\n' {
                        line += 1;
                        i += 1;
                    } else if bytes[i] == b'/' && bytes.get(i + 1) == Some(&b'-') {
                        depth += 1;
                        i += 2;
                    } else if bytes[i] == b'-' && bytes.get(i + 1) == Some(&b'/') {
                        depth -= 1;
                        if depth == 0 {
                            body_end = i;
                        }
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                if is_doc {
                    out.push(DocComment {
                        start_line,
                        is_module_doc,
                        body: lean[body_start..body_end].to_string(),
                    });
                }
            }
            _ => i += 1,
        }
    }
    out
}

/// Parses every `"..."` literal from a contiguous `>` block-quote region,
/// returning `(line, unescaped_quote)` or an error message if the block has no
/// string literal or an unterminated string literal. Also returns any text
/// outside `"..."` literals in the block so trailing `` (`path`) `` citations on
/// block-quote lines are visible to path extraction.
fn parse_blockquote_literals(
    start_line: usize,
    block: &str,
) -> Result<(Vec<(usize, String)>, String), (usize, String)> {
    let mut quotes = Vec::new();
    let mut outside = String::new();
    let chars: Vec<char> = block.chars().collect();
    let mut i = 0usize;
    let mut line = start_line;
    while i < chars.len() {
        let c = chars[i];
        if c == '"' {
            let q_line = line;
            i += 1;
            let mut buf = String::new();
            let mut closed = false;
            while i < chars.len() {
                match chars[i] {
                    '\n' => {
                        line += 1;
                        buf.push('\n');
                        i += 1;
                    }
                    '\\' => {
                        if let Some(&next) = chars.get(i + 1) {
                            if next == '\n' {
                                line += 1;
                            }
                            match next {
                                '"' => buf.push('"'),
                                '\\' => buf.push('\\'),
                                other => {
                                    buf.push('\\');
                                    buf.push(other);
                                }
                            }
                            i += 2;
                        } else {
                            break;
                        }
                    }
                    '"' => {
                        closed = true;
                        i += 1;
                        break;
                    }
                    other => {
                        buf.push(other);
                        i += 1;
                    }
                }
            }
            if !closed {
                return Err((q_line, "unterminated `\"` in block quote".to_string()));
            }
            quotes.push((q_line, buf));
        } else {
            if c == '\n' {
                line += 1;
            }
            outside.push(c);
            i += 1;
        }
    }
    if quotes.is_empty() {
        return Err((start_line, "block quote `>` contains no quoted `\"...\"` snippet".to_string()));
    }
    Ok((quotes, outside))
}

fn extract_backticked_corpus_paths(text: &str, valid_paths: &BTreeSet<String>) -> Vec<String> {
    let mut found = Vec::new();
    let mut rest = text;
    while let Some(open) = rest.find('`') {
        rest = &rest[open + 1..];
        let Some(close) = rest.find('`') else { break };
        let span = &rest[..close];
        if valid_paths.contains(span) && !found.iter().any(|p| p == span) {
            found.push(span.to_string());
        }
        rest = &rest[close + 1..];
    }
    found
}

#[derive(Debug, PartialEq, Eq)]
struct ExtractedQuote {
    line: usize,
    text: String,
    cited_file: String,
}

enum DocSegment {
    Prose(String),
    Block(usize, String),
}

/// Extracts every doc-comment block quote in `lean` together with the single
/// vendored file path cited immediately before (or on) that block quote, or by
/// the enclosing `/-! ## ... -/` section header.
fn extract_quotes(
    lean: &str,
    valid_paths: &BTreeSet<String>,
) -> Result<Vec<ExtractedQuote>, Vec<(usize, String)>> {
    let mut out = Vec::new();
    let mut errs = Vec::new();
    let mut section_path: Option<String> = None;

    for doc in doc_comments(lean) {
        if doc.is_module_doc && doc.body.trim_start().starts_with('#') {
            let hdr_paths = extract_backticked_corpus_paths(&doc.body, valid_paths);
            section_path = if hdr_paths.len() == 1 {
                Some(hdr_paths[0].clone())
            } else {
                None
            };
        }

        let mut segments: Vec<DocSegment> = Vec::new();
        let mut cur_prose = String::new();
        let mut cur_block: Option<(usize, String)> = None;
        for (idx, line) in doc.body.split('\n').enumerate() {
            let line_no = doc.start_line + idx;
            match line.trim_start().strip_prefix('>') {
                Some(rest) => {
                    if !cur_prose.is_empty() {
                        segments.push(DocSegment::Prose(std::mem::take(&mut cur_prose)));
                    }
                    let c = cur_block.get_or_insert((line_no, String::new()));
                    c.1.push_str(rest);
                    c.1.push('\n');
                }
                None => {
                    if let Some((b_line, b_text)) = cur_block.take() {
                        segments.push(DocSegment::Block(b_line, b_text));
                    }
                    cur_prose.push_str(line);
                    cur_prose.push('\n');
                }
            }
        }
        if let Some((b_line, b_text)) = cur_block.take() {
            segments.push(DocSegment::Block(b_line, b_text));
        }
        if !cur_prose.is_empty() {
            segments.push(DocSegment::Prose(cur_prose));
        }

        let mut pending_prose = String::new();
        let mut current_cited: Option<String> = None;
        for seg in segments {
            match seg {
                DocSegment::Prose(p) => pending_prose.push_str(&p),
                DocSegment::Block(b_line, b_text) => {
                    match parse_blockquote_literals(b_line, &b_text) {
                        Ok((qs, outside)) => {
                            let mut combined = std::mem::take(&mut pending_prose);
                            combined.push('\n');
                            combined.push_str(&outside);
                            let seg_paths = extract_backticked_corpus_paths(&combined, valid_paths);
                            if seg_paths.len() > 1 {
                                errs.push((
                                    b_line,
                                    format!(
                                        "ambiguous vendored file citations before block quote: {seg_paths:?}"
                                    ),
                                ));
                                continue;
                            } else if let Some(p) = seg_paths.into_iter().next() {
                                current_cited = Some(p);
                            }
                            let cited = current_cited.clone().or_else(|| section_path.clone());
                            for (q_line, q_text) in qs {
                                match &cited {
                                    Some(file) => out.push(ExtractedQuote {
                                        line: q_line,
                                        text: q_text,
                                        cited_file: file.clone(),
                                    }),
                                    None => errs.push((
                                        q_line,
                                        "no vendored upstream file cited in doc comment or section header"
                                            .to_string(),
                                    )),
                                }
                            }
                        }
                        Err(e) => errs.push(e),
                    }
                }
            }
        }
    }

    if errs.is_empty() {
        Ok(out)
    } else {
        Err(errs)
    }
}

/// Checks that `quote` occurs in order within `allowed_path` (or within at
/// least one file of `corpus` when `allowed_path` is `None`).
fn missing_piece_in<'a>(
    corpus: &'a [(String, String)],
    allowed_path: Option<&str>,
    quote: &str,
) -> Option<String> {
    let pieces: Vec<String> = strip_line_comments(quote)
        .split("..")
        .map(squash)
        .filter(|p| !p.is_empty())
        .collect();
    if pieces.is_empty()
        || !pieces
            .iter()
            .any(|p| p.chars().any(|c| c.is_ascii_alphanumeric()))
    {
        return Some("<empty or identifier-free quote>".to_string());
    }
    let mut best_matched = 0usize;
    let mut best_missing: Option<String> = None;
    for (path, file_text) in corpus {
        if let Some(allowed) = allowed_path {
            if path != allowed {
                continue;
            }
        }
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
    let valid_paths: BTreeSet<String> = corpus.iter().map(|(p, _)| p.clone()).collect();
    let lean_root = minirust_dir().join("lean");
    let mut files = Vec::new();
    walk(&lean_root, &mut files);
    let generated = lean_root.join("MiniRustSpec").join("Generated");
    let mut total = 0;
    let mut failures = Vec::new();
    for f in files {
        if f.starts_with(&generated)
            || f.file_name().unwrap() == "Generated.lean"
            || f.extension().unwrap_or_default() != "lean"
        {
            continue;
        }
        let text = std::fs::read_to_string(&f).unwrap();
        match extract_quotes(&text, &valid_paths) {
            Ok(qs) => {
                for q in qs {
                    total += 1;
                    if let Some(piece) =
                        missing_piece_in(&corpus, Some(&q.cited_file), &q.text)
                    {
                        failures.push(format!(
                            "{}:{}: not found in cited `{}`: {piece}",
                            f.display(),
                            q.line,
                            q.cited_file
                        ));
                    }
                }
            }
            Err(errs) => {
                for (line, msg) in errs {
                    failures.push(format!("{}:{line}: {msg}", f.display()));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} quotation check failure(s) (across {total} extracted quotations):\n{}",
        failures.len(),
        failures.join("\n")
    );
    // The interpretation and the translation quote dozens of upstream items;
    // a sudden drop means the extraction above broke.
    assert!(total >= 40, "only {total} quotations found");
}

#[test]
fn fabricated_quotations_are_rejected() {
    let corpus = corpus();
    let valid_paths: BTreeSet<String> = corpus.iter().map(|(p, _)| p.clone()).collect();
    let ops = "spec/lang/step/operators.md";
    let terms = "spec/lang/step/terminators.md";

    // Genuine, with an elision, in the cited file.
    assert_eq!(
        missing_piece_in(&corpus, Some(ops), "Add => left + right, .. Sub => left - right,"),
        None
    );
    // Genuine quote attributed to the WRONG vendored file must be rejected.
    assert!(
        missing_piece_in(&corpus, Some(terms), "Add => left + right, .. Sub => left - right,")
            .is_some()
    );
    // Altered operator.
    assert!(missing_piece_in(&corpus, Some(ops), "Add => left - right,").is_some());
    // Fabricated short token (< 4 chars) between elisions.
    assert!(
        missing_piece_in(
            &corpus,
            Some(ops),
            "Add => left + right, .. ??? .. Sub => left - right,"
        )
        .is_some()
    );
    // Cross-file splice (operators.md followed by terminators.md).
    assert!(
        missing_piece_in(
            &corpus,
            None,
            "Add => left + right, .. fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult"
        )
        .is_some()
    );
    // Reordered pieces (each occurs exactly once upstream, `Goto` first).
    assert_eq!(
        missing_piece_in(
            &corpus,
            Some(terms),
            "fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult .. \
             fn eval_terminator(&mut self, Terminator::Return: Terminator) -> NdResult"
        ),
        None
    );
    assert!(
        missing_piece_in(
            &corpus,
            Some(terms),
            "fn eval_terminator(&mut self, Terminator::Return: Terminator) -> NdResult .. \
             fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult"
        )
        .is_some()
    );

    // Doc-comment extraction: uncited quotes fail, multiple `"..."` literals in
    // one `>` block are extracted separately, and `\\"` closes the quote cleanly.
    let uncited = "/-- Missing file path:\n> \"Add => left + right,\" -/\ndef x := 1\n";
    assert!(extract_quotes(uncited, &valid_paths).is_err());

    // Lean character literal `'"'` outside comments must not swallow subsequent doc comments.
    let char_lit_and_escaped = "\
def quoteChar : Char := '\"'
/-! ## Section (`spec/lang/step/operators.md`) -/
/-- Two quotes and an escaped backslash before closing quote:
> \"Add => left + right,\" and then \"Sub => left - right,\"
> \"trailing_backslash\\\\\" -/
def y := 2
";
    let qs = extract_quotes(char_lit_and_escaped, &valid_paths).unwrap();
    assert_eq!(qs.len(), 3);
    assert_eq!(qs[0].text, "Add => left + right,");
    assert_eq!(qs[1].text, "Sub => left - right,");
    assert_eq!(qs[2].text, "trailing_backslash\\");
    assert_eq!(qs[0].cited_file, ops);

    // Per-quote file binding within a multi-quote doc comment (like `jumpToBlock`):
    // each block quote is bound to its preceding file citation, not the union of
    // all files mentioned anywhere in the doc comment; trailing prose mentions
    // after the last quote do not pollute the quote's `cited_file`.
    let per_block_citations = "\
/-- First (`spec/lang/machine.md`):
> \"self.next_block = b; self.next_stmt = Int::ZERO;\"
and second (`spec/lang/step/terminators.md`):
> \"self.try_mutate_cur_frame(|frame, _mem| { frame.jump_to_block(block); ret(()) })\"
See also (`spec/mem/interface.md`). -/
def jump := 1
";
    let qs2 = extract_quotes(per_block_citations, &valid_paths).unwrap();
    assert_eq!(qs2.len(), 2);
    assert_eq!(qs2[0].cited_file, "spec/lang/machine.md");
    assert_eq!(qs2[1].cited_file, "spec/lang/step/terminators.md");

    // Ambiguous multiple file citations before a single block quote are rejected.
    let ambiguous = "\
/-- Citing both (`spec/lang/machine.md`) and (`spec/lang/step/terminators.md`):
> \"self.next_block = b; self.next_stmt = Int::ZERO;\" -/
def amb := 1
";
    assert!(extract_quotes(ambiguous, &valid_paths).is_err());

    // A new `#` or `##` section header without a file citation resets `section_path`
    // rather than inheriting the previous section's file.
    let reset_sec = "\
/-! ## Old (`spec/lang/step/operators.md`) -/
/-! ## New section with no citation -/
/-- Quote under uncited section:
> \"Add => left + right,\" -/
def z := 3
";
    assert!(extract_quotes(reset_sec, &valid_paths).is_err());

    let reset_h1 = "\
/-! ## Old (`spec/lang/step/operators.md`) -/
/-! # Top-level heading with no citation -/
/-- Quote under uncited top-level heading:
> \"Add => left + right,\" -/
def z2 := 4
";
    assert!(extract_quotes(reset_h1, &valid_paths).is_err());

    // Hex/unicode/UTF-8 character literals outside comments must not corrupt scanning.
    let hex_char_lit = "\
def hexQuote : Char := '\\x22'
def uniQuote : Char := '\\u{0022}'
def utf8Char : Char := 'α'
/-! ## Section (`spec/lang/step/operators.md`) -/
/-- Quote after hex/unicode char literals:
> \"Add => left + right,\" -/
def w := 5
";
    let qs3 = extract_quotes(hex_char_lit, &valid_paths).unwrap();
    assert_eq!(qs3.len(), 1);
    assert_eq!(qs3[0].cited_file, ops);

    // Punctuation-only elisions (`"{ .. }"`) with no identifier/keyword/literal must fail.
    assert!(missing_piece_in(&corpus, Some(ops), "{ .. }").is_some());
}
