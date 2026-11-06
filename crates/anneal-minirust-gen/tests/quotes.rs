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
                        i = (i + 2).min(bytes.len());
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
                let fourth = bytes.get(i + 3).copied();
                let is_doc = match third {
                    Some(b'!') => fourth != Some(b'/'),
                    Some(b'-') => fourth != Some(b'/') && fourth != Some(b'-'),
                    _ => false,
                };
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
    for line in text.lines() {
        let mut rest = line;
        while let Some(open) = rest.find('`') {
            let after_open = &rest[open + 1..];
            let Some(close) = after_open.find('`') else { break };
            let span = &after_open[..close];
            if valid_paths.contains(span) {
                if !found.iter().any(|p| p == span) {
                    found.push(span.to_string());
                }
                rest = &after_open[close + 1..];
            } else if span.chars().any(char::is_whitespace) {
                rest = after_open;
            } else {
                rest = &after_open[close + 1..];
            }
        }
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
    assert!(total >= 170, "only {total} quotations found");

    // Every spec-transcribing `def` in `Interp.lean` (after `/-! ## Target`,
    // except the Lean recursion/iteration helpers `countOnesLoop` and `steps`)
    // must carry its own `/-- ... -/` doc comment with at least one `>` quote.
    let interp_text =
        std::fs::read_to_string(lean_root.join("MiniRustSpec/Interp.lean")).unwrap();
    let spec_start = interp_text
        .find("/-! ## Target `x86_64`")
        .expect("Target section in Interp.lean");
    let spec_slice = &interp_text[spec_start..];
    for chunk in spec_slice.split("\ndef ").skip(1) {
        let def_name: String = chunk
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '.')
            .collect();
        if matches!(def_name.as_str(), "countOnesLoop" | "steps") {
            continue;
        }
        let def_offset = spec_start + (chunk.as_ptr() as usize - spec_slice.as_ptr() as usize) - 4;
        let before = interp_text[..def_offset].trim_end();
        assert!(
            before.ends_with("-/"),
            "MiniRustSpec.Interp.{def_name} is not immediately preceded by a doc comment"
        );
        let doc_open = before.rfind("/--").unwrap_or_else(|| {
            panic!("MiniRustSpec.Interp.{def_name} has no `/-- ... -/` doc comment")
        });
        let doc_body = &before[doc_open..];
        assert!(
            doc_body.lines().any(|l| l.trim_start().starts_with('>')),
            "MiniRustSpec.Interp.{def_name} doc comment contains no `>` upstream block quote"
        );
    }
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

    // An unmatched backtick or `/---` divider comment must not swallow citations or quotes.
    let unmatched_tick_and_divider = "\
/----------/
/-- Let `x = 1 in (`spec/lang/step/operators.md`):
> \"Add => left + right,\" -/
def u := \"trailing\\";
    let qs4 = extract_quotes(unmatched_tick_and_divider, &valid_paths).unwrap();
    assert_eq!(qs4.len(), 1);
    assert_eq!(qs4[0].cited_file, ops);
}

/// The upstream items behind `bool`, comparisons, and transmutes (`MR-1.1`):
/// each quotation that the Lean transcriptions rely on occurs verbatim in its
/// vendored file, a one-token tampering of it is rejected, and the Lean
/// sources still carry it (so the doc comment cannot silently lose the quote
/// that justifies a definition).
#[test]
fn bool_comparison_and_transmute_quotations_are_pinned() {
    let corpus = corpus();
    let ops = "spec/lang/step/operators.md";
    let repr = "spec/lang/representation.md";
    let types = "spec/lang/types.md";
    let rvalue = "tooling/minimize/src/rvalue.rs";
    let bb = "tooling/minimize/src/bb.rs";
    let constant = "tooling/minimize/src/constant.rs";

    // Note: `tooling/miniutil/src/...` (e.g. `expr.rs`, `ty.rs`) is not vendored
    // by `minirust.lock.toml`, so quotations from it (`bool_to_int`, `not`,
    // `bool_and`, `bool_or`, `bool_xor`, `tuple_ty`) cannot be pinned here.

    // (cited file, genuine quotation, tampered quotation, Lean file quoting it)
    let cases: &[(&str, &str, &str, &str)] = &[
        // `Machine::transmute`: encode at the old type, decode at the new one.
        (
            repr,
            "let bytes = type1.encode::<M>(val); if let Some(raw_value) = type2.decode::<M>(bytes) { \
             self.check_value(raw_value, type2)?; ret(raw_value) } else { \
             throw_ub!(\"transmuted value is not valid at new type\") }",
            "let bytes = type1.encode::<M>(val); if let Some(raw_value) = type1.decode::<M>(bytes) {",
            "MiniRustSpec/Interp.lean",
        ),
        // `CastOp::Transmute` checks the sizes before transmuting.
        (
            ops,
            "Transmute(new_ty) => { if old_ty.layout::<M::T>().expect_size(\"WF ensures transmutes are sized\") \
             != new_ty.layout::<M::T>().expect_size(\"WF ensures transmutes are sized\") { \
             throw_ub!(\"transmute between types of different size\") }",
            "Transmute(new_ty) => { if old_ty.layout::<M::T>().expect_size(\"WF ensures transmutes are sized\") \
             == new_ty.layout::<M::T>().expect_size(\"WF ensures transmutes are sized\") {",
            "MiniRustSpec/Interp.lean",
        ),
        // `eval_rel_op`: every relational operator and the `i8` of `Cmp`.
        (
            ops,
            "Lt => (Value::Bool(ord.is_lt()), Type::Bool), Gt => (Value::Bool(ord.is_gt()), Type::Bool), \
             Le => (Value::Bool(ord.is_le()), Type::Bool), Ge => (Value::Bool(ord.is_ge()), Type::Bool), \
             Eq => (Value::Bool(ord.is_eq()), Type::Bool), Ne => (Value::Bool(ord.is_ne()), Type::Bool),",
            "Lt => (Value::Bool(ord.is_gt()), Type::Bool),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            ops,
            "(Value::Int(Int::from(val)), Type::Int(IntType::I8))",
            "(Value::Int(Int::from(val)), Type::Int(IntType::I32))",
            "MiniRustSpec/Interp.lean",
        ),
        // `BinOp::Rel` compares integers and Booleans with `cmp`.
        (
            ops,
            "(Type::Int(_), Value::Int(left), Value::Int(right)) => { left.cmp(&right) } \
             (Type::Bool, Value::Bool(left), Value::Bool(right)) => { left.cmp(&right) }",
            "(Type::Int(_), Value::Int(left), Value::Int(right)) => { right.cmp(&left) }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "pub const I8: IntType = IntType { signed: Signedness::Signed, size: Size::from_bytes_const(1) };",
            "pub const I8: IntType = IntType { signed: Signedness::Unsigned, size: Size::from_bytes_const(1) };",
            "MiniRustSpec/Interp.lean",
        ),
        // `bool` decodes only the bytes 0 and 1.
        (
            repr,
            "AbstractByte::Init(0, _) => Value::Bool(false), AbstractByte::Init(1, _) => Value::Bool(true), \
             _ => throw!(),",
            "AbstractByte::Init(2, _) => Value::Bool(true),",
            "MiniRustSpec/Interp.lean",
        ),
        // `minimize`: `!b` on a `bool` is `build::not`, comparisons are
        // `build::lt` and friends, `bool` constants go through `to_bool`, and a
        // `bool` switch is transmuted to `u8`.
        (
            rvalue,
            "(Not, Type::Int(_)) => build::bit_not(operand), (Not, Type::Bool) => build::not(operand),",
            "(Not, Type::Bool) => build::bit_not(operand),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            rvalue,
            "(BitAnd, Type::Bool) => build::bool_and(l, r), \
             (BitOr, Type::Bool) => build::bool_or(l, r), \
             (BitXor, Type::Bool) => build::bool_xor(l, r),",
            "(BitAnd, Type::Bool) => build::bit_and(l, r),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            rvalue,
            "(Lt, _) => build::lt(l, r), (Le, _) => build::le(l, r), (Gt, _) => build::gt(l, r), \
             (Ge, _) => build::ge(l, r), (Eq, _) => build::eq(l, r), (Ne, _) => build::ne(l, r),",
            "(Lt, _) => build::le(l, r),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            rvalue,
            "let operand = match operand_ty { Type::Int(_) => operand, \
             Type::Bool => build::transmute(operand, u8::get_type()),",
            "Type::Bool => build::transmute(operand, i8::get_type()),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            constant,
            "let val = ecx.read_scalar(&val).unwrap().to_bool().unwrap(); \
             ValueExpr::Constant(Constant::Bool(val), ty)",
            "let val = ecx.read_scalar(&val).unwrap().to_u8().unwrap();",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "let Type::Int(u8_inttype) = <u8>::get_type() else { unreachable!() }; ( ValueExpr::UnOp { \
             operator: UnOp::Cast(CastOp::Transmute(Type::Int(u8_inttype))), operand: GcCow::new(discr_op), }, \
             u8_inttype, )",
            "operator: UnOp::Cast(CastOp::IntToInt(u8_inttype)),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
    ];

    let lean_root = minirust_dir().join("lean");
    for (file, genuine, tampered, lean_file) in cases {
        assert_eq!(
            missing_piece_in(&corpus, Some(file), genuine),
            None,
            "genuine quotation not found in `{file}`: {genuine}"
        );
        assert!(
            missing_piece_in(&corpus, Some(file), tampered).is_some(),
            "tampered quotation unexpectedly found in `{file}`: {tampered}"
        );
        // The same quotation must be rejected when attributed to another file.
        let other = if *file == ops { repr } else { ops };
        assert!(
            missing_piece_in(&corpus, Some(other), genuine).is_some(),
            "quotation from `{file}` also matches `{other}`: {genuine}"
        );
        let lean = std::fs::read_to_string(lean_root.join(lean_file)).unwrap();
        let lean_squashed = squash(&lean.replace("\\\"", "\"").replace("\n>", "\n"));
        let first_piece = squash(genuine.split("..").next().unwrap());
        let probe: String = first_piece.chars().take(40).collect();
        assert!(
            lean_squashed.contains(&probe),
            "`{lean_file}` no longer quotes `{probe}`"
        );
    }
}

/// The upstream items behind `core::cmp::Ordering` and MIR's three-way `Cmp`
/// (`MR-1.1`): the representation of enums (`decode_discriminant`,
/// `encode_discriminant`, `Type::{decode, encode}` for `Enum`) and of the
/// tuples that carry variant data, `check_value` for both, the layout of
/// both, and `minimize`'s translation of `Cmp` and of directly tagged enums.
/// Each quotation occurs verbatim in its vendored file, a one-token tampering
/// of it is rejected, it does not match another file, and the Lean sources
/// still carry it.
#[test]
fn enum_tuple_and_cmp_quotations_are_pinned() {
    let corpus = corpus();
    let ops = "spec/lang/step/operators.md";
    let repr = "spec/lang/representation.md";
    let types = "spec/lang/types.md";
    let rvalue = "tooling/minimize/src/rvalue.rs";
    let enums = "tooling/minimize/src/enums.rs";

    // (cited file, genuine quotation, tampered quotation, Lean file quoting it)
    let cases: &[(&str, &str, &str, &str)] = &[
        // `decode_discriminant`: `Known` and `Invalid` leaves, and the
        // half-open ranges of `Branch` children.
        (
            repr,
            "fn decode_discriminant<M: Memory>(mut accessor: impl FnMut(Offset, Size) -> \
             Result<List<AbstractByte<M::Provenance>>>, discriminator: Discriminator) -> \
             Result<Option<Int>> { match discriminator { Discriminator::Known(val) => ret(Some(val)), \
             Discriminator::Invalid => ret(None),",
            "Discriminator::Invalid => ret(Some(val)),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            ".find_map(|((start, end), child)| if start <= val && val < end { Some(child) } else { None }) \
             .unwrap_or(fallback);",
            ".find_map(|((start, end), child)| if start <= val && val <= end { Some(child) } else { None })",
            "MiniRustSpec/Interp.lean",
        ),
        // `encode_discriminant` encodes each tag at its integer type.
        (
            repr,
            "for (offset, (value_type, value)) in tagger.iter() { \
             let bytes = Type::Int(value_type).encode::<M>(Value::Int(value)); accessor(offset, bytes)?; }",
            "let bytes = Type::Int(value_type).encode::<M>(Value::Int(offset));",
            "MiniRustSpec/Interp.lean",
        ),
        // `Type::decode` for `Enum` and for `Tuple`, and `Type::encode` for
        // `Tuple` (padding is `Uninit`).
        (
            repr,
            "if bytes.len() != size.bytes() { panic!(\"decode of Type::Enum with invalid length\"); }",
            "if bytes.len() != size.bytes() { throw_ub!(\"decode of Type::Enum with invalid length\"); }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "let Some(value) = variants[discriminant].ty.decode(bytes) else { return None }; \
             Some(Value::Variant { discriminant, data: value })",
            "Some(Value::Variant { discriminant: Int::ZERO, data: value })",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "assert!(unsized_field.is_none(), \"decode of Type::Tuple with unsized field\"); \
             let (size, _) = sized_head_layout.head_size_and_align(); \
             if bytes.len() != size.bytes() { panic!(\"decode of Type::Tuple with invalid length\"); }",
            "let (_, size) = sized_head_layout.head_size_and_align();",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "let mut bytes = list![AbstractByte::Uninit; size.bytes()];",
            "let mut bytes = list![AbstractByte::Init(0, None); size.bytes()];",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "sized_fields.try_map(|(offset, ty)| { \
             let subslice = bytes.subslice_with_length( \
                 offset.bytes(), \
                 ty.layout::<M::T>().expect_size(\"WF ensures all sized tuple fields are sized\").bytes() \
             ); \
             ty.decode::<M>(subslice) })?",
            "sized_fields.try_map(|(offset, ty)| { \
             let subslice = bytes.subslice_with_length(0, offset.bytes()); \
             ty.decode::<M>(subslice) })?",
            "MiniRustSpec/Interp.lean",
        ),
        // `check_value` for variants and tuples, and `ensure_else_ub`.
        (
            repr,
            "fn ensure_else_ub(b: bool, msg: &str) -> Result<()> { \
             if !b { throw_ub!(\"{}\", msg); } ret(()) }",
            "fn ensure_else_ub(b: bool, msg: &str) -> Result<()> { \
             if !b { panic!(\"{}\", msg); } ret(()) }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "let Some(variant) = variants.get(discriminant) else { \
             throw_ub!(\"Value::Variant: invalid discrimant\"); }; self.check_value(data, variant.ty)?;",
            "let Some(variant) = variants.get(discriminant) else { panic!(\"Value::Variant: invalid discrimant\"); };",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "ensure_else_ub(vals.len() == sized_fields.len(), \"Value::Tuple: invalid number of fields\")?;",
            "ensure_else_ub(vals.len() <= sized_fields.len(), \"Value::Tuple: invalid number of fields\")?;",
            "MiniRustSpec/Interp.lean",
        ),
        // `Type::decode`, `Type::encode`, and `check_value` for `Union`.
        (
            repr,
            "fn decode<M: Memory>(Type::Union { size, chunks, .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> { \
             if bytes.len() != size.bytes() { panic!(\"decode of Type::Union with invalid length\"); } \
             let mut chunk_data = list![]; \
             for (offset, size) in chunks { \
                 chunk_data.push(bytes.subslice_with_length(offset.bytes(), size.bytes())); \
             } \
             ret(Value::Union(chunk_data)) }",
            "if bytes.len() != size.bytes() { throw_ub!(\"decode of Type::Union with invalid length\"); }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "for ((offset, size), data) in chunks.zip(chunk_data) { \
             assert_eq!(size.bytes(), data.len()); \
             bytes.write_subslice_at_index(offset.bytes(), data); }",
            "for ((offset, size), data) in chunks.zip(chunk_data) { \
             assert_eq!(offset.bytes(), data.len()); \
             bytes.write_subslice_at_index(offset.bytes(), data); }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "(Value::Union(chunk_data), Type::Union { chunks, .. }) => { \
             ensure_else_ub(chunk_data.len() == chunks.len(), \"Value::Union: invalid chunk size\")?;",
            "(Value::Union(chunk_data), Type::Union { chunks, .. }) => { \
             ensure_else_ub(chunk_data.len() <= chunks.len(), \"Value::Union: invalid chunk size\")?;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "for (data, (_, size)) in chunk_data.zip(chunks) { \
             ensure_else_ub(data.len() == size.bytes(), \"Value::Union: invalid chunk data\")?; }",
            "for (data, (_, size)) in chunk_data.zip(chunks) { \
             ensure_else_ub(data.len() <= size.bytes(), \"Value::Union: invalid chunk data\")?; }",
            "MiniRustSpec/Interp.lean",
        ),
        // Layout of enums and sized tuples.
        (
            types,
            "pub fn head_size_and_align(self) -> (Size, Align) { \
             (self.end.align_to(self.align), self.align) }",
            "pub fn head_size_and_align(self) -> (Size, Align) { (self.end, self.align) }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "Union { size, align, .. } | Enum { size, align, .. } => Sized(size, align),",
            "Union { size, align, .. } | Enum { size, align, .. } => Sized(align, size),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "Some(tail_ty) => LayoutStrategy::Tuple { \
             head: sized_head_layout, \
             tail: tail_ty.layout::<T>(), },",
            "Some(tail_ty) => LayoutStrategy::Sized(sized_head_layout, tail_ty.layout::<T>()),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "Slice { elem } => LayoutStrategy::Slice( \
             elem.layout::<T>().expect_size(\"WF ensures slice element is sized\"), \
             elem.layout::<T>().expect_align(\"WF ensures array element is sized\"), ), \
             TraitObject(trait_name) => LayoutStrategy::TraitObject(trait_name),",
            "Slice { elem } => LayoutStrategy::Sized( \
             elem.layout::<T>().expect_size(\"WF ensures slice element is sized\"), \
             elem.layout::<T>().expect_align(\"WF ensures array element is sized\"), ),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "fn decode<M: Memory>(Type::Slice { .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> { \
             panic!(\"decode of Type::Slice\") }",
            "fn decode<M: Memory>(Type::Slice { .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> { \
             throw_ub!(\"decode of Type::Slice\") }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "fn decode<M: Memory>(Type::TraitObject(..): Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> { \
             panic!(\"decode of Type::TraitObject\") }",
            "fn decode<M: Memory>(Type::TraitObject(..): Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> { \
             throw_ub!(\"decode of Type::TraitObject\") }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "fn encode<M: Memory>(Type::Slice { .. }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> { \
             panic!(\"encode of Type::Slice\") }",
            "fn encode<M: Memory>(Type::Slice { .. }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> { \
             throw_ub!(\"encode of Type::Slice\") }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "fn encode<M: Memory>(Type::TraitObject(..): Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> { \
             panic!(\"encode of Type::TraitObject\") }",
            "fn encode<M: Memory>(Type::TraitObject(..): Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> { \
             throw_ub!(\"encode of Type::TraitObject\") }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            repr,
            "(_, Type::Slice { .. }) => panic!(\"Value: slices cannot be represented as values\"), \
             (_, Type::TraitObject { .. }) => panic!(\"Value: trait objects cannot be represented as values\"),",
            "(_, Type::Slice { .. }) => throw_ub!(\"Value: slices cannot be represented as values\"),",
            "MiniRustSpec/Interp.lean",
        ),
        // `minimize`: `Cmp` is `build::cmp` transmuted to the translation of
        // `Ordering`, and directly tagged enums tag every variant with its
        // own discriminant, with an `Invalid` fallback.
        (
            rvalue,
            "(Cmp, _) => { let res = build::cmp(l, r);",
            "(Cmp, _) => { let res = build::lt(l, r);",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            rvalue,
            "let ordering_ty: rs::Ty = self.tcx.ty_ordering_enum(rs::DUMMY_SP); \
             let ordering_ty: Type = self.translate_ty(ordering_ty, span); build::transmute(res, ordering_ty)",
            "let ordering_ty: Type = self.translate_ty(ordering_ty, span); build::int_cast(res, ordering_ty)",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            enums,
            "let tagger = [(tag_offset, (tag_ty, discr_int))] .into_iter() \
             .collect::<Map<Offset, (IntType, Int)>>();",
            "let tagger = [(tag_offset, (discriminant_ty, discr_int))]",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            enums,
            "discriminator_branches.insert( (discr_int, discr_int + Int::ONE), Discriminator::Known(discr_int), );",
            "discriminator_branches.insert( (discr_int, discr_int), Discriminator::Known(discr_int), );",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            enums,
            "rs::TagEncoding::Direct => GcCow::new(Discriminator::Invalid),",
            "rs::TagEncoding::Direct => GcCow::new(Discriminator::Known(discr_int)),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
    ];

    let lean_root = minirust_dir().join("lean");
    for (file, genuine, tampered, lean_file) in cases {
        assert_eq!(
            missing_piece_in(&corpus, Some(file), genuine),
            None,
            "genuine quotation not found in `{file}`: {genuine}"
        );
        assert!(
            missing_piece_in(&corpus, Some(file), tampered).is_some(),
            "tampered quotation unexpectedly found in `{file}`: {tampered}"
        );
        let other = if *file == ops { repr } else { ops };
        assert!(
            missing_piece_in(&corpus, Some(other), genuine).is_some(),
            "quotation from `{file}` also matches `{other}`: {genuine}"
        );
        let lean = std::fs::read_to_string(lean_root.join(lean_file)).unwrap();
        let lean_squashed = squash(&lean.replace("\\\"", "\"").replace("\n>", "\n"));
        let first_piece = squash(genuine.split("..").next().unwrap());
        let probe: String = first_piece.chars().take(40).collect();
        assert!(
            lean_squashed.contains(&probe),
            "`{lean_file}` no longer quotes `{probe}`"
        );
    }
}

/// The upstream items behind checked integer arithmetic (`IntWithOverflow`),
/// `(Int, bool)` 2-tuples (`IntType::with_overflow`, `ValueExpr::Tuple`), and
/// field projections (`PlaceExpr::Field`, `ptr_offset_inbounds`,
/// `LayoutStrategy::compute_size_and_align`) (`MR-1.2`).
#[test]
fn with_overflow_tuple_and_field_quotations_are_pinned() {
    let corpus = corpus();
    let ops = "spec/lang/step/operators.md";
    let exprs = "spec/lang/step/expressions.md";
    let types = "spec/lang/types.md";
    let ptr = "spec/mem/pointer.md";
    let basic = "spec/mem/basic.md";
    let iface = "spec/mem/interface.md";
    let conc = "spec/mem/concurrent.md";
    let mach = "spec/lang/machine.md";
    let rvalue = "tooling/minimize/src/rvalue.rs";
    let min_ty = "tooling/minimize/src/ty.rs";
    let bb = "tooling/minimize/src/bb.rs";

    // (cited file, genuine quotation, tampered quotation, Lean file quoting it)
    let cases: &[(&str, &str, &str, &str)] = &[
        // `IntType::with_overflow` constructs `(self, bool)` with trailing padding
        // up to `self.size + Size::from_bytes(align.bytes()).unwrap()`.
        (
            types,
            "pub fn with_overflow<T: Target>(&self) -> Type { \
             let fields = list![(Size::ZERO, Type::Int(*self)), (self.size, Type::Bool)]; \
             let align = self.align::<T>(); \
             let size = self.size + Size::from_bytes(align.bytes()).unwrap(); \
             Type::Tuple { \
                 sized_fields: fields, \
                 sized_head_layout: TupleHeadLayout { end: size, align, packed_align: None, }, \
                 unsized_field: None, \
             } }",
            "let size = self.size + Size::from_bytes_const(1);",
            "MiniRustSpec/Interp.lean",
        ),
        // `TupleHeadLayout::{capped_tail_align, tail_offset, full_size_and_align}` and
        // `LayoutStrategy::{is_sized, compute_size_and_align}`.
        (
            types,
            "fn capped_tail_align(self, tail_align: Align) -> Align { \
             match self.packed_align { \
                 Some(packed_align) => tail_align.min(packed_align), \
                 None => tail_align, \
             } }",
            "Some(packed_align) => tail_align.max(packed_align),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "pub fn tail_offset(self, tail_align: Align) -> Offset { \
             let capped_tail_align = self.capped_tail_align(tail_align); \
             let tail_offset = self.end.align_to(capped_tail_align); \
             tail_offset }",
            "let tail_offset = self.end;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "pub fn full_size_and_align(self, tail_size: Size, tail_align: Align) -> (Size, Align) { \
             let capped_tail_align = self.capped_tail_align(tail_align); \
             let align = capped_tail_align.max(self.align); \
             let tail_offset = self.tail_offset(tail_align); \
             let end = tail_offset + tail_size; \
             let size = end.align_to(align); \
             (size, align) }",
            "let align = capped_tail_align.min(self.align);",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "pub fn is_sized(self) -> bool { \
             matches!(self, LayoutStrategy::Sized(..)) }",
            "matches!(self, LayoutStrategy::Tuple { .. })",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "(LayoutStrategy::Tuple { head, tail }, Some(meta)) => { \
             let (tail_size, tail_align) = tail.compute_size_and_align(Some(meta), vtables); \
             head.full_size_and_align(tail_size, tail_align) }",
            "head.head_size_and_align()",
            "MiniRustSpec/Interp.lean",
        ),
        // `ThinPointer::{wrapping_offset, widen}`, `dereferenceable`, `signed_dereferenceable`.
        (
            ptr,
            "pub fn wrapping_offset<T: Target>(self, offset: Int) -> Self { \
             let addr = self.addr + offset; \
             let addr = addr.bring_in_bounds(Unsigned, T::PTR_SIZE); \
             ThinPointer { addr, ..self } }",
            "let addr = addr.bring_in_bounds(Signed, T::PTR_SIZE);",
            "MiniRustSpec/Interp.lean",
        ),
        (
            ptr,
            "pub fn widen(self, metadata: Option<PointerMeta<Provenance>>) -> Pointer<Provenance> { \
             Pointer { thin_pointer: self, metadata, } }",
            "Pointer { thin_pointer: self, metadata: None, }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            basic,
            "fn dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Size) -> Result { \
             self.check_ptr(ptr, len)?; ret(()) }",
            "self.check_ptr(ptr, Size::ZERO)?;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            iface,
            "fn signed_dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Int) -> Result { \
             if len > 0 { \
                 self.dereferenceable(ptr, Size::from_bytes(len).unwrap()) \
             } else { \
                 let begin_ptr = ThinPointer { addr: ptr.addr + len, ..ptr }; \
                 self.dereferenceable(begin_ptr, Size::from_bytes(-len).unwrap()) \
             } }",
            "let begin_ptr = ThinPointer { addr: ptr.addr - len, ..ptr };",
            "MiniRustSpec/Interp.lean",
        ),
        (
            conc,
            "pub fn signed_dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Int) -> Result { \
             self.memory.signed_dereferenceable(ptr, len) }",
            "self.memory.signed_dereferenceable(ptr, -len)",
            "MiniRustSpec/Interp.lean",
        ),
        // `Machine::{vtable_lookup, compute_size, compute_align}`.
        (
            mach,
            "fn compute_size(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Size { \
             let (size, _) = layout.compute_size_and_align(meta, self.vtable_lookup()); \
             size }",
            "let (_, size) = layout.compute_size_and_align(meta, self.vtable_lookup());",
            "MiniRustSpec/Interp.lean",
        ),
        (
            mach,
            "fn compute_align(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Align { \
             let (_, align) = layout.compute_size_and_align(meta, self.vtable_lookup()); \
             align }",
            "let (align, _) = layout.compute_size_and_align(meta, self.vtable_lookup());",
            "MiniRustSpec/Interp.lean",
        ),
        // `Machine::ptr_offset_inbounds` and `Machine::eval_place` (`PlaceExpr::Field`).
        (
            ops,
            "fn ptr_offset_inbounds(&self, ptr: ThinPointer<M::Provenance>, offset: Int) -> Result<ThinPointer<M::Provenance>> { \
             self.mem.signed_dereferenceable(ptr, offset)?; \
             assert!(offset.in_bounds(Signed, M::T::PTR_SIZE)); \
             assert!((ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE)); \
             ret(ThinPointer { addr: ptr.addr + offset, ..ptr }) }",
            "assert!(offset.in_bounds(Unsigned, M::T::PTR_SIZE));",
            "MiniRustSpec/Interp.lean",
        ),
        (
            exprs,
            "fn eval_place(&mut self, PlaceExpr::Field { root, field }: PlaceExpr) -> Result<(Place<M>, Type)> { \
             let (root, ty) = self.eval_place(root)?; \
             let (offset, field_ty) = match ty { \
                 Type::Tuple { sized_fields, unsized_field, sized_head_layout } => { \
                     if field >= 0 && field < sized_fields.len() { \
                         sized_fields[field] \
                     } else if field == sized_fields.len() {",
            "if field >= 0 && field <= sized_fields.len() { sized_fields[field] }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            exprs,
            "let tail_ty = unsized_field.expect(\"field projection to non-existing unsized tail\"); \
             let tail_align = self.compute_align(tail_ty.layout::<M::T>(), root.ptr.metadata); \
             let offset = sized_head_layout.tail_offset(tail_align); \
             (offset, tail_ty)",
            "let offset = Size::ZERO; (offset, tail_ty)",
            "MiniRustSpec/Interp.lean",
        ),
        (
            exprs,
            "Type::Union { fields, .. } => fields[field], \
             _ => panic!(\"field projection on non-projectable type\"),",
            "Type::Union { fields, .. } => panic!(\"field projection on non-projectable type\"),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            exprs,
            "assert!(offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)); \
             let ptr = self.ptr_offset_inbounds(root.ptr.thin_pointer, offset.bytes())?;",
            "let ptr = self.ptr_offset_inbounds(root.ptr.thin_pointer, -offset.bytes())?;",
            "MiniRustSpec/Interp.lean",
        ),
        // `Machine::eval_bin_op` for `BinOp::IntWithOverflow` and `Machine::eval_value` for `ValueExpr::Tuple`.
        (
            ops,
            "let result = match op { \
                 IntBinOpWithOverflow::Add => left + right, \
                 IntBinOpWithOverflow::Sub => left - right, \
                 IntBinOpWithOverflow::Mul => left * right, \
             }; \
             let overflow = !int_ty.can_represent(result); \
             let result = int_ty.bring_in_bounds(result); \
             let value = Value::Tuple(list![Value::Int::<M>(result), Value::Bool::<M>(overflow)]); \
             let ty = int_ty.with_overflow::<M::T>(); \
             ret((value, ty))",
            "let overflow = int_ty.can_represent(result);",
            "MiniRustSpec/Interp.lean",
        ),
        (
            exprs,
            "fn eval_value(&mut self, ValueExpr::Tuple(exprs, ty): ValueExpr) -> Result<(Value<M>, Type)> { \
             let vals = exprs.try_map(|e| self.eval_value(e))?.map(|e| e.0); \
             ret((Value::Tuple(vals), ty)) }",
            "let vals = exprs.try_map(|e| self.eval_value(e))?.map(|e| e.1);",
            "MiniRustSpec/Interp.lean",
        ),
        // `minimize`: `Tuple` layout, `ProjectionElem::Field`, `CheckedBinaryOp`, `AggregateKind::Tuple`.
        (
            min_ty,
            "fn tuple_from_layout(&mut self, layout: rs::TyAndLayout<'tcx>, span: rs::Span) -> Type { \
             let size = translate_size(layout.size); \
             let align = translate_align(layout.align.abi);",
            "let size = translate_align(layout.align.abi);",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            rvalue,
            "smir::ProjectionElem::Field(f, _ty) => { \
             let indirected = GcCow::new(expr); \
             PlaceExpr::Field { root: indirected, field: (*f).into() } }",
            "PlaceExpr::Field { root: indirected, field: Int::ZERO }",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            rvalue,
            "smir::Rvalue::CheckedBinaryOp(op, l, r) => { \
             let l = GcCow::new(self.translate_operand_smir(l, span)); \
             let r = GcCow::new(self.translate_operand_smir(r, span)); \
             let op = match op { \
                 smir::BinOp::Add => BinOp::IntWithOverflow(IntBinOpWithOverflow::Add), \
                 smir::BinOp::Sub => BinOp::IntWithOverflow(IntBinOpWithOverflow::Sub), \
                 smir::BinOp::Mul => BinOp::IntWithOverflow(IntBinOpWithOverflow::Mul), \
                 x => panic!(\"CheckedBinaryOp {x:?} not supported.\"), \
             }; \
             ValueExpr::BinOp { operator: op, left: l, right: r } }",
            "smir::BinOp::Sub => BinOp::IntWithOverflow(IntBinOpWithOverflow::Add),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            rvalue,
            "Type::Tuple { .. } | Type::Array { .. } => { \
             let ops: List<_> = operands.iter().map(|x| self.translate_operand_smir(x, span)).collect(); \
             ValueExpr::Tuple(ops, ty) }",
            "Type::Tuple { .. } | Type::Array { .. } => { ValueExpr::Tuple(list![], ty) }",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::StatementKind::PlaceMention(place) => { \
             let place = self.translate_place(place, span); \
             Statement::PlaceMention(place) }",
            "rs::StatementKind::PlaceMention(place) => { Statement::StorageLive(place) }",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
    ];
    assert_eq!(cases.len(), 25, "expected 25 pinned MR-1.2 quotations");

    let lean_root = minirust_dir().join("lean");
    for (file, genuine, tampered, lean_file) in cases {
        assert_eq!(
            missing_piece_in(&corpus, Some(file), genuine),
            None,
            "genuine quotation not found in `{file}`: {genuine}"
        );
        assert!(
            missing_piece_in(&corpus, Some(file), tampered).is_some(),
            "tampered quotation unexpectedly found in `{file}`: {tampered}"
        );
        let other = if *file == ops { types } else { ops };
        assert!(
            missing_piece_in(&corpus, Some(other), genuine).is_some(),
            "quotation from `{file}` also matches `{other}`: {genuine}"
        );
        let lean = std::fs::read_to_string(lean_root.join(lean_file)).unwrap();
        let lean_squashed = squash(&lean.replace("\\\"", "\"").replace("\n>", "\n"));
        let first_piece = squash(genuine.split("..").next().unwrap());
        let probe: String = first_piece.chars().take(40).collect();
        assert!(
            lean_squashed.contains(&probe),
            "`{lean_file}` no longer quotes `{probe}`"
        );
    }
}

/// The upstream items behind `MR-1.3`: arbitrary locals, `StorageLive`,
/// `StorageDead`, `Statement::Deinit`, `ConcurrentMemory::deinit`,
/// `ConcurrentMemory::allocate`, `BasicMemory::allocate`, `Allocation::overlaps`,
/// `x86_64::valid_size`, `Machine::try_mutate_cur_frame`, `Operand::Move`,
/// `initBlock` (`always_storage_live_locals`), and the predicate of the daemonic
/// address choice (`pick`) in `BasicMemory::allocate`.
#[test]
fn storage_live_dead_deinit_move_and_init_block_quotations_are_pinned() {
    let corpus = corpus();
    let valid_paths: BTreeSet<String> = corpus.iter().map(|(p, _)| p.clone()).collect();
    let stmts = "spec/lang/step/statements.md";
    let terms = "spec/lang/step/terminators.md";
    let mach = "spec/lang/machine.md";
    let basic = "spec/mem/basic.md";
    let conc = "spec/mem/concurrent.md";
    let target = "spec/prelude/target.md";
    let wf = "spec/lang/well-formed.md";
    let rvalue = "tooling/minimize/src/rvalue.rs";
    let bb = "tooling/minimize/src/bb.rs";
    let func = "tooling/minimize/src/function.rs";

    // (cited file, genuine quotation, tampered quotation, Lean file quoting it)
    let cases: &[(&str, &str, &str, &str)] = &[
        (
            target,
            "fn valid_size(size: Size) -> bool { \
             size.bytes().in_bounds(Signed, Self::PTR_SIZE) }",
            "size.bytes().in_bounds(Unsigned, Self::PTR_SIZE)",
            "MiniRustSpec/Interp.lean",
        ),
        (
            basic,
            "fn overlaps(self, other_addr: Address, other_size: Size) -> bool { \
             let end_addr = self.addr + self.size().bytes(); \
             let other_end_addr = other_addr + other_size.bytes(); \
             if end_addr <= other_addr || other_end_addr <= self.addr { \
                 self.addr == other_addr \
             } else { true } }",
            "if end_addr < other_addr || other_end_addr < self.addr { false }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            basic,
            "if !T::valid_size(size) { \
                 throw_ub!(\"asking for a too large allocation\"); \
             } .. \
             let allocation = Allocation { \
                 addr, align, kind, live: true, \
                 data: list![AbstractByte::Uninit; size.bytes()], \
                 extra: alloc_extra, \
             }; \
             let id = AllocId(self.allocations.len()); \
             self.allocations.push(allocation); \
             ret(ThinPointer { addr, provenance: Some((id, prov_extra)) })",
            "live: false, data: list![AbstractByte::Uninit; size.bytes()],",
            "MiniRustSpec/Interp.lean",
        ),
        (
            basic,
            "let addr = pick(distr, |addr: Address| { .. \
             if addr <= 0 { return false; } .. \
             if !align.is_aligned(addr) { return false; } .. \
             if !(addr+size.bytes()).in_bounds(Unsigned, T::PTR_SIZE) { return false; } .. \
             if self.allocations.any(|a| a.live && a.overlaps(addr, size)) { return false; } .. \
             true })?;",
            "if self.allocations.any(|a| a.overlaps(addr, size)) { return false; }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            basic,
            "let Some((id, prov_extra)) = ptr.provenance else { \
                 throw_ub!(\"deallocating invalid pointer\") \
             }; \
             let mut allocation = self.allocations[id.0]; \
             if !allocation.live { throw_ub!(\"double-free\"); } \
             if ptr.addr != allocation.addr { \
                 throw_ub!(\"deallocating with pointer not to the beginning of its allocation\"); \
             } \
             if kind != allocation.kind { \
                 throw_ub!(\"deallocating {:?} memory with {:?} deallocation operation\", allocation.kind, kind); \
             } \
             if size != allocation.size() { \
                 throw_ub!(\"deallocating with incorrect size information\"); \
             } \
             if align != allocation.align { \
                 throw_ub!(\"deallocating with incorrect alignment information\"); \
             } \
             handle_extra(&mut allocation.extra, prov_extra)?; \
             allocation.live = false; \
             self.allocations.set(id.0, allocation);",
            "if !allocation.live { ret(()); }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            conc,
            "pub fn allocate(&mut self, kind: AllocationKind, size: Size, align: Align) -> NdResult<ThinPointer<M::Provenance>> { \
             self.memory.allocate(kind, size, align) }",
            "pub fn allocate(&mut self, kind: AllocationKind, size: Size, align: Align) -> Result<ThinPointer<M::Provenance>>",
            "MiniRustSpec/Interp.lean",
        ),
        (
            conc,
            "pub fn deallocate(&mut self, ptr: ThinPointer<M::Provenance>, kind: AllocationKind, size: Size, align: Align) -> Result { \
             self.memory.deallocate(ptr, kind, size, align) }",
            "self.memory.deallocate(ptr, AllocationKind::Stack, size, align)",
            "MiniRustSpec/Interp.lean",
        ),
        (
            mach,
            "fn try_mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> NdResult<O>) -> NdResult<O> { \
             self.threads.try_mutate_at(self.active_thread, |thread| thread.try_mutate_cur_frame(|frame| f(frame, &mut self.mem))) }",
            "self.threads.mutate_at(self.active_thread, |thread| thread.cur_frame())",
            "MiniRustSpec/Interp.lean",
        ),
        (
            stmts,
            "fn deinit(&mut self, ptr: ThinPointer<M::Provenance>, len: Size, align: Align) -> Result { \
             self.store(ptr, list![AbstractByte::Uninit; len.bytes()], align, Atomicity::None)?; \
             ret(()) }",
            "self.store(ptr, list![AbstractByte::Uninit; len.bytes()], align, Atomicity::Atomic)?;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            stmts,
            "fn eval_statement(&mut self, Statement::Deinit { place }: Statement) -> NdResult { \
             let (p, ty) = self.eval_place(place)?; \
             if !p.aligned { \
                 throw_ub!(\"de-initializing a place based on a misaligned pointer\"); \
             } \
             self.mem.deinit(p.ptr.thin_pointer, ty.layout::<M::T>().expect_size(\"WF ensures deinits are sized\"), Align::ONE)?; \
             ret(()) }",
            "self.mem.deinit(p.ptr.thin_pointer, Size::ZERO, Align::ONE)?;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            stmts,
            "fn storage_live(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult { \
             self.storage_dead(mem, local)?; \
             let pointee_size = self.func.locals[local].layout::<M::T>().expect_size(\"WF ensures all locals are sized\"); \
             let pointee_align = self.func.locals[local].layout::<M::T>().expect_align(\"WF ensures all locals are sized\"); \
             let ptr = mem.allocate(AllocationKind::Stack, pointee_size, pointee_align)?; \
             self.locals.insert(local, ptr); \
             ret(()) }",
            "let ptr = mem.allocate(AllocationKind::Heap, pointee_size, pointee_align)?;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            stmts,
            "fn storage_dead(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult { \
             let pointee_size = self.func.locals[local].layout::<M::T>().expect_size(\"WF ensures all locals are sized\"); \
             let pointee_align = self.func.locals[local].layout::<M::T>().expect_align(\"WF ensures all locals are sized\"); \
             if let Some(ptr) = self.locals.remove(local) { \
                 mem.deallocate(ptr, AllocationKind::Stack, pointee_size, pointee_align)?; \
             } \
             ret(()) }",
            "mem.deallocate(ptr, AllocationKind::Global, pointee_size, pointee_align)?;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            stmts,
            "fn eval_statement(&mut self, Statement::StorageLive(local): Statement) -> NdResult { \
             self.try_mutate_cur_frame(|frame, mem| { frame.storage_live(mem, local) }) } \
             fn eval_statement(&mut self, Statement::StorageDead(local): Statement) -> NdResult { \
             self.try_mutate_cur_frame(|frame, mem| { frame.storage_dead(mem, local) }) }",
            "fn eval_statement(&mut self, Statement::StorageLive(local): Statement) -> NdResult { \
             self.try_mutate_cur_frame(|frame, mem| { frame.storage_dead(mem, local) }) }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "while let Some(local) = frame.locals.keys().next() { \
                 frame.storage_dead(&mut self.mem, local)?; \
             }",
            "while let Some(local) = frame.locals.keys().next() { \
                 frame.storage_live(&mut self.mem, local)?; \
             }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            rvalue,
            "smir::Operand::Copy(place) => \
             ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) }, \
             smir::Operand::Move(place) => \
             ValueExpr::Load { source: GcCow::new(self.translate_place_smir(place, span)) },",
            "smir::Operand::Move(place) => ValueExpr::Tuple(list![], ty),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::StatementKind::StorageLive(local) => \
             Statement::StorageLive(self.local_name_map[&local]), \
             rs::StatementKind::StorageDead(local) => \
             Statement::StorageDead(self.local_name_map[&local]),",
            "rs::StatementKind::StorageLive(local) => Statement::StorageDead(self.local_name_map[&local]),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            func,
            "for (id, local_name) in &self.local_name_map { \
                 let local_decl = &self.body.local_decls[*id]; \
                 let span = local_decl.source_info.span; \
                 let ty = self.cx.translate_ty(local_decl.ty, span); \
                 self.locals.insert(*local_name, ty); \
             }",
            "self.locals.remove(*local_name);",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            func,
            "for i in 1..=(self.body.arg_count) { \
                 if Some(i) == spread_local_idx { .. } else { \
                     args.push(LocalName(Name::from_internal(i as _))); \
                 } \
             } \
             let free_argc = self.body.arg_count + 1; .. \
             init_statements.extend(rs::always_storage_live_locals(&self.body).iter() \
             .map(|loc| self.local_name_map[&loc]) \
             .filter(|LocalName(i)| i.get_internal() as usize >= free_argc) \
             .map(Statement::StorageLive),); .. \
             self.blocks.insert(init_bb, init_blk); .. \
             let ret = LocalName(Name::from_internal(0));",
            ".filter(|LocalName(i)| i.get_internal() as usize < free_argc)",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            wf,
            "let mut start_live: Set<LocalName> = Set::new(); \
             for arg in self.args { \
                 ensure_wf(self.locals.contains_key(arg), \"Function: argument local does not exist\")?; \
                 if start_live.try_insert(arg).is_err() { \
                     throw_ill_formed!(\"Function: two arguments refer to the same local\"); \
                 }; \
             } \
             ensure_wf(self.locals.contains_key(self.ret), \"Function: return local does not exist\")?; \
             if start_live.try_insert(self.ret).is_err() { \
                 throw_ill_formed!(\"Function: return local is also used for an argument\"); \
             };",
            "ensure_wf(!self.locals.contains_key(self.ret), \"Function: return local does not exist\")?;",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            wf,
            "Deinit { place } => { \
                 let ty = place.check_wf::<T>(func.locals, prog)?; \
                 ensure_wf(ty.layout::<T>().is_sized(), \"Statement::Deinit: unsized place\")?; \
             }",
            "ensure_wf(!ty.layout::<T>().is_sized(), \"Statement::Deinit: unsized place\")?;",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            wf,
            "StorageLive(local) => { \
                 ensure_wf(func.locals.contains_key(local), \"Statement::StorageLive: invalid local variable\")?; \
             }",
            "StorageLive(local) => { \
                 ensure_wf(!func.locals.contains_key(local), \"Statement::StorageLive: invalid local variable\")?; \
             }",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            wf,
            "StorageDead(local) => { \
                 ensure_wf(func.locals.contains_key(local), \"Statement::StorageDead: invalid local variable\")?; \
                 if local == func.ret || func.args.any(|arg_name| local == arg_name) { \
                     throw_ill_formed!(\"Statement::StorageDead: trying to mark argument or return local as dead\"); \
                 } \
             }",
            "if local == func.ret && func.args.any(|arg_name| local == arg_name)",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
    ];
    assert_eq!(cases.len(), 22, "expected 22 pinned MR-1.3 quotations");

    let mr13_files = [target, basic, conc, mach, stmts, terms, wf, rvalue, bb, func];
    let lean_root = minirust_dir().join("lean");
    for (file, genuine, tampered, lean_file) in cases {
        assert_eq!(
            missing_piece_in(&corpus, Some(file), genuine),
            None,
            "genuine quotation not found in `{file}`: {genuine}"
        );
        assert!(
            missing_piece_in(&corpus, Some(file), tampered).is_some(),
            "tampered quotation unexpectedly found in `{file}`: {tampered}"
        );
        for other in mr13_files {
            if other != *file {
                assert!(
                    missing_piece_in(&corpus, Some(other), genuine).is_some(),
                    "quotation from `{file}` also matches `{other}`: {genuine}"
                );
            }
        }
        let lean = std::fs::read_to_string(lean_root.join(lean_file)).unwrap();
        let extracted = extract_quotes(&lean, &valid_paths)
            .unwrap_or_else(|e| panic!("extract_quotes failed on `{lean_file}`: {e:?}"));
        let pieces: Vec<String> = strip_line_comments(genuine)
            .split("..")
            .map(squash)
            .filter(|p| !p.is_empty())
            .collect();
        let matched_in_lean = extracted.iter().any(|q| {
            if q.cited_file != *file {
                return false;
            }
            let q_squashed = squash(&strip_line_comments(&q.text));
            let mut pos = 0usize;
            for piece in &pieces {
                let Some(j) = q_squashed[pos..].find(piece.as_str()) else {
                    return false;
                };
                pos += j + piece.len();
            }
            true
        });
        assert!(
            matched_in_lean,
            "`{lean_file}` has no extracted block quote citing `{file}` that contains all pieces of `{genuine}`"
        );
    }
}







#[test]
fn call_return_and_multi_fn_quotations_are_pinned() {
    let corpus = corpus();
    let valid_paths: BTreeSet<String> = corpus.iter().map(|(p, _)| p.clone()).collect();
    let ptr = "spec/mem/pointer.md";
    let types = "spec/lang/types.md";
    let exprs = "spec/lang/step/expressions.md";
    let mach = "spec/lang/machine.md";
    let terms = "spec/lang/step/terminators.md";
    let bb = "tooling/minimize/src/bb.rs";
    let prog = "tooling/minimize/src/program.rs";
    let ty_rs = "tooling/minimize/src/ty.rs";

    let cases: &[(&str, &str, &str, &str)] = &[
        (
            ptr,
            "pub fn meta_kind(self) -> PointerMetaKind { \
                 match self { \
                     PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => pointee.layout.meta_kind(), \
                     PtrType::Raw { meta_kind, .. } => meta_kind, \
                     PtrType::FnPtr | PtrType::VTablePtr(_) => PointerMetaKind::None, \
                 } \
             }",
            "PtrType::FnPtr | PtrType::VTablePtr(_) => PointerMetaKind::ElementCount,",
            "MiniRustSpec/Interp.lean",
        ),
        (
            types,
            "Ptr(p) if p.meta_kind() == PointerMetaKind::None => Sized(T::PTR_SIZE, T::PTR_ALIGN), \
             Ptr(_) => Sized(libspecr::Int::from(2) * T::PTR_SIZE, T::PTR_ALIGN), .. \
             Array { elem, count } => Sized( \
                 elem.layout::<T>().expect_size(\"WF ensures array element is sized\") * count, \
                 elem.layout::<T>().expect_align(\"WF ensures array element is sized\"), \
             ),",
            "Ptr(p) if p.meta_kind() == PointerMetaKind::None => Sized(libspecr::Int::from(2) * T::PTR_SIZE, T::PTR_ALIGN),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            exprs,
            "Constant::FnPointer(fn_name) => { let ptr = self.fn_ptrs[fn_name]; Value::Ptr(ptr.widen(None)) }",
            "Constant::FnPointer(fn_name) => { let ptr = self.fn_ptrs[fn_name]; Value::Ptr(ptr.widen(Some(0))) }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            mach,
            "fn fn_from_ptr(&self, ptr: Value<M>) -> Result<Function> { \
                 if let Value::Ptr(Pointer { thin_pointer: thin_ptr, metadata }) = ptr { \
                     if metadata.is_some() { \
                         throw_ub!(\"invalid pointer for function lookup\"); \
                     }",
            "fn fn_from_ptr(&self, ptr: Value<M>) -> Result<Method> {",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "fn check_abi_compatibility( caller_ty: Type, callee_ty: Type, ) -> bool {",
            "fn check_abi_compatibility( caller_ty: Type, callee_ty: Type, ) -> Result<bool> {",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "fn prepare_for_inplace_passing( &mut self, place: Place<M>, ty: Type, ) -> NdResult {",
            "fn prepare_for_in_place_passing( &mut self, place: Place<M>, ty: Type, ) -> NdResult {",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "fn eval_argument( &mut self, val: ArgumentExpr, ) -> NdResult<(Value<M>, Type)> {",
            "fn eval_argument( &mut self, val: ValueExpr, ) -> NdResult<(Value<M>, Type)> {",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "fn create_frame( \
                 &mut self, \
                 func: Function, \
                 stack_pop_action: StackPopAction<M>, \
                 caller_conv: CallingConvention, \
                 caller_ret_ty: Type, \
                 caller_args: List<(Value<M>, Type)>, \
             ) -> NdResult<StackFrame<M>> {",
            "fn create_frame( &mut self, func: Function, arg_vals: List<Place<M>>, ) -> NdResult<StackFrame<M>> {",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "fn eval_call( \
                 &mut self, \
                 callee: Function, \
                 caller_conv: CallingConvention, \
                 arguments: List<(Value<M>, Type)>, \
                 caller_ret: (Place<M>, Type), \
                 next_block: Option<BbName>, \
                 unwind_block: Option<BbName>, \
             ) -> NdResult {",
            "fn eval_call(&mut self, func: FnName, caller_conv: CallingConvention) -> NdResult {",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "Terminator::Call { callee, calling_convention: caller_conv, arguments, ret: ret_expr, next_block, unwind_block }: Terminator",
            "Terminator::Call { callee, calling_convention: caller_conv, arguments, ret: ret_expr, next_block, unwind_block }: Statement",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "StackPopAction::BackToCaller { ret_val_ptr: caller_ret_ptr, next_block, .. } => {",
            "StackPopAction::BackToCaller { ret_val_ptr: caller_ret_ptr, next_block } => {",
            "MiniRustSpec/Interp.lean",
        ),
        (
            prog,
            "let entry_name = FnName(Name::from_internal(0)); \
             self.fn_name_map.insert(entry_instance, entry_name);",
            "let entry_name = FnName(Name::from_internal(1)); \
             self.fn_name_map.insert(entry_instance, entry_name);",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "match &x.node { \
                 rs::Operand::Move(place) => \
                     ArgumentExpr::InPlace(self.translate_place(&place, x.span)), \
                 op => ArgumentExpr::ByValue(self.translate_operand(op, x.span)), \
             }",
            "rs::Operand::Move(place) => ArgumentExpr::ByValue(self.translate_place(&place, x.span)),",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::UnwindAction::Continue => { .. \
                 let block_kind = BbKind::Cleanup; \
                 let unwind_bb_name = self.fresh_bb_name(); \
                 let unwind_bb = BasicBlock { \
                     statements: list![], \
                     terminator: Terminator::ResumeUnwind, \
                     kind: block_kind, \
                 };",
            "rs::UnwindAction::Continue => { let block_kind = BbKind::Regular;",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "let unwind_block = Some(self.translate_unwind_action(unwind, bb)); .. \
             build::fn_ptr(self.cx.get_fn_name(instance)) .. \
             Terminator::Call { \
                 callee, \
                 calling_convention: conv, \
                 arguments: args, \
                 ret: self.translate_place(&destination, span), \
                 next_block: target.as_ref().map(|t| self.bb_name_map[t]), \
                 unwind_block, \
             }",
            "let unwind_block = None; Terminator::Call { callee,",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            prog,
            "fn mk_start_fn(entry: u32) -> Function { \
                 let b0_name = BbName(Name::from_internal(0)); \
                 let b1_name = BbName(Name::from_internal(1)); \
                 let b2_name = BbName(Name::from_internal(2)); \
                 let l0_name = LocalName(Name::from_internal(0));",
            "fn mk_start_fn(entry: u64) -> Function {",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            prog,
            "let number_of_fns = self.fn_name_map.len(); \
             let start = FnName(Name::from_internal(number_of_fns as _)); \
             self.functions.insert(start, mk_start_fn(0)); \
             Program { \
                 start, \
                 functions: self.functions, \
                 globals: self.globals, \
                 vtables: self.vtables, \
                 traits: self.traits, \
             }",
            "self.functions.insert(start, mk_start_fn(1));",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            ty_rs,
            "pub fn translate_calling_convention(conv: rs::CanonAbi) -> CallingConvention { \
                 match conv { \
                     rs::CanonAbi::C => CallingConvention::C, \
                     rs::CanonAbi::Rust => CallingConvention::Rust, \
                     .. \
                 } \
             }",
            "rs::CanonAbi::C => CallingConvention::Rust,",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "let abi = self \
                 .cx \
                 .tcx \
                 .fn_abi_of_instance(self.typing_env().as_query_input((instance, rs::List::empty()))) \
                 .unwrap(); \
             let conv = translate_calling_convention(abi.conv);",
            ".fn_abi_of_instance(self.typing_env().as_query_input((instance, rs::List::empty()))) \
                 .unwrap(); \
             let conv = CallingConvention::Rust;",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            prog,
            "pub fn get_fn_name(&mut self, key: rs::Instance<'tcx>) -> FnName { \
                 let len = self.fn_name_map.len(); \
                 *self.fn_name_map.entry(key).or_insert_with(|| FnName(Name::from_internal(len as _))) \
             }",
            "*self.fn_name_map.entry(key).or_insert_with(|| FnName(Name::from_internal(0)))",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
    ];
    assert_eq!(cases.len(), 20, "expected 20 pinned MR-4.1 quotations");

    let mr41_files = [ptr, types, exprs, mach, terms, bb, prog, ty_rs];
    let lean_root = minirust_dir().join("lean");
    for (file, genuine, tampered, lean_file) in cases {
        assert_eq!(
            missing_piece_in(&corpus, Some(file), genuine),
            None,
            "genuine quotation not found in `{file}`: {genuine}"
        );
        assert!(
            missing_piece_in(&corpus, Some(file), tampered).is_some(),
            "tampered quotation unexpectedly found in `{file}`: {tampered}"
        );
        for other in mr41_files {
            if other != *file {
                assert!(
                    missing_piece_in(&corpus, Some(other), genuine).is_some(),
                    "quotation from `{file}` also matches `{other}`: {genuine}"
                );
            }
        }
        let lean = std::fs::read_to_string(lean_root.join(lean_file)).unwrap();
        let extracted = extract_quotes(&lean, &valid_paths)
            .unwrap_or_else(|e| panic!("extract_quotes failed on `{lean_file}`: {e:?}"));
        let pieces: Vec<String> = strip_line_comments(genuine)
            .split("..")
            .map(squash)
            .filter(|p| !p.is_empty())
            .collect();
        let matched_in_lean = extracted.iter().any(|q| {
            if q.cited_file != *file {
                return false;
            }
            let q_squashed = squash(&strip_line_comments(&q.text));
            let mut pos = 0usize;
            for piece in &pieces {
                let Some(j) = q_squashed[pos..].find(piece.as_str()) else {
                    return false;
                };
                pos += j + piece.len();
            }
            true
        });
        assert!(
            matched_in_lean,
            "`{lean_file}` has no extracted block quote citing `{file}` that contains all pieces of `{genuine}`"
        );
    }
}

#[test]
fn intrinsic_and_assume_quotations_are_pinned() {
    let corpus = corpus();
    let valid_paths: BTreeSet<String> = corpus.iter().map(|(p, _)| p.clone()).collect();
    let intr = "spec/lang/step/intrinsics.md";
    let terms = "spec/lang/step/terminators.md";
    let exprs = "spec/lang/step/expressions.md";
    let prelude = "spec/prelude/main.md";
    let basic = "spec/mem/basic.md";
    let intptr = "spec/mem/intptrcast.md";
    let bb = "tooling/minimize/src/bb.rs";

    let cases: &[(&str, &str, &str, &str)] = &[
        (
            intr,
            "fn unit_value<M: Memory>() -> Value<M> { Value::Tuple(list![]) }",
            "fn unit_value<M: Memory>() -> Value<M> { Value::Tuple(list![Value::Bool(true)]) }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intr,
            "fn unit_type() -> Type { \
                 Type::Tuple { sized_fields: list![], sized_head_layout: TupleHeadLayout { \
                     end: Size::ZERO, align: Align::ONE, packed_align: None, \
                 }, unsized_field: None } \
             }",
            "end: Size::ZERO, align: Align::ONE, packed_align: Some(Align::ONE),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intr,
            "if !b { \
                 throw_ub!(\"`Assume` intrinsic called on condition that is violated\"); \
             } \
             ret(unit_value())",
            "if b { throw_ub!(\"`Assume` intrinsic called on condition that is violated\"); }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intr,
            "IntrinsicOp::Abort: IntrinsicOp, \
             arguments: List<(Value<M>, Type)>, \
             ret_ty: Type, \
             ) -> NdResult<Value<M>> { \
                 throw_abort!(); \
             }",
            "IntrinsicOp::Abort: IntrinsicOp, \
             arguments: List<(Value<M>, Type)>, \
             ret_ty: Type, \
             ) -> NdResult<Value<M>> { \
                 throw_ub!(\"abort\"); \
             }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intr,
            "fn exit(&self) -> NdResult<!> { .. self.mem.leak_check()?; .. throw_machine_stop!(); }",
            "fn exit(&self) -> NdResult<!> { throw_machine_stop!(); }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intr,
            "Value::Int(i) => write!(stream, \"{}\\n\", i).unwrap(), \
             Value::Bool(b) => write!(stream, \"{}\\n\", b).unwrap(), \
             _ => throw_ub!(\"unsupported value for printing\"),",
            "Value::Int(i) => write!(stream, \"{}\", i).unwrap(),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intr,
            "self.intptrcast.expose(ptr); ret(Value::Int(ptr.addr))",
            "self.intptrcast.expose(ptr); ret(Value::Int(ptr.addr + 1))",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "Terminator::Intrinsic { intrinsic, arguments, ret: ret_expr, next_block }: Terminator \
             ) -> NdResult { \
                 let (ret_place, ret_ty) = self.eval_place(ret_expr)?; \
                 let arguments = arguments.try_map(|arg| self.eval_value(arg))?; \
                 let value = self.eval_intrinsic(intrinsic, arguments, ret_ty)?; \
                 self.place_store(ret_place, value, ret_ty)?;",
            "let value = self.eval_intrinsic(intrinsic, arguments, ret_ty)?; \
             self.place_store(ret_place, value, unit_type())?;",
            "MiniRustSpec/Interp.lean",
        ),
        (
            terms,
            "throw_ub!(\"return from an intrinsic where caller did not specify next block\");",
            "throw_ub!(\"return from an intrinsic where callee did not specify next block\");",
            "MiniRustSpec/Interp.lean",
        ),
        (
            exprs,
            "let aligned = self.compute_align(ty.layout::<M::T>(), ptr.metadata).is_aligned(ptr.thin_pointer.addr); \
             ret((Place { ptr, aligned }, ty))",
            "ret((Place { ptr, aligned: true }, ty))",
            "MiniRustSpec/Interp.lean",
        ),
        (
            prelude,
            "macro_rules! throw_abort { () => { do yeet TerminationInfo::Abort } }",
            "macro_rules! throw_abort { () => { do yeet TerminationInfo::MachineStop } }",
            "MiniRustSpec/Interp.lean",
        ),
        (
            basic,
            "match allocation.kind { .. Heap => throw_memory_leak!(), .. \
                 Global | Function | Stack | VTable => {} \
             }",
            "Stack => throw_memory_leak!(),",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intptr,
            "pub fn expose(&mut self, ptr: ThinPointer<Provenance>) { \
                 if let Some(provenance) = ptr.provenance { .. \
                     self.exposed.insert(provenance); \
                 } \
             }",
            "if let Some(provenance) = ptr.provenance { self.exposed.remove(provenance);",
            "MiniRustSpec/Interp.lean",
        ),
        (
            bb,
            "enum StatementResult { \
                 Statement(Statement), \
                 Intrinsic { intrinsic: IntrinsicOp, destination: PlaceExpr, arguments: List<ValueExpr> }, \
             }",
            "Intrinsic { intrinsic: IntrinsicOp, arguments: List<ValueExpr> },",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::NonDivergingIntrinsic::Assume(op) => { \
                 let op = self.translate_operand(op, span); .. \
                 let destination = build::unit_place(); \
                 return StatementResult::Intrinsic { \
                     intrinsic: IntrinsicOp::Assume, \
                     destination, \
                     arguments: list![op], \
                 }; \
             }",
            "return StatementResult::Intrinsic { \
                 intrinsic: IntrinsicOp::Abort, \
                 destination, \
                 arguments: list![op], \
             };",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "StatementResult::Intrinsic { intrinsic, destination, arguments } => { .. \
                 let next_bb = self.fresh_bb_name(); .. \
                 let terminator = Terminator::Intrinsic { \
                     intrinsic, \
                     arguments, \
                     ret: destination, \
                     next_block: Some(next_bb), \
                 };",
            "let terminator = Terminator::Intrinsic { \
                 intrinsic, \
                 arguments, \
                 ret: destination, \
                 next_block: None, \
             };",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "let TerminatorResult { stmts, terminator } = self.translate_terminator(bb); \
             for stmt in stmts.iter() { \
                 cur_block_statements.push(stmt); \
             }",
            "let TerminatorResult { stmts, terminator } = self.translate_terminator(bb); \
             let cur_block =",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::NonDivergingIntrinsic::CopyNonOverlapping(_) => \
                 rs::span_bug!(span, \"NonDivergingIntrinsic not supported: {intrinsic:?}\"),",
            "rs::NonDivergingIntrinsic::CopyNonOverlapping(_) => StatementResult::Statement(",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            intr,
            "fn load_raw_data(&mut self, ptr : Pointer<<M as Memory>::Provenance>, ptr_ty : PtrType) -> Result<List<u8>> { \
                 let PtrType::Ref { pointee, .. } = ptr_ty else { \
                     throw_ub!(\"invalid argument to `RawEq` intrinsic: not a reference\"); \
                 }; .. \
                 let Some(data) = bytes.try_map(|byte| byte.data()) else { \
                     throw_ub!(\"invalid argument to `RawEq` intrinsic: byte is uninitialized\"); \
                 };",
            "let PtrType::Raw { .. } = ptr_ty else { \
                 throw_ub!(\"invalid argument to `RawEq` intrinsic: not a reference\");",
            "MiniRustSpec/Interp.lean",
        ),
        (
            intr,
            "IntrinsicOp::RawEq: IntrinsicOp, .. \
             if l_ty != r_ty { \
                 throw_ub!(\"invalid arguments to `RawEq` intrinsic: types of arguments are not identical\"); \
             } .. \
             let left_data = self.load_raw_data(left, l_ty)?; \
             let right_data = self.load_raw_data(right, l_ty)?; \
             ret(Value::Bool(left_data == right_data))",
            "ret(Value::Bool(left_data != right_data))",
            "MiniRustSpec/Interp.lean",
        ),
        (
            bb,
            "struct TerminatorResult { \
                 stmts: List<Statement>, \
                 terminator: Terminator, \
             }",
            "struct TerminatorResult { terminator: Terminator }",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::sym::raw_eq => \
                 return TerminatorResult { \
                     stmts: List::new(), \
                     terminator: Terminator::Intrinsic { \
                         intrinsic: IntrinsicOp::RawEq,",
            "rs::sym::raw_eq => return TerminatorResult { stmts: List::new(), terminator: Terminator::Goto(",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::sym::ctpop => { .. \
                 let val = build::count_ones(v); \
                 let stmt = Statement::Assign { destination, source: val }; \
                 let terminator = Terminator::Goto(self.bb_name_map[&target.unwrap()]); .. \
             } \
             rs::sym::exact_div => { .. \
                 let val = build::div_exact(l, r); \
                 let stmt = Statement::Assign { destination, source: val };",
            "rs::sym::ctpop => { let val = build::div_exact(v, v);",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::sym::cold_path => { .. \
                 let terminator = Terminator::Goto(self.bb_name_map[&target.unwrap()]); \
                 return TerminatorResult { stmts: list![], terminator }; \
             }",
            "rs::sym::cold_path => { let terminator = build::abort();",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
        (
            bb,
            "rs::sym::abort => { \
                 let terminator = build::abort(); \
                 TerminatorResult { stmts: list![], terminator } \
             }",
            "rs::sym::abort => { let terminator = Terminator::Unreachable;",
            "MiniRustSpec/Correspondence/Translate.lean",
        ),
    ];
    assert_eq!(cases.len(), 25, "expected 25 pinned MR-4.2 quotations");

    let mr42_files = [intr, terms, exprs, prelude, basic, intptr, bb];
    let lean_root = minirust_dir().join("lean");
    for (file, genuine, tampered, lean_file) in cases {
        assert_eq!(
            missing_piece_in(&corpus, Some(file), genuine),
            None,
            "genuine quotation not found in `{file}`: {genuine}"
        );
        assert!(
            missing_piece_in(&corpus, Some(file), tampered).is_some(),
            "tampered quotation unexpectedly found in `{file}`: {tampered}"
        );
        for other in mr42_files {
            if other != *file {
                assert!(
                    missing_piece_in(&corpus, Some(other), genuine).is_some(),
                    "quotation from `{file}` also matches `{other}`: {genuine}"
                );
            }
        }
        let lean = std::fs::read_to_string(lean_root.join(lean_file)).unwrap();
        let extracted = extract_quotes(&lean, &valid_paths)
            .unwrap_or_else(|e| panic!("extract_quotes failed on `{lean_file}`: {e:?}"));
        let pieces: Vec<String> = strip_line_comments(genuine)
            .split("..")
            .map(squash)
            .filter(|p| !p.is_empty())
            .collect();
        let matched_in_lean = extracted.iter().any(|q| {
            if q.cited_file != *file {
                return false;
            }
            let q_squashed = squash(&strip_line_comments(&q.text));
            let mut pos = 0usize;
            for piece in &pieces {
                let Some(j) = q_squashed[pos..].find(piece.as_str()) else {
                    return false;
                };
                pos += j + piece.len();
            }
            true
        });
        assert!(
            matched_in_lean,
            "`{lean_file}` has no extracted block quote citing `{file}` that contains all pieces of `{genuine}`"
        );
    }
}
