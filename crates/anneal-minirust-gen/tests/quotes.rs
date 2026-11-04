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
    assert!(total >= 40, "only {total} quotations found");

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
