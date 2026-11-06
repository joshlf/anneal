// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Extraction of fenced code blocks from MiniRust's Markdown specification.
//!
//! Upstream MiniRust writes its specification as Markdown files whose
//! ```` ```rust ```` fenced blocks contain specr-lang source. The upstream
//! `specr-transpile` tool concatenates those blocks per module; we keep each
//! block separate so that every generated Lean declaration can cite the exact
//! file and line it came from.
//!
//! The extractor is deliberately literal: a fence opens on a line whose trimmed
//! text starts with three backticks and closes on the next such line. The info
//! string after the opening backticks is recorded verbatim so that non-`rust`
//! blocks are reported (not silently dropped) by the coverage report.

/// One fenced code block from a Markdown file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeBlock {
    /// Info string after the opening fence (for example `rust`, or empty).
    pub info: String,
    /// 1-based line number of the first line *inside* the fence.
    pub first_line: usize,
    /// Text between the fences, with `\n` line endings.
    pub text: String,
}

/// Extracts every fenced code block from `markdown`, in source order.
///
/// Returns an error if a fence is left open at end of file, since a truncated
/// specification file must not be translated as if it were complete.
pub fn extract_code_blocks(markdown: &str) -> Result<Vec<CodeBlock>, String> {
    let mut blocks = Vec::new();
    let mut open: Option<(String, usize, Vec<&str>)> = None;
    for (idx, raw_line) in markdown.split('\n').enumerate() {
        let line = raw_line.strip_suffix('\r').unwrap_or(raw_line);
        let trimmed = line.trim_start();
        let is_fence = trimmed.starts_with("```");
        match (&mut open, is_fence) {
            (None, true) => {
                let info = trimmed.trim_start_matches('`').trim().to_string();
                open = Some((info, idx + 2, Vec::new()));
            }
            (Some(_), true) => {
                let (info, first_line, lines) = open.take().expect("checked Some");
                let mut text = lines.join("\n");
                text.push('\n');
                blocks.push(CodeBlock { info, first_line, text });
            }
            (Some((_, _, lines)), false) => lines.push(line),
            (None, false) => {}
        }
    }
    if let Some((_, first_line, _)) = open {
        return Err(format!("unterminated code fence opened before line {first_line}"));
    }
    Ok(blocks)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extracts_blocks_with_info_and_lines() {
        let md = "# T\n\n```rust\nfn a() {}\n```\ntext\n```\nraw\n```\n";
        let blocks = extract_code_blocks(md).unwrap();
        assert_eq!(blocks.len(), 2);
        assert_eq!(blocks[0].info, "rust");
        assert_eq!(blocks[0].first_line, 4);
        assert_eq!(blocks[0].text, "fn a() {}\n");
        assert_eq!(blocks[1].info, "");
        assert_eq!(blocks[1].text, "raw\n");
    }

    #[test]
    fn rejects_unterminated_fence() {
        assert!(extract_code_blocks("```rust\nfn a() {}\n").is_err());
    }
}
