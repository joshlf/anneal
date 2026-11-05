// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The Anneal specification grammar.
//!
//! # Where specifications come from
//!
//! A specification is a line of a doc comment (`/// anneal:...`) or of an
//! equivalent `#[doc = "anneal:..."]` attribute. The capture reads these from
//! `rustc`'s HIR attribute table after macro expansion and `cfg` stripping,
//! never from source text, so `rustc` alone decides which text is a doc
//! comment: an `anneal:` string inside a string literal, a `//` comment, or a
//! `/* */` comment is not an attribute and is invisible to the capture.
//!
//! Doc comments were chosen over a tool attribute (`#[anneal::spec(..)]`)
//! because tool attributes need the unstable `register_tool` feature, so the
//! annotated crate would no longer build with a stable toolchain, and
//! because the existing fixtures already use `///` comments.
//!
//! A plain `// anneal:spec ...` line comment is therefore silently ignored:
//! `rustc` discards ordinary comments, so the function is verified only against
//! its mandatory obligations. That is sound (fewer claims are proved, and the
//! emitted `Mir.lean` shows exactly which ones), but a user may not expect it.
//!
//! # Grammar
//!
//! Each doc-comment line is trimmed. A line that contains `anneal:` must
//! start with it, and must then be exactly one of:
//!
//! ```text
//! anneal:spec ensures(ret == IDENT)    on a function; IDENT is a parameter
//! anneal:spec well_formed              on a function; adds nothing
//! anneal:requires IDENT != INT         on a function; IDENT is a `usize`
//!                                      parameter (enters `SafetyPre` on
//!                                      `unsafe fn`, or narrows `ContractPost`
//!                                      on safe `fn`)
//! anneal:trusted reason = "..."        on a function; waives its behavioral
//!                                      obligation in `Crate.tcbWaivedIds`
//! anneal:invariant IDENT != INT        on a struct; IDENT is its `usize`
//!                                      field
//! ```
//!
//! Tokens may be separated by any whitespace. Any other `anneal:` line is an
//! error, as is a directive attached to an item kind that does not accept it.
//! `items.rs` enforces placement and resolves `IDENT`.

/// A parsed directive, with identifiers not yet resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Directive {
    EnsuresRetEq(String),
    WellFormed,
    Requires { ident: String, ne: u128 },
    Trusted { reason: String },
    Invariant { ident: String, ne: u128 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Int(u128),
    Str(String),
    LParen,
    RParen,
    Eq,
    EqEq,
    Ne,
}

fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let mut out = Vec::new();
    let mut it = s.char_indices().peekable();
    while let Some((i, c)) = it.next() {
        match c {
            c if c.is_whitespace() => {}
            '(' => out.push(Tok::LParen),
            ')' => out.push(Tok::RParen),
            '=' => match it.peek() {
                Some(&(_, '=')) => {
                    it.next();
                    out.push(Tok::EqEq);
                }
                _ => out.push(Tok::Eq),
            },
            '!' => match it.next() {
                Some((_, '=')) => out.push(Tok::Ne),
                _ => return Err(format!("expected `!=` at offset {i}")),
            },
            '"' => {
                let mut val = String::new();
                let mut closed = false;
                while let Some((_, d)) = it.next() {
                    match d {
                        '"' => {
                            closed = true;
                            break;
                        }
                        '\\' => match it.next() {
                            Some((_, esc @ ('"' | '\\'))) => val.push(esc),
                            _ => {
                                return Err(format!(
                                    "unsupported escape sequence in string \
                                     literal at offset {i}"
                                ));
                            }
                        },
                        _ => val.push(d),
                    }
                }
                if !closed {
                    return Err(format!(
                        "unterminated string literal at offset {i}"
                    ));
                }
                out.push(Tok::Str(val));
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut id = String::from(c);
                while let Some(&(_, d)) = it.peek() {
                    if d.is_ascii_alphanumeric() || d == '_' {
                        id.push(d);
                        it.next();
                    } else {
                        break;
                    }
                }
                out.push(Tok::Ident(id));
            }
            c if c.is_ascii_digit() => {
                let mut n = String::from(c);
                while let Some(&(_, d)) = it.peek() {
                    if d.is_ascii_digit() {
                        n.push(d);
                        it.next();
                    } else {
                        break;
                    }
                }
                out.push(Tok::Int(
                    n.parse()
                        .map_err(|_| format!("integer `{n}` too large"))?,
                ));
            }
            _ => {
                return Err(format!(
                    "unexpected character `{c}` at offset {i}"
                ));
            }
        }
    }
    Ok(out)
}

/// Parses every `anneal:` line of one doc-comment attribute.
///
/// Returns the directives in order; lines without `anneal:` are ordinary
/// documentation and are skipped.
pub fn parse_doc(doc: &str) -> Result<Vec<Directive>, String> {
    let mut out = Vec::new();
    for raw in doc.lines() {
        let line = raw.trim();
        if !line.contains("anneal:") {
            continue;
        }
        let Some(rest) = line.strip_prefix("anneal:") else {
            return Err(format!(
                "`anneal:` must start the doc-comment line: `{line}`"
            ));
        };
        let toks = lex(rest).map_err(|e| format!("in `{line}`: {e}"))?;
        use Tok::*;
        let d = match toks.as_slice() {
            [Ident(k), Ident(e), LParen, Ident(r), EqEq, Ident(x), RParen]
                if k == "spec" && e == "ensures" && r == "ret" =>
            {
                Directive::EnsuresRetEq(x.clone())
            }
            [Ident(k), Ident(w)] if k == "spec" && w == "well_formed" => {
                Directive::WellFormed
            }
            [Ident(k), Ident(x), Ne, Int(n)] if k == "requires" => {
                Directive::Requires { ident: x.clone(), ne: *n }
            }
            [Ident(k), Ident(r), Eq, Str(reason)]
                if k == "trusted" && r == "reason" =>
            {
                if reason.trim().is_empty() {
                    return Err(format!(
                        "`anneal:trusted` requires a non-empty reason: `{line}`"
                    ));
                }
                Directive::Trusted { reason: reason.clone() }
            }
            [Ident(k), Ident(x), Ne, Int(n)] if k == "invariant" => {
                Directive::Invariant { ident: x.clone(), ne: *n }
            }
            _ => return Err(format!("unsupported Anneal directive `{line}`")),
        };
        out.push(d);
    }
    Ok(out)
}
