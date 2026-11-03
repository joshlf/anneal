// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Lean 4 surface-syntax helpers: identifier escaping, string literals, and a
//! tiny deterministic pretty-printer for constructor terms.

/// Lean 4 keywords and reserved tokens that cannot be used as bare
/// identifiers. Any MiniRust identifier in this set is wrapped in `«»`.
const LEAN_RESERVED: &[&str] = &[
    "Prop", "Sort", "Type", "abbrev", "at", "axiom", "begin", "break", "by", "calc", "catch",
    "class", "continue", "def", "deriving", "do", "else", "end", "example", "exists", "export",
    "extends", "finally", "for", "forall", "from", "fun", "have", "hiding", "if", "import", "in",
    "include", "inductive", "infix", "infixl", "infixr", "instance", "let", "local", "macro",
    "match", "meta", "module", "mut", "mutual", "namespace", "noncomputable", "nomatch", "nofun",
    "notation", "obtain", "omit", "opaque", "open", "partial", "postfix", "prefix", "private",
    "protected", "public", "renaming", "return", "section", "set_option", "show", "structure",
    "suffices", "syntax", "then", "theorem", "try", "universe", "unless", "unsafe", "using",
    "variable", "where", "with", "λ",
];

/// Renders `name` as a Lean identifier component, escaping with `«»` when the
/// name is a Lean keyword or is not a plain ASCII identifier.
pub fn ident(name: &str) -> String {
    let plain = !name.is_empty()
        && name.chars().next().map(|c| c.is_ascii_alphabetic() || c == '_').unwrap_or(false)
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && name != "_";
    if plain && !LEAN_RESERVED.contains(&name) {
        name.to_string()
    } else {
        assert!(!name.contains('«') && !name.contains('»'), "unescapable identifier {name:?}");
        format!("«{name}»")
    }
}

/// Renders `s` as a Lean string literal.
pub fn string_lit(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Renders `s` so that it can appear inside a Lean `/-- ... -/` docstring.
pub fn doc_text(s: &str) -> String {
    s.replace("-/", "- /").replace("/-", "/ -")
}

/// A Lean term built only from constructor applications, list literals, and
/// atoms. Rendering is deterministic and width-bounded.
#[derive(Debug, Clone)]
pub enum Term {
    /// An atom rendered verbatim (`"str"`, `42`, `true`, `none`, a name).
    Atom(String),
    /// `(head arg₁ … argₙ)`; rendered without parentheses when `n = 0`.
    App(String, Vec<Term>),
    /// `[t₁, …, tₙ]`.
    List(Vec<Term>),
}

impl Term {
    pub fn atom(s: impl Into<String>) -> Term {
        Term::Atom(s.into())
    }
    pub fn app(head: impl Into<String>, args: Vec<Term>) -> Term {
        Term::App(head.into(), args)
    }
    pub fn str(s: &str) -> Term {
        Term::Atom(string_lit(s))
    }
    pub fn bool(b: bool) -> Term {
        Term::Atom(if b { "true" } else { "false" }.to_string())
    }
    pub fn nat(n: u128) -> Term {
        Term::Atom(n.to_string())
    }
    pub fn option(t: Option<Term>) -> Term {
        match t {
            None => Term::Atom("none".to_string()),
            Some(t) => Term::App("some".to_string(), vec![t]),
        }
    }

    fn flat(&self, out: &mut String) {
        match self {
            Term::Atom(s) => out.push_str(s),
            Term::App(h, args) if args.is_empty() => out.push_str(h),
            Term::App(h, args) => {
                out.push('(');
                out.push_str(h);
                for a in args {
                    out.push(' ');
                    a.flat(out);
                }
                out.push(')');
            }
            Term::List(items) => {
                out.push('[');
                for (i, a) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    a.flat(out);
                }
                out.push(']');
            }
        }
    }

    /// Renders the term flat (single line).
    pub fn to_flat(&self) -> String {
        let mut s = String::new();
        self.flat(&mut s);
        s
    }

    /// Renders the term with line breaks so that lines stay near `width`
    /// columns, starting at column `indent`.
    pub fn render(&self, indent: usize, width: usize) -> String {
        let mut out = String::new();
        self.render_into(indent, width, &mut out);
        out
    }

    fn render_into(&self, indent: usize, width: usize, out: &mut String) {
        let flat = self.to_flat();
        if indent + flat.len() <= width || matches!(self, Term::Atom(_)) {
            out.push_str(&flat);
            return;
        }
        let pad = " ".repeat(indent + 2);
        match self {
            Term::Atom(_) => unreachable!(),
            Term::App(h, args) => {
                if args.is_empty() {
                    out.push_str(h);
                    return;
                }
                out.push('(');
                out.push_str(h);
                for a in args {
                    out.push('\n');
                    out.push_str(&pad);
                    a.render_into(indent + 2, width, out);
                }
                out.push(')');
            }
            Term::List(items) => {
                if items.is_empty() {
                    out.push_str("[]");
                    return;
                }
                out.push('[');
                for (i, a) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push('\n');
                    out.push_str(&pad);
                    a.render_into(indent + 2, width, out);
                }
                out.push(']');
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_keywords_and_odd_names() {
        assert_eq!(ident("Type"), "«Type»");
        assert_eq!(ident("end"), "«end»");
        assert_eq!(ident("foo_bar"), "foo_bar");
        assert_eq!(ident("x86_64"), "x86_64");
        assert_eq!(ident("0abc"), "«0abc»");
    }

    #[test]
    fn string_literals_escape() {
        assert_eq!(string_lit("a\"b\\c\nd"), "\"a\\\"b\\\\c\\nd\"");
    }

    #[test]
    fn renders_flat_and_broken() {
        let t = Term::app("F", vec![Term::str("x"), Term::List(vec![Term::nat(1), Term::nat(2)])]);
        assert_eq!(t.render(0, 80), "(F \"x\" [1, 2])");
        assert_eq!(t.render(0, 5), "(F\n  \"x\"\n  [\n    1,\n    2])");
    }
}
