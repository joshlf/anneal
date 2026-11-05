// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The pin file `minirust/minirust.lock.toml`.
//!
//! The lock file records which upstream MiniRust snapshot the generated Lean
//! model was derived from, which `rustc` dialect Anneal's MIR model targets,
//! and the SHA-256 digest of every vendored upstream file. The generator
//! refuses to run unless the vendored tree matches the lock file exactly, so a
//! hand edit to a vendored specification file cannot silently change the
//! generated model.
//!
//! The file uses a small TOML subset (sections, string-valued keys, comments)
//! so that it can be parsed here without a TOML dependency while remaining
//! readable by standard TOML tools such as Python's `tomllib`.

use std::collections::BTreeMap;

/// A parsed lock file: section name to (key to string value).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Lock {
    pub sections: BTreeMap<String, BTreeMap<String, String>>,
}

impl Lock {
    /// Returns the value of `key` in `[section]`, or an error naming both.
    pub fn get(&self, section: &str, key: &str) -> Result<&str, String> {
        self.sections
            .get(section)
            .and_then(|s| s.get(key))
            .map(String::as_str)
            .ok_or_else(|| format!("lock file is missing `{key}` in `[{section}]`"))
    }

    /// Returns all entries of `[section]` (empty if the section is absent).
    pub fn section(&self, section: &str) -> BTreeMap<String, String> {
        self.sections.get(section).cloned().unwrap_or_default()
    }
}

fn parse_string(s: &str, line_no: usize) -> Result<(String, &str), String> {
    let rest = s.strip_prefix('"').ok_or_else(|| format!("line {line_no}: expected '\"'"))?;
    let mut out = String::new();
    let mut chars = rest.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '"' => return Ok((out, &rest[i + 1..])),
            '\\' => match chars.next() {
                Some((_, '"')) => out.push('"'),
                Some((_, '\\')) => out.push('\\'),
                other => return Err(format!("line {line_no}: unsupported escape {other:?}")),
            },
            c => out.push(c),
        }
    }
    Err(format!("line {line_no}: unterminated string"))
}

/// Parses the lock-file TOML subset.
pub fn parse(text: &str) -> Result<Lock, String> {
    let mut lock = Lock::default();
    let mut current: Option<String> = None;
    for (idx, raw) in text.lines().enumerate() {
        let line_no = idx + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(name) = line.strip_prefix('[') {
            let name = name
                .strip_suffix(']')
                .ok_or_else(|| format!("line {line_no}: malformed section header"))?;
            current = Some(name.trim().to_string());
            lock.sections.entry(name.trim().to_string()).or_default();
            continue;
        }
        let section =
            current.clone().ok_or_else(|| format!("line {line_no}: key outside any section"))?;
        let (key, rest) = if line.starts_with('"') {
            parse_string(line, line_no)?
        } else {
            let end = line.find(|c: char| c.is_whitespace() || c == '=').unwrap_or(line.len());
            (line[..end].to_string(), &line[end..])
        };
        let rest = rest.trim_start();
        let rest = rest
            .strip_prefix('=')
            .ok_or_else(|| format!("line {line_no}: expected '=' after key `{key}`"))?
            .trim_start();
        let (value, tail) = parse_string(rest, line_no)?;
        let tail = tail.trim();
        if !tail.is_empty() && !tail.starts_with('#') {
            return Err(format!("line {line_no}: trailing characters after value"));
        }
        let entries = lock.sections.entry(section).or_default();
        if entries.insert(key.clone(), value).is_some() {
            return Err(format!("line {line_no}: duplicate key `{key}`"));
        }
    }
    Ok(lock)
}

fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Renders a lock file deterministically: a header comment, then sections in
/// the order given, keys within each section in the order given.
pub fn render(header: &str, sections: &[(&str, Vec<(String, String)>)]) -> String {
    let mut out = String::new();
    for line in header.lines() {
        if line.is_empty() {
            out.push_str("#\n");
        } else {
            out.push_str("# ");
            out.push_str(line);
            out.push('\n');
        }
    }
    for (name, entries) in sections {
        out.push('\n');
        out.push_str(&format!("[{name}]\n"));
        for (k, v) in entries {
            let key = if k.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-') {
                k.clone()
            } else {
                quote(k)
            };
            out.push_str(&format!("{key} = {}\n", quote(v)));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips() {
        let text = render(
            "hdr",
            &[
                ("a", vec![("k".into(), "v\"q".into())]),
                ("files", vec![("spec/x.md".into(), "00".into())]),
            ],
        );
        let lock = parse(&text).unwrap();
        assert_eq!(lock.get("a", "k").unwrap(), "v\"q");
        assert_eq!(lock.get("files", "spec/x.md").unwrap(), "00");
    }

    #[test]
    fn rejects_duplicates_and_garbage() {
        assert!(parse("[a]\nk = \"1\"\nk = \"2\"\n").is_err());
        assert!(parse("k = \"1\"\n").is_err());
        assert!(parse("[a]\nk = \"1\" junk\n").is_err());
    }
}
