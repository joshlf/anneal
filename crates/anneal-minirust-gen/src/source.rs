// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Loading the vendored MiniRust specification: file discovery, fenced-block
//! extraction, `syn` parsing, and stable naming of top-level items.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::markdown::{CodeBlock, extract_code_blocks};
use crate::sha256::sha256_hex;

/// One parsed top-level specr-lang item with its provenance.
pub struct SourceItem {
    /// Stable Lean-facing name, unique within its file (for example
    /// `struct_Machine` or `impl_Machine__eval_terminator_2`).
    pub name: String,
    /// 1-based line in the Markdown file where the item starts.
    pub line: usize,
    /// 0-based index of the fenced block within the file.
    pub block: usize,
    /// SHA-256 of the item's token stream (whitespace- and comment-insensitive),
    /// used by interpretation anchors to detect upstream drift.
    pub token_sha256: String,
    pub item: syn::Item,
}

/// A fenced block that was not translated, with the reason.
pub struct SkippedBlock {
    pub line: usize,
    pub info: String,
    pub reason: String,
}

/// One specification file.
pub struct SourceFile {
    /// Path relative to the upstream repository root, with `/` separators
    /// (for example `spec/lang/syntax.md`).
    pub rel_path: String,
    pub sha256: String,
    pub rust_blocks: usize,
    pub skipped: Vec<SkippedBlock>,
    pub items: Vec<SourceItem>,
}

impl SourceFile {
    /// Lean module path components for this file under
    /// `MiniRustSpec.Generated.Items`, for example `["Lang", "Step",
    /// "Terminators"]` for `spec/lang/step/terminators.md`.
    pub fn module_components(&self) -> Vec<String> {
        let rel = self.rel_path.strip_prefix("spec/").unwrap_or(&self.rel_path);
        let rel = rel.strip_suffix(".md").unwrap_or(rel);
        rel.split('/').map(camel).collect()
    }
}

/// Converts `well-formed` / `state_machine` to `WellFormed` / `StateMachine`.
pub fn camel(s: &str) -> String {
    s.split(|c| c == '-' || c == '_')
        .filter(|p| !p.is_empty())
        .map(|p| {
            let mut cs = p.chars();
            match cs.next() {
                Some(f) => f.to_ascii_uppercase().to_string() + cs.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| format!("reading {}: {e}", dir.display()))?
        .map(|e| e.map(|e| e.path()).map_err(|e| e.to_string()))
        .collect::<Result<_, _>>()?;
    entries.sort();
    for p in entries {
        if p.is_dir() {
            walk(&p, out)?;
        } else {
            out.push(p);
        }
    }
    Ok(())
}

/// Lists all files under `root` (relative paths with `/`), sorted.
pub fn list_files(root: &Path) -> Result<Vec<String>, String> {
    let mut files = Vec::new();
    walk(root, &mut files)?;
    let mut rel: Vec<String> = files
        .iter()
        .map(|p| {
            p.strip_prefix(root)
                .expect("walk stays under root")
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/")
        })
        .collect();
    rel.sort();
    Ok(rel)
}

fn item_base_name(item: &syn::Item) -> String {
    use quote::ToTokens;
    let last_ident = |ty: &syn::Type| -> String {
        match ty {
            syn::Type::Path(p) => {
                p.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_else(|| "Type".into())
            }
            other => other.to_token_stream().to_string().chars().filter(|c| c.is_alphanumeric()).collect(),
        }
    };
    match item {
        syn::Item::Struct(s) => format!("struct_{}", s.ident),
        syn::Item::Enum(e) => format!("enum_{}", e.ident),
        syn::Item::Type(t) => format!("type_{}", t.ident),
        syn::Item::Trait(t) => format!("trait_{}", t.ident),
        syn::Item::Fn(f) => format!("fn_{}", f.sig.ident),
        syn::Item::Const(c) => format!("const_{}", c.ident),
        syn::Item::Static(s) => format!("static_{}", s.ident),
        syn::Item::Union(u) => format!("union_{}", u.ident),
        syn::Item::Mod(m) => format!("mod_{}", m.ident),
        syn::Item::Use(_) => "use".to_string(),
        syn::Item::Macro(m) => match &m.ident {
            Some(i) => format!("macro_rules_{i}"),
            None => "macro".to_string(),
        },
        syn::Item::Impl(i) => {
            let self_name = last_ident(&i.self_ty);
            let trait_part = match &i.trait_ {
                Some((_, p, _)) => {
                    format!("_for_{}", p.segments.last().map(|s| s.ident.to_string()).unwrap_or_default())
                }
                None => String::new(),
            };
            let first = i.items.iter().find_map(|x| match x {
                syn::ImplItem::Fn(f) => Some(f.sig.ident.to_string()),
                syn::ImplItem::Const(c) => Some(c.ident.to_string()),
                syn::ImplItem::Type(t) => Some(t.ident.to_string()),
                _ => None,
            });
            match first {
                Some(f) => format!("impl_{self_name}{trait_part}__{f}"),
                None => format!("impl_{self_name}{trait_part}"),
            }
        }
        _ => "item".to_string(),
    }
}

/// Reads, extracts, and parses one Markdown specification file.
pub fn load_file(repo_root: &Path, rel_path: &str) -> Result<SourceFile, String> {
    use quote::ToTokens;
    let bytes = std::fs::read(repo_root.join(rel_path)).map_err(|e| format!("reading {rel_path}: {e}"))?;
    let sha256 = sha256_hex(&bytes);
    let text = String::from_utf8(bytes).map_err(|e| format!("{rel_path} is not UTF-8: {e}"))?;
    let blocks: Vec<CodeBlock> = extract_code_blocks(&text).map_err(|e| format!("{rel_path}: {e}"))?;
    let mut items = Vec::new();
    let mut skipped = Vec::new();
    let mut rust_blocks = 0;
    let mut name_counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut raw: Vec<(String, usize, usize, syn::Item)> = Vec::new();
    for (bi, block) in blocks.iter().enumerate() {
        if block.info != "rust" {
            skipped.push(SkippedBlock {
                line: block.first_line,
                info: block.info.clone(),
                reason: "fenced block is not tagged `rust` (upstream specr-transpile also ignores it)".into(),
            });
            continue;
        }
        rust_blocks += 1;
        let file = syn::parse_file(&block.text)
            .map_err(|e| format!("{rel_path}:{}: syn parse error: {e}", block.first_line))?;
        if !file.attrs.is_empty() || file.shebang.is_some() {
            return Err(format!("{rel_path}:{}: unexpected inner attributes in block", block.first_line));
        }
        for item in file.items {
            let line = block.first_line + syn::spanned::Spanned::span(&item).start().line - 1;
            let base = item_base_name(&item);
            *name_counts.entry(base.clone()).or_default() += 1;
            raw.push((base, line, bi, item));
        }
    }
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    for (base, line, block, item) in raw {
        let name = if name_counts[&base] > 1 {
            let k = seen.entry(base.clone()).or_default();
            let n = format!("{base}_{k}");
            *k += 1;
            n
        } else {
            base
        };
        let token_sha256 = sha256_hex(item.to_token_stream().to_string().as_bytes());
        items.push(SourceItem { name, line, block, token_sha256, item });
    }
    Ok(SourceFile { rel_path: rel_path.to_string(), sha256, rust_blocks, skipped, items })
}
