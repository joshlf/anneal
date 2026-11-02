//! Mechanical `specr lang` lexical scanner, balanced declaration parser,
//! item classifier (`struct`, `enum`, `type`, `const`, `trait`, `fn`, `impl` method),
//! `GcCow<T>` detector, and `Result`/`NdResult` effect level classifier.

use crate::extractor::{CodeBlock, SourceSpan, SpecDomain};
use crate::sha256::sha256_hex;

/// Top-level or `impl`-member declaration kind in `specr lang`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ItemKind {
    Struct,
    Enum,
    TypeAlias,
    Const,
    Trait,
    Fn,
    ImplMethod,
    AssociatedType,
}

impl ItemKind {
    /// Canonical string name used in Lean reflection metadata and JSON reports.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Struct => "struct",
            Self::Enum => "enum",
            Self::TypeAlias => "type_alias",
            Self::Const => "const",
            Self::Trait => "trait",
            Self::Fn => "fn",
            Self::ImplMethod => "impl_method",
            Self::AssociatedType => "assoc_type",
        }
    }

    /// Lean constructor name inside `DeclKind`.
    #[must_use]
    pub const fn lean_ctor(self) -> &'static str {
        match self {
            Self::Struct => "DeclKind.structDecl",
            Self::Enum => "DeclKind.enumDecl",
            Self::TypeAlias => "DeclKind.typeAlias",
            Self::Const => "DeclKind.constDecl",
            Self::Trait => "DeclKind.traitDecl",
            Self::Fn => "DeclKind.fnDecl",
            Self::ImplMethod => "DeclKind.implMethod",
            Self::AssociatedType => "DeclKind.assocType",
        }
    }
}

/// Rust / `specr` visibility modifier on a declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Visibility {
    Public,
    Crate,
    Private,
}

impl Visibility {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Public => "pub",
            Self::Crate => "pub(crate)",
            Self::Private => "private",
        }
    }
}

/// Explicit monadic effect level in MiniRust's operational semantics.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EffectLevel {
    /// Pure total/partial helper returning a plain value `T` (or `()`).
    Pure,
    /// Partial lookup/helper returning `Option<T>`.
    OptionEffect,
    /// Fallible computation returning `Result<T>` / `TerminationInfo`.
    FallibleResult,
    /// Nondeterministic + fallible machine transition returning `NdResult<T>`.
    NondetResult,
}

impl EffectLevel {
    /// Classifies a return type signature into its MiniRust effect tier.
    #[must_use]
    pub fn from_return_type(ret_ty: Option<&str>) -> Self {
        let Some(rt) = ret_ty else {
            return Self::Pure;
        };
        let norm = normalize_whitespace(rt);
        if norm.contains("NdResult") || norm.contains("Nondet") {
            Self::NondetResult
        } else if norm.starts_with("Result<")
            || norm.starts_with("Result ")
            || norm == "Result"
            || norm.contains("std::result::Result")
            || norm.contains("TerminationInfo")
        {
            Self::FallibleResult
        } else if norm.starts_with("Option<") || norm.starts_with("Option ") {
            Self::OptionEffect
        } else {
            Self::Pure
        }
    }

    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pure => "Pure",
            Self::OptionEffect => "Option",
            Self::FallibleResult => "FallibleResult",
            Self::NondetResult => "NondetResult",
        }
    }

    #[must_use]
    pub const fn lean_ctor(self) -> &'static str {
        match self {
            Self::Pure => "EffectLevel.pure",
            Self::OptionEffect => "EffectLevel.optionEffect",
            Self::FallibleResult => "EffectLevel.fallibleResult",
            Self::NondetResult => "EffectLevel.nondetResult",
        }
    }
}

/// Struct field declaration extracted from a `struct` or struct enum variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDecl {
    pub name: String,
    pub ty: String,
    pub uses_gc_cow: bool,
}

/// Enum variant payload representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VariantPayload {
    Unit,
    Tuple(Vec<String>),
    Struct(Vec<FieldDecl>),
}

/// Enum variant declaration extracted from an `enum` definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantDecl {
    pub name: String,
    pub payload: VariantPayload,
    pub uses_gc_cow: bool,
}

/// Function or method parameter declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamDecl {
    pub name: String,
    pub ty: String,
    pub uses_gc_cow: bool,
}

/// A parsed and classified top-level or `impl`-member `specr lang` declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecrItem {
    pub qualified_name: String,
    pub ident: String,
    pub kind: ItemKind,
    pub domain: SpecDomain,
    pub visibility: Visibility,
    pub impl_target: Option<String>,
    pub impl_trait: Option<String>,
    pub generics: String,
    pub fields: Vec<FieldDecl>,
    pub variants: Vec<VariantDecl>,
    pub params: Vec<ParamDecl>,
    pub return_type: Option<String>,
    pub aliased_type: Option<String>,
    pub effect: EffectLevel,
    pub uses_gc_cow: bool,
    pub is_mutually_recursive: bool,
    pub signature_canonical: String,
    pub body_canonical: String,
    pub signature_sha256: String,
    pub body_sha256: String,
    pub doc_summary: String,
    pub span: SourceSpan,
}

/// Collapses all runs of whitespace to single ASCII spaces and trims ends.
#[must_use]
pub fn normalize_whitespace(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut prev_space = false;
    for ch in input.chars() {
        if ch.is_whitespace() {
            if !prev_space && !out.is_empty() {
                out.push(' ');
            }
            prev_space = true;
        } else {
            out.push(ch);
            prev_space = false;
        }
    }
    if out.ends_with(' ') {
        out.pop();
    }
    out
}

/// Strips `//` line comments and `/* ... */` block comments while preserving exact
/// newline count so 1-based line offsets stay 100% aligned with the raw source!
#[must_use]
pub fn strip_comments_preserve_newlines(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;
    let mut in_string = false;
    let mut block_comment_depth = 0usize;

    while i < bytes.len() {
        if block_comment_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
                block_comment_depth += 1;
                i += 2;
            } else if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b'/' {
                block_comment_depth -= 1;
                i += 2;
            } else {
                if bytes[i] == b'\n' {
                    out.push('\n');
                }
                i += 1;
            }
            continue;
        }

        if in_string {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                out.push(bytes[i] as char);
                out.push(bytes[i + 1] as char);
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = false;
            }
            out.push(bytes[i] as char);
            i += 1;
            continue;
        }

        if bytes[i] == b'"' {
            in_string = true;
            out.push('"');
            i += 1;
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            block_comment_depth = 1;
            i += 2;
            continue;
        }

        let ch = src[i..].chars().next().expect("valid utf8 boundary");
        out.push(ch);
        i += ch.len_utf8();
    }

    out
}

/// Checks whether a type or declaration snippet wraps `GcCow<...>`.
#[must_use]
pub fn contains_gc_cow(s: &str) -> bool {
    s.contains("GcCow")
}

/// Escapes Lean 4 reserved keywords to safe identifiers.
#[must_use]
pub fn escape_lean_ident(raw: &str) -> String {
    let cleaned: String = raw
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    match cleaned.as_str() {
        "" => "anon_item".to_string(),
        "def" | "theorem" | "lemma" | "axiom" | "abbrev" | "structure" | "inductive"
        | "class" | "instance" | "where" | "end" | "match" | "with" | "do" | "let"
        | "in" | "if" | "then" | "else" | "for" | "return" | "fun" | "by" | "have"
        | "show" | "from" | "open" | "import" | "namespace" | "section" | "variable"
        | "universe" | "mutual" | "partial" | "unsafe" | "opaque" | "private" | "protected"
        | "macro" | "syntax" | "elab" | "deriving" | "Type" | "Prop" | "Sort" => {
            format!("{cleaned}_")
        }
        _ => cleaned,
    }
}

/// Sanitizes extracted doc text so no forbidden task-tracking token or newline leaks into Lean strings.
fn sanitize_doc_text(raw: &str) -> String {
    let forbidden = ["TO", "DO"].concat();
    normalize_whitespace(raw)
        .replace(&forbidden, "NOTE_UPSTREAM")
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
}

/// Counts 1-based line number at byte offset `byte_pos` within `src`.
fn line_number_at_offset(src: &str, byte_pos: usize) -> usize {
    let clamped = byte_pos.min(src.len());
    1 + src[..clamped].bytes().filter(|&b| b == b'\n').count()
}

/// Finds the matching closing delimiter (`}`, `)`, `]`) starting from `open_pos`
/// (which points at `{`, `(`, or `[`), ignoring delimiters inside string literals.
fn find_matching_delim(src: &str, open_pos: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    let open_ch = *bytes.get(open_pos)?;
    let close_ch = match open_ch {
        b'{' => b'}',
        b'(' => b')',
        b'[' => b']',
        _ => return None,
    };

    let mut depth = 0usize;
    let mut i = open_pos;
    let mut in_str = false;

    while i < bytes.len() {
        if in_str {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_str = false;
            }
            i += 1;
            continue;
        }
        if bytes[i] == b'"' {
            in_str = true;
            i += 1;
            continue;
        }
        if bytes[i] == open_ch {
            depth += 1;
        } else if bytes[i] == close_ch {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

/// Finds the next top-level `;` (at brace/paren/bracket depth 0) starting from `start`.
fn find_top_level_semicolon(src: &str, start: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    let mut brace = 0usize;
    let mut paren = 0usize;
    let mut bracket = 0usize;
    let mut in_str = false;
    let mut i = start;

    while i < bytes.len() {
        if in_str {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_str = false;
            }
            i += 1;
            continue;
        }
        match bytes[i] {
            b'"' => in_str = true,
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b';' if brace == 0 && paren == 0 && bracket == 0 => return Some(i),
            _ => {}
        }
        i += 1;
    }
    None
}

/// Splits a comma-separated list at depth 0 of `(...)`, `<...>`, `[...]`, `{...}`.
fn split_top_level_commas(input: &str) -> Vec<&str> {
    let bytes = input.as_bytes();
    let mut parts = Vec::new();
    let mut start = 0usize;
    let mut paren = 0usize;
    let mut angle = 0usize;
    let mut bracket = 0usize;
    let mut brace = 0usize;
    let mut in_str = false;
    let mut i = 0usize;

    while i < bytes.len() {
        if in_str {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_str = false;
            }
            i += 1;
            continue;
        }
        match bytes[i] {
            b'"' => in_str = true,
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'<' => angle += 1,
            b'>' => {
                // Avoid counting `->` or `=>` as closing angle brackets
                if i == 0 || (bytes[i - 1] != b'-' && bytes[i - 1] != b'=') {
                    angle = angle.saturating_sub(1);
                }
            }
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b',' if paren == 0 && angle == 0 && bracket == 0 && brace == 0 => {
                let seg = input[start..i].trim();
                if !seg.is_empty() {
                    parts.push(seg);
                }
                start = i + 1;
            }
            _ => {}
        }
        i += 1;
    }

    let tail = input[start..].trim();
    if !tail.is_empty() {
        parts.push(tail);
    }
    parts
}

/// Strips leading attributes (`#[...]`) and returns the remaining slice + byte advance.
fn skip_leading_attributes(src: &str) -> (&str, usize) {
    let mut pos = 0usize;
    let bytes = src.as_bytes();
    loop {
        while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
            pos += 1;
        }
        if pos < bytes.len() && bytes[pos] == b'#' {
            if let Some(open_b) = src[pos..].find('[')
                && let Some(close_b) = find_matching_delim(src, pos + open_b)
            {
                pos = close_b + 1;
                continue;
            }
            break;
        }
        break;
    }
    (&src[pos..], pos)
}

/// Parses optional visibility prefix (`pub(...)` or `pub`).
fn parse_visibility(src: &str) -> (Visibility, usize) {
    let trimmed = src.trim_start();
    let ws = src.len() - trimmed.len();
    if let Some(after_pub) = trimmed.strip_prefix("pub") {
        let after_ws = after_pub.trim_start();
        if after_ws.starts_with('(')
            && let Some(close_p) = find_matching_delim(trimmed, 3 + (after_pub.len() - after_ws.len()))
        {
            return (Visibility::Crate, ws + close_p + 1);
        }
        if after_pub.starts_with(|c: char| c.is_whitespace()) {
            return (Visibility::Public, ws + 3);
        }
    }
    (Visibility::Private, ws)
}

/// Extracts an identifier `[A-Za-z_][A-Za-z0-9_]*` (supporting `r#ident`).
fn parse_ident(src: &str) -> Option<(&str, usize)> {
    let trimmed = src.trim_start();
    let ws = src.len() - trimmed.len();
    let raw = if let Some(stripped) = trimmed.strip_prefix("r#") {
        let len = stripped
            .bytes()
            .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
            .count();
        if len == 0 {
            return None;
        }
        return Some((&stripped[..len], ws + 2 + len));
    } else {
        trimmed
    };
    let len = raw
        .bytes()
        .take_while(|b| b.is_ascii_alphanumeric() || *b == b'_')
        .count();
    if len == 0 {
        None
    } else {
        Some((&raw[..len], ws + len))
    }
}

/// Parses optional `<...>` generic parameter list starting at `src` (if it begins with `<`).
fn parse_optional_generics(src: &str) -> (String, usize) {
    let trimmed = src.trim_start();
    let ws = src.len() - trimmed.len();
    if !trimmed.starts_with('<') {
        return (String::new(), ws);
    }
    let bytes = trimmed.as_bytes();
    let mut depth = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'<' {
            depth += 1;
        } else if bytes[i] == b'>' && (i == 0 || (bytes[i - 1] != b'-' && bytes[i - 1] != b'=')) {
            depth -= 1;
            if depth == 0 {
                return (normalize_whitespace(&trimmed[..=i]), ws + i + 1);
            }
        }
        i += 1;
    }
    (String::new(), ws)
}

/// Simplifies an `impl` target type (e.g. `Machine<M>` -> `Machine`, `&'a Foo<T>` -> `Foo`)
/// for clean qualified naming while preserving the full target string in metadata.
fn short_type_head(raw_target: &str) -> String {
    let norm = normalize_whitespace(raw_target);
    let stripped = norm
        .trim_start_matches('&')
        .trim_start_matches("mut ")
        .trim();
    // Drop generic args `<...>` for the qualified name prefix
    let without_generics = if let Some(lt) = stripped.find('<') {
        stripped[..lt].trim()
    } else {
        stripped
    };
    // Take final path segment if qualified (`tree_borrows::Tree` -> `Tree`)
    without_generics
        .rsplit("::")
        .next()
        .unwrap_or(without_generics)
        .trim()
        .replace(|c: char| !c.is_ascii_alphanumeric() && c != '_', "_")
}

/// Parses named struct fields from inside `{ ... }`.
fn parse_struct_fields(body_inside_braces: &str) -> Vec<FieldDecl> {
    let mut fields = Vec::new();
    for raw_entry in split_top_level_commas(body_inside_braces) {
        let (after_attrs, _) = skip_leading_attributes(raw_entry);
        let (_, vis_adv) = parse_visibility(after_attrs);
        let rest = after_attrs[vis_adv..].trim();
        if let Some((fname, ty_raw)) = rest.split_once(':') {
            let clean_name = fname.trim().to_string();
            let clean_ty = normalize_whitespace(ty_raw);
            if !clean_name.is_empty() && !clean_ty.is_empty() {
                let uses_gc_cow = contains_gc_cow(&clean_ty);
                fields.push(FieldDecl { name: clean_name, ty: clean_ty, uses_gc_cow });
            }
        }
    }
    fields
}

/// Parses enum variants from inside `enum Name { ... }`.
fn parse_enum_variants(body_inside_braces: &str) -> Vec<VariantDecl> {
    let mut variants = Vec::new();
    for raw_entry in split_top_level_commas(body_inside_braces) {
        let (after_attrs, _) = skip_leading_attributes(raw_entry);
        let trimmed = after_attrs.trim();
        if trimmed.is_empty() {
            continue;
        }
        let Some((vname, adv)) = parse_ident(trimmed) else {
            continue;
        };
        let rest = trimmed[adv..].trim();
        if rest.starts_with('(')
            && let Some(close_p) = find_matching_delim(rest, 0)
        {
            let inside = &rest[1..close_p];
            let tuple_tys: Vec<String> = split_top_level_commas(inside)
                .into_iter()
                .map(normalize_whitespace)
                .filter(|s| !s.is_empty())
                .collect();
            let uses_gc = tuple_tys.iter().any(|t| contains_gc_cow(t));
            variants.push(VariantDecl {
                name: vname.to_string(),
                payload: VariantPayload::Tuple(tuple_tys),
                uses_gc_cow: uses_gc,
            });
        } else if rest.starts_with('{')
            && let Some(close_b) = find_matching_delim(rest, 0)
        {
            let inside = &rest[1..close_b];
            let flds = parse_struct_fields(inside);
            let uses_gc = flds.iter().any(|f| f.uses_gc_cow);
            variants.push(VariantDecl {
                name: vname.to_string(),
                payload: VariantPayload::Struct(flds),
                uses_gc_cow: uses_gc,
            });
        } else {
            variants.push(VariantDecl {
                name: vname.to_string(),
                payload: VariantPayload::Unit,
                uses_gc_cow: false,
            });
        }
    }
    variants
}

/// Parses function/method parameters from inside `( ... )`.
fn parse_fn_params(params_inside_parens: &str) -> Vec<ParamDecl> {
    let mut params = Vec::new();
    for raw_param in split_top_level_commas(params_inside_parens) {
        let (after_attrs, _) = skip_leading_attributes(raw_param);
        let p = normalize_whitespace(after_attrs);
        if p.is_empty() {
            continue;
        }
        if p == "self" || p == "&self" || p == "&mut self" || p == "mut self" {
            params.push(ParamDecl {
                name: "self".to_string(),
                ty: p,
                uses_gc_cow: false,
            });
        } else if let Some((pat, ty_raw)) = p.split_once(':') {
            let name = normalize_whitespace(pat);
            let ty = normalize_whitespace(ty_raw);
            let uses_gc = contains_gc_cow(&ty);
            params.push(ParamDecl { name, ty, uses_gc_cow: uses_gc });
        } else {
            params.push(ParamDecl {
                name: p.clone(),
                ty: p,
                uses_gc_cow: false,
            });
        }
    }
    params
}

/// Extracts `///` doc comments immediately preceding 1-based local line `decl_start_local_line`
/// inside raw block source `raw_block_lines`.
fn extract_doc_comment_above(raw_block_lines: &[&str], decl_start_local_line: usize) -> String {
    if decl_start_local_line <= 1 || raw_block_lines.is_empty() {
        return String::new();
    }
    let mut idx = (decl_start_local_line - 1).min(raw_block_lines.len());
    let mut doc_lines = Vec::new();
    while idx > 0 {
        idx -= 1;
        let line = raw_block_lines[idx].trim();
        if let Some(doc) = line.strip_prefix("///") {
            doc_lines.push(doc.trim());
        } else if line.starts_with("#[") || line.is_empty() {
            continue;
        } else {
            break;
        }
    }
    doc_lines.reverse();
    sanitize_doc_text(&doc_lines.join(" "))
}

/// Parses all top-level and `impl`-block declarations inside a single extracted `CodeBlock`.
#[must_use]
pub fn parse_block_items(block: &CodeBlock) -> Vec<SpecrItem> {
    let raw_lines: Vec<&str> = block.source.lines().collect();
    let clean = strip_comments_preserve_newlines(&block.source);
    let domain = SpecDomain::from_chapter_path(&block.chapter_rel_path);
    let mut out = Vec::new();

    parse_items_in_scope(
        &clean,
        0,
        &raw_lines,
        block,
        domain,
        None,
        None,
        &mut out,
    );

    out
}

#[allow(clippy::too_many_arguments)]
fn parse_items_in_scope(
    clean_scope: &str,
    base_offset_in_block: usize,
    raw_lines: &[&str],
    block: &CodeBlock,
    domain: SpecDomain,
    impl_target: Option<&str>,
    impl_trait: Option<&str>,
    out: &mut Vec<SpecrItem>,
) {
    let mut pos = 0usize;
    let bytes = clean_scope.as_bytes();

    while pos < bytes.len() {
        while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
            pos += 1;
        }
        if pos >= bytes.len() {
            break;
        }

        let item_start_in_scope = pos;
        let (_, attr_adv) = skip_leading_attributes(&clean_scope[pos..]);
        pos += attr_adv;
        if pos >= bytes.len() {
            break;
        }

        let (vis, vis_adv) = parse_visibility(&clean_scope[pos..]);
        pos += vis_adv;

        // Skip optional qualifiers (`default`, `const`, `unsafe`, `async`, `extern "..."`)
        loop {
            let rest = &clean_scope[pos..];
            let trimmed = rest.trim_start();
            let ws = rest.len() - trimmed.len();
            if let Some(after) = trimmed
                .strip_prefix("const ")
                .or_else(|| trimmed.strip_prefix("unsafe "))
                .or_else(|| trimmed.strip_prefix("default "))
                .or_else(|| trimmed.strip_prefix("async "))
            {
                // Keep `const` if it is a `const NAME: T = ...;` item rather than `const fn`!
                if trimmed.starts_with("const ") {
                    let after_const = after.trim_start();
                    if !after_const.starts_with("fn ") && !after_const.starts_with("unsafe ") {
                        break;
                    }
                }
                let consumed_kw = trimmed.len() - after.len();
                pos += ws + consumed_kw;
                continue;
            }
            if let Some(after_ext) = trimmed.strip_prefix("extern") {
                let after_ws = after_ext.trim_start();
                if after_ws.starts_with('"')
                    && let Some(end_q) = after_ws[1..].find('"')
                {
                    pos += ws + 6 + (after_ext.len() - after_ws.len()) + 1 + end_q + 1;
                    continue;
                }
            }
            pos += ws;
            break;
        }

        if pos >= bytes.len() {
            break;
        }

        let rest = &clean_scope[pos..];
        let global_start_offset = base_offset_in_block + item_start_in_scope;
        let local_start_line = line_number_at_offset(&block.source, global_start_offset);

        // 1. `struct` declaration
        if let Some(after_kw) = rest.strip_prefix("struct ") {
            let kw_pos = pos;
            if let Some((ident, id_adv)) = parse_ident(after_kw) {
                let after_id_pos = kw_pos + 7 + id_adv;
                let (generics, gen_adv) = parse_optional_generics(&clean_scope[after_id_pos..]);
                let body_search_pos = after_id_pos + gen_adv;

                // Struct body can be `{ ... }`, `( ... );`, or unit `;`
                let brace_pos = clean_scope[body_search_pos..].find('{').map(|o| body_search_pos + o);
                let semi_pos = find_top_level_semicolon(clean_scope, body_search_pos);

                let (end_in_scope, fields, sig_str, body_str) = match (brace_pos, semi_pos) {
                    (Some(bp), Some(sp)) if sp < bp => {
                        // Tuple or unit struct ending at `;`
                        let raw_decl = &clean_scope[kw_pos..=sp];
                        let flds = if let Some(open_p) = raw_decl.find('(')
                            && let Some(close_p) = find_matching_delim(raw_decl, open_p)
                        {
                            split_top_level_commas(&raw_decl[open_p + 1..close_p])
                                .into_iter()
                                .enumerate()
                                .map(|(idx, t)| {
                                    let (_, vis_skip) = parse_visibility(t);
                                    let clean_t = normalize_whitespace(&t[vis_skip..]);
                                    FieldDecl {
                                        name: format!("_{idx}"),
                                        uses_gc_cow: contains_gc_cow(&clean_t),
                                        ty: clean_t,
                                    }
                                })
                                .collect()
                        } else {
                            Vec::new()
                        };
                        let norm = normalize_whitespace(raw_decl);
                        (sp + 1, flds, norm.clone(), norm)
                    }
                    (Some(bp), _) => {
                        if let Some(close_b) = find_matching_delim(clean_scope, bp) {
                            let inside = &clean_scope[bp + 1..close_b];
                            let flds = parse_struct_fields(inside);
                            let raw_decl = &clean_scope[kw_pos..=close_b];
                            let norm = normalize_whitespace(raw_decl);
                            (close_b + 1, flds, norm.clone(), norm)
                        } else {
                            break;
                        }
                    }
                    (None, Some(sp)) => {
                        let norm = normalize_whitespace(&clean_scope[kw_pos..=sp]);
                        (sp + 1, Vec::new(), norm.clone(), norm)
                    }
                    (None, None) => break,
                };

                let global_end_offset = base_offset_in_block + end_in_scope.saturating_sub(1);
                let local_end_line = line_number_at_offset(&block.source, global_end_offset);
                let uses_gc = fields.iter().any(|f| f.uses_gc_cow) || contains_gc_cow(&body_str);
                let span = make_decl_span(block, local_start_line, local_end_line);
                let doc = extract_doc_comment_above(raw_lines, local_start_line);

                out.push(SpecrItem {
                    qualified_name: ident.to_string(),
                    ident: ident.to_string(),
                    kind: ItemKind::Struct,
                    domain,
                    visibility: vis,
                    impl_target: None,
                    impl_trait: None,
                    generics,
                    fields,
                    variants: Vec::new(),
                    params: Vec::new(),
                    return_type: None,
                    aliased_type: None,
                    effect: EffectLevel::Pure,
                    uses_gc_cow: uses_gc,
                    is_mutually_recursive: false,
                    signature_sha256: sha256_hex(sig_str.as_bytes()),
                    body_sha256: sha256_hex(body_str.as_bytes()),
                    signature_canonical: sig_str,
                    body_canonical: body_str,
                    doc_summary: doc,
                    span,
                });

                pos = end_in_scope;
                continue;
            }
        }

        // 2. `enum` declaration
        if let Some(after_kw) = rest.strip_prefix("enum ") {
            let kw_pos = pos;
            if let Some((ident, id_adv)) = parse_ident(after_kw) {
                let after_id_pos = kw_pos + 5 + id_adv;
                let (generics, gen_adv) = parse_optional_generics(&clean_scope[after_id_pos..]);
                let body_search_pos = after_id_pos + gen_adv;
                if let Some(open_rel) = clean_scope[body_search_pos..].find('{') {
                    let bp = body_search_pos + open_rel;
                    if let Some(close_b) = find_matching_delim(clean_scope, bp) {
                        let inside = &clean_scope[bp + 1..close_b];
                        let variants = parse_enum_variants(inside);
                        let raw_decl = normalize_whitespace(&clean_scope[kw_pos..=close_b]);
                        let uses_gc =
                            variants.iter().any(|v| v.uses_gc_cow) || contains_gc_cow(&raw_decl);
                        let global_end_offset = base_offset_in_block + close_b;
                        let local_end_line = line_number_at_offset(&block.source, global_end_offset);
                        let span = make_decl_span(block, local_start_line, local_end_line);
                        let doc = extract_doc_comment_above(raw_lines, local_start_line);

                        out.push(SpecrItem {
                            qualified_name: ident.to_string(),
                            ident: ident.to_string(),
                            kind: ItemKind::Enum,
                            domain,
                            visibility: vis,
                            impl_target: None,
                            impl_trait: None,
                            generics,
                            fields: Vec::new(),
                            variants,
                            params: Vec::new(),
                            return_type: None,
                            aliased_type: None,
                            effect: EffectLevel::Pure,
                            uses_gc_cow: uses_gc,
                            is_mutually_recursive: false,
                            signature_sha256: sha256_hex(raw_decl.as_bytes()),
                            body_sha256: sha256_hex(raw_decl.as_bytes()),
                            signature_canonical: raw_decl.clone(),
                            body_canonical: raw_decl,
                            doc_summary: doc,
                            span,
                        });

                        pos = close_b + 1;
                        continue;
                    }
                }
            }
        }

        // 3. `type` alias or associated type (`type Foo<T> = Bar<T>;` or `type Params;`)
        if let Some(after_kw) = rest.strip_prefix("type ") {
            let kw_pos = pos;
            if let Some((ident, id_adv)) = parse_ident(after_kw) {
                let after_id_pos = kw_pos + 5 + id_adv;
                let (generics, _) = parse_optional_generics(&clean_scope[after_id_pos..]);
                if let Some(semi) = find_top_level_semicolon(clean_scope, after_id_pos) {
                    let full_decl = normalize_whitespace(&clean_scope[kw_pos..=semi]);
                    let aliased = full_decl
                        .split_once('=')
                        .map(|(_, rhs)| rhs.trim_end_matches(';').trim().to_string());
                    let uses_gc = contains_gc_cow(&full_decl);
                    let global_end_offset = base_offset_in_block + semi;
                    let local_end_line = line_number_at_offset(&block.source, global_end_offset);
                    let span = make_decl_span(block, local_start_line, local_end_line);
                    let doc = extract_doc_comment_above(raw_lines, local_start_line);

                    let (kind, qname) = if let Some(tgt) = impl_target {
                        let head = short_type_head(tgt);
                        let q = if let Some(tr) = impl_trait {
                            format!("{head}::{tr}::{ident}")
                        } else {
                            format!("{head}::{ident}")
                        };
                        (ItemKind::AssociatedType, q)
                    } else {
                        (ItemKind::TypeAlias, ident.to_string())
                    };

                    out.push(SpecrItem {
                        qualified_name: qname,
                        ident: ident.to_string(),
                        kind,
                        domain,
                        visibility: vis,
                        impl_target: impl_target.map(ToString::to_string),
                        impl_trait: impl_trait.map(ToString::to_string),
                        generics,
                        fields: Vec::new(),
                        variants: Vec::new(),
                        params: Vec::new(),
                        return_type: None,
                        aliased_type: aliased,
                        effect: EffectLevel::Pure,
                        uses_gc_cow: uses_gc,
                        is_mutually_recursive: false,
                        signature_sha256: sha256_hex(full_decl.as_bytes()),
                        body_sha256: sha256_hex(full_decl.as_bytes()),
                        signature_canonical: full_decl.clone(),
                        body_canonical: full_decl,
                        doc_summary: doc,
                        span,
                    });

                    pos = semi + 1;
                    continue;
                }
            }
        }

        // 4. `const` item (`const NAME: T = expr;`)
        if let Some(after_kw) = rest.strip_prefix("const ") {
            let kw_pos = pos;
            if let Some((ident, id_adv)) = parse_ident(after_kw)
                && ident != "fn"
                && ident != "unsafe"
            {
                let after_id_pos = kw_pos + 6 + id_adv;
                if let Some(semi) = find_top_level_semicolon(clean_scope, after_id_pos) {
                    let full_decl = normalize_whitespace(&clean_scope[kw_pos..=semi]);
                    let (sig_part, body_part) = if let Some((lhs, rhs)) = full_decl.split_once('=') {
                        (lhs.trim().to_string(), rhs.trim_end_matches(';').trim().to_string())
                    } else {
                        (full_decl.clone(), full_decl.clone())
                    };
                    let ret_ty = sig_part
                        .split_once(':')
                        .map(|(_, ty)| ty.trim().to_string());
                    let qname = if let Some(tgt) = impl_target {
                        format!("{}::{ident}", short_type_head(tgt))
                    } else {
                        ident.to_string()
                    };
                    let global_end_offset = base_offset_in_block + semi;
                    let local_end_line = line_number_at_offset(&block.source, global_end_offset);
                    let span = make_decl_span(block, local_start_line, local_end_line);
                    let doc = extract_doc_comment_above(raw_lines, local_start_line);

                    out.push(SpecrItem {
                        qualified_name: qname,
                        ident: ident.to_string(),
                        kind: ItemKind::Const,
                        domain,
                        visibility: vis,
                        impl_target: impl_target.map(ToString::to_string),
                        impl_trait: impl_trait.map(ToString::to_string),
                        generics: String::new(),
                        fields: Vec::new(),
                        variants: Vec::new(),
                        params: Vec::new(),
                        return_type: ret_ty,
                        aliased_type: None,
                        effect: EffectLevel::Pure,
                        uses_gc_cow: contains_gc_cow(&full_decl),
                        is_mutually_recursive: false,
                        signature_sha256: sha256_hex(sig_part.as_bytes()),
                        body_sha256: sha256_hex(body_part.as_bytes()),
                        signature_canonical: sig_part,
                        body_canonical: body_part,
                        doc_summary: doc,
                        span,
                    });

                    pos = semi + 1;
                    continue;
                }
            }
        }

        // 5. `trait` declaration (`trait Memory { ... }`)
        if let Some(after_kw) = rest.strip_prefix("trait ") {
            let kw_pos = pos;
            if let Some((ident, id_adv)) = parse_ident(after_kw) {
                let after_id_pos = kw_pos + 6 + id_adv;
                let (generics, gen_adv) = parse_optional_generics(&clean_scope[after_id_pos..]);
                if let Some(open_rel) = clean_scope[after_id_pos + gen_adv..].find('{') {
                    let bp = after_id_pos + gen_adv + open_rel;
                    if let Some(close_b) = find_matching_delim(clean_scope, bp) {
                        let header = normalize_whitespace(&clean_scope[kw_pos..bp]);
                        let full = normalize_whitespace(&clean_scope[kw_pos..=close_b]);
                        let global_end_offset = base_offset_in_block + close_b;
                        let local_end_line = line_number_at_offset(&block.source, global_end_offset);
                        let span = make_decl_span(block, local_start_line, local_end_line);
                        let doc = extract_doc_comment_above(raw_lines, local_start_line);

                        out.push(SpecrItem {
                            qualified_name: ident.to_string(),
                            ident: ident.to_string(),
                            kind: ItemKind::Trait,
                            domain,
                            visibility: vis,
                            impl_target: None,
                            impl_trait: None,
                            generics,
                            fields: Vec::new(),
                            variants: Vec::new(),
                            params: Vec::new(),
                            return_type: None,
                            aliased_type: None,
                            effect: EffectLevel::Pure,
                            uses_gc_cow: contains_gc_cow(&full),
                            is_mutually_recursive: false,
                            signature_sha256: sha256_hex(header.as_bytes()),
                            body_sha256: sha256_hex(full.as_bytes()),
                            signature_canonical: header,
                            body_canonical: full,
                            doc_summary: doc,
                            span,
                        });

                        // Also parse trait methods & associated types inside the trait body!
                        parse_items_in_scope(
                            &clean_scope[bp + 1..close_b],
                            base_offset_in_block + bp + 1,
                            raw_lines,
                            block,
                            domain,
                            Some(ident),
                            None,
                            out,
                        );

                        pos = close_b + 1;
                        continue;
                    }
                }
            }
        }

        // 6. `impl` block (`impl<...> [Trait for] Target { ... }`)
        if rest.starts_with("impl<") || rest.starts_with("impl ") {
            let kw_pos = pos;
            let after_impl = &clean_scope[kw_pos + 4..];
            let (_, gen_adv) = parse_optional_generics(after_impl);
            let header_start = kw_pos + 4 + gen_adv;
            if let Some(open_b) = find_impl_body_brace(clean_scope, header_start)
                && let Some(close_b) = find_matching_delim(clean_scope, open_b)
            {
                let raw_header = clean_scope[header_start..open_b].trim();
                let header_no_where = raw_header.split("\nwhere").next().unwrap_or(raw_header);
                let header_no_where = header_no_where.split(" where ").next().unwrap_or(header_no_where);

                let (trait_name, target_name) = if let Some((tr, tgt)) = header_no_where.split_once(" for ") {
                    (Some(short_type_head(tr)), normalize_whitespace(tgt))
                } else {
                    (None, normalize_whitespace(header_no_where))
                };

                parse_items_in_scope(
                    &clean_scope[open_b + 1..close_b],
                    base_offset_in_block + open_b + 1,
                    raw_lines,
                    block,
                    domain,
                    Some(&target_name),
                    trait_name.as_deref(),
                    out,
                );

                pos = close_b + 1;
                continue;
            }
        }

        // 7. `fn` item (free function, `impl` method, or trait method signature)
        if let Some(after_kw) = rest.strip_prefix("fn ") {
            let kw_pos = pos;
            if let Some((ident, id_adv)) = parse_ident(after_kw) {
                let after_id_pos = kw_pos + 3 + id_adv;
                let (generics, gen_adv) = parse_optional_generics(&clean_scope[after_id_pos..]);
                let search_paren = after_id_pos + gen_adv;
                if let Some(open_rel) = clean_scope[search_paren..].find('(') {
                    let open_p = search_paren + open_rel;
                    if let Some(close_p) = find_matching_delim(clean_scope, open_p) {
                        let params = parse_fn_params(&clean_scope[open_p + 1..close_p]);
                        let after_params = close_p + 1;

                        // Either has a body `{ ... }` or ends with `;` (trait method declaration)
                        let brace_pos = find_fn_body_brace(clean_scope, after_params);
                        let semi_pos = find_top_level_semicolon(clean_scope, after_params);

                        let (end_in_scope, sig_raw, body_raw) = match (brace_pos, semi_pos) {
                            (Some(sp_semi), _) if semi_pos.is_some_and(|s| s < brace_pos.unwrap_or(usize::MAX)) => {
                                let s = semi_pos.unwrap_or(sp_semi);
                                let sig = normalize_whitespace(&clean_scope[kw_pos..s]);
                                (s + 1, sig.clone(), sig)
                            }
                            (Some(bp), _) => {
                                if let Some(close_b) = find_matching_delim(clean_scope, bp) {
                                    let sig = normalize_whitespace(&clean_scope[kw_pos..bp]);
                                    let body = normalize_whitespace(&clean_scope[bp..=close_b]);
                                    (close_b + 1, sig, body)
                                } else {
                                    break;
                                }
                            }
                            (None, Some(s)) => {
                                let sig = normalize_whitespace(&clean_scope[kw_pos..s]);
                                (s + 1, sig.clone(), sig)
                            }
                            (None, None) => break,
                        };

                        let ret_ty = extract_return_type(&clean_scope[after_params..end_in_scope]);
                        let effect = EffectLevel::from_return_type(ret_ty.as_deref());
                        let uses_gc = params.iter().any(|p| p.uses_gc_cow)
                            || ret_ty.as_deref().is_some_and(contains_gc_cow)
                            || contains_gc_cow(&body_raw);

                        let (kind, qname) = if let Some(tgt) = impl_target {
                            let head = short_type_head(tgt);
                            let q = if let Some(tr) = impl_trait {
                                format!("{head}::{tr}::{ident}")
                            } else {
                                format!("{head}::{ident}")
                            };
                            (ItemKind::ImplMethod, q)
                        } else {
                            (ItemKind::Fn, ident.to_string())
                        };

                        let global_end_offset = base_offset_in_block + end_in_scope.saturating_sub(1);
                        let local_end_line = line_number_at_offset(&block.source, global_end_offset);
                        let span = make_decl_span(block, local_start_line, local_end_line);
                        let doc = extract_doc_comment_above(raw_lines, local_start_line);

                        out.push(SpecrItem {
                            qualified_name: qname,
                            ident: ident.to_string(),
                            kind,
                            domain,
                            visibility: vis,
                            impl_target: impl_target.map(ToString::to_string),
                            impl_trait: impl_trait.map(ToString::to_string),
                            generics,
                            fields: Vec::new(),
                            variants: Vec::new(),
                            params,
                            return_type: ret_ty,
                            aliased_type: None,
                            effect,
                            uses_gc_cow: uses_gc,
                            is_mutually_recursive: false,
                            signature_sha256: sha256_hex(sig_raw.as_bytes()),
                            body_sha256: sha256_hex(body_raw.as_bytes()),
                            signature_canonical: sig_raw,
                            body_canonical: body_raw,
                            doc_summary: doc,
                            span,
                        });

                        pos = end_in_scope;
                        continue;
                    }
                }
            }
        }

        // Skip unrecognized token/macro invocation up to next newline or top-level semicolon/brace
        if let Some(nl) = clean_scope[pos..].find('\n') {
            pos += nl + 1;
        } else {
            break;
        }
    }
}

/// Finds the `{` that starts an `impl` or `fn` body (at angle/paren depth 0).
fn find_impl_body_brace(src: &str, start: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    let mut angle = 0usize;
    let mut paren = 0usize;
    let mut i = start;
    while i < bytes.len() {
        match bytes[i] {
            b'<' => angle += 1,
            b'>' if i == 0 || (bytes[i - 1] != b'-' && bytes[i - 1] != b'=') => {
                angle = angle.saturating_sub(1);
            }
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'{' if angle == 0 && paren == 0 => return Some(i),
            _ => {}
        }
        i += 1;
    }
    None
}

fn find_fn_body_brace(src: &str, start: usize) -> Option<usize> {
    find_impl_body_brace(src, start)
}

/// Extracts return type `T` from `) -> T { ...` or `) -> T where ...`.
fn extract_return_type(after_params_slice: &str) -> Option<String> {
    let before_brace = after_params_slice
        .split('{')
        .next()
        .unwrap_or(after_params_slice)
        .split(';')
        .next()
        .unwrap_or(after_params_slice);
    let norm = normalize_whitespace(before_brace);
    let after_arrow = norm.strip_prefix("->")?.trim();
    let without_where = after_arrow
        .split(" where ")
        .next()
        .unwrap_or(after_arrow)
        .trim();
    if without_where.is_empty() {
        None
    } else {
        Some(without_where.to_string())
    }
}

/// Computes the exact 1-based markdown file `SourceSpan` for a declaration at local lines
/// `local_start_line..=local_end_line` inside `block`.
fn make_decl_span(block: &CodeBlock, local_start_line: usize, local_end_line: usize) -> SourceSpan {
    let md_start = block.span.start_line + local_start_line.saturating_sub(1);
    let md_end = (block.span.start_line + local_end_line.saturating_sub(1))
        .max(md_start)
        .min(block.span.end_line.max(md_start));
    SourceSpan {
        rel_path: block.span.rel_path.clone(),
        start_line: md_start,
        end_line: md_end,
        git_sha: block.span.git_sha.clone(),
    }
}
