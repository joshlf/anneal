//! General-purpose `specr lang` AST parser and Lean 4 code generator.
//!
//! Parses `specr` Rust types, patterns, expressions, statements, and item
//! declarations (`enum`, `struct`, `type`, `fn`, and `impl` methods) into a
//! structured AST and lowers them into executable Lean 4 definitions.

use std::collections::BTreeSet;

use crate::specr_ast::{
    EffectLevel, ItemKind, SpecrItem, VariantPayload, escape_lean_ident, normalize_whitespace,
};
use crate::type_env::TypeEnvironment;

/// Parsed `specr lang` type representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecrType {
    Unit,
    Bool,
    U8,
    Nat,
    Int,
    String,
    Size,
    Offset,
    Align,
    Signedness,
    Endianness,
    Tuple(Vec<SpecrType>),
    Option(Box<SpecrType>),
    Result(Box<SpecrType>),
    NdResult(Box<SpecrType>),
    List(Box<SpecrType>),
    Set(Box<SpecrType>),
    Map(Box<SpecrType>, Box<SpecrType>),
    Nominal(String),
}

/// Parsed literal value in `specr lang`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecrLit {
    Unit,
    Bool(bool),
    Int(i128),
    Str(String),
}

/// Parsed pattern in `let`, `match`, or `matches!`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecrPat {
    Wildcard,
    Bind {
        name: String,
        mutable: bool,
    },
    Lit(SpecrLit),
    Tuple(Vec<SpecrPat>),
    Path(Vec<String>),
    TupleVariant {
        path: Vec<String>,
        args: Vec<SpecrPat>,
    },
    StructVariant {
        path: Vec<String>,
        fields: Vec<(String, SpecrPat)>,
        has_rest: bool,
    },
    Or(Vec<SpecrPat>),
}

/// Binary operator in `specr lang`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecrBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

/// Unary operator in `specr lang`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecrUnOp {
    Not,
    Neg,
    Deref,
    Ref,
    RefMut,
}

/// A single arm in a `match` expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecrMatchArm {
    pub pat: SpecrPat,
    pub guard: Option<SpecrExpr>,
    pub body: SpecrExpr,
}

/// Parsed expression in `specr lang`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecrExpr {
    Lit(SpecrLit),
    Path(Vec<String>),
    Tuple(Vec<SpecrExpr>),
    StructLit {
        path: Vec<String>,
        fields: Vec<(String, SpecrExpr)>,
        spread: Option<Box<SpecrExpr>>,
    },
    Field {
        base: Box<SpecrExpr>,
        field: String,
    },
    TupleIndex {
        base: Box<SpecrExpr>,
        index: usize,
    },
    Call {
        func: Box<SpecrExpr>,
        args: Vec<SpecrExpr>,
    },
    MethodCall {
        receiver: Box<SpecrExpr>,
        method: String,
        args: Vec<SpecrExpr>,
    },
    Unary {
        op: SpecrUnOp,
        expr: Box<SpecrExpr>,
    },
    Binary {
        op: SpecrBinOp,
        lhs: Box<SpecrExpr>,
        rhs: Box<SpecrExpr>,
    },
    Range {
        start: Box<SpecrExpr>,
        end: Box<SpecrExpr>,
        inclusive: bool,
    },
    Try(Box<SpecrExpr>),
    Return(Option<Box<SpecrExpr>>),
    ThrowUb {
        msg: String,
        args: Vec<SpecrExpr>,
    },
    ThrowIllFormed {
        msg: String,
        args: Vec<SpecrExpr>,
    },
    ThrowMachineStop,
    Matches {
        expr: Box<SpecrExpr>,
        pat: SpecrPat,
    },
    Closure {
        params: Vec<String>,
        body: Box<SpecrExpr>,
    },
    If {
        cond: Box<SpecrExpr>,
        then_branch: Vec<SpecrStmt>,
        else_branch: Option<Box<SpecrExpr>>,
    },
    Match {
        scrutinee: Box<SpecrExpr>,
        arms: Vec<SpecrMatchArm>,
    },
    Block(Vec<SpecrStmt>),
}

/// Parsed statement in a `specr lang` block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecrStmt {
    Let {
        pat: SpecrPat,
        ty: Option<SpecrType>,
        init: SpecrExpr,
    },
    Assign {
        lhs: SpecrExpr,
        op: Option<SpecrBinOp>,
        rhs: SpecrExpr,
    },
    Expr {
        expr: SpecrExpr,
        has_semi: bool,
    },
}

/// Finds the matching closing delimiter (`}`, `)`, `]`) starting at `open_pos`.
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

/// Splits a comma-separated list at depth 0 of `()`, `<>` (when `track_angles`
/// is true), `[]`, `{}`.
fn split_commas_opts(input: &str, track_angles: bool) -> Vec<&str> {
    let bytes = input.as_bytes();
    let mut parts = Vec::new();
    let mut start = 0usize;
    let (mut paren, mut angle, mut bracket, mut brace) = (0usize, 0usize, 0usize, 0usize);
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
            b'<' if track_angles => angle += 1,
            b'>' if track_angles => {
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

/// Splits a pattern on top-level `|` (ignoring `||` and nested delimiters).
fn split_top_level_bar(input: &str) -> Vec<&str> {
    let bytes = input.as_bytes();
    let mut parts = Vec::new();
    let mut start = 0usize;
    let (mut paren, mut bracket, mut brace) = (0usize, 0usize, 0usize);
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
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'|' if paren == 0 && bracket == 0 && brace == 0 => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'|' {
                    i += 2;
                    continue;
                }
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

/// Parses a `specr lang` type string into a structured `SpecrType`.
#[must_use]
pub fn parse_specr_type(raw_ty: &str) -> SpecrType {
    let norm = normalize_whitespace(raw_ty);
    let mut s = norm.as_str().trim();
    if s.is_empty() || s == "()" {
        return SpecrType::Unit;
    }
    if s == "&str" || s == "& str" || s == "str" || s == "String" {
        return SpecrType::String;
    }
    while let Some(rest) = s.strip_prefix('&') {
        let mut r = rest.trim_start();
        if r.starts_with('\'')
            && let Some(sp) = r.find(char::is_whitespace)
        {
            r = r[sp..].trim_start();
        }
        if let Some(after_mut) = r.strip_prefix("mut ") {
            r = after_mut.trim_start();
        } else if let Some(after_mut) = r.strip_prefix("mut")
            && after_mut.starts_with(['(', '[', '&'])
        {
            r = after_mut.trim_start();
        }
        if r == "str" {
            return SpecrType::String;
        }
        s = r;
    }
    if s.starts_with('[') && s.ends_with(']') && find_matching_delim(s, 0) == Some(s.len() - 1) {
        let inner = s[1..s.len() - 1].trim();
        let elem = inner.split(';').next().unwrap_or(inner).trim();
        return SpecrType::List(Box::new(parse_specr_type(elem)));
    }
    if s.starts_with('(') && s.ends_with(')') && find_matching_delim(s, 0) == Some(s.len() - 1) {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return SpecrType::Unit;
        }
        let parts = split_commas_opts(inner, true);
        if parts.len() == 1 && !inner.ends_with(',') {
            return parse_specr_type(parts[0]);
        }
        return SpecrType::Tuple(parts.into_iter().map(parse_specr_type).collect());
    }
    if let Some(lt_pos) = s.find('<')
        && s.ends_with('>')
    {
        let head = s[..lt_pos].trim().rsplit("::").next().unwrap_or("").trim();
        let inner = s[lt_pos + 1..s.len() - 1].trim();
        let args = split_commas_opts(inner, true);
        match head {
            "GcCow" if !args.is_empty() => return parse_specr_type(args[0]),
            "Option" if !args.is_empty() => {
                return SpecrType::Option(Box::new(parse_specr_type(args[0])));
            }
            "Result" => {
                let inner_ty = args.first().copied().unwrap_or("()");
                return SpecrType::Result(Box::new(parse_specr_type(inner_ty)));
            }
            "NdResult" => {
                let inner_ty = args.first().copied().unwrap_or("()");
                return SpecrType::NdResult(Box::new(parse_specr_type(inner_ty)));
            }
            "List" | "Vec" if !args.is_empty() => {
                return SpecrType::List(Box::new(parse_specr_type(args[0])));
            }
            "Set" if !args.is_empty() => {
                return SpecrType::Set(Box::new(parse_specr_type(args[0])));
            }
            "Map" if args.len() >= 2 => {
                return SpecrType::Map(
                    Box::new(parse_specr_type(args[0])),
                    Box::new(parse_specr_type(args[1])),
                );
            }
            _ => return SpecrType::Nominal(escape_lean_ident(head)),
        }
    }
    let last_seg = s.rsplit("::").next().unwrap_or(s).trim();
    match last_seg {
        "bool" | "Bool" => SpecrType::Bool,
        "u8" => SpecrType::U8,
        "u16" | "u32" | "u64" | "u128" | "usize" | "Nat" => SpecrType::Nat,
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "Int" => SpecrType::Int,
        "String" | "str" => SpecrType::String,
        "Size" => SpecrType::Size,
        "Offset" => SpecrType::Offset,
        "Align" => SpecrType::Align,
        "Signedness" => SpecrType::Signedness,
        "Endianness" => SpecrType::Endianness,
        "Result" => SpecrType::Result(Box::new(SpecrType::Unit)),
        "NdResult" => SpecrType::NdResult(Box::new(SpecrType::Unit)),
        other => SpecrType::Nominal(escape_lean_ident(other)),
    }
}

impl SpecrType {
    /// Renders a `SpecrType` as a Lean 4 type expression.
    #[must_use]
    pub fn to_lean(&self) -> String {
        match self {
            Self::Unit => "Unit".to_string(),
            Self::Bool => "Bool".to_string(),
            Self::U8 => "UInt8".to_string(),
            Self::Nat => "Nat".to_string(),
            Self::Int => "SpecrInt".to_string(),
            Self::String => "String".to_string(),
            Self::Size => "Size".to_string(),
            Self::Offset => "Offset".to_string(),
            Self::Align => "Align".to_string(),
            Self::Signedness => "Signedness".to_string(),
            Self::Endianness => "Endianness".to_string(),
            Self::Tuple(elems) => {
                if elems.is_empty() {
                    "Unit".to_string()
                } else {
                    let rendered: Vec<String> = elems.iter().map(Self::to_lean).collect();
                    format!("({})", rendered.join(" × "))
                }
            }
            Self::Option(inner) => format!("Option ({})", inner.to_lean()),
            Self::Result(inner) => format!("Except TerminationInfo ({})", inner.to_lean()),
            Self::NdResult(inner) => format!("NdComp ({})", inner.to_lean()),
            Self::List(inner) => format!("List ({})", inner.to_lean()),
            Self::Set(inner) => format!("SpecrSet ({})", inner.to_lean()),
            Self::Map(k, v) => format!("SpecrMap ({}) ({})", k.to_lean(), v.to_lean()),
            Self::Nominal(name) => name.clone(),
        }
    }
}

/// Lowers a raw `specr lang` type string into its Lean 4 representation.
#[must_use]
pub fn lower_specr_type_to_lean(raw_ty: &str) -> String {
    parse_specr_type(raw_ty).to_lean()
}

fn parse_path_segments(raw: &str) -> Vec<String> {
    raw.split("::")
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|s| {
            if let Some(lt) = s.find('<') {
                s[..lt].trim().to_string()
            } else {
                s.to_string()
            }
        })
        .collect()
}

fn is_valid_ident(s: &str) -> bool {
    let stripped = s.strip_prefix("r#").unwrap_or(s);
    !stripped.is_empty()
        && stripped
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !stripped.bytes().next().unwrap_or(b'0').is_ascii_digit()
}

fn parse_int_literal(s: &str) -> Option<i128> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return None;
    }
    let (neg, rest) = if let Some(r) = trimmed.strip_prefix('-') {
        (true, r.trim_start())
    } else {
        (false, trimmed)
    };
    if !rest.bytes().next()?.is_ascii_digit() {
        return None;
    }
    let cleaned: String = rest.chars().filter(|&c| c != '_').collect();
    let (radix, digits) = if let Some(hex) = cleaned
        .strip_prefix("0x")
        .or_else(|| cleaned.strip_prefix("0X"))
    {
        let d_len = hex.bytes().take_while(u8::is_ascii_hexdigit).count();
        (16, &hex[..d_len])
    } else if let Some(bin) = cleaned
        .strip_prefix("0b")
        .or_else(|| cleaned.strip_prefix("0B"))
    {
        let d_len = bin.bytes().take_while(|&b| b == b'0' || b == b'1').count();
        (2, &bin[..d_len])
    } else {
        let d_len = cleaned.bytes().take_while(u8::is_ascii_digit).count();
        let suffix = &cleaned[d_len..];
        if !suffix.is_empty()
            && !matches!(
                suffix,
                "u8" | "u16"
                    | "u32"
                    | "u64"
                    | "u128"
                    | "usize"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "i64"
                    | "i128"
                    | "isize"
            )
        {
            return None;
        }
        (10, &cleaned[..d_len])
    };
    let val = i128::from_str_radix(digits, radix).ok()?;
    Some(if neg { -val } else { val })
}

/// Parses a `specr lang` pattern into a structured `SpecrPat`.
pub fn parse_specr_pat(raw_pat: &str) -> Result<SpecrPat, String> {
    let mut s = raw_pat.trim();
    if s.is_empty() {
        return Err("empty pattern".to_string());
    }
    let alts = split_top_level_bar(s);
    if alts.len() > 1 {
        let mut parsed = Vec::with_capacity(alts.len());
        for a in alts {
            parsed.push(parse_specr_pat(a)?);
        }
        return Ok(SpecrPat::Or(parsed));
    }
    while let Some(rest) = s.strip_prefix('&') {
        let r = rest.trim_start();
        s = r.strip_prefix("mut ").unwrap_or(r).trim_start();
    }
    if s == "_" || s == ".." {
        return Ok(SpecrPat::Wildcard);
    }
    if s == "()" {
        return Ok(SpecrPat::Lit(SpecrLit::Unit));
    }
    if s == "true" {
        return Ok(SpecrPat::Lit(SpecrLit::Bool(true)));
    }
    if s == "false" {
        return Ok(SpecrPat::Lit(SpecrLit::Bool(false)));
    }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return Ok(SpecrPat::Lit(SpecrLit::Str(s[1..s.len() - 1].to_string())));
    }
    if let Some(n) = parse_int_literal(s) {
        return Ok(SpecrPat::Lit(SpecrLit::Int(n)));
    }
    if s.starts_with('(') && s.ends_with(')') && find_matching_delim(s, 0) == Some(s.len() - 1) {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return Ok(SpecrPat::Lit(SpecrLit::Unit));
        }
        let parts = split_commas_opts(inner, false);
        if parts.len() == 1 && !inner.ends_with(',') {
            return parse_specr_pat(parts[0]);
        }
        let mut elems = Vec::with_capacity(parts.len());
        for p in parts {
            elems.push(parse_specr_pat(p)?);
        }
        return Ok(SpecrPat::Tuple(elems));
    }
    if let Some(open_p) = s.find('(')
        && find_matching_delim(s, open_p) == Some(s.len() - 1)
    {
        let head = s[..open_p].trim();
        let path = parse_path_segments(head);
        let inner = s[open_p + 1..s.len() - 1].trim();
        let parts = split_commas_opts(inner, false);
        let mut args = Vec::with_capacity(parts.len());
        for p in parts {
            args.push(parse_specr_pat(p)?);
        }
        return Ok(SpecrPat::TupleVariant { path, args });
    }
    if let Some(open_b) = s.find('{')
        && find_matching_delim(s, open_b) == Some(s.len() - 1)
    {
        let head = s[..open_b].trim();
        let path = parse_path_segments(head);
        let inner = s[open_b + 1..s.len() - 1].trim();
        let mut fields = Vec::new();
        let mut has_rest = false;
        for entry in split_commas_opts(inner, false) {
            let e = entry.trim();
            if e == ".." {
                has_rest = true;
            } else if let Some((fname, fpat)) = e.split_once(':') {
                fields.push((fname.trim().to_string(), parse_specr_pat(fpat.trim())?));
            } else {
                let e_no_ref = e.strip_prefix("ref ").unwrap_or(e).trim();
                let (mutable, ident) = if let Some(r) = e_no_ref.strip_prefix("mut ") {
                    (true, r.trim())
                } else {
                    (false, e_no_ref)
                };
                fields.push((
                    ident.to_string(),
                    SpecrPat::Bind {
                        name: ident.to_string(),
                        mutable,
                    },
                ));
            }
        }
        return Ok(SpecrPat::StructVariant {
            path,
            fields,
            has_rest,
        });
    }
    let s_no_ref = s.strip_prefix("ref ").unwrap_or(s).trim();
    if let Some(rest) = s_no_ref.strip_prefix("mut ") {
        let ident = rest.trim();
        if is_valid_ident(ident) {
            return Ok(SpecrPat::Bind {
                name: ident.to_string(),
                mutable: true,
            });
        }
    }
    if let Some((lhs, rhs)) = s_no_ref.split_once('@') {
        let _ = lhs;
        return parse_specr_pat(rhs.trim());
    }
    if s_no_ref.contains("::") || s_no_ref.starts_with(|c: char| c.is_ascii_uppercase()) {
        return Ok(SpecrPat::Path(parse_path_segments(s_no_ref)));
    }
    if is_valid_ident(s_no_ref) {
        return Ok(SpecrPat::Bind {
            name: s_no_ref.to_string(),
            mutable: false,
        });
    }
    Err(format!("unsupported pattern: `{raw_pat}`"))
}

/// Finds the next top-level `;` at delimiter depth 0.
fn find_top_level_semi(src: &str) -> Option<usize> {
    let bytes = src.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
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

/// Finds a top-level `=` (excluding `==`, `!=`, `<=`, `>=`, `=>`).
fn find_top_level_eq(src: &str) -> Option<usize> {
    let bytes = src.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
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
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'=' if brace == 0 && paren == 0 && bracket == 0 => {
                let prev = if i > 0 { bytes[i - 1] } else { 0 };
                let next = if i + 1 < bytes.len() { bytes[i + 1] } else { 0 };
                if !matches!(prev, b'=' | b'!' | b'<' | b'>') && !matches!(next, b'=' | b'>') {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Splits a top-level assignment (`=`, `+=`, `-=`, `*=`, `/=`, `%=`, `&=`,
/// `|=`, `^=`).
fn split_top_level_assign(src: &str) -> Option<(&str, Option<SpecrBinOp>, &str)> {
    let pos = find_top_level_eq(src)?;
    let bytes = src.as_bytes();
    let prev = if pos > 0 { bytes[pos - 1] } else { 0 };
    let (lhs_end, op) = match prev {
        b'+' => (pos - 1, Some(SpecrBinOp::Add)),
        b'-' => (pos - 1, Some(SpecrBinOp::Sub)),
        b'*' => (pos - 1, Some(SpecrBinOp::Mul)),
        b'/' => (pos - 1, Some(SpecrBinOp::Div)),
        b'%' => (pos - 1, Some(SpecrBinOp::Rem)),
        b'&' => (pos - 1, Some(SpecrBinOp::BitAnd)),
        b'|' => (pos - 1, Some(SpecrBinOp::BitOr)),
        b'^' => (pos - 1, Some(SpecrBinOp::BitXor)),
        _ => (pos, None),
    };
    let lhs = src[..lhs_end].trim();
    let rhs = src[pos + 1..].trim();
    if lhs.is_empty() || rhs.is_empty() {
        return None;
    }
    Some((lhs, op, rhs))
}

/// Finds a top-level `:` (excluding `::`) inside a `let pat: Ty` binding.
fn split_top_level_colon(src: &str) -> Option<(&str, &str)> {
    let bytes = src.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
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
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b':' if brace == 0 && paren == 0 && bracket == 0 => {
                let prev = if i > 0 { bytes[i - 1] } else { 0 };
                let next = if i + 1 < bytes.len() { bytes[i + 1] } else { 0 };
                if prev != b':' && next != b':' {
                    return Some((src[..i].trim(), src[i + 1..].trim()));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Finds the byte length of a leading `if ... { ... } [else ...]` or
/// `match ... { ... }` or `{ ... }` control-flow expression at `src`.
fn extract_control_flow_prefix(src: &str) -> Option<usize> {
    let bytes = src.as_bytes();
    if bytes.first() == Some(&b'{') {
        return find_matching_delim(src, 0).map(|c| c + 1);
    }
    let is_if = src.starts_with("if ") || src.starts_with("if(") || src.starts_with("if\n");
    let is_match =
        src.starts_with("match ") || src.starts_with("match(") || src.starts_with("match\n");
    if !is_if && !is_match {
        return None;
    }
    let (mut paren, mut bracket) = (0usize, 0usize);
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
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'{' if paren == 0 && bracket == 0 => {
                let close_b = find_matching_delim(src, i)?;
                let after_brace = &src[close_b + 1..];
                let trimmed_after = after_brace.trim_start();
                let ws_len = after_brace.len() - trimmed_after.len();
                // If this `{ ... }` is followed by `=` or `.` or `,` inside the
                // condition/scrutinee (e.g. a struct literal in the condition),
                // keep scanning for the body brace.
                if trimmed_after.starts_with("==")
                    || trimmed_after.starts_with("!=")
                    || trimmed_after.starts_with("&&")
                    || trimmed_after.starts_with("||")
                    || (trimmed_after.starts_with('=') && !trimmed_after.starts_with("=>"))
                {
                    i = close_b + 1;
                    continue;
                }
                if is_match {
                    return Some(close_b + 1);
                }
                let mut end_pos = close_b + 1;
                loop {
                    let rem = &src[end_pos..];
                    let rem_trim = rem.trim_start();
                    let rem_ws = rem.len() - rem_trim.len();
                    if let Some(after_else) = rem_trim.strip_prefix("else") {
                        let ae_trim = after_else.trim_start();
                        let ae_ws = after_else.len() - ae_trim.len();
                        if ae_trim.starts_with('{') {
                            let c = find_matching_delim(ae_trim, 0)?;
                            end_pos += rem_ws + 4 + ae_ws + c + 1;
                            break;
                        } else if ae_trim.starts_with("if ") || ae_trim.starts_with("if(") {
                            let sub_len = extract_control_flow_prefix(ae_trim)?;
                            end_pos += rem_ws + 4 + ae_ws + sub_len;
                            break;
                        }
                    }
                    let _ = ws_len;
                    break;
                }
                return Some(end_pos);
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Parses a block of `specr lang` statements into a `Vec<SpecrStmt>`.
pub fn parse_specr_stmts(raw_block: &str) -> Result<Vec<SpecrStmt>, String> {
    let clean = crate::specr_ast::strip_comments_preserve_newlines(raw_block);
    let mut s = clean.trim();
    if s.starts_with('{') && s.ends_with('}') && find_matching_delim(s, 0) == Some(s.len() - 1) {
        s = s[1..s.len() - 1].trim();
    }
    let mut stmts = Vec::new();
    let mut rest = s;
    while !rest.is_empty() {
        rest = rest.trim_start();
        while let Some(r) = rest.strip_prefix(';') {
            rest = r.trim_start();
        }
        if rest.is_empty() {
            break;
        }
        if (rest.starts_with("let ") || rest.starts_with("let(") || rest.starts_with("let\n"))
            && let Some(semi_pos) = find_top_level_semi(rest)
        {
            let let_inner = rest[3..semi_pos].trim();
            let eq_pos = find_top_level_eq(let_inner)
                .ok_or_else(|| format!("missing `=` in let statement: `{let_inner}`"))?;
            let lhs = let_inner[..eq_pos].trim();
            let rhs = let_inner[eq_pos + 1..].trim();
            let (pat_str, ty) = if let Some((p, t)) = split_top_level_colon(lhs) {
                (p, Some(parse_specr_type(t)))
            } else {
                (lhs, None)
            };
            let pat = parse_specr_pat(pat_str)?;
            let init = parse_specr_expr(rhs)?;
            stmts.push(SpecrStmt::Let { pat, ty, init });
            rest = &rest[semi_pos + 1..];
            continue;
        }
        if let Some(cf_len) = extract_control_flow_prefix(rest) {
            let after = rest[cf_len..].trim_start();
            let cont_with_op = after.starts_with('.')
                || after.starts_with('?')
                || after.starts_with('+')
                || after.starts_with('-')
                || after.starts_with('*')
                || after.starts_with('/')
                || after.starts_with('%')
                || after.starts_with("&&")
                || after.starts_with("||")
                || after.starts_with("==")
                || after.starts_with("!=");
            if !cont_with_op {
                let expr = parse_specr_expr(&rest[..cf_len])?;
                if let Some(after_semi) = after.strip_prefix(';') {
                    stmts.push(SpecrStmt::Expr {
                        expr,
                        has_semi: true,
                    });
                    rest = after_semi;
                } else if after.is_empty() {
                    stmts.push(SpecrStmt::Expr {
                        expr,
                        has_semi: false,
                    });
                    break;
                } else {
                    stmts.push(SpecrStmt::Expr {
                        expr,
                        has_semi: true,
                    });
                    rest = after;
                }
                continue;
            }
        }
        if let Some(semi_pos) = find_top_level_semi(rest) {
            let chunk = rest[..semi_pos].trim();
            if let Some((lhs_s, op, rhs_s)) = split_top_level_assign(chunk) {
                stmts.push(SpecrStmt::Assign {
                    lhs: parse_specr_expr(lhs_s)?,
                    op,
                    rhs: parse_specr_expr(rhs_s)?,
                });
            } else {
                stmts.push(SpecrStmt::Expr {
                    expr: parse_specr_expr(chunk)?,
                    has_semi: true,
                });
            }
            rest = &rest[semi_pos + 1..];
        } else {
            let chunk = rest.trim();
            if let Some((lhs_s, op, rhs_s)) = split_top_level_assign(chunk) {
                stmts.push(SpecrStmt::Assign {
                    lhs: parse_specr_expr(lhs_s)?,
                    op,
                    rhs: parse_specr_expr(rhs_s)?,
                });
            } else {
                stmts.push(SpecrStmt::Expr {
                    expr: parse_specr_expr(chunk)?,
                    has_semi: false,
                });
            }
            break;
        }
    }
    Ok(stmts)
}

/// Splits `<pat> [if <guard>]` at a top-level `if` keyword.
fn split_pat_and_guard(src: &str) -> (&str, Option<&str>) {
    let bytes = src.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
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
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'i' if brace == 0 && paren == 0 && bracket == 0 => {
                let prev_ws = i == 0 || bytes[i - 1].is_ascii_whitespace() || bytes[i - 1] == b')';
                if prev_ws
                    && src[i..].starts_with("if")
                    && src[i + 2..]
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_whitespace() || c == '(')
                {
                    return (src[..i].trim(), Some(src[i + 2..].trim()));
                }
            }
            _ => {}
        }
        i += 1;
    }
    (src.trim(), None)
}

/// Finds the next top-level `=>` at delimiter depth 0.
fn find_top_level_fat_arrow(src: &str) -> Option<usize> {
    let bytes = src.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
    let mut in_str = false;
    let mut i = 0usize;
    while i + 1 < bytes.len() {
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
            b'=' if brace == 0 && paren == 0 && bracket == 0 && bytes[i + 1] == b'>' => {
                return Some(i);
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Parses all arms inside `match scrutinee { ... }`.
fn parse_match_arms(inner: &str) -> Result<Vec<SpecrMatchArm>, String> {
    let mut arms = Vec::new();
    let mut rest = inner.trim();
    while !rest.is_empty() {
        rest = rest.trim_start_matches([',', ';', ' ', '\t', '\n', '\r']);
        if rest.is_empty() {
            break;
        }
        let arrow_pos = find_top_level_fat_arrow(rest)
            .ok_or_else(|| format!("missing `=>` in match arm: `{rest}`"))?;
        let lhs = rest[..arrow_pos].trim();
        let (pat_s, guard_s) = split_pat_and_guard(lhs);
        let pat = parse_specr_pat(pat_s)?;
        let guard = match guard_s {
            Some(g) => Some(parse_specr_expr(g)?),
            None => None,
        };
        let after_arrow = rest[arrow_pos + 2..].trim_start();
        if let Some(cf_len) = extract_control_flow_prefix(after_arrow) {
            let after_cf = after_arrow[cf_len..].trim_start();
            let cont_op = after_cf.starts_with('.') || after_cf.starts_with('?');
            if !cont_op {
                let body = parse_specr_expr(&after_arrow[..cf_len])?;
                arms.push(SpecrMatchArm { pat, guard, body });
                rest = after_cf.strip_prefix(',').unwrap_or(after_cf).trim_start();
                continue;
            }
        }
        // Scan for top-level `,` ending the arm
        let bytes = after_arrow.as_bytes();
        let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
        let mut in_str = false;
        let mut comma_pos = None;
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
                b'{' => brace += 1,
                b'}' => brace = brace.saturating_sub(1),
                b'(' => paren += 1,
                b')' => paren = paren.saturating_sub(1),
                b'[' => bracket += 1,
                b']' => bracket = bracket.saturating_sub(1),
                b',' if brace == 0 && paren == 0 && bracket == 0 => {
                    comma_pos = Some(i);
                    break;
                }
                _ => {}
            }
            i += 1;
        }
        if let Some(cpos) = comma_pos {
            let body = parse_specr_expr(after_arrow[..cpos].trim())?;
            arms.push(SpecrMatchArm { pat, guard, body });
            rest = &after_arrow[cpos + 1..];
        } else {
            let body = parse_specr_expr(after_arrow.trim())?;
            arms.push(SpecrMatchArm { pat, guard, body });
            break;
        }
    }
    Ok(arms)
}

fn is_operand_end_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b')' | b']' | b'}' | b'"' | b'\'' | b'?')
}

/// Scans `s` for the rightmost top-level binary operator in `ops` (for
/// left-associative grouping).
fn find_rightmost_binop(s: &str, tier: u8) -> Option<(usize, usize, SpecrBinOp)> {
    let bytes = s.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
    let mut in_str = false;
    let mut last_match: Option<(usize, usize, SpecrBinOp)> = None;
    let mut prev_non_ws: u8 = 0;
    let mut i = 0usize;
    while i < bytes.len() {
        if in_str {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_str = false;
                prev_non_ws = b'"';
            }
            i += 1;
            continue;
        }
        let b = bytes[i];
        if b == b'"' {
            in_str = true;
            i += 1;
            continue;
        }
        match b {
            b'{' => {
                brace += 1;
                i += 1;
                continue;
            }
            b'}' => {
                brace = brace.saturating_sub(1);
                prev_non_ws = b'}';
                i += 1;
                continue;
            }
            b'(' => {
                paren += 1;
                i += 1;
                continue;
            }
            b')' => {
                paren = paren.saturating_sub(1);
                prev_non_ws = b')';
                i += 1;
                continue;
            }
            b'[' => {
                bracket += 1;
                i += 1;
                continue;
            }
            b']' => {
                bracket = bracket.saturating_sub(1);
                prev_non_ws = b']';
                i += 1;
                continue;
            }
            _ => {}
        }
        if brace == 0 && paren == 0 && bracket == 0 && is_operand_end_byte(prev_non_ws) {
            let next = if i + 1 < bytes.len() { bytes[i + 1] } else { 0 };
            let prev = if i > 0 { bytes[i - 1] } else { 0 };
            let matched = match tier {
                1 if b == b'|' && next == b'|' => Some((i, 2, SpecrBinOp::Or)),
                2 if b == b'&' && next == b'&' => Some((i, 2, SpecrBinOp::And)),
                3 => match (b, next) {
                    (b'=', b'=') => Some((i, 2, SpecrBinOp::Eq)),
                    (b'!', b'=') => Some((i, 2, SpecrBinOp::Ne)),
                    (b'<', b'=') => Some((i, 2, SpecrBinOp::Le)),
                    (b'>', b'=') => Some((i, 2, SpecrBinOp::Ge)),
                    (b'<', _) if next != b'<' && prev != b'<' => Some((i, 1, SpecrBinOp::Lt)),
                    (b'>', _) if next != b'>' && !matches!(prev, b'>' | b'-' | b'=' | b'<') => {
                        Some((i, 1, SpecrBinOp::Gt))
                    }
                    _ => None,
                },
                4 if b == b'|' && next != b'|' && prev != b'|' => Some((i, 1, SpecrBinOp::BitOr)),
                5 if b == b'^' => Some((i, 1, SpecrBinOp::BitXor)),
                6 if b == b'&' && next != b'&' && prev != b'&' => Some((i, 1, SpecrBinOp::BitAnd)),
                7 => match (b, next) {
                    (b'<', b'<') => Some((i, 2, SpecrBinOp::Shl)),
                    (b'>', b'>') => Some((i, 2, SpecrBinOp::Shr)),
                    _ => None,
                },
                8 => match b {
                    b'+' => Some((i, 1, SpecrBinOp::Add)),
                    b'-' if next != b'>' => Some((i, 1, SpecrBinOp::Sub)),
                    _ => None,
                },
                9 => match b {
                    b'*' => Some((i, 1, SpecrBinOp::Mul)),
                    b'/' => Some((i, 1, SpecrBinOp::Div)),
                    b'%' => Some((i, 1, SpecrBinOp::Rem)),
                    _ => None,
                },
                _ => None,
            };
            if let Some((pos, len, op)) = matched {
                last_match = Some((pos, len, op));
                prev_non_ws = 0;
                i += len;
                continue;
            }
        }
        if !b.is_ascii_whitespace() {
            prev_non_ws = b;
        }
        i += 1;
    }
    last_match
}

/// Finds a top-level range operator (`..=` or `..`) outside `{ .. }`.
fn find_top_level_range(s: &str) -> Option<(usize, usize, bool)> {
    let bytes = s.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
    let mut in_str = false;
    let mut i = 0usize;
    while i + 1 < bytes.len() {
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
            b'.' if brace == 0 && paren == 0 && bracket == 0 && bytes[i + 1] == b'.' => {
                if i + 2 < bytes.len() && bytes[i + 2] == b'=' {
                    return Some((i, 3, true));
                }
                return Some((i, 2, false));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Finds the matching `(` for a trailing `)` at the end of `s`.
fn find_matching_open_paren_at_end(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    if bytes.last() != Some(&b')') {
        return None;
    }
    let mut i = 0usize;
    let (mut brace, mut bracket) = (0usize, 0usize);
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
        match bytes[i] {
            b'"' => in_str = true,
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'(' if brace == 0 && bracket == 0 => {
                let close = find_matching_delim(s, i)?;
                if close == bytes.len() - 1 {
                    return Some(i);
                }
                i = close;
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Finds the rightmost top-level `.` (excluding `..` and numeric literals).
fn find_rightmost_top_level_dot(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let (mut brace, mut paren, mut bracket) = (0usize, 0usize, 0usize);
    let mut in_str = false;
    let mut last_dot = None;
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
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'.' if brace == 0 && paren == 0 && bracket == 0 => {
                let prev = if i > 0 { bytes[i - 1] } else { 0 };
                let next = if i + 1 < bytes.len() { bytes[i + 1] } else { 0 };
                if prev != b'.' && next != b'.' {
                    last_dot = Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    last_dot
}

fn parse_macro_call(macro_name: &str, inner: &str) -> Result<SpecrExpr, String> {
    let name = macro_name.trim_end_matches('!').trim();
    let last_seg = name.rsplit("::").next().unwrap_or(name);
    match last_seg {
        "throw_machine_stop" => Ok(SpecrExpr::ThrowMachineStop),
        "throw_ub" | "throw_ill_formed" | "panic" | "todo" | "unreachable" => {
            let parts = split_commas_opts(inner, false);
            let msg = if let Some(&first) = parts.first() {
                let f = first.trim();
                if f.starts_with('"') && f.ends_with('"') && f.len() >= 2 {
                    f[1..f.len() - 1].to_string()
                } else {
                    f.to_string()
                }
            } else {
                last_seg.to_string()
            };
            let mut args = Vec::new();
            for &arg_s in parts.iter().skip(1) {
                args.push(parse_specr_expr(arg_s)?);
            }
            if last_seg == "throw_ill_formed" {
                Ok(SpecrExpr::ThrowIllFormed { msg, args })
            } else {
                Ok(SpecrExpr::ThrowUb { msg, args })
            }
        }
        "matches" => {
            let parts = split_commas_opts(inner, false);
            if parts.len() < 2 {
                return Err(format!("matches! requires 2 arguments: `{inner}`"));
            }
            let expr = Box::new(parse_specr_expr(parts[0])?);
            let pat = parse_specr_pat(&parts[1..].join(", "))?;
            Ok(SpecrExpr::Matches { expr, pat })
        }
        _ => {
            let parts = split_commas_opts(inner, false);
            let mut args = Vec::with_capacity(parts.len());
            for p in parts {
                args.push(parse_specr_expr(p)?);
            }
            Ok(SpecrExpr::Call {
                func: Box::new(SpecrExpr::Path(vec![last_seg.to_string()])),
                args,
            })
        }
    }
}

/// Parses a `specr lang` expression string into a structured `SpecrExpr`.
pub fn parse_specr_expr(raw_expr: &str) -> Result<SpecrExpr, String> {
    let clean = crate::specr_ast::strip_comments_preserve_newlines(raw_expr);
    let s = clean.trim();
    if s.is_empty() || s == "()" {
        return Ok(SpecrExpr::Lit(SpecrLit::Unit));
    }
    if s.starts_with('(') && s.ends_with(')') && find_matching_delim(s, 0) == Some(s.len() - 1) {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return Ok(SpecrExpr::Lit(SpecrLit::Unit));
        }
        let parts = split_commas_opts(inner, false);
        if parts.len() == 1 && !inner.ends_with(',') {
            return parse_specr_expr(parts[0]);
        }
        let mut elems = Vec::with_capacity(parts.len());
        for p in parts {
            elems.push(parse_specr_expr(p)?);
        }
        return Ok(SpecrExpr::Tuple(elems));
    }
    if s == "return" {
        return Ok(SpecrExpr::Return(None));
    }
    if let Some(rest) = s.strip_prefix("return ") {
        return Ok(SpecrExpr::Return(Some(Box::new(parse_specr_expr(
            rest.trim(),
        )?))));
    }
    if let Some(rest) = s.strip_prefix("||") {
        return Ok(SpecrExpr::Closure {
            params: Vec::new(),
            body: Box::new(parse_specr_expr(rest.trim())?),
        });
    }
    if s.starts_with('|')
        && let Some(close_bar) = s[1..].find('|')
    {
        let param_str = &s[1..1 + close_bar];
        let body_str = s[1 + close_bar + 1..].trim();
        let params: Vec<String> = split_commas_opts(param_str, true)
            .into_iter()
            .map(|p| {
                let p_col = p.split(':').next().unwrap_or(p).trim();
                p_col
                    .strip_prefix("mut ")
                    .unwrap_or(p_col)
                    .trim()
                    .to_string()
            })
            .filter(|p| !p.is_empty())
            .collect();
        return Ok(SpecrExpr::Closure {
            params,
            body: Box::new(parse_specr_expr(body_str)?),
        });
    }
    if extract_control_flow_prefix(s) == Some(s.len()) {
        if s.starts_with('{') {
            return Ok(SpecrExpr::Block(parse_specr_stmts(&s[1..s.len() - 1])?));
        }
        if s.starts_with("if") {
            return parse_if_expr(s);
        }
        if s.starts_with("match") {
            return parse_match_expr(s);
        }
    }
    if let Some((pos, len, inclusive)) = find_top_level_range(s) {
        let lhs = s[..pos].trim();
        let rhs = s[pos + len..].trim();
        if !lhs.is_empty() && !rhs.is_empty() {
            return Ok(SpecrExpr::Range {
                start: Box::new(parse_specr_expr(lhs)?),
                end: Box::new(parse_specr_expr(rhs)?),
                inclusive,
            });
        }
    }
    for tier in 1..=9 {
        if let Some((pos, len, op)) = find_rightmost_binop(s, tier) {
            let lhs = s[..pos].trim();
            let rhs = s[pos + len..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                return Ok(SpecrExpr::Binary {
                    op,
                    lhs: Box::new(parse_specr_expr(lhs)?),
                    rhs: Box::new(parse_specr_expr(rhs)?),
                });
            }
        }
    }
    parse_unary_or_postfix(s)
}

fn find_body_brace(s: &str, start_offset: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    let (mut paren, mut bracket) = (0usize, 0usize);
    let mut in_str = false;
    let mut i = start_offset;
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
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'{' if paren == 0 && bracket == 0 => {
                let close_b = find_matching_delim(s, i)?;
                let after = s[close_b + 1..].trim_start();
                if after.starts_with("==")
                    || after.starts_with("!=")
                    || after.starts_with("&&")
                    || after.starts_with("||")
                    || (after.starts_with('=') && !after.starts_with("=>"))
                {
                    i = close_b + 1;
                    continue;
                }
                return Some(i);
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn parse_if_expr(s: &str) -> Result<SpecrExpr, String> {
    let open_b = find_body_brace(s, 2).ok_or_else(|| format!("missing `{{` in if expr: `{s}`"))?;
    let cond_raw = s[2..open_b].trim();
    let close_b =
        find_matching_delim(s, open_b).ok_or_else(|| format!("unclosed `{{` in if: `{s}`"))?;
    let then_branch = parse_specr_stmts(&s[open_b + 1..close_b])?;
    let rem = s[close_b + 1..].trim();
    let else_branch = if let Some(after_else) = rem.strip_prefix("else") {
        let ae = after_else.trim();
        Some(Box::new(parse_specr_expr(ae)?))
    } else {
        None
    };
    if let Some(after_let) = cond_raw.strip_prefix("let ") {
        let eq_pos = find_top_level_eq(after_let)
            .ok_or_else(|| format!("missing `=` in `if let`: `{cond_raw}`"))?;
        let pat = parse_specr_pat(after_let[..eq_pos].trim())?;
        let scrut = parse_specr_expr(after_let[eq_pos + 1..].trim())?;
        let else_body = match else_branch {
            Some(eb) => *eb,
            None => SpecrExpr::Block(Vec::new()),
        };
        return Ok(SpecrExpr::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                SpecrMatchArm {
                    pat,
                    guard: None,
                    body: SpecrExpr::Block(then_branch),
                },
                SpecrMatchArm {
                    pat: SpecrPat::Wildcard,
                    guard: None,
                    body: else_body,
                },
            ],
        });
    }
    let cond = parse_specr_expr(cond_raw)?;
    Ok(SpecrExpr::If {
        cond: Box::new(cond),
        then_branch,
        else_branch,
    })
}

fn parse_match_expr(s: &str) -> Result<SpecrExpr, String> {
    let open_b =
        find_body_brace(s, 5).ok_or_else(|| format!("missing `{{` in match expr: `{s}`"))?;
    let scrutinee = Box::new(parse_specr_expr(s[5..open_b].trim())?);
    let close_b =
        find_matching_delim(s, open_b).ok_or_else(|| format!("unclosed `{{` in match: `{s}`"))?;
    let arms = parse_match_arms(&s[open_b + 1..close_b])?;
    Ok(SpecrExpr::Match { scrutinee, arms })
}

fn parse_unary_or_postfix(s: &str) -> Result<SpecrExpr, String> {
    if s == "true" {
        return Ok(SpecrExpr::Lit(SpecrLit::Bool(true)));
    }
    if s == "false" {
        return Ok(SpecrExpr::Lit(SpecrLit::Bool(false)));
    }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return Ok(SpecrExpr::Lit(SpecrLit::Str(s[1..s.len() - 1].to_string())));
    }
    if let Some(n) = parse_int_literal(s) {
        return Ok(SpecrExpr::Lit(SpecrLit::Int(n)));
    }
    if let Some(rest) = s.strip_prefix('!') {
        return Ok(SpecrExpr::Unary {
            op: SpecrUnOp::Not,
            expr: Box::new(parse_specr_expr(rest.trim())?),
        });
    }
    if let Some(rest) = s.strip_prefix('-') {
        return Ok(SpecrExpr::Unary {
            op: SpecrUnOp::Neg,
            expr: Box::new(parse_specr_expr(rest.trim())?),
        });
    }
    if let Some(rest) = s.strip_prefix('*') {
        return Ok(SpecrExpr::Unary {
            op: SpecrUnOp::Deref,
            expr: Box::new(parse_specr_expr(rest.trim())?),
        });
    }
    if let Some(rest) = s.strip_prefix('&') {
        let r = rest.trim_start();
        if let Some(after_mut) = r.strip_prefix("mut ") {
            return Ok(SpecrExpr::Unary {
                op: SpecrUnOp::RefMut,
                expr: Box::new(parse_specr_expr(after_mut.trim())?),
            });
        }
        return Ok(SpecrExpr::Unary {
            op: SpecrUnOp::Ref,
            expr: Box::new(parse_specr_expr(r)?),
        });
    }
    if let Some(stripped) = s.strip_suffix('?') {
        return Ok(SpecrExpr::Try(Box::new(parse_specr_expr(stripped.trim())?)));
    }
    if let Some(open_p) = find_matching_open_paren_at_end(s)
        && open_p > 0
    {
        let head = s[..open_p].trim();
        let inner = s[open_p + 1..s.len() - 1].trim();
        if head.ends_with('!') {
            return parse_macro_call(head, inner);
        }
        let arg_strs = split_commas_opts(inner, false);
        let mut args = Vec::with_capacity(arg_strs.len());
        for a in arg_strs {
            args.push(parse_specr_expr(a)?);
        }
        if let Some(dot_pos) = find_rightmost_top_level_dot(head) {
            let recv_str = head[..dot_pos].trim();
            let method_raw = head[dot_pos + 1..].trim();
            let method = method_raw
                .split("::")
                .next()
                .unwrap_or(method_raw)
                .trim()
                .to_string();
            return Ok(SpecrExpr::MethodCall {
                receiver: Box::new(parse_specr_expr(recv_str)?),
                method,
                args,
            });
        }
        return Ok(SpecrExpr::Call {
            func: Box::new(parse_specr_expr(head)?),
            args,
        });
    }
    if let Some(dot_pos) = find_rightmost_top_level_dot(s) {
        let base_str = s[..dot_pos].trim();
        let field_str = s[dot_pos + 1..].trim();
        if let Ok(idx) = field_str.parse::<usize>() {
            return Ok(SpecrExpr::TupleIndex {
                base: Box::new(parse_specr_expr(base_str)?),
                index: idx,
            });
        }
        if is_valid_ident(field_str) {
            return Ok(SpecrExpr::Field {
                base: Box::new(parse_specr_expr(base_str)?),
                field: field_str.to_string(),
            });
        }
    }
    if s.ends_with('}')
        && let Some(open_b) = s.find('{')
        && open_b > 0
        && find_matching_delim(s, open_b) == Some(s.len() - 1)
    {
        let head = s[..open_b].trim();
        let path = parse_path_segments(head);
        let inner = s[open_b + 1..s.len() - 1].trim();
        let mut fields = Vec::new();
        let mut spread = None;
        for entry in split_commas_opts(inner, false) {
            let e = entry.trim();
            if let Some(sp) = e.strip_prefix("..") {
                if !sp.trim().is_empty() {
                    spread = Some(Box::new(parse_specr_expr(sp.trim())?));
                }
            } else if let Some((fname, fexpr)) = e.split_once(':') {
                fields.push((fname.trim().to_string(), parse_specr_expr(fexpr.trim())?));
            } else if is_valid_ident(e) {
                fields.push((e.to_string(), SpecrExpr::Path(vec![e.to_string()])));
            }
        }
        return Ok(SpecrExpr::StructLit {
            path,
            fields,
            spread,
        });
    }
    if s.starts_with('[') && s.ends_with(']') && find_matching_delim(s, 0) == Some(s.len() - 1) {
        let inner = s[1..s.len() - 1].trim();
        let mut args = Vec::new();
        for a in split_commas_opts(inner, false) {
            args.push(parse_specr_expr(a)?);
        }
        return Ok(SpecrExpr::Call {
            func: Box::new(SpecrExpr::Path(vec!["list".to_string()])),
            args,
        });
    }
    let segs = parse_path_segments(s);
    if !segs.is_empty() {
        return Ok(SpecrExpr::Path(segs));
    }
    Err(format!("unsupported expression: `{s}`"))
}

/// Lowers a `specr lang` `enum` declaration to a Lean 4 `inductive` type.
pub fn lower_specr_enum_to_lean(
    item: &SpecrItem,
    lean_name_override: Option<&str>,
) -> Result<String, String> {
    if item.kind != ItemKind::Enum {
        return Err(format!("expected Enum item, got {:?}", item.kind));
    }
    let name = lean_name_override
        .map(escape_lean_ident)
        .unwrap_or_else(|| escape_lean_ident(&item.ident));
    let mut out = format!(
        "-- @specr-source: {}:{}..{} ({})\n-- @specr-body-sha256: {}\ninductive {name} : Type where\n",
        item.span.rel_path,
        item.span.start_line,
        item.span.end_line,
        item.qualified_name,
        item.body_sha256
    );
    for v in &item.variants {
        let vname = escape_lean_ident(&v.name);
        match &v.payload {
            VariantPayload::Unit => {
                out.push_str(&format!("  | {vname} : {name}\n"));
            }
            VariantPayload::Tuple(tys) => {
                if tys.is_empty() {
                    out.push_str(&format!("  | {vname} : {name}\n"));
                } else {
                    let mut sig = String::new();
                    for (idx, ty) in tys.iter().enumerate() {
                        let lt = lower_specr_type_to_lean(ty).replace("Self", &name);
                        sig.push_str(&format!(" (arg_{idx} : {lt})"));
                    }
                    out.push_str(&format!("  | {vname}{sig} : {name}\n"));
                }
            }
            VariantPayload::Struct(flds) => {
                if flds.is_empty() {
                    out.push_str(&format!("  | {vname} : {name}\n"));
                } else {
                    let mut sig = String::new();
                    for f in flds {
                        let fname = escape_lean_ident(&f.name);
                        let lt = lower_specr_type_to_lean(&f.ty).replace("Self", &name);
                        sig.push_str(&format!(" ({fname} : {lt})"));
                    }
                    out.push_str(&format!("  | {vname}{sig} : {name}\n"));
                }
            }
        }
    }
    out.push_str("  deriving Inhabited, DecidableEq, Repr\n\n");
    Ok(out)
}

/// Lowers a `specr lang` `struct` declaration to a Lean 4 `structure` type.
pub fn lower_specr_struct_to_lean(
    item: &SpecrItem,
    lean_name_override: Option<&str>,
) -> Result<String, String> {
    if item.kind != ItemKind::Struct {
        return Err(format!("expected Struct item, got {:?}", item.kind));
    }
    let name = lean_name_override
        .map(escape_lean_ident)
        .unwrap_or_else(|| escape_lean_ident(&item.ident));
    let mut out = format!(
        "-- @specr-source: {}:{}..{} ({})\n-- @specr-body-sha256: {}\nstructure {name} : Type where\n",
        item.span.rel_path,
        item.span.start_line,
        item.span.end_line,
        item.qualified_name,
        item.body_sha256
    );
    if item.fields.is_empty() {
        out.push_str("  mk ::\n");
    } else {
        for f in &item.fields {
            let fname = escape_lean_ident(&f.name);
            let lt = lower_specr_type_to_lean(&f.ty).replace("Self", &name);
            out.push_str(&format!("  {fname} : {lt}\n"));
        }
    }
    out.push_str("  deriving Inhabited, DecidableEq, Repr\n\n");
    Ok(out)
}

/// Lowers a `specr lang` `type` alias declaration to a Lean 4 `abbrev`.
pub fn lower_specr_type_alias_to_lean(
    item: &SpecrItem,
    lean_name_override: Option<&str>,
) -> Result<String, String> {
    if item.kind != ItemKind::TypeAlias {
        return Err(format!("expected TypeAlias item, got {:?}", item.kind));
    }
    let name = lean_name_override
        .map(escape_lean_ident)
        .unwrap_or_else(|| escape_lean_ident(&item.ident));
    let aliased = item.aliased_type.as_deref().unwrap_or("()");
    let lean_ty = lower_specr_type_to_lean(aliased);
    Ok(format!(
        "-- @specr-source: {}:{}..{} ({})\n-- @specr-body-sha256: {}\nabbrev {name} : Type := {lean_ty}\n\n",
        item.span.rel_path,
        item.span.start_line,
        item.span.end_line,
        item.qualified_name,
        item.body_sha256
    ))
}

fn lookup_struct_variant_fields<'a>(
    env: &'a TypeEnvironment,
    path: &[String],
    self_type: Option<&str>,
) -> Option<&'a [crate::specr_ast::FieldDecl]> {
    let var_name = path.last()?.as_str();
    let enum_hint = if path.len() >= 2 {
        let h = path[path.len() - 2].as_str();
        if h == "Self" { self_type } else { Some(h) }
    } else {
        self_type
    };
    if let Some(en) = enum_hint {
        for item in &env.items {
            if item.kind == ItemKind::Enum && item.ident == en {
                for v in &item.variants {
                    if v.name == var_name
                        && let VariantPayload::Struct(ref flds) = v.payload
                    {
                        return Some(flds.as_slice());
                    }
                }
            }
        }
    }
    if path.len() == 1 && var_name != "Self" && is_known_struct_name(env, var_name) {
        return None;
    }
    for item in &env.items {
        if item.kind == ItemKind::Enum {
            for v in &item.variants {
                if v.name == var_name
                    && let VariantPayload::Struct(ref flds) = v.payload
                {
                    return Some(flds.as_slice());
                }
            }
        }
    }
    None
}

fn is_known_struct_name(env: &TypeEnvironment, name: &str) -> bool {
    env.items
        .iter()
        .any(|i| i.kind == ItemKind::Struct && i.ident == name)
}

/// Expands top-level and nested `SpecrPat::Or` alternatives into flat patterns.
fn expand_or_pat(pat: &SpecrPat) -> Vec<SpecrPat> {
    match pat {
        SpecrPat::Or(alts) => alts.iter().flat_map(expand_or_pat).collect(),
        SpecrPat::Tuple(elems) => {
            let mut acc = vec![Vec::new()];
            for e in elems {
                let choices = expand_or_pat(e);
                let mut next = Vec::new();
                for prefix in &acc {
                    for c in &choices {
                        let mut p = prefix.clone();
                        p.push(c.clone());
                        next.push(p);
                    }
                }
                acc = next;
            }
            acc.into_iter().map(SpecrPat::Tuple).collect()
        }
        SpecrPat::TupleVariant { path, args } => {
            let mut acc = vec![Vec::new()];
            for a in args {
                let choices = expand_or_pat(a);
                let mut next = Vec::new();
                for prefix in &acc {
                    for c in &choices {
                        let mut p = prefix.clone();
                        p.push(c.clone());
                        next.push(p);
                    }
                }
                acc = next;
            }
            acc.into_iter()
                .map(|a| SpecrPat::TupleVariant {
                    path: path.clone(),
                    args: a,
                })
                .collect()
        }
        other => vec![other.clone()],
    }
}

fn lower_pat_to_lean(pat: &SpecrPat, env: &TypeEnvironment, self_type: Option<&str>) -> String {
    match pat {
        SpecrPat::Wildcard => "_".to_string(),
        SpecrPat::Bind { name, .. } => escape_lean_ident(name),
        SpecrPat::Lit(SpecrLit::Unit) => "()".to_string(),
        SpecrPat::Lit(SpecrLit::Bool(b)) => b.to_string(),
        SpecrPat::Lit(SpecrLit::Int(n)) => {
            if *n < 0 {
                format!("({n})")
            } else {
                n.to_string()
            }
        }
        SpecrPat::Lit(SpecrLit::Str(s)) => format!("\"{s}\""),
        SpecrPat::Tuple(elems) => {
            let inner: Vec<String> = elems
                .iter()
                .map(|e| lower_pat_to_lean(e, env, self_type))
                .collect();
            format!("({})", inner.join(", "))
        }
        SpecrPat::Path(segs) => {
            let last = segs.last().map(String::as_str).unwrap_or("_");
            match last {
                "None" => "none".to_string(),
                "Ok" => ".ok".to_string(),
                "Err" => ".error".to_string(),
                other => format!(".{}", escape_lean_ident(other)),
            }
        }
        SpecrPat::TupleVariant { path, args } => {
            let last = path.last().map(String::as_str).unwrap_or("mk");
            let rendered_args: Vec<String> = args
                .iter()
                .map(|a| lower_pat_to_lean(a, env, self_type))
                .collect();
            match last {
                "Some" if rendered_args.len() == 1 => format!("(some {})", rendered_args[0]),
                "Ok" if rendered_args.len() == 1 => format!("(.ok {})", rendered_args[0]),
                "Err" if rendered_args.len() == 1 => format!("(.error {})", rendered_args[0]),
                other => {
                    if rendered_args.is_empty() {
                        format!(".{}", escape_lean_ident(other))
                    } else {
                        format!(
                            "(.{} {})",
                            escape_lean_ident(other),
                            rendered_args.join(" ")
                        )
                    }
                }
            }
        }
        SpecrPat::StructVariant { path, fields, .. } => {
            let last = path.last().map(String::as_str).unwrap_or("mk");
            let resolved_last = if last == "Self" {
                self_type.unwrap_or("Self")
            } else {
                last
            };
            if let Some(decl_fields) = lookup_struct_variant_fields(env, path, self_type) {
                let mut positional = Vec::with_capacity(decl_fields.len());
                for df in decl_fields {
                    if let Some((_, fpat)) = fields.iter().find(|(n, _)| n == &df.name) {
                        positional.push(lower_pat_to_lean(fpat, env, self_type));
                    } else {
                        positional.push("_".to_string());
                    }
                }
                if positional.is_empty() {
                    format!(".{}", escape_lean_ident(resolved_last))
                } else {
                    format!(
                        "(.{} {})",
                        escape_lean_ident(resolved_last),
                        positional.join(" ")
                    )
                }
            } else if path.len() == 1 && is_known_struct_name(env, resolved_last) {
                let f_assigns: Vec<String> = fields
                    .iter()
                    .map(|(fname, fpat)| {
                        format!(
                            "{} := {}",
                            escape_lean_ident(fname),
                            lower_pat_to_lean(fpat, env, self_type)
                        )
                    })
                    .collect();
                format!("{{ {} }}", f_assigns.join(", "))
            } else {
                let positional: Vec<String> = fields
                    .iter()
                    .map(|(_, fpat)| lower_pat_to_lean(fpat, env, self_type))
                    .collect();
                if positional.is_empty() {
                    format!(".{}", escape_lean_ident(resolved_last))
                } else {
                    format!(
                        "(.{} {})",
                        escape_lean_ident(resolved_last),
                        positional.join(" ")
                    )
                }
            }
        }
        SpecrPat::Or(alts) => alts
            .first()
            .map(|a| lower_pat_to_lean(a, env, self_type))
            .unwrap_or_else(|| "_".to_string()),
    }
}

struct LowerCtx<'a> {
    env: &'a TypeEnvironment,
    self_type: Option<&'a str>,
    effect: EffectLevel,
}

fn stmt_always_exits(stmt: &SpecrStmt) -> bool {
    match stmt {
        SpecrStmt::Expr { expr, .. } => expr_always_exits(expr),
        _ => false,
    }
}

fn expr_always_exits(expr: &SpecrExpr) -> bool {
    match expr {
        SpecrExpr::Return(_)
        | SpecrExpr::ThrowUb { .. }
        | SpecrExpr::ThrowIllFormed { .. }
        | SpecrExpr::ThrowMachineStop => true,
        SpecrExpr::Call { func, .. } => {
            if let SpecrExpr::Path(segs) = func.as_ref() {
                matches!(
                    segs.last().map(String::as_str),
                    Some("throw_ub" | "throw_ill_formed" | "throw_machine_stop" | "ret")
                )
            } else {
                false
            }
        }
        SpecrExpr::Block(stmts) => stmts.last().is_some_and(stmt_always_exits),
        SpecrExpr::If {
            then_branch,
            else_branch: Some(eb),
            ..
        } => then_branch.last().is_some_and(stmt_always_exits) && expr_always_exits(eb),
        SpecrExpr::Match { arms, .. } => {
            !arms.is_empty()
                && arms
                    .iter()
                    .all(|a| a.guard.is_none() && expr_always_exits(&a.body))
        }
        _ => false,
    }
}

fn stmt_has_early_exit(stmt: &SpecrStmt) -> bool {
    match stmt {
        SpecrStmt::Expr { expr, .. } => expr_has_early_exit(expr),
        _ => false,
    }
}

fn expr_has_early_exit(expr: &SpecrExpr) -> bool {
    if expr_always_exits(expr) {
        return true;
    }
    match expr {
        SpecrExpr::Block(stmts) => stmts.iter().any(stmt_has_early_exit),
        SpecrExpr::If {
            then_branch,
            else_branch,
            ..
        } => {
            then_branch.iter().any(stmt_has_early_exit)
                || else_branch
                    .as_ref()
                    .is_some_and(|eb| expr_has_early_exit(eb))
        }
        SpecrExpr::Match { arms, .. } => arms.iter().any(|a| expr_has_early_exit(&a.body)),
        _ => false,
    }
}

fn splice_continuation_into_stmts(stmts: &[SpecrStmt], rest: &[SpecrStmt]) -> Vec<SpecrStmt> {
    if stmts.last().is_some_and(stmt_always_exits) {
        return stmts.to_vec();
    }
    if let Some((last, prefix)) = stmts.split_last()
        && let SpecrStmt::Expr { expr, .. } = last
        && matches!(
            expr,
            SpecrExpr::If { .. } | SpecrExpr::Match { .. } | SpecrExpr::Block(_)
        )
        && expr_has_early_exit(expr)
    {
        let mut out = prefix.to_vec();
        out.push(SpecrStmt::Expr {
            expr: splice_continuation_into_expr(expr, rest),
            has_semi: false,
        });
        return out;
    }
    let mut out = stmts.to_vec();
    out.extend_from_slice(rest);
    out
}

fn splice_continuation_into_expr(expr: &SpecrExpr, rest: &[SpecrStmt]) -> SpecrExpr {
    if expr_always_exits(expr) {
        return expr.clone();
    }
    match expr {
        SpecrExpr::Block(stmts) => SpecrExpr::Block(splice_continuation_into_stmts(stmts, rest)),
        SpecrExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let new_then = splice_continuation_into_stmts(then_branch, rest);
            let new_else = match else_branch {
                Some(eb) => Box::new(splice_continuation_into_expr(eb, rest)),
                None => Box::new(SpecrExpr::Block(rest.to_vec())),
            };
            SpecrExpr::If {
                cond: cond.clone(),
                then_branch: new_then,
                else_branch: Some(new_else),
            }
        }
        SpecrExpr::Match { scrutinee, arms } => {
            let new_arms = arms
                .iter()
                .map(|a| SpecrMatchArm {
                    pat: a.pat.clone(),
                    guard: a.guard.clone(),
                    body: splice_continuation_into_expr(&a.body, rest),
                })
                .collect();
            SpecrExpr::Match {
                scrutinee: scrutinee.clone(),
                arms: new_arms,
            }
        }
        other => {
            let mut stmts = vec![SpecrStmt::Expr {
                expr: other.clone(),
                has_semi: true,
            }];
            stmts.extend_from_slice(rest);
            SpecrExpr::Block(stmts)
        }
    }
}

fn push_ret_into_stmts(stmts: &[SpecrStmt], wrapper: &str) -> Vec<SpecrStmt> {
    let Some((last, prefix)) = stmts.split_last() else {
        return vec![SpecrStmt::Expr {
            expr: SpecrExpr::Call {
                func: Box::new(SpecrExpr::Path(vec![wrapper.to_string()])),
                args: vec![SpecrExpr::Lit(SpecrLit::Unit)],
            },
            has_semi: false,
        }];
    };
    let mut out = prefix.to_vec();
    match last {
        SpecrStmt::Expr {
            expr,
            has_semi: false,
        } => {
            out.push(SpecrStmt::Expr {
                expr: push_ret_into_expr(expr, wrapper),
                has_semi: false,
            });
        }
        other => {
            out.push(other.clone());
            out.push(SpecrStmt::Expr {
                expr: SpecrExpr::Call {
                    func: Box::new(SpecrExpr::Path(vec![wrapper.to_string()])),
                    args: vec![SpecrExpr::Lit(SpecrLit::Unit)],
                },
                has_semi: false,
            });
        }
    }
    out
}

fn push_ret_into_expr(expr: &SpecrExpr, wrapper: &str) -> SpecrExpr {
    if expr_always_exits(expr) {
        return expr.clone();
    }
    match expr {
        SpecrExpr::Try(inner) if wrapper == "ret" => (**inner).clone(),
        SpecrExpr::Block(stmts) => SpecrExpr::Block(push_ret_into_stmts(stmts, wrapper)),
        SpecrExpr::If {
            cond,
            then_branch,
            else_branch,
        } => SpecrExpr::If {
            cond: cond.clone(),
            then_branch: push_ret_into_stmts(then_branch, wrapper),
            else_branch: else_branch
                .as_ref()
                .map(|eb| Box::new(push_ret_into_expr(eb, wrapper))),
        },
        SpecrExpr::Match { scrutinee, arms } => SpecrExpr::Match {
            scrutinee: scrutinee.clone(),
            arms: arms
                .iter()
                .map(|a| SpecrMatchArm {
                    pat: a.pat.clone(),
                    guard: a.guard.clone(),
                    body: push_ret_into_expr(&a.body, wrapper),
                })
                .collect(),
        },
        other => SpecrExpr::Call {
            func: Box::new(SpecrExpr::Path(vec![wrapper.to_string()])),
            args: vec![other.clone()],
        },
    }
}

fn format_interpolated_msg(
    msg: &str,
    args: &[SpecrExpr],
    ctx: &LowerCtx,
) -> Result<String, String> {
    if args.is_empty() || !msg.contains("{}") {
        let escaped = msg.replace('\\', "\\\\").replace('"', "\\\"");
        return Ok(format!("\"{escaped}\""));
    }
    let parts: Vec<&str> = msg.split("{}").collect();
    let mut pieces = Vec::new();
    for (idx, part) in parts.iter().enumerate() {
        if !part.is_empty() {
            let escaped = part.replace('\\', "\\\\").replace('"', "\\\"");
            pieces.push(format!("\"{escaped}\""));
        }
        if let Some(arg) = args.get(idx) {
            let arg_lean = lower_expr_to_lean(arg, ctx, 0)?;
            pieces.push(arg_lean);
        }
    }
    if pieces.is_empty() {
        Ok("\"\"".to_string())
    } else if pieces.len() == 1 {
        Ok(pieces.remove(0))
    } else {
        Ok(format!("({})", pieces.join(" ++ ")))
    }
}

fn lower_binop_to_lean(
    op: SpecrBinOp,
    lhs: &SpecrExpr,
    rhs: &SpecrExpr,
    ctx: &LowerCtx,
    indent: usize,
) -> Result<String, String> {
    let l = lower_expr_to_lean(lhs, ctx, indent)?;
    let r = lower_expr_to_lean(rhs, ctx, indent)?;
    Ok(match op {
        SpecrBinOp::Add => format!("({l} + {r})"),
        SpecrBinOp::Sub => format!("({l} - {r})"),
        SpecrBinOp::Mul => format!("({l} * {r})"),
        SpecrBinOp::Div => format!("(Int.tdiv {l} {r})"),
        SpecrBinOp::Rem => format!("(Int.tmod {l} {r})"),
        SpecrBinOp::BitAnd => {
            format!(
                "(Int.ofNat (Nat.land (Int.toNat ({l} : SpecrInt)) (Int.toNat ({r} : SpecrInt))))"
            )
        }
        SpecrBinOp::BitOr => {
            format!(
                "(Int.ofNat (Nat.lor (Int.toNat ({l} : SpecrInt)) (Int.toNat ({r} : SpecrInt))))"
            )
        }
        SpecrBinOp::BitXor => {
            format!(
                "(Int.ofNat (Nat.xor (Int.toNat ({l} : SpecrInt)) (Int.toNat ({r} : SpecrInt))))"
            )
        }
        SpecrBinOp::Shl => {
            format!("(({l} : SpecrInt) * Int.ofNat (2 ^ Int.toNat ({r} : SpecrInt)))")
        }
        SpecrBinOp::Shr => {
            format!("(Int.fdiv ({l} : SpecrInt) (Int.ofNat (2 ^ Int.toNat ({r} : SpecrInt))))")
        }
        SpecrBinOp::Eq => format!("({l} == {r})"),
        SpecrBinOp::Ne => format!("({l} != {r})"),
        SpecrBinOp::Lt => format!("(decide ({l} < {r}))"),
        SpecrBinOp::Le => format!("(decide ({l} ≤ {r}))"),
        SpecrBinOp::Gt => format!("(decide ({l} > {r}))"),
        SpecrBinOp::Ge => format!("(decide ({l} ≥ {r}))"),
        SpecrBinOp::And => format!("({l} && {r})"),
        SpecrBinOp::Or => format!("({l} || {r})"),
    })
}

fn lower_stmts_to_lean(
    stmts: &[SpecrStmt],
    ctx: &LowerCtx,
    indent: usize,
) -> Result<String, String> {
    let pad = " ".repeat(indent);
    if stmts.is_empty() {
        return Ok(match ctx.effect {
            EffectLevel::FallibleResult => "(.ok ())".to_string(),
            EffectLevel::OptionEffect => "none".to_string(),
            EffectLevel::NondetResult => "(NdComp.pure ())".to_string(),
            EffectLevel::Pure => "()".to_string(),
        });
    }
    let first = &stmts[0];
    let rest = &stmts[1..];
    if rest.is_empty() {
        return match first {
            SpecrStmt::Expr { expr, has_semi } => {
                if *has_semi && let SpecrExpr::Try(inner) = expr {
                    let rhs_lean = lower_expr_to_lean(inner, ctx, indent)?;
                    return Ok(match ctx.effect {
                        EffectLevel::OptionEffect => format!(
                            "match {rhs_lean} with\n{pad}| none => none\n{pad}| some _ => some ()"
                        ),
                        _ => format!(
                            "match {rhs_lean} with\n{pad}| .error e => .error e\n{pad}| .ok _ => (.ok ())"
                        ),
                    });
                }
                lower_expr_to_lean(expr, ctx, indent)
            }
            SpecrStmt::Let { pat, init, .. } => {
                let pat_lean = lower_pat_to_lean(pat, ctx.env, ctx.self_type);
                let init_lean = lower_expr_to_lean(init, ctx, indent)?;
                Ok(format!("let {pat_lean} := {init_lean}\n{pad}()"))
            }
            SpecrStmt::Assign { lhs, op, rhs } => {
                let lhs_lean = lower_expr_to_lean(lhs, ctx, indent)?;
                let rhs_lean = match op {
                    Some(bop) => lower_binop_to_lean(*bop, lhs, rhs, ctx, indent)?,
                    None => lower_expr_to_lean(rhs, ctx, indent)?,
                };
                Ok(format!("let {lhs_lean} := {rhs_lean}\n{pad}()"))
            }
        };
    }

    let rest_lean = lower_stmts_to_lean(rest, ctx, indent)?;
    match first {
        SpecrStmt::Let { pat, init, .. } => {
            let pat_lean = lower_pat_to_lean(pat, ctx.env, ctx.self_type);
            if let SpecrExpr::Try(inner) = init {
                let rhs_lean = lower_expr_to_lean(inner, ctx, indent)?;
                let rest_indented = lower_stmts_to_lean(rest, ctx, indent + 2)?;
                let pad2 = " ".repeat(indent + 2);
                return Ok(match ctx.effect {
                    EffectLevel::OptionEffect => format!(
                        "match {rhs_lean} with\n{pad}| none => none\n{pad}| some {pat_lean} =>\n{pad2}{rest_indented}"
                    ),
                    _ => format!(
                        "match {rhs_lean} with\n{pad}| .error e => .error e\n{pad}| .ok {pat_lean} =>\n{pad2}{rest_indented}"
                    ),
                });
            }
            let init_lean = lower_expr_to_lean(init, ctx, indent)?;
            if matches!(
                pat,
                SpecrPat::TupleVariant { .. } | SpecrPat::StructVariant { .. }
            ) {
                let rest_indented = lower_stmts_to_lean(rest, ctx, indent + 2)?;
                let pad2 = " ".repeat(indent + 2);
                Ok(format!(
                    "match {init_lean} with\n{pad}| {pat_lean} =>\n{pad2}{rest_indented}"
                ))
            } else {
                Ok(format!("let {pat_lean} := {init_lean}\n{pad}{rest_lean}"))
            }
        }
        SpecrStmt::Assign { lhs, op, rhs } => {
            let lhs_lean = lower_expr_to_lean(lhs, ctx, indent)?;
            let rhs_lean = match op {
                Some(bop) => lower_binop_to_lean(*bop, lhs, rhs, ctx, indent)?,
                None => lower_expr_to_lean(rhs, ctx, indent)?,
            };
            Ok(format!("let {lhs_lean} := {rhs_lean}\n{pad}{rest_lean}"))
        }
        SpecrStmt::Expr { expr, .. } => {
            if let SpecrExpr::Try(inner) = expr {
                let rhs_lean = lower_expr_to_lean(inner, ctx, indent)?;
                let rest_indented = lower_stmts_to_lean(rest, ctx, indent + 2)?;
                let pad2 = " ".repeat(indent + 2);
                return Ok(match ctx.effect {
                    EffectLevel::OptionEffect => format!(
                        "match {rhs_lean} with\n{pad}| none => none\n{pad}| some _ =>\n{pad2}{rest_indented}"
                    ),
                    _ => format!(
                        "match {rhs_lean} with\n{pad}| .error e => .error e\n{pad}| .ok _ =>\n{pad2}{rest_indented}"
                    ),
                });
            }
            if matches!(
                expr,
                SpecrExpr::If { .. } | SpecrExpr::Match { .. } | SpecrExpr::Block(_)
            ) && expr_has_early_exit(expr)
            {
                let spliced = splice_continuation_into_expr(expr, rest);
                return lower_expr_to_lean(&spliced, ctx, indent);
            }
            if let SpecrExpr::If {
                cond,
                then_branch,
                else_branch: None,
            } = expr
                && then_branch.len() == 1
                && let SpecrStmt::Assign { lhs, op, rhs } = &then_branch[0]
            {
                let cond_lean = lower_expr_to_lean(cond, ctx, indent)?;
                let lhs_lean = lower_expr_to_lean(lhs, ctx, indent)?;
                let upd_lean = match op {
                    Some(bop) => lower_binop_to_lean(*bop, lhs, rhs, ctx, indent)?,
                    None => lower_expr_to_lean(rhs, ctx, indent)?,
                };
                return Ok(format!(
                    "let {lhs_lean} := if {cond_lean} then {upd_lean} else {lhs_lean}\n{pad}{rest_lean}"
                ));
            }
            let e_lean = lower_expr_to_lean(expr, ctx, indent)?;
            Ok(format!("let _ := {e_lean}\n{pad}{rest_lean}"))
        }
    }
}

fn lower_expr_to_lean(expr: &SpecrExpr, ctx: &LowerCtx, indent: usize) -> Result<String, String> {
    let pad = " ".repeat(indent);
    match expr {
        SpecrExpr::Lit(SpecrLit::Unit) => Ok("()".to_string()),
        SpecrExpr::Lit(SpecrLit::Bool(b)) => Ok(b.to_string()),
        SpecrExpr::Lit(SpecrLit::Int(n)) => Ok(if *n < 0 {
            format!("({n})")
        } else {
            n.to_string()
        }),
        SpecrExpr::Lit(SpecrLit::Str(s)) => {
            let esc = s.replace('\\', "\\\\").replace('"', "\\\"");
            Ok(format!("\"{esc}\""))
        }
        SpecrExpr::Path(segs) => {
            if segs.is_empty() {
                return Ok("()".to_string());
            }
            if segs.len() == 1 {
                let name = segs[0].as_str();
                return Ok(match name {
                    "None" => "none".to_string(),
                    "true" | "false" => name.to_string(),
                    other if other.starts_with(|c: char| c.is_ascii_uppercase()) => {
                        format!(".{}", escape_lean_ident(other))
                    }
                    other => escape_lean_ident(other),
                });
            }
            let prev = segs[segs.len() - 2].as_str();
            let last = segs[segs.len() - 1].as_str();
            if last == "None" {
                return Ok("none".to_string());
            }
            let resolved_prev = if prev == "Self" {
                ctx.self_type.unwrap_or("Self")
            } else {
                prev
            };
            if last.starts_with(|c: char| c.is_ascii_uppercase()) {
                Ok(format!(
                    "{}.{}",
                    escape_lean_ident(resolved_prev),
                    escape_lean_ident(last)
                ))
            } else {
                Ok(format!(
                    "{}_{}",
                    escape_lean_ident(resolved_prev),
                    escape_lean_ident(last)
                ))
            }
        }
        SpecrExpr::Tuple(elems) => {
            let mut rendered = Vec::with_capacity(elems.len());
            for e in elems {
                rendered.push(lower_expr_to_lean(e, ctx, indent)?);
            }
            Ok(format!("({})", rendered.join(", ")))
        }
        SpecrExpr::StructLit {
            path,
            fields,
            spread,
        } => {
            if let Some(decl_fields) = lookup_struct_variant_fields(ctx.env, path, ctx.self_type) {
                let vname = escape_lean_ident(path.last().map(String::as_str).unwrap_or("mk"));
                let mut args = Vec::with_capacity(decl_fields.len());
                for df in decl_fields {
                    if let Some((_, fexpr)) = fields.iter().find(|(n, _)| n == &df.name) {
                        args.push(lower_expr_to_lean(fexpr, ctx, indent)?);
                    } else if let Some(sp) = spread {
                        let sp_lean = lower_expr_to_lean(sp, ctx, indent)?;
                        args.push(format!("{sp_lean}.{}", escape_lean_ident(&df.name)));
                    } else {
                        args.push("default".to_string());
                    }
                }
                if args.is_empty() {
                    return Ok(format!(".{vname}"));
                }
                return Ok(format!("(.{vname} {})", args.join(" ")));
            }
            let mut assigns = Vec::with_capacity(fields.len());
            for (fname, fexpr) in fields {
                let fe = lower_expr_to_lean(fexpr, ctx, indent)?;
                assigns.push(format!("{} := {fe}", escape_lean_ident(fname)));
            }
            if let Some(sp) = spread {
                let sp_lean = lower_expr_to_lean(sp, ctx, indent)?;
                if assigns.is_empty() {
                    Ok(sp_lean)
                } else {
                    Ok(format!("{{ {sp_lean} with {} }}", assigns.join(", ")))
                }
            } else {
                Ok(format!("{{ {} }}", assigns.join(", ")))
            }
        }
        SpecrExpr::Field { base, field } => {
            let b = lower_expr_to_lean(base, ctx, indent)?;
            Ok(format!("{b}.{}", escape_lean_ident(field)))
        }
        SpecrExpr::TupleIndex { base, index } => {
            let b = lower_expr_to_lean(base, ctx, indent)?;
            if *index == 0 {
                Ok(format!("{b}.1"))
            } else {
                Ok(format!("{b}{}.1", ".2".repeat(*index)))
            }
        }
        SpecrExpr::Unary { op, expr: inner } => {
            let e = lower_expr_to_lean(inner, ctx, indent)?;
            Ok(match op {
                SpecrUnOp::Not => format!("(!{e})"),
                SpecrUnOp::Neg => format!("(-{e})"),
                SpecrUnOp::Deref | SpecrUnOp::Ref | SpecrUnOp::RefMut => e,
            })
        }
        SpecrExpr::Binary { op, lhs, rhs } => lower_binop_to_lean(*op, lhs, rhs, ctx, indent),
        SpecrExpr::Range {
            start,
            end,
            inclusive,
        } => {
            let a = lower_expr_to_lean(start, ctx, indent)?;
            let b = lower_expr_to_lean(end, ctx, indent)?;
            if *inclusive {
                Ok(format!(
                    "((List.range (Int.toNat (({b} : SpecrInt) + 1 - ({a} : SpecrInt)))).map (fun i => ({a} : SpecrInt) + Int.ofNat i))"
                ))
            } else {
                Ok(format!(
                    "((List.range (Int.toNat (({b} : SpecrInt) - ({a} : SpecrInt)))).map (fun i => ({a} : SpecrInt) + Int.ofNat i))"
                ))
            }
        }
        SpecrExpr::Try(inner) => lower_expr_to_lean(inner, ctx, indent),
        SpecrExpr::Return(opt) => match opt {
            Some(inner) => lower_expr_to_lean(inner, ctx, indent),
            None => Ok(match ctx.effect {
                EffectLevel::FallibleResult => "(.ok ())".to_string(),
                _ => "()".to_string(),
            }),
        },
        SpecrExpr::ThrowUb { msg, args } => {
            let m = format_interpolated_msg(msg, args, ctx)?;
            Ok(if ctx.effect == EffectLevel::NondetResult {
                format!("(NdComp.fail (.ub {m}))")
            } else {
                format!("(.error (.ub {m}))")
            })
        }
        SpecrExpr::ThrowIllFormed { msg, args } => {
            let m = format_interpolated_msg(msg, args, ctx)?;
            Ok(if ctx.effect == EffectLevel::NondetResult {
                format!("(NdComp.fail (.illFormed {m}))")
            } else {
                format!("(.error (.illFormed {m}))")
            })
        }
        SpecrExpr::ThrowMachineStop => Ok(if ctx.effect == EffectLevel::NondetResult {
            "(NdComp.fail .machineStop)".to_string()
        } else {
            "(.error .machineStop)".to_string()
        }),
        SpecrExpr::Matches { expr: scrut, pat } => {
            let s_lean = lower_expr_to_lean(scrut, ctx, indent)?;
            let alts = expand_or_pat(pat);
            let mut arms_str = String::new();
            for alt in &alts {
                let p_lean = lower_pat_to_lean(alt, ctx.env, ctx.self_type);
                arms_str.push_str(&format!(" | {p_lean} => true"));
            }
            Ok(format!("(match {s_lean} with{arms_str} | _ => false)"))
        }
        SpecrExpr::Closure { params, body } => {
            let b_lean = lower_expr_to_lean(body, ctx, indent)?;
            if params.is_empty() {
                Ok(format!("(fun _ => {b_lean})"))
            } else {
                let ps: Vec<String> = params.iter().map(|p| escape_lean_ident(p)).collect();
                Ok(format!("(fun {} => {b_lean})", ps.join(" ")))
            }
        }
        SpecrExpr::Block(stmts) => lower_stmts_to_lean(stmts, ctx, indent),
        SpecrExpr::If {
            cond,
            then_branch,
            else_branch,
        } => lower_if_to_lean(cond, then_branch, else_branch.as_deref(), ctx, indent, &pad),
        SpecrExpr::Match { scrutinee, arms } => {
            lower_match_to_lean(scrutinee, arms, ctx, indent, &pad)
        }
        SpecrExpr::Call { func, args } => lower_call_to_lean(func, args, ctx, indent),
        SpecrExpr::MethodCall {
            receiver,
            method,
            args,
        } => lower_method_call_to_lean(receiver, method, args, ctx, indent),
    }
}

fn lower_if_to_lean(
    cond: &SpecrExpr,
    then_branch: &[SpecrStmt],
    else_branch: Option<&SpecrExpr>,
    ctx: &LowerCtx,
    indent: usize,
    pad: &str,
) -> Result<String, String> {
    let cond_lean = lower_expr_to_lean(cond, ctx, indent)?;
    let pad2 = " ".repeat(indent + 2);
    let then_lean = lower_stmts_to_lean(then_branch, ctx, indent + 2)?;
    let else_lean = match else_branch {
        Some(eb) => lower_expr_to_lean(eb, ctx, indent + 2)?,
        None => match ctx.effect {
            EffectLevel::FallibleResult => "(.ok ())".to_string(),
            EffectLevel::OptionEffect => "none".to_string(),
            EffectLevel::NondetResult => "(NdComp.pure ())".to_string(),
            EffectLevel::Pure => "()".to_string(),
        },
    };
    Ok(format!(
        "if {cond_lean} then\n{pad2}{then_lean}\n{pad}else\n{pad2}{else_lean}"
    ))
}

fn lower_match_to_lean(
    scrutinee: &SpecrExpr,
    arms: &[SpecrMatchArm],
    ctx: &LowerCtx,
    indent: usize,
    pad: &str,
) -> Result<String, String> {
    let scrut_lean = lower_expr_to_lean(scrutinee, ctx, indent)?;
    let mut flat_arms: Vec<(SpecrPat, Option<&SpecrExpr>, &SpecrExpr)> = Vec::new();
    for arm in arms {
        for p in expand_or_pat(&arm.pat) {
            flat_arms.push((p, arm.guard.as_ref(), &arm.body));
        }
    }
    let has_any_guard = flat_arms.iter().any(|(_, g, _)| g.is_some());
    if !has_any_guard {
        let mut out = format!("match {scrut_lean} with");
        for (pat, _, body) in &flat_arms {
            let pat_lean = lower_pat_to_lean(pat, ctx.env, ctx.self_type);
            let body_lean = lower_expr_to_lean(body, ctx, indent + 2)?;
            out.push_str(&format!("\n{pad}| {pat_lean} => {body_lean}"));
        }
        return Ok(out);
    }

    let mut suffix_start = flat_arms.len();
    while suffix_start > 0 && flat_arms[suffix_start - 1].1.is_none() {
        suffix_start -= 1;
    }
    let mut acc = if suffix_start < flat_arms.len() {
        if flat_arms.len() - suffix_start == 1
            && matches!(flat_arms[suffix_start].0, SpecrPat::Wildcard)
        {
            lower_expr_to_lean(flat_arms[suffix_start].2, ctx, indent + 2)?
        } else {
            let mut m = "match __scrut with".to_string();
            let mut has_catchall = false;
            for (pat, _, body) in &flat_arms[suffix_start..] {
                if matches!(pat, SpecrPat::Wildcard | SpecrPat::Bind { .. }) {
                    has_catchall = true;
                }
                let pat_lean = lower_pat_to_lean(pat, ctx.env, ctx.self_type);
                let body_lean = lower_expr_to_lean(body, ctx, indent + 2)?;
                m.push_str(&format!("\n{pad}| {pat_lean} => {body_lean}"));
            }
            if suffix_start > 0 && !has_catchall {
                m.push_str(&format!("\n{pad}| _ => default"));
            }
            format!("({m})")
        }
    } else {
        "default".to_string()
    };

    for idx in (0..suffix_start).rev() {
        let (pat, guard_opt, body) = &flat_arms[idx];
        let body_lean = lower_expr_to_lean(body, ctx, indent + 2)?;
        let guarded = if let Some(g) = guard_opt {
            let g_lean = lower_expr_to_lean(g, ctx, indent + 2)?;
            format!("if {g_lean} then {body_lean} else {acc}")
        } else {
            body_lean
        };
        if matches!(pat, SpecrPat::Wildcard) {
            acc = guarded;
        } else if let SpecrPat::Bind { name, .. } = pat {
            acc = format!(
                "(let {} := __scrut\n{pad}{guarded})",
                escape_lean_ident(name)
            );
        } else {
            let pat_lean = lower_pat_to_lean(pat, ctx.env, ctx.self_type);
            acc =
                format!("(match __scrut with\n{pad}| {pat_lean} => {guarded}\n{pad}| _ => {acc})");
        }
    }
    Ok(format!("let __scrut := {scrut_lean}\n{pad}{acc}"))
}

fn lower_call_to_lean(
    func: &SpecrExpr,
    args: &[SpecrExpr],
    ctx: &LowerCtx,
    indent: usize,
) -> Result<String, String> {
    if let SpecrExpr::Path(segs) = func {
        let last = segs.last().map(String::as_str).unwrap_or("");
        if matches!(last, "ret" | "Ok")
            && let Some(arg0) = args.first()
            && (matches!(
                arg0,
                SpecrExpr::Match { .. }
                    | SpecrExpr::If { .. }
                    | SpecrExpr::Block(_)
                    | SpecrExpr::Try(_)
            ) || expr_always_exits(arg0))
        {
            return lower_expr_to_lean(&push_ret_into_expr(arg0, last), ctx, indent);
        }
    }
    let mut r_args = Vec::with_capacity(args.len());
    for a in args {
        r_args.push(lower_expr_to_lean(a, ctx, indent)?);
    }
    if let SpecrExpr::Path(segs) = func {
        let last = segs.last().map(String::as_str).unwrap_or("");
        match last {
            "ret" | "Ok" => {
                let val = r_args.first().map(String::as_str).unwrap_or("()");
                return Ok(
                    if ctx.effect == EffectLevel::NondetResult && last == "ret" {
                        format!("(NdComp.pure {val})")
                    } else {
                        format!("(.ok {val})")
                    },
                );
            }
            "Err" => {
                let val = r_args.first().map(String::as_str).unwrap_or("()");
                return Ok(format!("(.error {val})"));
            }
            "Some" => {
                let val = r_args.first().map(String::as_str).unwrap_or("()");
                return Ok(format!("(some {val})"));
            }
            "int" if r_args.len() == 1 => return Ok(r_args[0].clone()),
            "bool_to_int" if r_args.len() == 1 => {
                return Ok(format!("(if {} then (1 : SpecrInt) else 0)", r_args[0]));
            }
            "list" => return Ok(format!("[{}]", r_args.join(", "))),
            _ if segs.len() == 2 => {
                let prefix = if segs[0] == "Self" {
                    ctx.self_type.unwrap_or("Self")
                } else {
                    segs[0].as_str()
                };
                if matches!(
                    (prefix, last),
                    ("Size", "from_bytes" | "from_bits" | "from_bytes_const")
                        | ("Offset", "from_bytes")
                        | ("Align", "from_bytes" | "from_bits")
                ) {
                    let method = if last == "from_bytes_const" {
                        "from_bytes"
                    } else {
                        last
                    };
                    if r_args.is_empty() {
                        return Ok(format!("({prefix}.{method} ())"));
                    }
                    return Ok(format!("({prefix}.{method} {})", r_args.join(" ")));
                }
            }
            _ => {}
        }
    }
    let f_lean = lower_expr_to_lean(func, ctx, indent)?;
    if r_args.is_empty() {
        Ok(format!("({f_lean} ())"))
    } else {
        Ok(format!("({f_lean} {})", r_args.join(" ")))
    }
}

fn lower_method_call_to_lean(
    receiver: &SpecrExpr,
    method: &str,
    args: &[SpecrExpr],
    ctx: &LowerCtx,
    indent: usize,
) -> Result<String, String> {
    let recv_lean = lower_expr_to_lean(receiver, ctx, indent)?;
    let mut r_args = Vec::with_capacity(args.len());
    for a in args {
        r_args.push(lower_expr_to_lean(a, ctx, indent)?);
    }
    match (method, r_args.len()) {
        ("bytes" | "bits" | "is_zero" | "size" | "align", 0) => {
            return Ok(format!("{recv_lean}.{method}"));
        }
        ("signed", 0) => return Ok(format!("({recv_lean} == .Signed)")),
        ("unsigned", 0) => return Ok(format!("({recv_lean} == .Unsigned)")),
        ("is_some", 0) => return Ok(format!("{recv_lean}.isSome")),
        ("is_none", 0) => return Ok(format!("{recv_lean}.isNone")),
        ("is_empty", 0) => return Ok(format!("{recv_lean}.isEmpty")),
        ("is_ok", 0) => {
            return Ok(format!(
                "(match {recv_lean} with | .ok _ => true | .error _ => false)"
            ));
        }
        ("is_err", 0) => {
            return Ok(format!(
                "(match {recv_lean} with | .ok _ => false | .error _ => true)"
            ));
        }
        ("len" | "count", 0) => return Ok(format!("(Int.ofNat {recv_lean}.length)")),
        ("abs", 0) => return Ok(format!("(Int.ofNat (Int.natAbs ({recv_lean} : SpecrInt)))")),
        (
            "into" | "clone" | "copied" | "iter" | "into_iter" | "by_ref" | "extract" | "as_ref",
            0,
        ) => {
            return Ok(recv_lean);
        }
        ("try_into" | "ok", 0) => return Ok(format!("(some {recv_lean})")),
        ("unwrap_or", 1) => return Ok(format!("({recv_lean}.getD {})", r_args[0])),
        ("contains" | "all" | "any" | "map" | "filter", 1) => {
            return Ok(format!("({recv_lean}.{method} {})", r_args[0]));
        }
        ("and_then", 1) => return Ok(format!("({recv_lean}.bind {})", r_args[0])),
        ("insert", 1) => return Ok(format!("({recv_lean}.insert {})", r_args[0])),
        ("insert", 2) => return Ok(format!("({recv_lean}.insert {} {})", r_args[0], r_args[1])),
        ("remove", 1) => return Ok(format!("({recv_lean}.erase {})", r_args[0])),
        ("get", 1) => return Ok(format!("({recv_lean}.find? {})", r_args[0])),
        ("pow", 1) => {
            return Ok(format!(
                "(({recv_lean} : SpecrInt) ^ Int.toNat ({} : SpecrInt))",
                r_args[0]
            ));
        }
        ("rem_euclid", 1) => return Ok(format!("(Int.emod {recv_lean} {})", r_args[0])),
        ("div_euclid", 1) => return Ok(format!("(Int.ediv {recv_lean} {})", r_args[0])),
        ("min", 1) => return Ok(format!("(min {recv_lean} {})", r_args[0])),
        ("max", 1) => return Ok(format!("(max {recv_lean} {})", r_args[0])),
        ("in_bounds", 2) => {
            return Ok(format!(
                "(in_bounds {recv_lean} {} {})",
                r_args[0], r_args[1]
            ));
        }
        _ => {}
    }

    if let SpecrExpr::Path(segs) = receiver
        && segs.len() == 1
        && segs[0] == "self"
        && let Some(st) = ctx.self_type
    {
        let fn_name = format!("{}.{}", escape_lean_ident(st), escape_lean_ident(method));
        if r_args.is_empty() {
            return Ok(format!("({fn_name} self)"));
        }
        return Ok(format!("({fn_name} self {})", r_args.join(" ")));
    }

    if r_args.is_empty() {
        Ok(format!("({recv_lean}.{})", escape_lean_ident(method)))
    } else {
        Ok(format!(
            "({recv_lean}.{} {})",
            escape_lean_ident(method),
            r_args.join(" ")
        ))
    }
}

/// Lowers a `specr lang` `fn` or `impl` method declaration into a Lean 4 `def`.
pub fn lower_specr_fn_to_lean(
    item: &SpecrItem,
    env: &TypeEnvironment,
    lean_name_override: Option<&str>,
) -> Result<String, String> {
    if !matches!(item.kind, ItemKind::Fn | ItemKind::ImplMethod) {
        return Err(format!("expected Fn or ImplMethod, got {:?}", item.kind));
    }
    let self_type = item.impl_target.as_deref();
    let lean_name = if let Some(ov) = lean_name_override {
        escape_lean_ident(ov)
    } else if let Some(st) = self_type {
        format!(
            "{}_{}",
            escape_lean_ident(st),
            escape_lean_ident(&item.ident)
        )
    } else {
        escape_lean_ident(&item.ident)
    };

    let mut param_sig = String::new();
    let mut preamble = String::new();
    if item.params.is_empty() {
        param_sig.push_str(" (_ : Unit)");
    } else {
        for (idx, p) in item.params.iter().enumerate() {
            if p.name == "self" {
                let st_lean = self_type
                    .map(escape_lean_ident)
                    .unwrap_or_else(|| "Unit".to_string());
                param_sig.push_str(&format!(" (self : {st_lean})"));
            } else {
                let clean_p = p.name.strip_prefix("mut ").unwrap_or(&p.name).trim();
                let mut p_ty = lower_specr_type_to_lean(&p.ty);
                if let Some(st) = self_type {
                    p_ty = p_ty.replace("Self", &escape_lean_ident(st));
                }
                if is_valid_ident(clean_p) {
                    param_sig.push_str(&format!(" ({} : {p_ty})", escape_lean_ident(clean_p)));
                } else {
                    let arg_tmp = format!("__arg_{idx}");
                    param_sig.push_str(&format!(" ({arg_tmp} : {p_ty})"));
                    let pat = parse_specr_pat(clean_p)?;
                    let pat_lean = lower_pat_to_lean(&pat, env, self_type);
                    preamble.push_str(&format!("let {pat_lean} := {arg_tmp}\n  "));
                }
            }
        }
    }

    let raw_ret = item.return_type.as_deref().unwrap_or("()");
    let mut ret_lean = lower_specr_type_to_lean(raw_ret);
    if let Some(st) = self_type {
        ret_lean = ret_lean.replace("Self", &escape_lean_ident(st));
    }

    let stmts = parse_specr_stmts(&item.body_canonical)?;
    let ctx = LowerCtx {
        env,
        self_type,
        effect: item.effect,
    };
    let body_lean = lower_stmts_to_lean(&stmts, &ctx, 2)?;
    let dot_alias = if lean_name_override.is_none()
        && let Some(st) = self_type
    {
        format!(
            "abbrev {}.{} := {lean_name}\n\n",
            escape_lean_ident(st),
            escape_lean_ident(&item.ident)
        )
    } else {
        String::new()
    };

    Ok(format!(
        "-- @specr-source: {}:{}..{} ({})\n-- @specr-body-sha256: {}\n@[reducible]\ndef {lean_name}{param_sig} : {ret_lean} :=\n  {preamble}{body_lean}\n\n{dot_alias}",
        item.span.rel_path,
        item.span.start_line,
        item.span.end_line,
        item.qualified_name,
        item.body_sha256
    ))
}

fn specr_type_is_closed(
    ty: &SpecrType,
    known_types: &BTreeSet<String>,
    self_name: Option<&str>,
) -> bool {
    match ty {
        SpecrType::Unit
        | SpecrType::Bool
        | SpecrType::U8
        | SpecrType::Nat
        | SpecrType::Int
        | SpecrType::String
        | SpecrType::Size
        | SpecrType::Offset
        | SpecrType::Align
        | SpecrType::Signedness
        | SpecrType::Endianness => true,
        SpecrType::Tuple(elems) => elems
            .iter()
            .all(|e| specr_type_is_closed(e, known_types, self_name)),
        SpecrType::Option(inner)
        | SpecrType::Result(inner)
        | SpecrType::NdResult(inner)
        | SpecrType::List(inner)
        | SpecrType::Set(inner) => specr_type_is_closed(inner, known_types, self_name),
        SpecrType::Map(k, v) => {
            specr_type_is_closed(k, known_types, self_name)
                && specr_type_is_closed(v, known_types, self_name)
        }
        SpecrType::Nominal(name) => {
            known_types.contains(name) || self_name.is_some_and(|s| s == name)
        }
    }
}

fn item_type_decl_is_closed(item: &SpecrItem, known_types: &BTreeSet<String>) -> bool {
    if !item.generics.is_empty() || item.is_mutually_recursive {
        return false;
    }
    let self_name = Some(item.ident.as_str());
    match item.kind {
        ItemKind::Enum => {
            if item.variants.is_empty() {
                return false;
            }
            for v in &item.variants {
                match &v.payload {
                    VariantPayload::Unit => {}
                    VariantPayload::Tuple(tys) => {
                        for t in tys {
                            if !specr_type_is_closed(&parse_specr_type(t), known_types, self_name) {
                                return false;
                            }
                        }
                    }
                    VariantPayload::Struct(flds) => {
                        for f in flds {
                            if !specr_type_is_closed(
                                &parse_specr_type(&f.ty),
                                known_types,
                                self_name,
                            ) {
                                return false;
                            }
                        }
                    }
                }
            }
            true
        }
        ItemKind::Struct => item
            .fields
            .iter()
            .all(|f| specr_type_is_closed(&parse_specr_type(&f.ty), known_types, self_name)),
        ItemKind::TypeAlias => item.aliased_type.as_ref().is_some_and(|aliased| {
            specr_type_is_closed(&parse_specr_type(aliased), known_types, None)
        }),
        _ => false,
    }
}

fn collect_pat_bindings(pat: &SpecrPat, locals: &mut BTreeSet<String>) {
    match pat {
        SpecrPat::Bind { name, .. } => {
            locals.insert(escape_lean_ident(name));
        }
        SpecrPat::Tuple(elems) | SpecrPat::Or(elems) => {
            for e in elems {
                collect_pat_bindings(e, locals);
            }
        }
        SpecrPat::TupleVariant { args, .. } => {
            for a in args {
                collect_pat_bindings(a, locals);
            }
        }
        SpecrPat::StructVariant { fields, .. } => {
            for (_, p) in fields {
                collect_pat_bindings(p, locals);
            }
        }
        SpecrPat::Wildcard | SpecrPat::Lit(_) | SpecrPat::Path(_) => {}
    }
}

fn expr_is_closed(
    expr: &SpecrExpr,
    locals: &BTreeSet<String>,
    known_types: &BTreeSet<String>,
    known_callables: &BTreeSet<String>,
    self_type: Option<&str>,
) -> bool {
    match expr {
        SpecrExpr::Lit(_) | SpecrExpr::ThrowMachineStop => true,
        SpecrExpr::Path(segs) => {
            if segs.is_empty() {
                return false;
            }
            if segs.len() == 1 {
                let s = segs[0].as_str();
                return s == "true"
                    || s == "false"
                    || s == "None"
                    || locals.contains(&escape_lean_ident(s))
                    || known_callables.contains(&escape_lean_ident(s))
                    || s.starts_with(|c: char| c.is_ascii_uppercase());
            }
            let prev = if segs[segs.len() - 2] == "Self" {
                self_type.unwrap_or("Self")
            } else {
                segs[segs.len() - 2].as_str()
            };
            let last = segs[segs.len() - 1].as_str();
            if last.starts_with(|c: char| c.is_ascii_uppercase()) {
                known_types.contains(&escape_lean_ident(prev))
            } else {
                let combined = format!("{}_{}", escape_lean_ident(prev), escape_lean_ident(last));
                known_callables.contains(&combined)
            }
        }
        SpecrExpr::Tuple(elems) => elems
            .iter()
            .all(|e| expr_is_closed(e, locals, known_types, known_callables, self_type)),
        SpecrExpr::StructLit {
            path,
            fields,
            spread,
        } => {
            let head = path.first().map(String::as_str).unwrap_or("");
            let resolved = if head == "Self" {
                self_type.unwrap_or("Self")
            } else {
                head
            };
            let ty_ok = known_types.contains(&escape_lean_ident(resolved))
                || self_type.is_some_and(|st| known_types.contains(&escape_lean_ident(st)));
            ty_ok
                && fields.iter().all(|(_, e)| {
                    expr_is_closed(e, locals, known_types, known_callables, self_type)
                })
                && spread.as_ref().is_none_or(|sp| {
                    expr_is_closed(sp, locals, known_types, known_callables, self_type)
                })
        }
        SpecrExpr::Field { base, .. }
        | SpecrExpr::TupleIndex { base, .. }
        | SpecrExpr::Unary { expr: base, .. }
        | SpecrExpr::Try(base) => {
            expr_is_closed(base, locals, known_types, known_callables, self_type)
        }
        SpecrExpr::Binary { lhs, rhs, .. }
        | SpecrExpr::Range {
            start: lhs,
            end: rhs,
            ..
        } => {
            expr_is_closed(lhs, locals, known_types, known_callables, self_type)
                && expr_is_closed(rhs, locals, known_types, known_callables, self_type)
        }
        SpecrExpr::Return(opt) => opt
            .as_ref()
            .is_none_or(|e| expr_is_closed(e, locals, known_types, known_callables, self_type)),
        SpecrExpr::ThrowUb { args, .. } | SpecrExpr::ThrowIllFormed { args, .. } => args
            .iter()
            .all(|a| expr_is_closed(a, locals, known_types, known_callables, self_type)),
        SpecrExpr::Matches { expr: inner, .. } => {
            expr_is_closed(inner, locals, known_types, known_callables, self_type)
        }
        SpecrExpr::Closure { params, body } => {
            let mut inner_locals = locals.clone();
            for p in params {
                inner_locals.insert(escape_lean_ident(p));
            }
            expr_is_closed(body, &inner_locals, known_types, known_callables, self_type)
        }
        SpecrExpr::Block(stmts) => {
            stmts_are_closed(stmts, locals, known_types, known_callables, self_type)
        }
        SpecrExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_is_closed(cond, locals, known_types, known_callables, self_type)
                && stmts_are_closed(then_branch, locals, known_types, known_callables, self_type)
                && else_branch.as_ref().is_none_or(|eb| {
                    expr_is_closed(eb, locals, known_types, known_callables, self_type)
                })
        }
        SpecrExpr::Match { scrutinee, arms } => {
            expr_is_closed(scrutinee, locals, known_types, known_callables, self_type)
                && arms.iter().all(|arm| {
                    let mut arm_locals = locals.clone();
                    collect_pat_bindings(&arm.pat, &mut arm_locals);
                    arm.guard.as_ref().is_none_or(|g| {
                        expr_is_closed(g, &arm_locals, known_types, known_callables, self_type)
                    }) && expr_is_closed(
                        &arm.body,
                        &arm_locals,
                        known_types,
                        known_callables,
                        self_type,
                    )
                })
        }
        SpecrExpr::Call { func, args } => {
            let args_ok = args
                .iter()
                .all(|a| expr_is_closed(a, locals, known_types, known_callables, self_type));
            if !args_ok {
                return false;
            }
            if let SpecrExpr::Path(segs) = func.as_ref() {
                let last = segs.last().map(String::as_str).unwrap_or("");
                if matches!(
                    last,
                    "ret"
                        | "Ok"
                        | "Err"
                        | "Some"
                        | "int"
                        | "bool_to_int"
                        | "list"
                        | "from_bytes"
                        | "from_bits"
                        | "from_bytes_const"
                ) {
                    return true;
                }
            }
            expr_is_closed(func, locals, known_types, known_callables, self_type)
        }
        SpecrExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if !expr_is_closed(receiver, locals, known_types, known_callables, self_type)
                || !args
                    .iter()
                    .all(|a| expr_is_closed(a, locals, known_types, known_callables, self_type))
            {
                return false;
            }
            if matches!(
                method.as_str(),
                "bytes"
                    | "bits"
                    | "is_zero"
                    | "signed"
                    | "unsigned"
                    | "is_some"
                    | "is_none"
                    | "is_empty"
                    | "is_ok"
                    | "is_err"
                    | "len"
                    | "count"
                    | "abs"
                    | "into"
                    | "clone"
                    | "copied"
                    | "iter"
                    | "into_iter"
                    | "by_ref"
                    | "extract"
                    | "as_ref"
                    | "try_into"
                    | "ok"
                    | "unwrap_or"
                    | "contains"
                    | "all"
                    | "any"
                    | "map"
                    | "filter"
                    | "and_then"
                    | "insert"
                    | "remove"
                    | "get"
                    | "pow"
                    | "rem_euclid"
                    | "div_euclid"
                    | "min"
                    | "max"
                    | "in_bounds"
            ) {
                return true;
            }
            if let SpecrExpr::Path(segs) = receiver.as_ref()
                && segs.len() == 1
                && segs[0] == "self"
                && let Some(st) = self_type
            {
                let fn_name = format!("{}_{}", escape_lean_ident(st), escape_lean_ident(method));
                return known_callables.contains(&fn_name);
            }
            known_callables.contains(&escape_lean_ident(method))
        }
    }
}

fn stmts_are_closed(
    stmts: &[SpecrStmt],
    locals: &BTreeSet<String>,
    known_types: &BTreeSet<String>,
    known_callables: &BTreeSet<String>,
    self_type: Option<&str>,
) -> bool {
    let mut cur_locals = locals.clone();
    for (idx, stmt) in stmts.iter().enumerate() {
        let is_last = idx + 1 == stmts.len();
        match stmt {
            SpecrStmt::Let { pat, ty, init } => {
                if let Some(t) = ty
                    && !specr_type_is_closed(t, known_types, self_type)
                {
                    return false;
                }
                if !expr_is_closed(init, &cur_locals, known_types, known_callables, self_type) {
                    return false;
                }
                collect_pat_bindings(pat, &mut cur_locals);
            }
            SpecrStmt::Assign { lhs, rhs, .. } => {
                if !expr_is_closed(lhs, &cur_locals, known_types, known_callables, self_type)
                    || !expr_is_closed(rhs, &cur_locals, known_types, known_callables, self_type)
                {
                    return false;
                }
            }
            SpecrStmt::Expr { expr, has_semi } => {
                if *has_semi && !is_last {
                    let valid_intermediate = matches!(expr, SpecrExpr::Try(_))
                        || (matches!(
                            expr,
                            SpecrExpr::If { .. } | SpecrExpr::Match { .. } | SpecrExpr::Block(_)
                        ) && expr_has_early_exit(expr))
                        || matches!(
                            expr,
                            SpecrExpr::If {
                                then_branch,
                                else_branch: None,
                                ..
                            } if then_branch.len() == 1
                                && matches!(then_branch[0], SpecrStmt::Assign { .. })
                        );
                    if !valid_intermediate {
                        return false;
                    }
                }
                if !expr_is_closed(expr, &cur_locals, known_types, known_callables, self_type) {
                    return false;
                }
            }
        }
    }
    true
}

/// Lowers all self-contained `enum`, `struct`, `type`, `fn`, and `impl` method
/// items in `env` that are not yet in `already_emitted`.
pub fn emit_general_lowered_items(
    s: &mut String,
    env: &TypeEnvironment,
    already_emitted: &BTreeSet<String>,
) {
    let builtin_names: BTreeSet<&str> = [
        "Unit",
        "Bool",
        "UInt8",
        "Nat",
        "SpecrInt",
        "Int",
        "String",
        "Size",
        "Offset",
        "Align",
        "Signedness",
        "Endianness",
        "TerminationInfo",
        "Option",
        "Except",
        "Result",
        "NdResult",
        "NdComp",
        "List",
        "Set",
        "Map",
        "SpecrSet",
        "SpecrMap",
    ]
    .into_iter()
    .collect();

    let mut emitted_qnames: BTreeSet<String> = already_emitted.clone();
    let mut emitted_lean_names: BTreeSet<String> =
        builtin_names.iter().map(|&n| n.to_string()).collect();
    let mut known_types: BTreeSet<String> = builtin_names.iter().map(|&n| n.to_string()).collect();
    let mut general_lowered_types: BTreeSet<String> = [
        "IntUnOp",
        "IntBinOp",
        "IntBinOpWithOverflow",
        "RelOp",
        "IntType",
        "AllocationKind",
        "AccessKind",
        "NodeRelation",
        "Protected",
        "PermissionUnprot",
        "PermissionProt",
        "Permission",
        "TreeBorrowsParams",
        "Predictor",
        "StackPopAction",
    ]
    .into_iter()
    .map(String::from)
    .collect();
    let mut known_callables: BTreeSet<String> = BTreeSet::new();

    for item in &env.items {
        if already_emitted.contains(&item.qualified_name) || already_emitted.contains(&item.ident) {
            let ln = if let Some(ref tgt) = item.impl_target {
                format!(
                    "{}_{}",
                    escape_lean_ident(tgt),
                    escape_lean_ident(&item.ident)
                )
            } else {
                escape_lean_ident(&item.ident)
            };
            emitted_lean_names.insert(ln.clone());
            if matches!(
                item.kind,
                ItemKind::Enum | ItemKind::Struct | ItemKind::TypeAlias
            ) {
                known_types.insert(escape_lean_ident(&item.ident));
            } else if matches!(item.kind, ItemKind::Fn | ItemKind::ImplMethod) {
                known_callables.insert(ln);
                known_callables.insert(escape_lean_ident(&item.ident));
            }
        }
    }

    // Pass 1: fixed-point lowering of closed non-generic, non-cyclic nominal
    // types.
    loop {
        let mut progress = false;
        for item in &env.items {
            if emitted_qnames.contains(&item.qualified_name) {
                continue;
            }
            let lean_name = escape_lean_ident(&item.ident);
            if emitted_lean_names.contains(&lean_name) {
                continue;
            }
            if !item_type_decl_is_closed(item, &known_types) {
                continue;
            }
            let lowered = match item.kind {
                ItemKind::Enum => lower_specr_enum_to_lean(item, None).ok(),
                ItemKind::Struct => lower_specr_struct_to_lean(item, None).ok(),
                ItemKind::TypeAlias => lower_specr_type_alias_to_lean(item, None).ok(),
                _ => None,
            };
            if let Some(code) = lowered {
                s.push_str(&code);
                emitted_qnames.insert(item.qualified_name.clone());
                emitted_lean_names.insert(lean_name.clone());
                known_types.insert(lean_name.clone());
                general_lowered_types.insert(lean_name);
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }

    // Pass 2: fixed-point lowering of closed non-generic functions and impl
    // methods.
    loop {
        let mut progress = false;
        for item in &env.items {
            if emitted_qnames.contains(&item.qualified_name) {
                continue;
            }
            if !matches!(item.kind, ItemKind::Fn | ItemKind::ImplMethod)
                || !item.generics.is_empty()
                || item.impl_trait.is_some()
            {
                continue;
            }
            let self_type = item.impl_target.as_deref();
            if let Some(st) = self_type {
                let st_lean = escape_lean_ident(st);
                if st.contains('<') || !general_lowered_types.contains(&st_lean) {
                    continue;
                }
            }
            let lean_name = if let Some(st) = self_type {
                format!(
                    "{}_{}",
                    escape_lean_ident(st),
                    escape_lean_ident(&item.ident)
                )
            } else {
                escape_lean_ident(&item.ident)
            };
            if emitted_lean_names.contains(&lean_name) {
                continue;
            }
            let params_ok = item.params.iter().all(|p| {
                if p.name == "self" {
                    true
                } else {
                    let pt = parse_specr_type(&p.ty);
                    specr_type_is_closed(&pt, &general_lowered_types, self_type)
                }
            });
            let ret_ok = item.return_type.as_ref().is_none_or(|rt| {
                let pt = parse_specr_type(rt);
                specr_type_is_closed(&pt, &general_lowered_types, self_type)
            });
            if !params_ok || !ret_ok {
                continue;
            }
            let Ok(stmts) = parse_specr_stmts(&item.body_canonical) else {
                continue;
            };
            if stmts.is_empty() {
                continue;
            }
            let mut locals = BTreeSet::new();
            for p in &item.params {
                if p.name == "self" {
                    locals.insert("self".to_string());
                } else if let Ok(pat) = parse_specr_pat(&p.name) {
                    collect_pat_bindings(&pat, &mut locals);
                }
            }
            if !stmts_are_closed(&stmts, &locals, &known_types, &known_callables, self_type) {
                continue;
            }
            if let Ok(code) = lower_specr_fn_to_lean(item, env, None) {
                s.push_str(&code);
                emitted_qnames.insert(item.qualified_name.clone());
                emitted_lean_names.insert(lean_name.clone());
                known_callables.insert(lean_name);
                known_callables.insert(escape_lean_ident(&item.ident));
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::extractor::{Chapter, CodeBlock, ExtractedSnapshot, SourceSpan, SpecDomain};

    fn dummy_env(rust_src: &str) -> TypeEnvironment {
        let lines = rust_src.lines().count().max(1);
        let block = CodeBlock {
            chapter_index: 0,
            chapter_rel_path: "spec/mem/holdout.md".to_string(),
            chapter_title: "Holdout".to_string(),
            block_index: 0,
            info_string: "rust".to_string(),
            span: SourceSpan {
                rel_path: "spec/mem/holdout.md".to_string(),
                start_line: 1,
                end_line: lines,
                git_sha: "0000".to_string(),
            },
            source: rust_src.to_string(),
            line_count: lines,
        };
        let chapter = Chapter {
            index: 0,
            rel_path: "spec/mem/holdout.md".to_string(),
            title: "Holdout".to_string(),
            domain: SpecDomain::MemoryInterface,
            sha256: "0000".to_string(),
            byte_len: rust_src.len(),
            total_lines: lines,
            blocks: vec![block],
        };
        let snap = ExtractedSnapshot {
            snapshot_id: "test".to_string(),
            git_sha: "0000".to_string(),
            root_dir: PathBuf::from("."),
            chapters: vec![chapter],
            total_blocks: 1,
            total_rust_lines: lines,
        };
        TypeEnvironment::build(&snap)
    }

    #[test]
    fn type_parsing_and_lowering_covers_primitives_and_containers() {
        assert_eq!(lower_specr_type_to_lean("bool"), "Bool");
        assert_eq!(lower_specr_type_to_lean("u8"), "UInt8");
        assert_eq!(lower_specr_type_to_lean("usize"), "Nat");
        assert_eq!(lower_specr_type_to_lean("Int"), "SpecrInt");
        assert_eq!(lower_specr_type_to_lean("&mut GcCow<Foo>"), "Foo");
        assert_eq!(lower_specr_type_to_lean("(Int, bool)"), "(SpecrInt × Bool)");
        assert_eq!(
            lower_specr_type_to_lean("Result<Option<Size>>"),
            "Except TerminationInfo (Option (Size))"
        );
        assert_eq!(
            lower_specr_type_to_lean("NdResult<List<Align>>"),
            "NdComp (List (Align))"
        );
        assert_eq!(
            lower_specr_type_to_lean("Map<Int, Set<u8>>"),
            "SpecrMap (SpecrInt) (SpecrSet (UInt8))"
        );
    }

    #[test]
    fn pattern_and_expression_parsing_handles_guards_and_operators() {
        let pat = parse_specr_pat(
            "PermissionProt::Reserved { had_local_read: true, .. } | PermissionProt::Frozen",
        )
        .expect("valid pattern");
        assert!(matches!(pat, SpecrPat::Or(_)));

        let expr = parse_specr_expr("a + b * 2 <= c && !flag || matches!(x, Some(1))")
            .expect("valid expression");
        assert!(matches!(
            expr,
            SpecrExpr::Binary {
                op: SpecrBinOp::Or,
                ..
            }
        ));
    }

    #[test]
    fn general_lowering_emits_enums_structs_aliases_and_functions() {
        let src = r#"
pub enum LeaseState {
    Idle,
    Shared(Int),
    Exclusive { owner: Int, pinned: bool },
}

pub struct LeaseRecord {
    pub state: LeaseState,
    pub epoch: Int,
}

pub type EpochId = Int;

impl LeaseState {
    pub fn transition(self, writer: Int, protect: bool) -> Result<LeaseState> {
        if writer < 0 {
            throw_ub!("negative writer");
        }
        match self {
            LeaseState::Idle => ret(LeaseState::Shared(1)),
            LeaseState::Shared(n) if !protect => ret(LeaseState::Shared(n + 1)),
            LeaseState::Shared(_) => ret(LeaseState::Exclusive { owner: writer, pinned: true }),
            LeaseState::Exclusive { owner, pinned: true } if owner != writer => {
                throw_ub!("pinned exclusive conflict: {}", owner)
            }
            LeaseState::Exclusive { .. } => {
                ret(LeaseState::Exclusive { owner: writer, pinned: false })
            }
        }
    }
}

pub fn advance_record(rec: LeaseRecord, writer: Int) -> Result<LeaseRecord> {
    let next_state = rec.state.transition(writer, false)?;
    ret(LeaseRecord { state: next_state, epoch: rec.epoch + 1 })
}
"#;
        let env = dummy_env(src);
        let mut out = String::new();
        let already = BTreeSet::new();
        emit_general_lowered_items(&mut out, &env, &already);

        assert!(out.contains("inductive LeaseState : Type where"));
        assert!(out.contains("| Exclusive (owner : SpecrInt) (pinned : Bool) : LeaseState"));
        assert!(out.contains("structure LeaseRecord : Type where"));
        assert!(out.contains("abbrev EpochId : Type := SpecrInt"));
        assert!(out.contains("def LeaseState_transition"));
        assert!(out.contains("abbrev LeaseState.transition := LeaseState_transition"));
        assert!(out.contains("decide (writer < 0)"));
        assert!(out.contains("def advance_record"));
    }

    #[test]
    fn lowering_handles_else_if_early_exits_if_let_and_ret_match() {
        let src = r#"
pub fn check_bounds_and_opt(a: Int, b: Int, opt: Option<Int>) -> Result<Int> {
    if a < 0 {
        throw_ub!("a negative");
    } else if b < 0 {
        throw_ub!("b negative");
    }
    let extra = if let Some(v) = opt {
        v + (a & 3) + (b << 1)
    } else {
        0
    };
    ret(match extra {
        0 => a + b,
        n if n > 100 => throw_ub!("overflow"),
        n => n,
    })
}
"#;
        let env = dummy_env(src);
        let mut out = String::new();
        let already = BTreeSet::new();
        emit_general_lowered_items(&mut out, &env, &already);

        assert!(out.contains("def check_bounds_and_opt"));
        assert!(out.contains("(.error (.ub \"a negative\"))"));
        assert!(out.contains("(.error (.ub \"b negative\"))"));
        assert!(out.contains("(some v) =>"));
        assert!(out.contains("Int.toNat (3 : SpecrInt)"));
        assert!(!out.contains("(.ok match"));
    }
}
