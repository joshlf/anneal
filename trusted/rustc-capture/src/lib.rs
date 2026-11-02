// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Mechanical `rustc` MIR capture and `.anneal/Mir.lean` emission for
//! Anneal.
//!
//! This crate belongs to `trusted/`. It invokes `rustc` on the target crate in
//! a sanitized subprocess environment, extracts the lowered
//! `Runtime(PostCleanup)` MIR for the supported vertical slice
//! (`pub fn id(x: usize) -> usize { x }`), and writes `.anneal/Mir.lean` and
//! optional candidate `.anneal/Proof.lean` artifacts consumed by
//! `cargo-anneal`.
//!
//! Every type and extraction helper in this module that interprets `rustc` MIR
//! structures or Rust lexical syntax cites its normative `rustc_middle::mir` or
//! Rust Reference source at the repository's pinned revisions
//! (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
//! `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

pub mod proof_gen;
pub use proof_gen::render_proof_lean;

use std::collections::BTreeMap;
use std::env;
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Host environment variables preserved across sanitized `rustc` invocations.
const SANITIZED_ENV_ALLOWLIST: [&str; 10] = [
    "PATH",
    "HOME",
    "TMPDIR",
    "USER",
    "LANG",
    "LC_ALL",
    "TERM",
    "RUSTUP_HOME",
    "RUSTUP_TOOLCHAIN",
    "CARGO_HOME",
];

/// Construct a [`Command`] with a cleared environment populated only from
/// [`SANITIZED_ENV_ALLOWLIST`].
fn sanitized_command(program: impl AsRef<OsStr>) -> Command {
    let mut cmd = Command::new(program);
    cmd.env_clear();
    for key in SANITIZED_ENV_ALLOWLIST {
        if let Some(val) = env::var_os(key) {
            cmd.env(key, val);
        }
    }
    cmd
}

/// Errors returned when `rustc` compilation or fail-closed MIR extraction
/// rejects a target crate.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CaptureError {
    /// I/O error reading source files or writing `.anneal/` artifacts.
    #[error("I/O error during MIR capture: {0}")]
    Io(String),
    /// `rustc` exited with a non-zero status code.
    #[error("rustc compilation failed: {0}")]
    CompilationFailed(String),
    /// The crate or MIR contains a construct outside the supported MIR subset.
    #[error("unsupported MIR construct (fail-closed): {0}")]
    UnsupportedMir(String),
}

/// Configuration options for [`capture_crate_with_config`].
#[derive(Debug, Clone, Default)]
pub struct CaptureOptions {
    /// When `true`, synthesize a candidate `.anneal/Proof.lean` script.
    pub emit_proof: bool,
    /// Optional explicit path to the pinned `rustc` compiler binary.
    pub rustc_bin: Option<PathBuf>,
}

/// Captured MIR type (`usize` or `()`).
///
/// Corresponds to `Trusted.MirTy` in `trusted/lean/Trusted/MirAst.lean` and
/// Rust's `usize` type:
///
/// > "The `usize` type is an unsigned integer type with the same number of
/// > bits as the platform's pointer type. It can represent every memory
/// > address in the process."
///
/// Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapturedTy {
    Usize,
    Unit,
}

impl CapturedTy {
    fn to_lean(self) -> &'static str {
        match self {
            Self::Usize => "Trusted.MirTy.usize",
            Self::Unit => "Trusted.MirTy.unit",
        }
    }
}

/// Captured MIR operand.
///
/// Corresponds to `rustc_middle::mir::Operand` (`Copy`, `Move`, `Constant`)
/// over unprojected local places (`Place { local, projection: [] }`):
///
/// > "Creates a value by loading the given place.
/// >
/// > Before drop elaboration, the type of the place must be `Copy`. After drop
/// > elaboration there is no such requirement."
/// >
/// > "Creates a value by performing loading the place, just like the `Copy`
/// > operand."
/// >
/// > "Constants are already semantically values, and remain unchanged."
///
/// Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L1282-L1310
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapturedOperand {
    Copy(usize),
    Move(usize),
    ConstUsize(u128),
}

impl CapturedOperand {
    fn to_lean(&self) -> String {
        match self {
            Self::Copy(local) => format!("(Trusted.Operand.copy ⟨{local}⟩)"),
            Self::Move(local) => format!("(Trusted.Operand.move ⟨{local}⟩)"),
            Self::ConstUsize(bits) => format!(
                "(Trusted.Operand.constVal (Trusted.MirVal.usize {bits}))"
            ),
        }
    }
}

/// Captured MIR statement in a basic block.
///
/// Corresponds to `rustc_middle::mir::StatementKind` (`Assign` with
/// `Rvalue::Use`, `StorageLive`, `StorageDead`, and `Nop`):
///
/// > "Assign statements roughly correspond to an assignment in Rust proper
/// > (`x = ...`) except without the possibility of dropping the previous value
/// > (that must be done separately, if at all)."
/// >
/// > "`StorageLive` and `StorageDead` statements mark the live range of a
/// > local."
///
/// Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L305-L385
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapturedStmt {
    AssignUse { dst: usize, op: CapturedOperand },
    StorageLive(usize),
    StorageDead(usize),
    Nop,
}

impl CapturedStmt {
    fn to_lean(&self) -> String {
        match self {
            Self::AssignUse { dst, op } => format!(
                "Trusted.Stmt.assign ⟨{dst}⟩ (Trusted.Rvalue.use {})",
                op.to_lean()
            ),
            Self::StorageLive(loc) => {
                format!("Trusted.Stmt.storageLive ⟨{loc}⟩")
            }
            Self::StorageDead(loc) => {
                format!("Trusted.Stmt.storageDead ⟨{loc}⟩")
            }
            Self::Nop => "Trusted.Stmt.nop".to_string(),
        }
    }
}

/// Captured MIR basic-block terminator.
///
/// Corresponds to `rustc_middle::mir::TerminatorKind` (`Return`, `Goto`,
/// `Unreachable`):
///
/// > "Block has one successor; we continue execution there."
/// >
/// > "Returns from the function."
/// >
/// > "Indicates a terminator that can never be reached.
/// >
/// > Executing this terminator is UB."
///
/// Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L683-L731
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapturedTerminator {
    Return,
    Goto(usize),
    Unreachable,
}

impl CapturedTerminator {
    fn to_lean(&self) -> String {
        match self {
            Self::Return => "Trusted.Terminator.return_".to_string(),
            Self::Goto(target) => format!("(Trusted.Terminator.goto ⟨{target}⟩)"),
            Self::Unreachable => "Trusted.Terminator.unreachable".to_string(),
        }
    }
}

/// Captured MIR basic block (`bb0`, `bb1`, ...).
///
/// Corresponds to `rustc_middle::mir::BasicBlockData` in `Body::basic_blocks`:
///
/// > "A list of basic blocks. References to basic block use a newtyped index
/// > type [`BasicBlock`] that indexes into this vector."
///
/// Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L207-L209
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapturedBlock {
    pub index: usize,
    pub stmts: Vec<CapturedStmt>,
    pub terminator: CapturedTerminator,
}

/// Specification attached to a captured function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CapturedSpec {
    /// Baseline well-formedness (`specs := []`, so `MirLang.WellFormedOn fn.pre
    /// :: fn.specs` reduces to `[Trusted.MirLang.WellFormed]`).
    #[default]
    WellFormed,
    /// Postcondition `ensures(ret == <arg>)` (`specs := [Trusted.EnsuresEqArg
    /// 1]`).
    EnsuresEqArg(usize),
}

impl CapturedSpec {
    fn to_lean_specs(self) -> String {
        match self {
            Self::WellFormed => "[]".to_string(),
            Self::EnsuresEqArg(local) => {
                format!("[Trusted.EnsuresEqArg {local}]")
            }
        }
    }
}

/// Source-level metadata extracted from `src/lib.rs` via [`scan_rust_source`].
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SourceMetadata {
    /// Default specification when a single-function crate is parsed via
    /// [`parse_emitted_mir`].
    pub spec: CapturedSpec,
    /// Per-function specifications keyed by module-qualified function name.
    pub fn_specs: BTreeMap<String, CapturedSpec>,
    /// Full source text of `src/lib.rs` bound into `Mir.crate.artifacts`.
    pub source_text: String,
}

/// Captured MIR function body and metadata (`rustc_middle::mir::Body`).
///
/// > "The lowered representation of a single function."
/// >
/// > "The first local is the return value pointer, followed by `arg_count`
/// > locals for the function arguments, followed by any user-declared
/// > variables and temporaries."
///
/// Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/mod.rs#L204-L240
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapturedFunction {
    pub name: String,
    pub arg_tys: Vec<CapturedTy>,
    pub ret_ty: CapturedTy,
    pub local_count: usize,
    pub blocks: Vec<CapturedBlock>,
    pub spec: CapturedSpec,
}

/// Complete capture output for a crate written to `.anneal/Mir.lean`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaptureOutput {
    pub functions: Vec<CapturedFunction>,
    pub mir_lean_path: PathBuf,
}

fn ensure_non_symlink(
    path: &Path,
    expect_dir: bool,
) -> Result<(), CaptureError> {
    let meta = fs::symlink_metadata(path).map_err(|e| {
        CaptureError::Io(format!("cannot stat {}: {e}", path.display()))
    })?;
    if meta.file_type().is_symlink() {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to follow symlink at {}",
            path.display()
        )));
    }
    if expect_dir && !meta.is_dir() {
        return Err(CaptureError::Io(format!(
            "expected directory at {}",
            path.display()
        )));
    }
    if !expect_dir && !meta.is_file() {
        return Err(CaptureError::Io(format!(
            "expected regular file at {}",
            path.display()
        )));
    }
    Ok(())
}

/// Resolve the `rustc` compiler binary from `options.rustc_bin`, the installed
/// user-global `.anneal/toolchain` cache, or `"rustc"`.
fn resolve_rustc_binary(options: &CaptureOptions) -> PathBuf {
    if let Some(bin) = &options.rustc_bin {
        return bin.clone();
    }
    if let Some(cache_base) = env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))
    {
        let tc_root = cache_base.join(".anneal").join("toolchain");
        if let Ok(entries) = fs::read_dir(tc_root) {
            let mut dirs: Vec<PathBuf> = entries
                .filter_map(|e| e.ok().map(|entry| entry.path()))
                .filter(|p| p.is_dir())
                .collect();
            dirs.sort();
            for dir in dirs {
                let candidate = dir.join("rust/bin/rustc");
                if candidate.is_file() {
                    return candidate;
                }
            }
        }
    }
    PathBuf::from("rustc")
}

/// Compile `crate_dir/src/lib.rs` with `rustc --emit=mir,metadata`, extract the
/// lowered MIR, and emit `.anneal/Mir.lean`.
pub fn capture_crate(crate_dir: &Path) -> Result<CaptureOutput, CaptureError> {
    capture_crate_with_options(crate_dir, false)
}

/// Compile `crate_dir/src/lib.rs` with `rustc`, emit `.anneal/Mir.lean`, and
/// optionally emit `.anneal/Proof.lean`.
pub fn capture_crate_with_options(
    crate_dir: &Path,
    emit_proof: bool,
) -> Result<CaptureOutput, CaptureError> {
    capture_crate_with_config(
        crate_dir,
        &CaptureOptions {
            emit_proof,
            rustc_bin: None,
        },
    )
}

/// Compile `crate_dir/src/lib.rs` using `options`, emit `.anneal/Mir.lean`, and
/// optionally emit `.anneal/Proof.lean`.
pub fn capture_crate_with_config(
    crate_dir: &Path,
    options: &CaptureOptions,
) -> Result<CaptureOutput, CaptureError> {
    ensure_non_symlink(crate_dir, true)?;
    ensure_non_symlink(&crate_dir.join("src"), true)?;
    ensure_non_symlink(&crate_dir.join("src/lib.rs"), false)?;
    let cargo_toml = crate_dir.join("Cargo.toml");
    if fs::symlink_metadata(&cargo_toml)
        .is_ok_and(|m| m.file_type().is_symlink())
    {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to follow symlinked Cargo.toml at {}",
            cargo_toml.display()
        )));
    }
    let raw_anneal_dir = crate_dir.join(".anneal");
    if fs::symlink_metadata(&raw_anneal_dir)
        .is_ok_and(|m| m.file_type().is_symlink())
    {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to follow symlinked .anneal directory at {}",
            raw_anneal_dir.display()
        )));
    }
    if options.emit_proof {
        let user_proof = crate_dir.join("src/proof.lean");
        if fs::symlink_metadata(&user_proof).is_ok() {
            return Err(CaptureError::UnsupportedMir(format!(
                "refusing to overwrite existing proof file at {}",
                user_proof.display()
            )));
        }
    }

    let crate_dir = crate_dir
        .canonicalize()
        .map_err(|e| CaptureError::Io(format!("{}: {e}", crate_dir.display())))?;
    let src_path = crate_dir.join("src/lib.rs");
    let src_text = fs::read_to_string(&src_path).map_err(|e| {
        CaptureError::Io(format!("cannot read {}: {e}", src_path.display()))
    })?;
    let meta = scan_rust_source(&src_text)?;

    let anneal_dir = crate_dir.join(".anneal");
    let build_dir = anneal_dir.join("rustc-out");
    fs::create_dir_all(&build_dir).map_err(|e| {
        CaptureError::Io(format!("cannot create {}: {e}", build_dir.display()))
    })?;
    let mir_dump_path = build_dir.join("crate.mir");
    let rmeta_path = build_dir.join("libcrate.rmeta");

    let rustc_bin = resolve_rustc_binary(options);
    let mut cmd = sanitized_command(&rustc_bin);
    if let Some(rust_root) = rustc_bin.parent().and_then(Path::parent) {
        let rust_lib = rust_root.join("lib");
        if rust_lib.is_dir() {
            let lib_var = if cfg!(target_os = "macos") {
                "DYLD_LIBRARY_PATH"
            } else {
                "LD_LIBRARY_PATH"
            };
            cmd.env(lib_var, rust_lib);
        }
    }
    let output = cmd
        .arg("--edition=2024")
        .arg("--crate-name=anneal_target")
        .arg("--crate-type=lib")
        .arg(format!(
            "--emit=mir={},metadata={}",
            mir_dump_path.display(),
            rmeta_path.display()
        ))
        .arg(&src_path)
        .output()
        .map_err(|e| {
            CaptureError::Io(format!("failed to invoke rustc: {e}"))
        })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        return Err(CaptureError::CompilationFailed(stderr));
    }

    let mir_text = fs::read_to_string(&mir_dump_path).map_err(|e| {
        CaptureError::Io(format!(
            "cannot read emitted MIR {}: {e}",
            mir_dump_path.display()
        ))
    })?;
    let _ = fs::remove_dir_all(&build_dir);

    let functions = parse_emitted_mir_with_metadata(&mir_text, &meta)?;
    if functions.is_empty() {
        return Err(CaptureError::UnsupportedMir(
            "crate contains no captured functions".to_string(),
        ));
    }

    let mir_lean_source = render_mir_lean_with_metadata(&functions, &meta);
    let mir_lean_path = anneal_dir.join("Mir.lean");
    if fs::symlink_metadata(&mir_lean_path)
        .is_ok_and(|m| m.file_type().is_symlink())
    {
        return Err(CaptureError::UnsupportedMir(format!(
            "refusing to write symlinked {}",
            mir_lean_path.display()
        )));
    }
    fs::write(&mir_lean_path, mir_lean_source.as_bytes()).map_err(|e| {
        CaptureError::Io(format!(
            "cannot write {}: {e}",
            mir_lean_path.display()
        ))
    })?;
    if options.emit_proof {
        let proof_path = anneal_dir.join("Proof.lean");
        if fs::symlink_metadata(&proof_path)
            .is_ok_and(|m| m.file_type().is_symlink())
        {
            return Err(CaptureError::UnsupportedMir(format!(
                "refusing to write symlinked {}",
                proof_path.display()
            )));
        }
        let proof_src = render_proof_lean(&functions);
        fs::write(&proof_path, proof_src.as_bytes()).map_err(|e| {
            CaptureError::Io(format!(
                "cannot write {}: {e}",
                proof_path.display()
            ))
        })?;
    }

    Ok(CaptureOutput {
        functions,
        mir_lean_path,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LexToken {
    Ident(String),
    Punct(char),
    Literal,
    AnnealSpec(CapturedSpec),
    AnnealSafety(String),
}

/// Check whether `bytes[pos..]` starts with a Rust character literal (`'c'` or
/// `'\...'`) rather than a lifetime (`'a` or `'static`), returning the byte
/// index immediately after the closing `'` when it is a character literal.
///
/// Corresponds to the Rust Reference lexical grammar for character literals vs.
/// lifetime tokens (`r[lex.token.literal.char]` and `r[lex.token.life]`):
///
/// > "A character literal is a single Unicode character enclosed within two
/// > `U+0027` (single-quote) characters, with the exception of `U+0027` itself,
/// > which must be escaped by a preceding `U+005C` (`\`) character."
///
/// Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/tokens.md#L121-L125
fn try_consume_char_literal(src: &str, quote_pos: usize) -> Option<usize> {
    let rest = &src[quote_pos + 1..];
    let mut chars = rest.char_indices();
    let (_, first) = chars.next()?;
    if first == '\n' || first == '\r' || first == '\'' {
        return None;
    }
    if first == '\\' {
        for (idx, ch) in chars {
            if ch == '\n' || ch == '\r' {
                return None;
            }
            if ch == '\'' {
                return Some(quote_pos + 1 + idx + 1);
            }
        }
        return None;
    }
    let (second_offset, second) = chars.next()?;
    if second == '\'' {
        Some(quote_pos + 1 + second_offset + 1)
    } else {
        None
    }
}

/// Check whether `src[pos..]` starts a raw string literal (`r"..."`,
/// `r#"..."#`, `br"..."`, `cr"..."`), returning `(opening_quote_pos,
/// num_hashes)`.
fn try_start_raw_string(src: &str, pos: usize) -> Option<(usize, usize)> {
    let bytes = src.as_bytes();
    let after_prefix = if bytes[pos..].starts_with(b"br")
        || bytes[pos..].starts_with(b"cr")
    {
        pos + 2
    } else if bytes[pos] == b'r' {
        pos + 1
    } else {
        return None;
    };
    let mut cur = after_prefix;
    let mut hashes = 0usize;
    while cur < bytes.len() && bytes[cur] == b'#' {
        hashes += 1;
        cur += 1;
    }
    if cur < bytes.len() && bytes[cur] == b'"' {
        Some((cur, hashes))
    } else {
        None
    }
}

fn parse_anneal_spec_clause(clause: &str) -> Result<CapturedSpec, CaptureError> {
    let trimmed = clause.trim();
    let inner = if let Some(s) =
        trimmed.strip_prefix('(').and_then(|s| s.strip_suffix(')'))
    {
        let s = s.trim();
        // Only unwrap outer parens if they balance across `s`.
        let mut depth = 0i32;
        let mut balanced = true;
        for c in s.chars() {
            if c == '(' {
                depth += 1;
            } else if c == ')' {
                depth -= 1;
                if depth < 0 {
                    balanced = false;
                    break;
                }
            }
        }
        if balanced && depth == 0 { s } else { trimmed }
    } else {
        trimmed
    };
    match inner.trim() {
        "ensures(ret == x)" | "ret == x" => Ok(CapturedSpec::EnsuresEqArg(1)),
        "well_formed" => Ok(CapturedSpec::WellFormed),
        other => Err(CaptureError::UnsupportedMir(format!(
            "unsupported anneal:spec annotation: `{other}`"
        ))),
    }
}

fn parse_anneal_line_comment(
    comment_body: &str,
) -> Result<Option<LexToken>, CaptureError> {
    if !comment_body.contains("anneal:") {
        return Ok(None);
    }
    if comment_body.starts_with('!') {
        return Err(CaptureError::UnsupportedMir(
            "anneal: directives are not permitted in inner doc comments (`//!`)"
                .to_string(),
        ));
    }
    let stripped = comment_body.trim_start_matches('/').trim();
    if !stripped.starts_with("anneal:") {
        return Err(CaptureError::UnsupportedMir(format!(
            "malformed or trailing anneal: directive in comment: `{stripped}`"
        )));
    }
    if let Some(rest) = stripped.strip_prefix("anneal:spec") {
        let rest_trim = rest.trim();
        if rest_trim.is_empty()
            || (!rest.starts_with(char::is_whitespace)
                && !rest_trim.starts_with('('))
        {
            return Err(CaptureError::UnsupportedMir(format!(
                "unrecognized anneal: directive `{stripped}`"
            )));
        }
        let spec = parse_anneal_spec_clause(rest_trim)?;
        return Ok(Some(LexToken::AnnealSpec(spec)));
    }
    if let Some(rest) = stripped.strip_prefix("anneal:safety") {
        let rest_trim = rest.trim();
        if rest_trim.is_empty()
            || (!rest.starts_with(char::is_whitespace)
                && !rest_trim.starts_with('('))
        {
            return Err(CaptureError::UnsupportedMir(format!(
                "unrecognized anneal: directive `{stripped}`"
            )));
        }
        let inner = rest_trim
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(rest_trim)
            .trim();
        if inner.is_empty() {
            return Err(CaptureError::UnsupportedMir(
                "empty anneal:safety annotation".to_string(),
            ));
        }
        return Ok(Some(LexToken::AnnealSafety(inner.to_string())));
    }
    Err(CaptureError::UnsupportedMir(format!(
        "unrecognized anneal: directive `{stripped}`"
    )))
}

/// Tokenize `src` into [`LexToken`]s while stripping comments and string/char
/// literals according to the Rust Reference lexical rules (`r[lex.comment]`,
/// `r[lex.token.literal]`).
///
/// > "Block comments (`/* ... */`) can be nested."
///
/// Source: https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/comments.md#L12-L24
fn lex_rust_source(src: &str) -> Result<Vec<LexToken>, CaptureError> {
    let bytes = src.as_bytes();
    let mut pos = 0usize;
    let mut tokens = Vec::new();

    while pos < bytes.len() {
        let b = bytes[pos];
        if b.is_ascii_whitespace() {
            pos += 1;
            continue;
        }

        // Line comment `//`, `///`, `//!`.
        if bytes[pos..].starts_with(b"//") {
            let start = pos + 2;
            pos += 2;
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            let body = src[start..pos].trim_end_matches('\r');
            if let Some(tok) = parse_anneal_line_comment(body)? {
                tokens.push(tok);
            }
            continue;
        }

        // Nested block comment `/* ... */`.
        if bytes[pos..].starts_with(b"/*") {
            let start = pos;
            pos += 2;
            let mut depth = 1usize;
            while pos < bytes.len() && depth > 0 {
                if bytes[pos..].starts_with(b"/*") {
                    depth += 1;
                    pos += 2;
                } else if bytes[pos..].starts_with(b"*/") {
                    depth -= 1;
                    pos += 2;
                } else {
                    pos += 1;
                }
            }
            if depth > 0 {
                return Err(CaptureError::UnsupportedMir(
                    "unterminated block comment in source".to_string(),
                ));
            }
            if src[start..pos].contains("anneal:") {
                return Err(CaptureError::UnsupportedMir(
                    "anneal: directives are not permitted inside block comments"
                        .to_string(),
                ));
            }
            continue;
        }

        // Raw string literal (`r"..."`, `r#"..."#`, `br#*"..."#*`,
        // `cr#*"..."#*`).
        if let Some((quote_pos, hashes)) = try_start_raw_string(src, pos) {
            pos = quote_pos + 1;
            let mut closed = false;
            while pos < bytes.len() {
                if bytes[pos] == b'"' {
                    let mut matched = 0usize;
                    while matched < hashes
                        && pos + 1 + matched < bytes.len()
                        && bytes[pos + 1 + matched] == b'#'
                    {
                        matched += 1;
                    }
                    if matched == hashes {
                        pos += 1 + hashes;
                        closed = true;
                        break;
                    }
                }
                pos += 1;
            }
            if !closed {
                return Err(CaptureError::UnsupportedMir(
                    "unterminated raw string literal".to_string(),
                ));
            }
            tokens.push(LexToken::Literal);
            continue;
        }

        // Byte or C string literal prefix (`b"..."`, `c"..."`) or byte char
        // literal (`b'c'`).
        if (b == b'b' || b == b'c')
            && pos + 1 < bytes.len()
            && bytes[pos + 1] == b'"'
        {
            pos += 1;
        } else if b == b'b'
            && pos + 1 < bytes.len()
            && bytes[pos + 1] == b'\''
            && let Some(next_pos) = try_consume_char_literal(src, pos + 1)
        {
            pos = next_pos;
            tokens.push(LexToken::Literal);
            continue;
        }

        // Standard string literal `"..."`.
        if bytes[pos] == b'"' {
            pos += 1;
            let mut closed = false;
            while pos < bytes.len() {
                if bytes[pos] == b'\\' {
                    pos += 1;
                    if pos < bytes.len() {
                        let ch_len =
                            src[pos..].chars().next().map_or(1, char::len_utf8);
                        pos += ch_len;
                    }
                    continue;
                }
                if bytes[pos] == b'"' {
                    pos += 1;
                    closed = true;
                    break;
                }
                let ch_len =
                    src[pos..].chars().next().map_or(1, char::len_utf8);
                pos += ch_len;
            }
            if !closed {
                return Err(CaptureError::UnsupportedMir(
                    "unterminated string literal".to_string(),
                ));
            }
            tokens.push(LexToken::Literal);
            continue;
        }

        // Character literal `'c'` vs. lifetime `'a`.
        if bytes[pos] == b'\'' {
            if let Some(next_pos) = try_consume_char_literal(src, pos) {
                pos = next_pos;
                tokens.push(LexToken::Literal);
                continue;
            }
            pos += 1;
            while pos < bytes.len()
                && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'_')
            {
                pos += 1;
            }
            continue;
        }

        // Raw identifier `r#ident`.
        if bytes[pos..].starts_with(b"r#")
            && pos + 2 < bytes.len()
            && (bytes[pos + 2].is_ascii_alphabetic() || bytes[pos + 2] == b'_')
        {
            pos += 2;
            let start = pos;
            while pos < bytes.len()
                && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'_')
            {
                pos += 1;
            }
            tokens.push(LexToken::Ident(src[start..pos].to_string()));
            continue;
        }

        // Identifier or keyword.
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = pos;
            while pos < bytes.len()
                && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'_')
            {
                pos += 1;
            }
            tokens.push(LexToken::Ident(src[start..pos].to_string()));
            continue;
        }

        // Numeric literal.
        if b.is_ascii_digit() {
            while pos < bytes.len()
                && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'_')
            {
                pos += 1;
            }
            tokens.push(LexToken::Literal);
            continue;
        }

        // Single-character punctuation.
        let ch = src[pos..].chars().next().unwrap();
        pos += ch.len_utf8();
        tokens.push(LexToken::Punct(ch));
    }

    Ok(tokens)
}

/// Scan `src/lib.rs` with a single-pass lexical and structural state machine to
/// extract per-function `anneal:spec` annotations and module scopes.
pub fn scan_rust_source(src: &str) -> Result<SourceMetadata, CaptureError> {
    let tokens = lex_rust_source(src)?;
    let mut fn_specs = BTreeMap::new();
    let mut first_spec = None;
    let mut pending_spec: Option<CapturedSpec> = None;
    let mut pending_safety: Option<String> = None;
    let mut mod_stack: Vec<(String, usize)> = Vec::new();
    let mut brace_depth = 0usize;

    let mut idx = 0usize;
    while idx < tokens.len() {
        // Skip attributes `#[...]` and `#![...]`.
        if tokens[idx] == LexToken::Punct('#') {
            let bracket_start = if idx + 1 < tokens.len()
                && tokens[idx + 1] == LexToken::Punct('[')
            {
                Some(idx + 1)
            } else if idx + 2 < tokens.len()
                && tokens[idx + 1] == LexToken::Punct('!')
                && tokens[idx + 2] == LexToken::Punct('[')
            {
                Some(idx + 2)
            } else {
                None
            };
            if let Some(b_idx) = bracket_start {
                let mut depth = 1usize;
                idx = b_idx + 1;
                while idx < tokens.len() && depth > 0 {
                    if tokens[idx] == LexToken::Punct('[') {
                        depth += 1;
                    } else if tokens[idx] == LexToken::Punct(']') {
                        depth -= 1;
                    }
                    idx += 1;
                }
                continue;
            }
        }

        match &tokens[idx] {
            LexToken::AnnealSpec(spec) => {
                if pending_spec.is_some() {
                    return Err(CaptureError::UnsupportedMir(
                        "duplicate anneal:spec annotation on function"
                            .to_string(),
                    ));
                }
                pending_spec = Some(*spec);
                idx += 1;
                continue;
            }
            LexToken::AnnealSafety(safety) => {
                if pending_safety.is_some() {
                    return Err(CaptureError::UnsupportedMir(
                        "duplicate anneal:safety annotation on function"
                            .to_string(),
                    ));
                }
                pending_safety = Some(safety.clone());
                idx += 1;
                continue;
            }
            _ => {}
        }

        // If `pending_spec` or `pending_safety` is set, the next tokens must
        // form a function declaration (`[pub [(...)]] [unsafe] [const] fn
        // <name>`).
        if pending_spec.is_some() || pending_safety.is_some() {
            let mut probe = idx;
            if probe < tokens.len()
                && tokens[probe] == LexToken::Ident("pub".to_string())
            {
                probe += 1;
                if probe < tokens.len()
                    && tokens[probe] == LexToken::Punct('(')
                {
                    let mut p_depth = 1usize;
                    probe += 1;
                    while probe < tokens.len() && p_depth > 0 {
                        if tokens[probe] == LexToken::Punct('(') {
                            p_depth += 1;
                        } else if tokens[probe] == LexToken::Punct(')') {
                            p_depth -= 1;
                        }
                        probe += 1;
                    }
                }
            }
            if probe < tokens.len()
                && tokens[probe] == LexToken::Ident("unsafe".to_string())
            {
                probe += 1;
            }
            if probe < tokens.len()
                && tokens[probe] == LexToken::Ident("const".to_string())
                && probe + 1 < tokens.len()
                && tokens[probe + 1] == LexToken::Ident("fn".to_string())
            {
                probe += 1;
            }
            if probe >= tokens.len()
                || tokens[probe] != LexToken::Ident("fn".to_string())
            {
                return Err(CaptureError::UnsupportedMir(
                    "dangling anneal: annotation not attached to a function declaration"
                        .to_string(),
                ));
            }
            idx = probe;
        }

        if tokens[idx] == LexToken::Punct('{') {
            brace_depth += 1;
            idx += 1;
            continue;
        }
        if tokens[idx] == LexToken::Punct('}') {
            brace_depth = brace_depth.saturating_sub(1);
            if let Some((_, mod_depth)) = mod_stack.last()
                && brace_depth < *mod_depth
            {
                mod_stack.pop();
            }
            idx += 1;
            continue;
        }

        if tokens[idx] == LexToken::Ident("mod".to_string()) {
            if let Some(LexToken::Ident(mod_name)) = tokens.get(idx + 1)
                && tokens.get(idx + 2) == Some(&LexToken::Punct('{'))
            {
                brace_depth += 1;
                mod_stack.push((mod_name.clone(), brace_depth));
                idx += 3;
                continue;
            }
        }

        if tokens[idx] == LexToken::Ident("fn".to_string()) {
            let Some(LexToken::Ident(fn_name)) = tokens.get(idx + 1) else {
                return Err(CaptureError::UnsupportedMir(
                    "expected function identifier after `fn`".to_string(),
                ));
            };
            let qualified = if mod_stack.is_empty() {
                fn_name.clone()
            } else {
                let mut prefix: Vec<&str> =
                    mod_stack.iter().map(|(m, _)| m.as_str()).collect();
                prefix.push(fn_name.as_str());
                prefix.join("::")
            };
            let spec = pending_spec.take().unwrap_or(CapturedSpec::WellFormed);
            let _ = pending_safety.take();
            if first_spec.is_none() && spec != CapturedSpec::WellFormed {
                first_spec = Some(spec);
            }
            fn_specs.insert(qualified, spec);
            idx += 2;
            continue;
        }

        idx += 1;
    }

    if pending_spec.is_some() || pending_safety.is_some() {
        return Err(CaptureError::UnsupportedMir(
            "dangling anneal: annotation at end of file".to_string(),
        ));
    }

    Ok(SourceMetadata {
        spec: first_spec.unwrap_or(CapturedSpec::WellFormed),
        fn_specs,
        source_text: src.to_string(),
    })
}

/// Check whether `line` is a `rustc --emit=mir` global allocation dump header
/// (`alloc<digits> (...) {`).
///
/// Checking for one or more ASCII digits followed by `" ("` after `"alloc"`
/// ensures functions named `alloc_passthrough` or `allocate` are never mistaken
/// for CTFE allocation blocks.
fn is_alloc_header(line: &str) -> bool {
    let Some(rest) = line.strip_prefix("alloc") else {
        return false;
    };
    let digit_count = rest.chars().take_while(char::is_ascii_digit).count();
    digit_count > 0
        && rest[digit_count..].starts_with(" (")
        && line.ends_with('{')
}

/// Parse the textual `Runtime(PostCleanup)` MIR emitted by `rustc --emit=mir`,
/// failing closed on any unrecognized item, signature, statement, or
/// terminator.
pub fn parse_emitted_mir(
    mir_text: &str,
    spec: CapturedSpec,
) -> Result<Vec<CapturedFunction>, CaptureError> {
    let meta = SourceMetadata {
        spec,
        ..SourceMetadata::default()
    };
    parse_emitted_mir_with_metadata(mir_text, &meta)
}

/// Parse textual `rustc --emit=mir` output using source metadata from
/// [`scan_rust_source`].
pub fn parse_emitted_mir_with_metadata(
    mir_text: &str,
    meta: &SourceMetadata,
) -> Result<Vec<CapturedFunction>, CaptureError> {
    let mut functions = Vec::new();
    let mut lines = mir_text.lines().peekable();

    while let Some(raw_line) = lines.next() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        if is_alloc_header(line) {
            let mut alloc_depth = 1usize;
            for alloc_line in lines.by_ref() {
                let t = alloc_line.trim();
                if t.ends_with('{') {
                    alloc_depth += 1;
                } else if t == "}" {
                    alloc_depth -= 1;
                    if alloc_depth == 0 {
                        break;
                    }
                }
            }
            continue;
        }
        let Some(fn_rest) = line.strip_prefix("fn ") else {
            return Err(CaptureError::UnsupportedMir(format!(
                "unexpected top-level MIR line: `{line}`"
            )));
        };
        let (name, arg_tys, ret_ty) = parse_fn_header(fn_rest)?;
        let mut max_local = arg_tys.len();
        let mut blocks = Vec::new();
        let mut scope_brace_depth = 0usize;

        loop {
            let Some(body_raw) = lines.next() else {
                return Err(CaptureError::UnsupportedMir(format!(
                    "unterminated MIR body for `{name}`"
                )));
            };
            let body_line = body_raw.trim();
            if body_line.is_empty()
                || body_line.starts_with("//")
                || body_line.starts_with("debug ")
            {
                continue;
            }
            if body_line.starts_with("scope ") && body_line.ends_with('{') {
                scope_brace_depth += 1;
                continue;
            }
            if body_line == "}" {
                if scope_brace_depth > 0 {
                    scope_brace_depth -= 1;
                    continue;
                }
                break;
            }
            if let Some(decl_rest) = body_line.strip_prefix("let ") {
                let (local_idx, _ty) = parse_local_decl(decl_rest)?;
                if local_idx > max_local {
                    max_local = local_idx;
                }
                continue;
            }
            if let Some(bb_header) = body_line.strip_suffix_or_block() {
                let bb_idx = parse_bb_index(bb_header)?;
                if bb_idx != blocks.len() {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "non-contiguous basic block index bb{bb_idx}"
                    )));
                }
                let mut stmts = Vec::new();
                let mut terminator = None;
                loop {
                    let Some(stmt_raw) = lines.next() else {
                        return Err(CaptureError::UnsupportedMir(format!(
                            "unterminated basic block bb{bb_idx}"
                        )));
                    };
                    let stmt_line = stmt_raw.trim();
                    if stmt_line.is_empty() || stmt_line.starts_with("//") {
                        continue;
                    }
                    if stmt_line == "}" {
                        break;
                    }
                    if terminator.is_some() {
                        return Err(CaptureError::UnsupportedMir(format!(
                            "statement after terminator in bb{bb_idx}: `{stmt_line}`"
                        )));
                    }
                    match parse_stmt_or_terminator(stmt_line)? {
                        StmtOrTerm::Stmt(s) => stmts.push(s),
                        StmtOrTerm::Term(t) => terminator = Some(t),
                    }
                }
                let Some(terminator) = terminator else {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "basic block bb{bb_idx} missing terminator"
                    )));
                };
                blocks.push(CapturedBlock {
                    index: bb_idx,
                    stmts,
                    terminator,
                });
                continue;
            }
            return Err(CaptureError::UnsupportedMir(format!(
                "unrecognized MIR body line in `{name}`: `{body_line}`"
            )));
        }

        if blocks.is_empty() {
            return Err(CaptureError::UnsupportedMir(format!(
                "MIR body for `{name}` has no basic blocks"
            )));
        }
        let fn_spec = meta.fn_specs.get(&name).copied().unwrap_or(meta.spec);
        functions.push(CapturedFunction {
            name,
            arg_tys,
            ret_ty,
            local_count: max_local + 1,
            blocks,
            spec: fn_spec,
        });
    }

    Ok(functions)
}

trait BlockHeaderExt {
    fn strip_suffix_or_block(&self) -> Option<&str>;
}

impl BlockHeaderExt for str {
    fn strip_suffix_or_block(&self) -> Option<&str> {
        let before_brace = self.strip_suffix('{')?.trim();
        let before_cleanup = before_brace
            .strip_suffix("(cleanup):")
            .map(str::trim)
            .or_else(|| before_brace.strip_suffix(':'));
        before_cleanup
    }
}

fn is_valid_qualified_ident(name: &str) -> bool {
    !name.is_empty()
        && name.split("::").all(|seg| {
            !seg.is_empty()
                && seg
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && seg.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}

fn lean_ident(name: &str) -> String {
    name.replace("::", "__")
}

fn parse_fn_header(
    fn_rest: &str,
) -> Result<(String, Vec<CapturedTy>, CapturedTy), CaptureError> {
    let header = fn_rest
        .strip_suffix('{')
        .ok_or_else(|| {
            CaptureError::UnsupportedMir(format!(
                "malformed fn header: `{fn_rest}`"
            ))
        })?
        .trim();
    let (name_part, after_name) = header.split_once('(').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "missing parameter list in `{header}`"
        ))
    })?;
    let name = name_part.trim().to_string();
    if !is_valid_qualified_ident(&name) {
        return Err(CaptureError::UnsupportedMir(format!(
            "unsupported function identifier `{name}`"
        )));
    }
    let (params_str, ret_part) = after_name.split_once(')').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "unclosed parameter list in `{header}`"
        ))
    })?;
    let mut arg_tys = Vec::new();
    if !params_str.trim().is_empty() {
        for (idx, param) in params_str.split(',').enumerate() {
            let (local_str, ty_str) = param.split_once(':').ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "malformed parameter `{param}`"
                ))
            })?;
            let local_idx = parse_local_token(local_str.trim())?;
            if local_idx != idx + 1 {
                return Err(CaptureError::UnsupportedMir(format!(
                    "expected parameter local _{}, found _{local_idx}",
                    idx + 1
                )));
            }
            arg_tys.push(parse_ty(ty_str.trim())?);
        }
    }
    let ret_ty = if let Some(arrow_rest) = ret_part.trim().strip_prefix("->") {
        parse_ty(arrow_rest.trim())?
    } else if ret_part.trim().is_empty() {
        CapturedTy::Unit
    } else {
        return Err(CaptureError::UnsupportedMir(format!(
            "malformed return type in `{header}`"
        )));
    };
    Ok((name, arg_tys, ret_ty))
}

fn parse_local_decl(
    decl_rest: &str,
) -> Result<(usize, CapturedTy), CaptureError> {
    let without_semi = decl_rest.strip_suffix(';').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "missing semicolon in local decl `{decl_rest}`"
        ))
    })?;
    let without_mut = without_semi
        .strip_prefix("mut ")
        .unwrap_or(without_semi)
        .trim();
    let (local_str, ty_str) = without_mut.split_once(':').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "malformed local decl `{decl_rest}`"
        ))
    })?;
    let idx = parse_local_token(local_str.trim())?;
    let ty = parse_ty(ty_str.trim())?;
    Ok((idx, ty))
}

fn parse_local_token(token: &str) -> Result<usize, CaptureError> {
    let digits = token.strip_prefix('_').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "expected local `_<n>`, found `{token}`"
        ))
    })?;
    digits.parse::<usize>().map_err(|_| {
        CaptureError::UnsupportedMir(format!("invalid local index `{token}`"))
    })
}

fn parse_bb_index(token: &str) -> Result<usize, CaptureError> {
    let digits = token.trim().strip_prefix("bb").ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "expected basic block `bb<n>`, found `{token}`"
        ))
    })?;
    digits.parse::<usize>().map_err(|_| {
        CaptureError::UnsupportedMir(format!(
            "invalid basic block index `{token}`"
        ))
    })
}

fn parse_ty(ty_str: &str) -> Result<CapturedTy, CaptureError> {
    match ty_str {
        "usize" => Ok(CapturedTy::Usize),
        "()" => Ok(CapturedTy::Unit),
        other => Err(CaptureError::UnsupportedMir(format!(
            "unsupported MIR type `{other}`"
        ))),
    }
}

enum StmtOrTerm {
    Stmt(CapturedStmt),
    Term(CapturedTerminator),
}

fn parse_stmt_or_terminator(line: &str) -> Result<StmtOrTerm, CaptureError> {
    let stmt = line.strip_suffix(';').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "missing semicolon in MIR statement/terminator: `{line}`"
        ))
    })?;
    if stmt == "return" {
        return Ok(StmtOrTerm::Term(CapturedTerminator::Return));
    }
    if stmt == "unreachable" {
        return Ok(StmtOrTerm::Term(CapturedTerminator::Unreachable));
    }
    if let Some(target_str) = stmt.strip_prefix("goto -> ") {
        let target = parse_bb_index(target_str.trim())?;
        return Ok(StmtOrTerm::Term(CapturedTerminator::Goto(target)));
    }
    if stmt == "nop" {
        return Ok(StmtOrTerm::Stmt(CapturedStmt::Nop));
    }
    if let Some(inner) = stmt
        .strip_prefix("StorageLive(")
        .and_then(|s| s.strip_suffix(')'))
    {
        return Ok(StmtOrTerm::Stmt(CapturedStmt::StorageLive(
            parse_local_token(inner.trim())?,
        )));
    }
    if let Some(inner) = stmt
        .strip_prefix("StorageDead(")
        .and_then(|s| s.strip_suffix(')'))
    {
        return Ok(StmtOrTerm::Stmt(CapturedStmt::StorageDead(
            parse_local_token(inner.trim())?,
        )));
    }
    if let Some((lhs, rhs)) = stmt.split_once('=') {
        let dst = parse_local_token(lhs.trim())?;
        let op = parse_operand(rhs.trim())?;
        return Ok(StmtOrTerm::Stmt(CapturedStmt::AssignUse { dst, op }));
    }
    Err(CaptureError::UnsupportedMir(format!(
        "unsupported MIR statement or terminator: `{line}`"
    )))
}

fn parse_operand(rhs: &str) -> Result<CapturedOperand, CaptureError> {
    if let Some(local_str) = rhs.strip_prefix("copy ") {
        return Ok(CapturedOperand::Copy(parse_local_token(local_str.trim())?));
    }
    if let Some(local_str) = rhs.strip_prefix("move ") {
        return Ok(CapturedOperand::Move(parse_local_token(local_str.trim())?));
    }
    if let Some(const_str) = rhs.strip_prefix("const ") {
        if let Some(num_str) = const_str.trim().strip_suffix("_usize") {
            let cleaned = num_str.replace('_', "");
            let val = cleaned.parse::<u128>().map_err(|_| {
                CaptureError::UnsupportedMir(format!(
                    "invalid usize constant `{const_str}`"
                ))
            })?;
            return Ok(CapturedOperand::ConstUsize(val));
        }
    }
    Err(CaptureError::UnsupportedMir(format!(
        "unsupported MIR rvalue/operand: `{rhs}`"
    )))
}

fn render_lean_list(items: &[String]) -> String {
    format!("[{}]", items.join(", "))
}

fn lean_quote_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => {
                let _ = write!(out, "\\x{:02x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Render the read-only `.anneal/Mir.lean` module defining
/// `Mir.crate : Trusted.Crate`.
pub fn render_mir_lean(functions: &[CapturedFunction]) -> String {
    render_mir_lean_with_metadata(functions, &SourceMetadata::default())
}

/// Render the read-only `.anneal/Mir.lean` module defining
/// `Mir.crate : Trusted.Crate` with source artifact bindings.
pub fn render_mir_lean_with_metadata(
    functions: &[CapturedFunction],
    meta: &SourceMetadata,
) -> String {
    let mut out = String::from("prelude\nimport Trusted\n\nnamespace Mir\n\n");
    for func in functions {
        let ident = lean_ident(&func.name);
        let arg_tys: Vec<String> =
            func.arg_tys.iter().map(|t| t.to_lean().to_string()).collect();
        let blocks: Vec<String> = func
            .blocks
            .iter()
            .map(|b| {
                let stmts: Vec<String> =
                    b.stmts.iter().map(CapturedStmt::to_lean).collect();
                format!(
                    "{{ stmts := {}, terminator := {} }}",
                    render_lean_list(&stmts),
                    b.terminator.to_lean()
                )
            })
            .collect();
        let _ = writeln!(
            out,
            "def {ident}_body : Trusted.MirBody where\n  \
             argTys := {}\n  \
             retTy := {}\n  \
             localCount := {}\n  \
             blocks := {}\n",
            render_lean_list(&arg_tys),
            func.ret_ty.to_lean(),
            func.local_count,
            render_lean_list(&blocks),
        );
    }

    let fn_entries: Vec<String> = functions
        .iter()
        .map(|f| {
            let ident = lean_ident(&f.name);
            format!(
                "{{ name := {}, prog := {ident}_body, specs := {} }}",
                lean_quote_string(&f.name),
                f.spec.to_lean_specs()
            )
        })
        .collect();
    let tcb_entries: Vec<String> = functions
        .iter()
        .map(|f| {
            let ident = lean_ident(&f.name);
            format!(
                "Trusted.TCBItem.rustcLowering {} {ident}_body",
                lean_quote_string(&f.name)
            )
        })
        .collect();
    let quoted_src = lean_quote_string(&meta.source_text);
    let _ = writeln!(
        out,
        "def crate : Trusted.Crate where\n  \
         functions := {}\n  \
         tcb := {}\n  \
         artifacts := [{{ path := \"src/lib.rs\", contents := {quoted_src}, expected := {quoted_src} }}]\n\n\
         end Mir",
        render_lean_list(&fn_entries),
        render_lean_list(&tcb_entries),
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_rustc_id_mir() {
        let sample = "\
// WARNING: This output format is intended for human consumers only
fn id(_1: usize) -> usize {
    debug x => _1;
    let mut _0: usize;

    bb0: {
        _0 = copy _1;
        return;
    }
}
";
        let fns =
            parse_emitted_mir(sample, CapturedSpec::EnsuresEqArg(1)).unwrap();
        assert_eq!(fns.len(), 1);
        assert_eq!(fns[0].name, "id");
        assert_eq!(fns[0].arg_tys, vec![CapturedTy::Usize]);
        assert_eq!(fns[0].ret_ty, CapturedTy::Usize);
        assert_eq!(fns[0].local_count, 2);
        assert_eq!(
            fns[0].blocks,
            vec![CapturedBlock {
                index: 0,
                stmts: vec![CapturedStmt::AssignUse {
                    dst: 0,
                    op: CapturedOperand::Copy(1),
                }],
                terminator: CapturedTerminator::Return,
            }]
        );
    }

    #[test]
    fn parses_alloc_prefixed_fn_and_nested_scopes() {
        let src = "\
/// Returns the input unchanged.
/// anneal:spec ensures(ret == x)
pub fn alloc_passthrough(x: usize) -> usize {
    let a = x;
    {
        let b = a;
        b
    }
}
";
        let meta = scan_rust_source(src).unwrap();
        assert_eq!(
            meta.fn_specs.get("alloc_passthrough"),
            Some(&CapturedSpec::EnsuresEqArg(1))
        );

        let sample_mir = "\
alloc1 (size: 16, align: 1) {
    00 01 02 03
}

fn alloc_passthrough(_1: usize) -> usize {
    debug x => _1;
    let mut _0: usize;
    scope 1 {
        debug a => _1;
        scope 2 {
            debug b => _1;
        }
    }

    bb0: {
        _0 = copy _1;
        return;
    }
}
";
        let fns = parse_emitted_mir_with_metadata(sample_mir, &meta).unwrap();
        assert_eq!(fns.len(), 1);
        assert_eq!(fns[0].name, "alloc_passthrough");
        assert_eq!(fns[0].spec, CapturedSpec::EnsuresEqArg(1));
    }

    #[test]
    fn scanner_handles_char_literals_raw_strings_and_rejects_bad_anneal_directives() {
        let src = r####"
const QUOTE: char = '"';
const OPEN: char = '{';
const RAW: &str = r#"
// anneal:spec unknown_directive
"#;
/* outer /* nested */ comment */
/// anneal:spec(ensures(ret == x))
pub fn id<'a>(x: usize) -> usize {
    x
}
"####;
        let meta = scan_rust_source(src).unwrap();
        assert_eq!(meta.fn_specs.get("id"), Some(&CapturedSpec::EnsuresEqArg(1)));

        // Reject inner doc comment `//! anneal:spec(...)`.
        assert!(scan_rust_source("//! anneal:spec ensures(ret == x)\npub fn id(x: usize) -> usize { x }\n").is_err());
        // Reject block comment `/* anneal:spec(...) */`.
        assert!(scan_rust_source("/* anneal:spec ensures(ret == x) */\npub fn id(x: usize) -> usize { x }\n").is_err());
        // Reject unknown `anneal:` directive.
        assert!(scan_rust_source("/// anneal:requires(x > 0)\npub fn id(x: usize) -> usize { x }\n").is_err());
        // Reject duplicate `anneal:spec` on the same function.
        assert!(scan_rust_source("// anneal:spec well_formed\n/// anneal:spec ensures(ret == x)\npub fn id(x: usize) -> usize { x }\n").is_err());
        // Reject dangling `anneal:spec` before a struct or at EOF.
        assert!(scan_rust_source("/// anneal:spec ensures(ret == x)\npub struct Foo { x: usize }\n").is_err());
        assert!(scan_rust_source("pub fn id(x: usize) -> usize { x }\n/// anneal:spec ensures(ret == x)\n").is_err());
    }
}
