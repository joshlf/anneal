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
//! This crate belongs to `trusted/`. It invokes `rustc` on the target crate,
//! extracts the lowered `Runtime(PostCleanup)` MIR for the supported vertical
//! slice (`pub fn id(x: usize) -> usize { x }`), and writes `.anneal/Mir.lean`
//! and optional candidate `.anneal/Proof.lean`
//! artifacts consumed by `cargo-anneal`.
//!
//! Every type and extraction helper in this module that interprets `rustc` MIR
//! structures cites its normative `rustc_middle::mir` source at the
//! repository's pinned revision
//! (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

pub mod proof_gen;
pub use proof_gen::render_proof_lean;

use std::env;
use std::fmt::{self, Write as _};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Errors returned when `rustc` compilation or fail-closed MIR extraction
/// rejects a target crate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureError {
    /// I/O error reading source files or writing `.anneal/` artifacts.
    Io(String),
    /// `rustc` exited with a non-zero status code.
    CompilationFailed(String),
    /// The crate or MIR contains a construct outside the supported MIR subset.
    UnsupportedMir(String),
}

impl fmt::Display for CaptureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(msg) => write!(f, "I/O error during MIR capture: {msg}"),
            Self::CompilationFailed(msg) => {
                write!(f, "rustc compilation failed: {msg}")
            }
            Self::UnsupportedMir(msg) => {
                write!(f, "unsupported MIR construct (fail-closed): {msg}")
            }
        }
    }
}

impl std::error::Error for CaptureError {}

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

/// Captured MIR operand .
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapturedSpec {
    /// Baseline well-formedness (`specs := []`, so `MirLang.WellFormedOn fn.pre
    /// :: fn.specs`
    /// reduces to `[Trusted.MirLang.WellFormed]`).
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
    let crate_dir = crate_dir
        .canonicalize()
        .map_err(|e| CaptureError::Io(format!("{}: {e}", crate_dir.display())))?;
    let src_path = crate_dir.join("src/lib.rs");
    let src_text = fs::read_to_string(&src_path).map_err(|e| {
        CaptureError::Io(format!("cannot read {}: {e}", src_path.display()))
    })?;
    let spec = parse_source_spec(&src_text)?;

    let anneal_dir = crate_dir.join(".anneal");
    let build_dir = anneal_dir.join("rustc-out");
    fs::create_dir_all(&build_dir).map_err(|e| {
        CaptureError::Io(format!("cannot create {}: {e}", build_dir.display()))
    })?;
    let mir_dump_path = build_dir.join("crate.mir");
    let rmeta_path = build_dir.join("libcrate.rmeta");

    let rustc_bin = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let output = Command::new(rustc_bin)
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

    let functions = parse_emitted_mir(&mir_text, spec)?;
    if functions.is_empty() {
        return Err(CaptureError::UnsupportedMir(
            "crate contains no captured functions".to_string(),
        ));
    }

    let mir_lean_source = render_mir_lean(&functions);
    let mir_lean_path = anneal_dir.join("Mir.lean");
    fs::write(&mir_lean_path, mir_lean_source.as_bytes()).map_err(|e| {
        CaptureError::Io(format!(
            "cannot write {}: {e}",
            mir_lean_path.display()
        ))
    })?;
    if emit_proof {
        let proof_path = anneal_dir.join("Proof.lean");
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

fn parse_source_spec(src: &str) -> Result<CapturedSpec, CaptureError> {
    let mut found = None;
    for raw_line in src.lines() {
        let line = raw_line.trim();
        if let Some(rest) = line.strip_prefix("// anneal:spec") {
            let clause = rest.trim();
            let parsed = match clause {
                "ensures(ret == x)" => CapturedSpec::EnsuresEqArg(1),
                "well_formed" => CapturedSpec::WellFormed,
                other => {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "unsupported anneal:spec annotation: `{other}`"
                    )));
                }
            };
            if found.is_some() {
                return Err(CaptureError::UnsupportedMir(
                    "multiple anneal:spec annotations in file".to_string(),
                ));
            }
            found = Some(parsed);
        }
    }
    Ok(found.unwrap_or(CapturedSpec::WellFormed))
}

/// Parse the textual `Runtime(PostCleanup)` MIR emitted by `rustc --emit=mir`
/// , failing closed on any unrecognized item,
/// signature, statement, or terminator.
pub fn parse_emitted_mir(
    mir_text: &str,
    spec: CapturedSpec,
) -> Result<Vec<CapturedFunction>, CaptureError> {
    let mut functions = Vec::new();
    let mut lines = mir_text.lines().peekable();

    while let Some(raw_line) = lines.next() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with("//") {
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
                || body_line.starts_with("scope ")
            {
                continue;
            }
            if body_line == "}" {
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
        functions.push(CapturedFunction {
            name,
            arg_tys,
            ret_ty,
            local_count: max_local + 1,
            blocks,
            spec,
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
    if name.is_empty()
        || !name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
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

/// Render the read-only `.anneal/Mir.lean` module defining
/// `Mir.crate : Trusted.Crate`.
pub fn render_mir_lean(functions: &[CapturedFunction]) -> String {
    let mut out = String::from("prelude\nimport Trusted\n\nnamespace Mir\n\n");
    for func in functions {
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
            "def {}_body : Trusted.MirBody where\n  \
             argTys := {}\n  \
             retTy := {}\n  \
             localCount := {}\n  \
             blocks := {}\n",
            func.name,
            render_lean_list(&arg_tys),
            func.ret_ty.to_lean(),
            func.local_count,
            render_lean_list(&blocks),
        );
    }

    let fn_entries: Vec<String> = functions
        .iter()
        .map(|f| {
            format!(
                "{{ name := \"{}\", prog := {}_body, specs := {} }}",
                f.name,
                f.name,
                f.spec.to_lean_specs()
            )
        })
        .collect();
    let tcb_entries: Vec<String> = functions
        .iter()
        .map(|f| {
            format!("Trusted.TCBItem.rustcLowering \"{}\" {}_body", f.name, f.name)
        })
        .collect();
    let _ = writeln!(
        out,
        "def crate : Trusted.Crate where\n  \
         functions := {}\n  \
         tcb := {}\n\n\
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
}
