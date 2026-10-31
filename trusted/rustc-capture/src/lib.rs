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
//! extracts the lowered `Runtime(PostCleanup)` MIR (including compile-time
//! constant bodies referenced for Post-Monomorphization Errors and ADT/function
//! visibility metadata for library verification promises), and writes
//! `.anneal/Mir.lean` and optional candidate `.anneal/Proof.lean` artifacts
//! consumed by `cargo-anneal`.
//!
//! Every type and extraction helper in this module that interprets `rustc` MIR
//! structures cites its normative `rustc_middle::mir` source at the
//! repository's pinned revision
//! (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).

pub mod proof_gen;
pub use proof_gen::render_proof_lean;

use std::collections::BTreeSet;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

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

/// Captured MIR type (`usize`, `bool`, `()`, ADT, generic type parameter, or
/// shared reference to a generic type parameter).
///
/// Corresponds to `Trusted.MirTy` in `trusted/lean/Trusted/MirAst.lean` and
/// `rustc_type_ir::TyKind`:
///
/// > "The `usize` type is an unsigned integer type with the same number of
/// > bits as the platform's pointer type. It can represent every memory
/// > address in the process."
///
/// Sources:
/// - https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/types/numeric.md#L37-L38
/// - https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_type_ir/src/ty_kind.rs#L106-L165
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapturedTy {
    Usize,
    Bool,
    Unit,
    Adt(usize),
    Param(usize),
    RefParam(usize),
}

impl CapturedTy {
    fn to_lean(self) -> String {
        match self {
            Self::Usize => "Trusted.MirTy.usize".to_string(),
            Self::Bool => "Trusted.MirTy.bool".to_string(),
            Self::Unit => "Trusted.MirTy.unit".to_string(),
            Self::Adt(id) => format!("(Trusted.MirTy.adt {id})"),
            Self::Param(idx) => format!("(Trusted.MirTy.param {idx})"),
            Self::RefParam(idx) => {
                format!("(Trusted.MirTy.ref (Trusted.MirTy.param {idx}))")
            }
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
    ConstUnit,
}

impl CapturedOperand {
    fn to_lean(&self) -> String {
        match self {
            Self::Copy(local) => format!("(Trusted.Operand.copy ⟨{local}⟩)"),
            Self::Move(local) => format!("(Trusted.Operand.move ⟨{local}⟩)"),
            Self::ConstUsize(bits) => format!(
                "(Trusted.Operand.constVal (Trusted.MirVal.usize {bits}))"
            ),
            Self::ConstUnit => {
                "(Trusted.Operand.constVal Trusted.MirVal.unit)".to_string()
            }
        }
    }
}

/// Captured MIR statement in a basic block.
///
/// Corresponds to `rustc_middle::mir::StatementKind` (`Assign`, `StorageLive`,
/// `StorageDead`, and `Nop` / `ConstEvalCounter`):
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
    AssignUse {
        dst: usize,
        op: CapturedOperand,
    },
    AssignEq {
        dst: usize,
        lhs: CapturedOperand,
        rhs: CapturedOperand,
    },
    AssignAggregate {
        dst: usize,
        adt_id: usize,
        op: CapturedOperand,
    },
    AssignField0 {
        dst: usize,
        src: usize,
    },
    AssignRef {
        dst: usize,
        src: usize,
    },
    AssignReborrow {
        dst: usize,
        src: usize,
    },
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
            Self::AssignEq { dst, lhs, rhs } => format!(
                "Trusted.Stmt.assign ⟨{dst}⟩ (Trusted.Rvalue.binaryOp Trusted.BinOp.eq {} {})",
                lhs.to_lean(),
                rhs.to_lean()
            ),
            Self::AssignAggregate { dst, adt_id, op } => format!(
                "Trusted.Stmt.assign ⟨{dst}⟩ (Trusted.Rvalue.aggregate {adt_id} {})",
                op.to_lean()
            ),
            Self::AssignField0 { dst, src } => format!(
                "Trusted.Stmt.assign ⟨{dst}⟩ (Trusted.Rvalue.field0 ⟨{src}⟩)"
            ),
            Self::AssignRef { dst, src } => format!(
                "Trusted.Stmt.assign ⟨{dst}⟩ (Trusted.Rvalue.ref ⟨{src}⟩)"
            ),
            Self::AssignReborrow { dst, src } => format!(
                "Trusted.Stmt.assign ⟨{dst}⟩ (Trusted.Rvalue.reborrow ⟨{src}⟩)"
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
/// `Unreachable`, `SwitchInt`, and `Call`):
///
/// > "Block has one successor; we continue execution there."
/// >
/// > "Returns from the function."
/// >
/// > "Indicates a terminator that can never be reached.
/// >
/// > Executing this terminator is UB."
///
/// Source: https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/syntax.rs#L683-L798
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapturedTerminator {
    Return,
    Goto(usize),
    Unreachable,
    Panic,
    SwitchInt {
        discr: CapturedOperand,
        false_target: usize,
        true_target: usize,
    },
    CallSizeOf {
        dst: usize,
        ty: CapturedTy,
        target: usize,
    },
    CallTransmuteCopy {
        dst: usize,
        src_ty: CapturedTy,
        dst_ty: CapturedTy,
        op: CapturedOperand,
        target: usize,
    },
    Call1 {
        dst: usize,
        callee_name: String,
        arg: CapturedOperand,
        target: usize,
    },
}

impl CapturedTerminator {
    fn to_lean(&self) -> String {
        match self {
            Self::Return => "Trusted.Terminator.return_".to_string(),
            Self::Goto(target) => format!("(Trusted.Terminator.goto ⟨{target}⟩)"),
            Self::Unreachable => "Trusted.Terminator.unreachable".to_string(),
            Self::Panic => "Trusted.Terminator.panic".to_string(),
            Self::SwitchInt {
                discr,
                false_target,
                true_target,
            } => format!(
                "(Trusted.Terminator.switchInt {} ⟨{false_target}⟩ ⟨{true_target}⟩)",
                discr.to_lean()
            ),
            Self::CallSizeOf { dst, ty, target } => format!(
                "(Trusted.Terminator.callSizeOf ⟨{dst}⟩ {} ⟨{target}⟩)",
                ty.to_lean()
            ),
            Self::CallTransmuteCopy {
                dst,
                src_ty,
                dst_ty,
                op,
                target,
            } => format!(
                "(Trusted.Terminator.callTransmuteCopy ⟨{dst}⟩ {} {} {} ⟨{target}⟩)",
                src_ty.to_lean(),
                dst_ty.to_lean(),
                op.to_lean()
            ),
            Self::Call1 {
                dst,
                callee_name,
                arg,
                target,
            } => format!(
                "(Trusted.Terminator.call1 ⟨{dst}⟩ {callee_name}_body {} ⟨{target}⟩)",
                arg.to_lean()
            ),
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
    /// Baseline well-formedness (`specs := []`).
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

/// Visibility and safety role of a captured function (`Trusted.FnKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CapturedFnKind {
    /// Public safe function (`pub fn`).
    PubSafe,
    /// Public unsafe function `pub unsafe fn new_unchecked(x: usize) ->
    /// NonZeroUsize`.
    PubUnsafeNewUnchecked,
}

/// Captured MIR function or constant body (`rustc_middle::mir::Body`).
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
    pub is_const: bool,
    pub required_consts: Vec<String>,
    pub kind: CapturedFnKind,
}

/// Crate-level source metadata extracted from `src/lib.rs` (such as ADT field
/// visibility and `pub unsafe fn` headers).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceMetadata {
    pub spec: CapturedSpec,
    /// `Some(true)` if `struct NonZeroUsize` has `pub val: usize`,
    /// `Some(false)` if `val: usize` is private, or `None` if `NonZeroUsize` is
    /// not defined.
    pub nonzero_field_pub_safe: Option<bool>,
    /// Set of function names declared with `pub unsafe fn`.
    pub unsafe_fns: BTreeSet<String>,
}

impl Default for CapturedSpec {
    fn default() -> Self {
        Self::WellFormed
    }
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
    let meta = parse_source_metadata(&src_text)?;

    let anneal_dir = crate_dir.join(".anneal");
    let build_dir = anneal_dir.join("rustc-out");
    fs::create_dir_all(&build_dir).map_err(|e| {
        CaptureError::Io(format!("cannot create {}: {e}", build_dir.display()))
    })?;
    let mir_dump_path = build_dir.join("crate.mir");
    let rmeta_path = build_dir.join("libcrate.rmeta");

    // Pass `-Z mir-opt-level=0` so `rustc`'s `RemoveZsts` and `SimplifyLocals`
    // passes do not strip zero-sized PME constant evaluations (`_2 = const
    // <...>::ASSERT` or `_2 = const ...::{constant#0}`) before MIR emission.
    let rustc_bin = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let output = Command::new(rustc_bin)
        .env("RUSTC_BOOTSTRAP", "1")
        .arg("--edition=2024")
        .arg("--crate-name=anneal_target")
        .arg("--crate-type=lib")
        .arg("-Z")
        .arg("mir-opt-level=0")
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

    let all_items = parse_emitted_mir_with_metadata(&mir_text, &meta)?;
    let functions: Vec<CapturedFunction> = all_items
        .iter()
        .filter(|f| !f.is_const)
        .cloned()
        .collect();
    if functions.is_empty() {
        return Err(CaptureError::UnsupportedMir(
            "crate contains no captured functions".to_string(),
        ));
    }

    let mir_lean_source = render_mir_lean_with_metadata(&all_items, &meta);
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

fn parse_source_metadata(src: &str) -> Result<SourceMetadata, CaptureError> {
    let mut found_spec = None;
    let mut nonzero_field_pub_safe = None;
    let mut unsafe_fns = BTreeSet::new();

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
            if found_spec.is_some() {
                return Err(CaptureError::UnsupportedMir(
                    "multiple anneal:spec annotations in file".to_string(),
                ));
            }
            found_spec = Some(parsed);
        }
        if line.contains("struct NonZeroUsize") {
            if line.contains("pub val: usize") {
                nonzero_field_pub_safe = Some(true);
            } else if line.contains("val: usize") {
                nonzero_field_pub_safe = Some(false);
            } else {
                nonzero_field_pub_safe = Some(false);
            }
        } else if nonzero_field_pub_safe.is_some() {
            if line.starts_with("pub val: usize") {
                nonzero_field_pub_safe = Some(true);
            } else if line.starts_with("val: usize") {
                nonzero_field_pub_safe = Some(false);
            }
        }
        if let Some(after_unsafe) = line.strip_prefix("pub unsafe fn ")
            && let Some((fn_name, _)) = after_unsafe.split_once('(')
        {
            let name = fn_name
                .split('<')
                .next()
                .unwrap_or(fn_name)
                .trim()
                .to_string();
            unsafe_fns.insert(name);
        }
    }

    Ok(SourceMetadata {
        spec: found_spec.unwrap_or(CapturedSpec::WellFormed),
        nonzero_field_pub_safe,
        unsafe_fns,
    })
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

/// Parse the textual `Runtime(PostCleanup)` MIR emitted by `rustc -Z
/// mir-opt-level=0 --emit=mir` along with crate-level [`SourceMetadata`].
pub fn parse_emitted_mir_with_metadata(
    mir_text: &str,
    meta: &SourceMetadata,
) -> Result<Vec<CapturedFunction>, CaptureError> {
    let mut items = Vec::new();
    let mut lines = mir_text.lines().peekable();

    while let Some(raw_line) = lines.next() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        // Skip constant allocation dumps (`alloc1 (size: ..., align: ...)`)
        // emitted after CTFE panic messages.
        if line.starts_with("alloc") && line.ends_with('{') {
            for alloc_line in lines.by_ref() {
                if alloc_line.trim() == "}" {
                    break;
                }
            }
            continue;
        }

        let (name, arg_tys, ret_ty, is_const) = if (line.starts_with("const ")
            || line.contains("::{constant#"))
            && line.ends_with(": () = {")
        {
            ("pme_assert_const".to_string(), Vec::new(), CapturedTy::Unit, true)
        } else if let Some(fn_rest) = line.strip_prefix("fn ") {
            let (n, args, ret) = parse_fn_header(fn_rest)?;
            (n, args, ret, false)
        } else {
            return Err(CaptureError::UnsupportedMir(format!(
                "unexpected top-level MIR line: `{line}`"
            )));
        };

        let mut max_local = arg_tys.len();
        let mut blocks = Vec::new();
        let mut required_consts = Vec::new();

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
                for scope_line in lines.by_ref() {
                    if scope_line.trim() == "}" {
                        break;
                    }
                }
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
                    let (parsed, maybe_const) =
                        parse_stmt_or_terminator(stmt_line)?;
                    if let Some(const_name) = maybe_const
                        && !required_consts.contains(&const_name)
                    {
                        required_consts.push(const_name);
                    }
                    match parsed {
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
        let kind = if meta.unsafe_fns.contains(&name) {
            CapturedFnKind::PubUnsafeNewUnchecked
        } else {
            CapturedFnKind::PubSafe
        };
        items.push(CapturedFunction {
            name,
            arg_tys,
            ret_ty,
            local_count: max_local + 1,
            blocks,
            spec: meta.spec,
            is_const,
            required_consts,
            kind,
        });
    }

    Ok(items)
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
    let raw_name = name_part.trim();
    let name = raw_name
        .rsplit("::")
        .next()
        .unwrap_or(raw_name)
        .trim()
        .to_string();
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
    match ty_str.trim() {
        "usize" => Ok(CapturedTy::Usize),
        "bool" => Ok(CapturedTy::Bool),
        "()" | "!" => Ok(CapturedTy::Unit),
        "NonZeroUsize" => Ok(CapturedTy::Adt(0)),
        "Src" => Ok(CapturedTy::Param(0)),
        "Dst" => Ok(CapturedTy::Param(1)),
        "&Src" => Ok(CapturedTy::RefParam(0)),
        "&Dst" => Ok(CapturedTy::RefParam(1)),
        other => Err(CaptureError::UnsupportedMir(format!(
            "unsupported MIR type `{other}`"
        ))),
    }
}

enum StmtOrTerm {
    Stmt(CapturedStmt),
    Term(CapturedTerminator),
}

fn parse_stmt_or_terminator(
    line: &str,
) -> Result<(StmtOrTerm, Option<String>), CaptureError> {
    let stmt = line.strip_suffix(';').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "missing semicolon in MIR statement/terminator: `{line}`"
        ))
    })?;
    if stmt == "return" {
        return Ok((StmtOrTerm::Term(CapturedTerminator::Return), None));
    }
    if stmt == "unreachable" {
        return Ok((StmtOrTerm::Term(CapturedTerminator::Unreachable), None));
    }
    if let Some(target_str) = stmt.strip_prefix("goto -> ") {
        let target = parse_bb_index(target_str.trim())?;
        return Ok((StmtOrTerm::Term(CapturedTerminator::Goto(target)), None));
    }
    if stmt == "nop" || stmt == "ConstEvalCounter" {
        return Ok((StmtOrTerm::Stmt(CapturedStmt::Nop), None));
    }
    if let Some(sw_rest) = stmt.strip_prefix("switchInt(") {
        let (discr_str, targets_part) =
            sw_rest.split_once(") -> [").ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "malformed switchInt terminator `{line}`"
                ))
            })?;
        let discr = parse_operand(discr_str.trim())?;
        let targets_inner =
            targets_part.strip_suffix(']').ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "unclosed switchInt target list in `{line}`"
                ))
            })?;
        let (zero_arm, otherwise_arm) =
            targets_inner.split_once(',').ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "expected two arms in switchInt `{line}`"
                ))
            })?;
        let false_bb_str =
            zero_arm.trim().strip_prefix("0:").ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "expected `0: bbN` arm in switchInt `{line}`"
                ))
            })?;
        let true_bb_str = otherwise_arm
            .trim()
            .strip_prefix("otherwise:")
            .ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "expected `otherwise: bbM` arm in switchInt `{line}`"
                ))
            })?;
        let false_target = parse_bb_index(false_bb_str.trim())?;
        let true_target = parse_bb_index(true_bb_str.trim())?;
        return Ok((
            StmtOrTerm::Term(CapturedTerminator::SwitchInt {
                discr,
                false_target,
                true_target,
            }),
            None,
        ));
    }
    if let Some(inner) = stmt
        .strip_prefix("StorageLive(")
        .and_then(|s| s.strip_suffix(')'))
    {
        return Ok((
            StmtOrTerm::Stmt(CapturedStmt::StorageLive(parse_local_token(
                inner.trim(),
            )?)),
            None,
        ));
    }
    if let Some(inner) = stmt
        .strip_prefix("StorageDead(")
        .and_then(|s| s.strip_suffix(')'))
    {
        return Ok((
            StmtOrTerm::Stmt(CapturedStmt::StorageDead(parse_local_token(
                inner.trim(),
            )?)),
            None,
        ));
    }
    if let Some((lhs, rhs)) = stmt.split_once('=') {
        let dst = parse_local_token(lhs.trim())?;
        let rhs = rhs.trim();

        // Check call terminators (`_dst = callee(...) -> ...`) first.
        if rhs.contains("->") {
            if rhs.ends_with("unreachable_unchecked() -> unwind continue") {
                return Ok((
                    StmtOrTerm::Term(CapturedTerminator::Unreachable),
                    None,
                ));
            }
            if rhs.starts_with("panic(")
                && rhs.ends_with(") -> unwind continue")
            {
                return Ok((StmtOrTerm::Term(CapturedTerminator::Panic), None));
            }
            if let Some((call_part, after_ret)) =
                rhs.split_once(") -> [return: ")
                && let Some(target_str) =
                    after_ret.strip_suffix(", unwind continue]")
            {
                let target = parse_bb_index(target_str.trim())?;
                if let Some(sz_rest) = call_part
                    .strip_prefix("std::mem::size_of::<")
                    .or_else(|| call_part.strip_prefix("core::mem::size_of::<"))
                    && let Some(ty_str) = sz_rest.strip_suffix(">(")
                {
                    let ty = parse_ty(ty_str.trim())?;
                    return Ok((
                        StmtOrTerm::Term(CapturedTerminator::CallSizeOf {
                            dst,
                            ty,
                            target,
                        }),
                        None,
                    ));
                }
                if let Some(tc_rest) = call_part
                    .strip_prefix("transmute_copy::<")
                    .or_else(|| {
                        call_part.strip_prefix("std::mem::transmute_copy::<")
                    })
                    .or_else(|| {
                        call_part.strip_prefix("core::mem::transmute_copy::<")
                    })
                    && let Some((tys_part, arg_str)) = tc_rest.split_once(">(")
                    && let Some((src_ty_str, dst_ty_str)) =
                        tys_part.split_once(',')
                {
                    let src_ty = parse_ty(src_ty_str.trim())?;
                    let dst_ty = parse_ty(dst_ty_str.trim())?;
                    let op = parse_operand(arg_str.trim())?;
                    return Ok((
                        StmtOrTerm::Term(
                            CapturedTerminator::CallTransmuteCopy {
                                dst,
                                src_ty,
                                dst_ty,
                                op,
                                target,
                            },
                        ),
                        None,
                    ));
                }
                if let Some((callee_raw, arg_str)) = call_part.split_once('(') {
                    let callee_base = callee_raw
                        .split("::<")
                        .next()
                        .unwrap_or(callee_raw)
                        .trim();
                    let callee_name = callee_base
                        .rsplit("::")
                        .next()
                        .unwrap_or(callee_base)
                        .trim()
                        .to_string();
                    if !callee_name.is_empty()
                        && callee_name
                            .chars()
                            .all(|c| c.is_ascii_alphanumeric() || c == '_')
                    {
                        let arg = parse_operand(arg_str.trim())?;
                        return Ok((
                            StmtOrTerm::Term(CapturedTerminator::Call1 {
                                dst,
                                callee_name,
                                arg,
                                target,
                            }),
                            None,
                        ));
                    }
                }
            }
            return Err(CaptureError::UnsupportedMir(format!(
                "unsupported MIR call terminator: `{line}`"
            )));
        }

        // Check PME constant reference (`_2 = const <...>::ASSERT` or
        // `_2 = const fn_name::<Src, Dst>::{constant#0}`).
        if rhs.starts_with("const ")
            && (rhs.ends_with("::ASSERT") || rhs.contains("::{constant#"))
        {
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignUse {
                    dst,
                    op: CapturedOperand::ConstUnit,
                }),
                Some("pme_assert_const".to_string()),
            ));
        }

        // Check `Eq(lhs, rhs)`.
        if let Some(eq_inner) =
            rhs.strip_prefix("Eq(").and_then(|s| s.strip_suffix(')'))
            && let Some((lhs_str, rhs_str)) = eq_inner.split_once(',')
        {
            let lhs_op = parse_operand(lhs_str.trim())?;
            let rhs_op = parse_operand(rhs_str.trim())?;
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignEq {
                    dst,
                    lhs: lhs_op,
                    rhs: rhs_op,
                }),
                None,
            ));
        }

        // Check `NonZeroUsize { val: <op> }`.
        if let Some(agg_inner) = rhs
            .strip_prefix("NonZeroUsize { val:")
            .and_then(|s| s.strip_suffix('}'))
        {
            let op = parse_operand(agg_inner.trim())?;
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignAggregate {
                    dst,
                    adt_id: 0,
                    op,
                }),
                None,
            ));
        }

        // Check field projection `copy (_1.0: usize)`.
        if let Some(proj_inner) = rhs
            .strip_prefix("copy (")
            .and_then(|s| s.strip_suffix(".0: usize)"))
        {
            let src = parse_local_token(proj_inner.trim())?;
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignField0 { dst, src }),
                None,
            ));
        }

        // Check shared reborrow `&(*_x)`.
        if let Some(reb_inner) =
            rhs.strip_prefix("&(*").and_then(|s| s.strip_suffix(')'))
        {
            let src = parse_local_token(reb_inner.trim())?;
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignReborrow { dst, src }),
                None,
            ));
        }

        // Check shared borrow `&_x`.
        if let Some(ref_inner) = rhs.strip_prefix('&') {
            let src = parse_local_token(ref_inner.trim())?;
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignRef { dst, src }),
                None,
            ));
        }

        let op = parse_operand(rhs)?;
        return Ok((
            StmtOrTerm::Stmt(CapturedStmt::AssignUse { dst, op }),
            None,
        ));
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
    if rhs == "const ()" {
        return Ok(CapturedOperand::ConstUnit);
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
    render_mir_lean_with_metadata(functions, &SourceMetadata::default())
}

/// Render the read-only `.anneal/Mir.lean` module defining
/// `Mir.crate : Trusted.Crate` with crate-level ADT and library invariant
/// metadata.
pub fn render_mir_lean_with_metadata(
    items: &[CapturedFunction],
    meta: &SourceMetadata,
) -> String {
    let mut out = String::from("prelude\nimport Trusted\n\nnamespace Mir\n\n");

    // Emit constant MIR bodies before function MIR bodies so `requiredConsts`
    // references (`pme_assert_const_body`) are in scope regardless of the order
    // in which `rustc --emit=mir` printed them.
    for is_const_pass in [true, false] {
        for func in items.iter().filter(|f| f.is_const == is_const_pass) {
            let arg_tys: Vec<String> = func
                .arg_tys
                .iter()
                .map(|t| t.to_lean())
                .collect();
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
            if func.required_consts.is_empty() {
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
            } else {
                let req_consts: Vec<String> = func
                    .required_consts
                    .iter()
                    .map(|c| format!("{c}_body"))
                    .collect();
                let _ = writeln!(
                    out,
                    "def {}_body : Trusted.MirBody where\n  \
                     argTys := {}\n  \
                     retTy := {}\n  \
                     localCount := {}\n  \
                     blocks := {}\n  \
                     requiredConsts := {}\n",
                    func.name,
                    render_lean_list(&arg_tys),
                    func.ret_ty.to_lean(),
                    func.local_count,
                    render_lean_list(&blocks),
                    render_lean_list(&req_consts),
                );
            }
        }
    }

    if meta.nonzero_field_pub_safe.is_some() {
        let _ = writeln!(
            out,
            "abbrev nonZeroAdtInv : Trusted.AdtInv :=\n  \
             fun id v =>\n    \
             match id, v with\n    \
             | 0, .usize n => n ≠ 0\n    \
             | _, _ => False\n\n\
             abbrev newUncheckedSafetyPre (q : Trusted.ExecQuery Trusted.MirState) : Prop :=\n  \
             ∀ n, q.init.locals 1 = some (.usize n) → n ≠ 0\n"
        );
    }

    let runtime_fns: Vec<&CapturedFunction> =
        items.iter().filter(|f| !f.is_const).collect();
    let fn_entries: Vec<String> = runtime_fns
        .iter()
        .map(|f| match f.kind {
            CapturedFnKind::PubSafe => format!(
                "{{ name := \"{}\", prog := {}_body, specs := {} }}",
                f.name,
                f.name,
                f.spec.to_lean_specs()
            ),
            CapturedFnKind::PubUnsafeNewUnchecked => format!(
                "{{ name := \"{}\", prog := {}_body, kind := Trusted.FnKind.pubUnsafe True newUncheckedSafetyPre, specs := {} }}",
                f.name,
                f.name,
                f.spec.to_lean_specs()
            ),
        })
        .collect();
    let tcb_entries: Vec<String> = runtime_fns
        .iter()
        .map(|f| {
            format!("Trusted.TCBItem.rustcLowering \"{}\" {}_body", f.name, f.name)
        })
        .collect();

    if let Some(is_pub_safe) = meta.nonzero_field_pub_safe {
        let access_str = if is_pub_safe {
            "Trusted.FieldAccess.pubSafe"
        } else {
            "Trusted.FieldAccess.priv"
        };
        let _ = writeln!(
            out,
            "def crate : Trusted.Crate where\n  \
             adts := [{{ id := 0, fields := [{{ ty := Trusted.MirTy.usize, access := {access_str} }}] }}]\n  \
             adtInv := nonZeroAdtInv\n  \
             functions := {}\n  \
             tcb := {}\n\n\
             end Mir",
            render_lean_list(&fn_entries),
            render_lean_list(&tcb_entries),
        );
    } else {
        let _ = writeln!(
            out,
            "def crate : Trusted.Crate where\n  \
             functions := {}\n  \
             tcb := {}\n\n\
             end Mir",
            render_lean_list(&fn_entries),
            render_lean_list(&tcb_entries),
        );
    }
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
