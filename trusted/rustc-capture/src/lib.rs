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

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Allowlisted environment variables forwarded to child `rustc` invocations.
const SANITIZED_ENV_ALLOWLIST: &[&str] = &[
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

/// Configuration options for [`capture_crate_with_config`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CaptureOptions {
    /// Whether to emit `.anneal/Proof.lean` alongside `.anneal/Mir.lean`.
    pub emit_proof: bool,
    /// Optional explicit path to the pinned `rustc` binary.
    pub rustc_bin: Option<PathBuf>,
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

    fn to_lean_in_list(self) -> String {
        match self {
            Self::Adt(id) => format!("Trusted.MirTy.adt {id}"),
            Self::Param(idx) => format!("Trusted.MirTy.param {idx}"),
            Self::RefParam(idx) => {
                format!("Trusted.MirTy.ref (Trusted.MirTy.param {idx})")
            }
            other => other.to_lean(),
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
                "Trusted.Stmt.assign ⟨{dst}⟩ \
                 (Trusted.Rvalue.binaryOp Trusted.BinOp.eq {} {})",
                lhs.to_lean(),
                rhs.to_lean()
            ),
            Self::AssignAggregate { dst, adt_id, op } => format!(
                "Trusted.Stmt.assign ⟨{dst}⟩ \
                 (Trusted.Rvalue.aggregate {adt_id} {})",
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
        type_args: Vec<CapturedTy>,
    },
}

impl CapturedTerminator {
    fn to_lean(&self) -> String {
        match self {
            Self::Return => "Trusted.Terminator.return_".to_string(),
            Self::Goto(target) => {
                format!("(Trusted.Terminator.goto ⟨{target}⟩)")
            }
            Self::Unreachable => "Trusted.Terminator.unreachable".to_string(),
            Self::Panic => "Trusted.Terminator.panic".to_string(),
            Self::SwitchInt {
                discr,
                false_target,
                true_target,
            } => format!(
                "(Trusted.Terminator.switchInt {} \
                 ⟨{false_target}⟩ ⟨{true_target}⟩)",
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
                "(Trusted.Terminator.callTransmuteCopy ⟨{dst}⟩ \
                 {} {} {} ⟨{target}⟩)",
                src_ty.to_lean(),
                dst_ty.to_lean(),
                op.to_lean()
            ),
            Self::Call1 {
                dst,
                callee_name,
                arg,
                target,
                type_args,
            } => {
                if type_args.is_empty() {
                    format!(
                        "(Trusted.Terminator.call1 ⟨{dst}⟩ \
                         {callee_name}_body {} ⟨{target}⟩)",
                        arg.to_lean()
                    )
                } else {
                    let tys: Vec<String> = type_args
                        .iter()
                        .map(|t| t.to_lean_in_list())
                        .collect();
                    format!(
                        "(Trusted.Terminator.call1 ⟨{dst}⟩ \
                         {callee_name}_body {} ⟨{target}⟩ {})",
                        arg.to_lean(),
                        render_lean_list(&tys)
                    )
                }
            }
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

impl Default for CapturedSpec {
    fn default() -> Self {
        Self::WellFormed
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
    pub required_consts: Vec<(String, Vec<CapturedTy>)>,
    pub kind: CapturedFnKind,
}

/// Classification of the `Self` type in a trait implementation header (`impl
/// Trait for SelfTy`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SelfTyKind {
    /// The unit type `()`.
    Unit,
    /// A generic type parameter declared on the `impl` block.
    Param,
    /// A concrete named type (such as `NonZeroUsize` or `usize`).
    Named(String),
}

/// Source-level metadata for an associated `const` inside a trait `impl` block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplConstMeta {
    /// 1-based start line of the `impl` block in `src/lib.rs`.
    pub start_line: usize,
    /// 1-based end line of the `impl` block in `src/lib.rs`.
    pub end_line: usize,
    /// Unqualified trait identifier (`SizeEq`, etc.).
    pub trait_name: String,
    /// Associated constant identifier (`ASSERT`, etc.).
    pub const_name: String,
    /// Classification of the `Self` type (`()`, type parameter, or named type).
    pub self_ty_kind: SelfTyKind,
    /// Raw `Self` type token (`"()"` or identifier).
    pub self_ty_name: String,
    /// Generic type parameter names declared on `impl<...>` in declaration
    /// order.
    pub impl_params: Vec<String>,
    /// Type argument identifiers written on `Trait<...>` in the `impl` header.
    pub trait_args: Vec<String>,
}

/// Crate-level source metadata extracted from `src/lib.rs` (such as ADT field
/// visibility, `unsafe fn` headers, generic parameters, and trait associated
/// constants).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceMetadata {
    pub spec: CapturedSpec,
    /// `Some(true)` if `struct NonZeroUsize` has `pub val: usize`,
    /// `Some(false)` if `val: usize` is private or crate-restricted, or `None`
    /// if `NonZeroUsize` is not defined.
    pub nonzero_field_pub_safe: Option<bool>,
    /// Set of function names declared with `unsafe fn`.
    pub unsafe_fns: BTreeSet<String>,
    /// Per-function generic type parameter names in declaration order.
    pub fn_generics: BTreeMap<String, Vec<String>>,
    /// Associated constants defined inside trait `impl` blocks.
    pub impl_consts: Vec<ImplConstMeta>,
    /// Whether `rustc` must be invoked with `-Z mir-opt-level=0` to preserve
    /// zero-sized PME constant evaluations or multi-block library control flow.
    pub needs_unoptimized_mir: bool,
    /// Exact source text of `src/lib.rs` for `Trusted.Crate.artifacts`.
    pub src_text: String,
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
    let meta = parse_source_metadata(&src_text)?;

    let anneal_dir = crate_dir.join(".anneal");
    let build_dir = anneal_dir.join("rustc-out");
    fs::create_dir_all(&build_dir).map_err(|e| {
        CaptureError::Io(format!("cannot create {}: {e}", build_dir.display()))
    })?;
    let mir_dump_path = build_dir.join("crate.mir");
    let rmeta_path = build_dir.join("libcrate.rmeta");

    // Pass `-Z mir-opt-level=0` when the crate contains constants, traits,
    // ADTs, unsafe blocks, control flow, or multiple functions so `rustc`'s
    // `RemoveZsts` and `SimplifyLocals` passes do not strip zero-sized PME
    // constant evaluations (`_2 = const <...>::ASSERT` or `_2 = const
    // ...::{constant#0}`) before MIR emission. Single-function pure crates
    // (`pub fn id`, `pub fn alloc_passthrough`) run at default MIR optimization
    // so temporary `let` bindings collapse to canonical `idCopyBody`.
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
    cmd.env("RUSTC_BOOTSTRAP", "1")
        .arg("--edition=2024")
        .arg("--crate-name=anneal_target")
        .arg("--crate-type=lib");
    if meta.needs_unoptimized_mir {
        cmd.arg("-Z").arg("mir-opt-level=0");
    }
    let output = cmd
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

/// Lexical token from `src/lib.rs` with comments and string literals separated
/// from item syntax.
///
/// Follows the Rust Reference lexical grammar for comments and string literals:
///
/// > "Comments in Rust code follow the general C++ style of line (`//`) and
/// > block (`/* ... */`) comment forms. Nested block comments are supported."
///
/// Source:
/// https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/comments.md#L1-L20
#[derive(Debug, Clone, PartialEq, Eq)]
enum LexToken {
    /// A doc comment (`/// ...`, `//! ...`, `/** ... */`, `/*! ... */`) or a
    /// standalone `// anneal:...` directive comment.
    DocComment(String),
    /// An identifier or keyword (`pub`, `fn`, `struct`, `impl`, `id`, ...).
    Ident(String),
    /// A lifetime token (`'a`, `'static`).
    Lifetime(String),
    /// A single punctuation character (`{`, `}`, `(`, `)`, `[`, `]`, `<`, `>`,
    /// `:`, `;`, `,`, `#`, etc.).
    Punct(char),
    /// A string, raw string, byte string, or character literal.
    Literal,
}

/// A [`LexToken`] paired with its 1-based starting line number in `src/lib.rs`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SpannedToken {
    token: LexToken,
    line: usize,
}

/// Tokenize `src/lib.rs` into [`SpannedToken`]s, stripping non-documentation
/// comments (`// ...`, `/* ... */`) and collapsing string, raw string, byte
/// string, character, and numeric literals into [`LexToken::Literal`] so code
/// or `anneal:spec` text embedded inside comments or string literals is never
/// misinterpreted as item syntax.
///
/// Follows the Rust Reference lexical rules for comments, string literals, raw
/// string literals, and character/lifetime tokens:
///
/// > "Comments in Rust code follow the general C++ style of line (`//`) and
/// > block (`/* ... */`) comment forms. Nested block comments are supported."
/// >
/// > "Line doc comments beginning with exactly three slashes (`///`), and block
/// > doc comments (`/** ... */`), are interpreted as a syntax sugar for doc
/// > attributes."
///
/// Source:
/// https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/comments.md#L1-L29
fn lex_rust_source(src: &str) -> Result<Vec<SpannedToken>, CaptureError> {
    let bytes = src.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    let mut line = 1usize;
    let mut tokens = Vec::new();

    while i < len {
        let b = bytes[i];
        if b == b'\n' {
            line += 1;
            i += 1;
            continue;
        }
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }

        // Line comments (`//`, `///`, `//!`).
        if i + 1 < len && b == b'/' && bytes[i + 1] == b'/' {
            let token_line = line;
            let start = i;
            i += 2;
            while i < len && bytes[i] != b'\n' {
                i += 1;
            }
            let comment_slice = &src[start..i];
            let after_slashes = &comment_slice[2..];
            let is_doc = (after_slashes.starts_with('/')
                && !after_slashes.starts_with("//"))
                || after_slashes.starts_with('!')
                || after_slashes.trim_start().starts_with("anneal:");
            if is_doc {
                let text = after_slashes
                    .strip_prefix('/')
                    .or_else(|| after_slashes.strip_prefix('!'))
                    .unwrap_or(after_slashes)
                    .trim()
                    .to_string();
                tokens.push(SpannedToken {
                    token: LexToken::DocComment(text),
                    line: token_line,
                });
            }
            continue;
        }

        // Block comments (`/* ... */`, `/** ... */`, `/*! ... */`) with
        // nesting.
        if i + 1 < len && b == b'/' && bytes[i + 1] == b'*' {
            let token_line = line;
            let start = i;
            i += 2;
            let mut depth = 1usize;
            while i < len && depth > 0 {
                if i + 1 < len && bytes[i] == b'/' && bytes[i + 1] == b'*' {
                    depth += 1;
                    i += 2;
                } else if i + 1 < len
                    && bytes[i] == b'*'
                    && bytes[i + 1] == b'/'
                {
                    depth -= 1;
                    i += 2;
                } else {
                    if bytes[i] == b'\n' {
                        line += 1;
                    }
                    let ch_len = src[i..]
                        .chars()
                        .next()
                        .map_or(1, char::len_utf8);
                    i += ch_len;
                }
            }
            if depth != 0 {
                return Err(CaptureError::UnsupportedMir(
                    "unterminated block comment in source".to_string(),
                ));
            }
            let comment_slice = &src[start..i];
            let inner = &comment_slice[2..comment_slice.len() - 2];
            let is_doc = (inner.starts_with('*') && !inner.starts_with("**"))
                || inner.starts_with('!');
            if is_doc {
                let text = inner[1..].trim().to_string();
                tokens.push(SpannedToken {
                    token: LexToken::DocComment(text),
                    line: token_line,
                });
            }
            continue;
        }

        // Raw string literals (`r"..."`, `r#"..."#`, `br"..."`, `br#"..."#`,
        // `cr"..."`, `cr#"..."#`).
        if (b == b'r'
            || ((b == b'b' || b == b'c')
                && i + 1 < len
                && bytes[i + 1] == b'r'))
            && let Some((next_i, newlines)) = try_consume_raw_string(src, i)
        {
            tokens.push(SpannedToken {
                token: LexToken::Literal,
                line,
            });
            line += newlines;
            i = next_i;
            continue;
        }

        // Normal string literals (`"..."`, `b"..."`, `c"..."`).
        if b == b'"'
            || ((b == b'b' || b == b'c')
                && i + 1 < len
                && bytes[i + 1] == b'"')
        {
            let token_line = line;
            if b != b'"' {
                i += 1;
            }
            i += 1; // skip opening `"`
            let mut closed = false;
            while i < len {
                if bytes[i] == b'\\' {
                    if i + 1 < len && bytes[i + 1] == b'\n' {
                        line += 1;
                    }
                    i += 2.min(len - i);
                } else if bytes[i] == b'"' {
                    i += 1;
                    closed = true;
                    break;
                } else {
                    if bytes[i] == b'\n' {
                        line += 1;
                    }
                    let ch_len = src[i..]
                        .chars()
                        .next()
                        .map_or(1, char::len_utf8);
                    i += ch_len;
                }
            }
            if !closed {
                return Err(CaptureError::UnsupportedMir(
                    "unterminated string literal in source".to_string(),
                ));
            }
            tokens.push(SpannedToken {
                token: LexToken::Literal,
                line: token_line,
            });
            continue;
        }

        // Character literals (`'a'`, `'\''`, `b'a'`) vs lifetimes (`'a`).
        if b == b'\''
            || (b == b'b' && i + 1 < len && bytes[i + 1] == b'\'')
        {
            let token_line = line;
            let quote_pos = if b == b'b' { i + 1 } else { i };
            if let Some(after_char) = try_consume_char_literal(src, quote_pos) {
                tokens.push(SpannedToken {
                    token: LexToken::Literal,
                    line: token_line,
                });
                i = after_char;
                continue;
            }
            if b == b'\'' {
                let start = i;
                i += 1;
                while i < len
                    && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_')
                {
                    i += 1;
                }
                tokens.push(SpannedToken {
                    token: LexToken::Lifetime(src[start..i].to_string()),
                    line: token_line,
                });
                continue;
            }
        }

        // Identifiers and keywords.
        if b.is_ascii_alphabetic() || b == b'_' {
            let token_line = line;
            let start = i;
            i += 1;
            while i < len
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_')
            {
                i += 1;
            }
            tokens.push(SpannedToken {
                token: LexToken::Ident(src[start..i].to_string()),
                line: token_line,
            });
            continue;
        }

        // Numeric literals (`0`, `1_usize`, etc.).
        if b.is_ascii_digit() {
            let token_line = line;
            while i < len
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_')
            {
                i += 1;
            }
            tokens.push(SpannedToken {
                token: LexToken::Literal,
                line: token_line,
            });
            continue;
        }

        let ch = src[i..].chars().next().unwrap();
        tokens.push(SpannedToken {
            token: LexToken::Punct(ch),
            line,
        });
        i += ch.len_utf8();
    }

    Ok(tokens)
}

/// Attempt to consume a Rust raw string (`r#"..."#`), raw byte string
/// (`br#"..."#`), or raw C string (`cr#"..."#`) starting at byte index `start`,
/// returning `(end_index, newline_count)` on match.
///
/// Follows the Rust Reference grammar for raw string literals:
///
/// > "Raw string literals do not process any escapes. They start with the
/// > character `U+0072` (`r`), followed by fewer than 256 of the character
/// > `U+0023` (`#`), and a `U+0022` (double-quote) character. The raw string
/// > body can contain any sequence of Unicode characters and is terminated
/// > only by another `U+0022` (double-quote) character, followed by the same
/// > number of `U+0023` (`#`) characters that preceded the opening `U+0022`
/// > (double-quote) character."
///
/// Source:
/// https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/tokens.md#L214-L221
fn try_consume_raw_string(src: &str, start: usize) -> Option<(usize, usize)> {
    let bytes = src.as_bytes();
    let len = bytes.len();
    let mut i = start;
    if bytes[i] == b'b' || bytes[i] == b'c' {
        i += 1;
    }
    if i >= len || bytes[i] != b'r' {
        return None;
    }
    i += 1;
    let mut hashes = 0usize;
    while i < len && bytes[i] == b'#' {
        hashes += 1;
        i += 1;
    }
    if i >= len || bytes[i] != b'"' {
        return None;
    }
    i += 1;
    let mut newlines = 0usize;
    while i < len {
        if bytes[i] == b'\n' {
            newlines += 1;
        }
        if bytes[i] == b'"' && i + hashes < len {
            let mut matched = true;
            for h in 0..hashes {
                if bytes[i + 1 + h] != b'#' {
                    matched = false;
                    break;
                }
            }
            if matched {
                return Some((i + 1 + hashes, newlines));
            }
        }
        let ch_len = src[i..].chars().next().map_or(1, char::len_utf8);
        i += ch_len;
    }
    None
}

/// Attempt to consume a character literal (`'a'`, `'\n'`, `b'a'`) whose opening
/// single quote is at `quote_pos`, distinguishing it from a lifetime token
/// (`'a`) by checking for a matching closing single quote on the same line.
///
/// Follows the Rust Reference grammar for character and byte literals:
///
/// > "A character literal is a single Unicode character enclosed within two
/// > `U+0027` (single-quote) characters, with the exception of `U+0027` itself,
/// > which must be escaped by a preceding `U+005C` (`\`) character."
///
/// Source:
/// https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/tokens.md#L121-L125
fn try_consume_char_literal(src: &str, quote_pos: usize) -> Option<usize> {
    let rest = &src[quote_pos + 1..];
    let mut chars = rest.char_indices();
    let (_, first) = chars.next()?;
    if first == '\\' {
        let (_, _) = chars.next()?;
        for (idx, ch) in chars {
            if ch == '\'' {
                return Some(quote_pos + 1 + idx + 1);
            }
            if ch == '\n' || idx > 10 {
                return None;
            }
        }
        None
    } else if first != '\'' && first != '\n' {
        let (idx, second) = chars.next()?;
        if second == '\'' {
            Some(quote_pos + 1 + idx + 1)
        } else {
            None
        }
    } else {
        None
    }
}

/// Extract source-level metadata (`anneal:spec` directives, `NonZeroUsize`
/// field visibility, `unsafe fn` declarations, per-function generic type
/// parameters, and trait `impl` associated constants) from `src/lib.rs`,
/// failing closed on unsupported Rust item constructs (`enum`, `union`, `unsafe
/// trait`, `unsafe impl`, tuple/unit structs, or `impl` methods).
pub fn parse_source_metadata(src: &str) -> Result<SourceMetadata, CaptureError> {
    let tokens = lex_rust_source(src)?;
    let mut found_spec = None;
    let mut nonzero_field_pub_safe = None;
    let mut unsafe_fns = BTreeSet::new();
    let mut fn_generics = BTreeMap::new();
    let mut impl_consts = Vec::new();
    let mut fn_count = 0usize;
    let mut has_complex_tokens = false;

    for sp in &tokens {
        if let LexToken::Ident(kw) = &sp.token
            && matches!(
                kw.as_str(),
                "const"
                    | "trait"
                    | "impl"
                    | "struct"
                    | "unsafe"
                    | "if"
                    | "match"
                    | "loop"
                    | "while"
            )
        {
            has_complex_tokens = true;
        }
    }

    // 1. Validate all `anneal:` doc comments and ensure each is attached to a
    //    subsequent `fn` item.
    for (idx, sp) in tokens.iter().enumerate() {
        let LexToken::DocComment(text) = &sp.token else {
            continue;
        };
        for raw_line in text.lines() {
            let line = raw_line.trim();
            if let Some(rest) = line.strip_prefix("anneal:") {
                let Some(spec_rest) = rest.strip_prefix("spec") else {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "unsupported anneal directive: `anneal:{rest}`"
                    )));
                };
                let clause = spec_rest.trim();
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
                if !is_attached_to_fn(&tokens, idx + 1) {
                    return Err(CaptureError::UnsupportedMir(
                        "anneal:spec comment must be attached to a function"
                            .to_string(),
                    ));
                }
                found_spec = Some(parsed);
            }
        }
    }

    // 2. Walk top-level items to extract struct fields, trait impl constants,
    //    and function signatures.
    let mut i = 0usize;
    let len = tokens.len();
    while i < len {
        // Skip doc comments and outer/inner attributes `#[...]` / `#![...]`.
        if matches!(tokens[i].token, LexToken::DocComment(_)) {
            i += 1;
            continue;
        }
        if tokens[i].token == LexToken::Punct('#') {
            i = skip_attribute(&tokens, i)?;
            continue;
        }

        // Parse optional item visibility (`pub`, `pub(...)`) and item
        // modifiers (`unsafe`, `const`, `async`, `extern`).
        let mut is_unsafe_item = false;
        let mut is_const_item = false;
        loop {
            if i >= len {
                break;
            }
            match &tokens[i].token {
                LexToken::DocComment(_) => {
                    i += 1;
                }
                LexToken::Punct('#') => {
                    i = skip_attribute(&tokens, i)?;
                }
                LexToken::Ident(kw) if kw == "pub" => {
                    i += 1;
                    if i < len && tokens[i].token == LexToken::Punct('(') {
                        i = skip_balanced_delim(&tokens, i, '(', ')')?;
                    }
                }
                LexToken::Ident(kw) if kw == "unsafe" => {
                    is_unsafe_item = true;
                    i += 1;
                }
                LexToken::Ident(kw) if kw == "const" => {
                    is_const_item = true;
                    i += 1;
                    break;
                }
                LexToken::Ident(kw) if kw == "async" || kw == "extern" => {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "unsupported `{kw}` item in crate"
                    )));
                }
                _ => break,
            }
        }
        if i >= len {
            break;
        }

        // Top-level `const NAME: () = ...;` item.
        if is_const_item {
            if let LexToken::Ident(next_kw) = &tokens[i].token
                && next_kw == "fn"
            {
                return Err(CaptureError::UnsupportedMir(
                    "`const fn` is not supported".to_string(),
                ));
            }
            i = skip_until_top_level_semi(&tokens, i)?;
            continue;
        }

        let LexToken::Ident(item_kw) = &tokens[i].token else {
            return Err(CaptureError::UnsupportedMir(format!(
                "unexpected token at top level on line {}: {:?}",
                tokens[i].line, tokens[i].token
            )));
        };

        match item_kw.as_str() {
            "enum" | "union" => {
                return Err(CaptureError::UnsupportedMir(format!(
                    "`{item_kw}` definitions are not supported"
                )));
            }
            "trait" => {
                if is_unsafe_item {
                    return Err(CaptureError::UnsupportedMir(
                        "`unsafe trait` is not supported".to_string(),
                    ));
                }
                i = parse_trait_item(&tokens, i)?;
            }
            "struct" => {
                let (next_i, is_pub_safe) = parse_struct_item(&tokens, i)?;
                if nonzero_field_pub_safe.is_some() {
                    return Err(CaptureError::UnsupportedMir(
                        "multiple struct definitions are not supported"
                            .to_string(),
                    ));
                }
                nonzero_field_pub_safe = Some(is_pub_safe);
                i = next_i;
            }
            "impl" => {
                if is_unsafe_item {
                    return Err(CaptureError::UnsupportedMir(
                        "`unsafe impl` is not supported".to_string(),
                    ));
                }
                let (next_i, mut consts) = parse_impl_item(&tokens, i)?;
                impl_consts.append(&mut consts);
                i = next_i;
            }
            "fn" => {
                fn_count += 1;
                let (next_i, fn_name, generics) = parse_fn_item(&tokens, i)?;
                if is_unsafe_item {
                    unsafe_fns.insert(fn_name.clone());
                }
                if fn_generics.insert(fn_name.clone(), generics).is_some() {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "duplicate function definition `{fn_name}`"
                    )));
                }
                i = next_i;
            }
            other => {
                return Err(CaptureError::UnsupportedMir(format!(
                    "unsupported top-level item `{other}`"
                )));
            }
        }
    }

    Ok(SourceMetadata {
        spec: found_spec.unwrap_or(CapturedSpec::WellFormed),
        nonzero_field_pub_safe,
        unsafe_fns,
        fn_generics,
        impl_consts,
        needs_unoptimized_mir: has_complex_tokens || fn_count > 1,
        src_text: src.to_string(),
    })
}

/// Return `true` if the token stream starting at `i` (immediately after a doc
/// comment) leads directly to a `fn` item after skipping intervening doc
/// comments, outer attributes (`#[...]`), visibility (`pub`, `pub(...)`), and
/// `unsafe`.
fn is_attached_to_fn(tokens: &[SpannedToken], mut i: usize) -> bool {
    let len = tokens.len();
    while i < len {
        match &tokens[i].token {
            LexToken::DocComment(_) => i += 1,
            LexToken::Punct('#') => {
                let Ok(next_i) = skip_attribute(tokens, i) else {
                    return false;
                };
                i = next_i;
            }
            LexToken::Ident(kw) if kw == "pub" => {
                i += 1;
                if i < len && tokens[i].token == LexToken::Punct('(') {
                    let Ok(next_i) = skip_balanced_delim(tokens, i, '(', ')')
                    else {
                        return false;
                    };
                    i = next_i;
                }
            }
            LexToken::Ident(kw) if kw == "unsafe" => i += 1,
            LexToken::Ident(kw) => return kw == "fn",
            _ => return false,
        }
    }
    false
}

/// Skip a balanced outer (`#[...]`) or inner (`#![...]`) attribute starting at
/// the `#` token at `i`.
fn skip_attribute(
    tokens: &[SpannedToken],
    mut i: usize,
) -> Result<usize, CaptureError> {
    let len = tokens.len();
    i += 1; // skip `#`
    if i < len && tokens[i].token == LexToken::Punct('!') {
        i += 1;
    }
    if i >= len || tokens[i].token != LexToken::Punct('[') {
        return Err(CaptureError::UnsupportedMir(
            "malformed attribute syntax".to_string(),
        ));
    }
    skip_balanced_delim(tokens, i, '[', ']')
}

/// Skip a balanced delimiter group `( ... )`, `[ ... ]`, or `{ ... }` starting
/// at index `i` (which must hold `LexToken::Punct(open)`), returning the index
/// immediately after the matching closing delimiter.
fn skip_balanced_delim(
    tokens: &[SpannedToken],
    mut i: usize,
    open: char,
    close: char,
) -> Result<usize, CaptureError> {
    let len = tokens.len();
    if i >= len || tokens[i].token != LexToken::Punct(open) {
        return Err(CaptureError::UnsupportedMir(format!(
            "expected `{open}` delimiter"
        )));
    }
    let mut depth = 1usize;
    i += 1;
    while i < len && depth > 0 {
        if tokens[i].token == LexToken::Punct(open) {
            depth += 1;
        } else if tokens[i].token == LexToken::Punct(close) {
            depth -= 1;
        }
        i += 1;
    }
    if depth != 0 {
        return Err(CaptureError::UnsupportedMir(format!(
            "unclosed `{open}` delimiter"
        )));
    }
    Ok(i)
}

/// Advance `i` past a `const` item body until the terminating `;` at brace
/// depth 0.
fn skip_until_top_level_semi(
    tokens: &[SpannedToken],
    mut i: usize,
) -> Result<usize, CaptureError> {
    let len = tokens.len();
    let mut brace_depth = 0usize;
    while i < len {
        match tokens[i].token {
            LexToken::Punct('{') => brace_depth += 1,
            LexToken::Punct('}') => {
                brace_depth = brace_depth.saturating_sub(1);
            }
            LexToken::Punct(';') if brace_depth == 0 => return Ok(i + 1),
            _ => {}
        }
        i += 1;
    }
    Err(CaptureError::UnsupportedMir(
        "unterminated top-level const item".to_string(),
    ))
}

/// Parse an optional generic parameter list `<T1: Bound, T2, ...>` starting at
/// `i`, extracting type parameter identifiers in declaration order and failing
/// closed on lifetime (`'a`) or `const` generic parameters.
fn parse_generic_params(
    tokens: &[SpannedToken],
    mut i: usize,
) -> Result<(usize, Vec<String>), CaptureError> {
    let len = tokens.len();
    if i >= len || tokens[i].token != LexToken::Punct('<') {
        return Ok((i, Vec::new()));
    }
    i += 1; // skip `<`
    let mut params = Vec::new();
    let mut expect_param = true;
    let mut angle_depth = 1usize;

    while i < len && angle_depth > 0 {
        match &tokens[i].token {
            LexToken::Lifetime(_) => {
                return Err(CaptureError::UnsupportedMir(
                    "lifetime generic parameters are not supported".to_string(),
                ));
            }
            LexToken::Ident(kw) if kw == "const" => {
                return Err(CaptureError::UnsupportedMir(
                    "const generic parameters are not supported".to_string(),
                ));
            }
            LexToken::Punct('<') => {
                angle_depth += 1;
                i += 1;
            }
            LexToken::Punct('>') => {
                angle_depth -= 1;
                i += 1;
            }
            LexToken::Punct(',') if angle_depth == 1 => {
                expect_param = true;
                i += 1;
            }
            LexToken::Ident(ident) if angle_depth == 1 && expect_param => {
                params.push(ident.clone());
                expect_param = false;
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }
    if angle_depth != 0 {
        return Err(CaptureError::UnsupportedMir(
            "unclosed `<` in generic parameter list".to_string(),
        ));
    }
    Ok((i, params))
}

/// Parse a top-level `trait` definition starting at `i`, rejecting trait
/// methods (`fn`) so only associated constant declarations (`const ASSERT: ();`)
/// are admitted.
fn parse_trait_item(
    tokens: &[SpannedToken],
    mut i: usize,
) -> Result<usize, CaptureError> {
    let len = tokens.len();
    i += 1; // skip `trait`
    let Some(SpannedToken {
        token: LexToken::Ident(_),
        ..
    }) = tokens.get(i)
    else {
        return Err(CaptureError::UnsupportedMir(
            "expected trait identifier".to_string(),
        ));
    };
    i += 1;
    let (next_i, _) = parse_generic_params(tokens, i)?;
    i = next_i;
    while i < len && tokens[i].token != LexToken::Punct('{') {
        i += 1;
    }
    if i >= len {
        return Err(CaptureError::UnsupportedMir(
            "expected `{` in trait definition".to_string(),
        ));
    }
    let end_i = skip_balanced_delim(tokens, i, '{', '}')?;
    for tok in &tokens[i + 1..end_i - 1] {
        if let LexToken::Ident(kw) = &tok.token
            && kw == "fn"
        {
            return Err(CaptureError::UnsupportedMir(
                "trait methods are not supported".to_string(),
            ));
        }
    }
    Ok(end_i)
}

/// Parse `struct NonZeroUsize { ... }` starting at `i` and return `(end_i,
/// is_pub_safe)` where `is_pub_safe` is `true` iff `val: usize` has
/// unrestricted `pub` visibility.
///
/// Follows the Rust Reference visibility rules for struct fields:
///
/// > "With no visibility qualifier, an item is visible only within the current
/// > module and its descendants. `pub` makes an item visible everywhere...
/// > `pub(crate)` makes an item visible within the current crate."
///
/// Source:
/// https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/visibility-and-privacy.md#L1-L45
fn parse_struct_item(
    tokens: &[SpannedToken],
    mut i: usize,
) -> Result<(usize, bool), CaptureError> {
    let len = tokens.len();
    i += 1; // skip `struct`
    let Some(SpannedToken {
        token: LexToken::Ident(struct_name),
        ..
    }) = tokens.get(i)
    else {
        return Err(CaptureError::UnsupportedMir(
            "expected struct identifier".to_string(),
        ));
    };
    if struct_name != "NonZeroUsize" {
        return Err(CaptureError::UnsupportedMir(format!(
            "unsupported struct `{struct_name}` (only `NonZeroUsize` is supported)"
        )));
    }
    i += 1;
    if i >= len || tokens[i].token != LexToken::Punct('{') {
        return Err(CaptureError::UnsupportedMir(
            "tuple, unit, and generic structs are not supported".to_string(),
        ));
    }
    let end_i = skip_balanced_delim(tokens, i, '{', '}')?;
    let mut f_idx = i + 1;
    let body_end = end_i - 1;
    let mut fields = Vec::new();

    while f_idx < body_end {
        if matches!(tokens[f_idx].token, LexToken::DocComment(_)) {
            f_idx += 1;
            continue;
        }
        if tokens[f_idx].token == LexToken::Punct('#') {
            f_idx = skip_attribute(tokens, f_idx)?;
            continue;
        }
        let mut is_pub_safe = false;
        if let LexToken::Ident(kw) = &tokens[f_idx].token
            && kw == "pub"
        {
            f_idx += 1;
            if f_idx < body_end && tokens[f_idx].token == LexToken::Punct('(')
            {
                // Restricted visibility (`pub(crate)`, `pub(super)`,
                // `pub(self)`, `pub(in ...)`) is module/crate-scoped and cannot
                // be accessed by arbitrary downstream crates.
                f_idx = skip_balanced_delim(tokens, f_idx, '(', ')')?;
                is_pub_safe = false;
            } else {
                is_pub_safe = true;
            }
        }
        let Some(SpannedToken {
            token: LexToken::Ident(field_name),
            ..
        }) = tokens.get(f_idx)
        else {
            return Err(CaptureError::UnsupportedMir(
                "expected field identifier in struct".to_string(),
            ));
        };
        f_idx += 1;
        if f_idx >= body_end || tokens[f_idx].token != LexToken::Punct(':') {
            return Err(CaptureError::UnsupportedMir(format!(
                "expected `:` after struct field `{field_name}`"
            )));
        }
        f_idx += 1;
        let Some(SpannedToken {
            token: LexToken::Ident(field_ty),
            ..
        }) = tokens.get(f_idx)
        else {
            return Err(CaptureError::UnsupportedMir(format!(
                "unsupported type on struct field `{field_name}`"
            )));
        };
        f_idx += 1;
        if f_idx < body_end && tokens[f_idx].token == LexToken::Punct(',') {
            f_idx += 1;
        }
        fields.push((field_name.clone(), field_ty.clone(), is_pub_safe));
    }

    if fields.len() != 1 || fields[0].0 != "val" || fields[0].1 != "usize" {
        return Err(CaptureError::UnsupportedMir(
            "`NonZeroUsize` must have a single `val: usize` field".to_string(),
        ));
    }
    Ok((end_i, fields[0].2))
}

/// Parse a trait `impl<...> Trait<...> for SelfTy { const ... }` block starting
/// at `i`, recording the line span and generic parameter order of each
/// associated constant in [`ImplConstMeta`] and failing closed on inherent
/// `impl` blocks or `impl` methods.
fn parse_impl_item(
    tokens: &[SpannedToken],
    mut i: usize,
) -> Result<(usize, Vec<ImplConstMeta>), CaptureError> {
    let len = tokens.len();
    let start_line = tokens[i].line;
    i += 1; // skip `impl`
    let (next_i, impl_params) = parse_generic_params(tokens, i)?;
    i = next_i;

    let Some(SpannedToken {
        token: LexToken::Ident(trait_name),
        ..
    }) = tokens.get(i).cloned()
    else {
        return Err(CaptureError::UnsupportedMir(
            "expected trait name in `impl` header".to_string(),
        ));
    };
    i += 1;
    let (next_i, trait_args) = parse_generic_params(tokens, i)?;
    i = next_i;

    let Some(SpannedToken {
        token: LexToken::Ident(for_kw),
        ..
    }) = tokens.get(i)
    else {
        return Err(CaptureError::UnsupportedMir(
            "inherent `impl` blocks are not supported (expected `for`)"
                .to_string(),
        ));
    };
    if for_kw != "for" {
        return Err(CaptureError::UnsupportedMir(
            "inherent `impl` blocks are not supported".to_string(),
        ));
    }
    i += 1;

    // Parse `Self` type (`()` or identifier).
    let (self_ty_name, self_ty_kind) = if i + 1 < len
        && tokens[i].token == LexToken::Punct('(')
        && tokens[i + 1].token == LexToken::Punct(')')
    {
        i += 2;
        ("()".to_string(), SelfTyKind::Unit)
    } else if let Some(SpannedToken {
        token: LexToken::Ident(id),
        ..
    }) = tokens.get(i)
    {
        i += 1;
        let kind = if impl_params.contains(id) {
            SelfTyKind::Param
        } else {
            SelfTyKind::Named(id.clone())
        };
        (id.clone(), kind)
    } else {
        return Err(CaptureError::UnsupportedMir(
            "unsupported `Self` type in `impl` block".to_string(),
        ));
    };

    if i >= len || tokens[i].token != LexToken::Punct('{') {
        return Err(CaptureError::UnsupportedMir(
            "expected `{` after `impl` header".to_string(),
        ));
    }
    let end_i = skip_balanced_delim(tokens, i, '{', '}')?;
    let end_line = tokens[end_i - 1].line;

    let mut consts = Vec::new();
    let mut b_idx = i + 1;
    let body_end = end_i - 1;
    while b_idx < body_end {
        match &tokens[b_idx].token {
            LexToken::Ident(kw) if kw == "fn" => {
                return Err(CaptureError::UnsupportedMir(
                    "methods inside `impl` blocks are not supported"
                        .to_string(),
                ));
            }
            LexToken::Ident(kw) if kw == "const" => {
                b_idx += 1;
                let Some(SpannedToken {
                    token: LexToken::Ident(const_name),
                    ..
                }) = tokens.get(b_idx)
                else {
                    return Err(CaptureError::UnsupportedMir(
                        "expected associated const identifier in `impl`"
                            .to_string(),
                    ));
                };
                consts.push(ImplConstMeta {
                    start_line,
                    end_line,
                    trait_name: trait_name.clone(),
                    const_name: const_name.clone(),
                    self_ty_kind: self_ty_kind.clone(),
                    self_ty_name: self_ty_name.clone(),
                    impl_params: impl_params.clone(),
                    trait_args: trait_args.clone(),
                });
                b_idx = skip_until_top_level_semi(tokens, b_idx)?;
            }
            _ => {
                b_idx += 1;
            }
        }
    }

    Ok((end_i, consts))
}

/// Parse a top-level `fn name<...>(...) -> ... { ... }` item starting at `i`,
/// returning `(end_i, fn_name, generic_param_names)` and failing closed on
/// `where` clauses.
fn parse_fn_item(
    tokens: &[SpannedToken],
    mut i: usize,
) -> Result<(usize, String, Vec<String>), CaptureError> {
    let len = tokens.len();
    i += 1; // skip `fn`
    let Some(SpannedToken {
        token: LexToken::Ident(fn_name),
        ..
    }) = tokens.get(i).cloned()
    else {
        return Err(CaptureError::UnsupportedMir(
            "expected function identifier after `fn`".to_string(),
        ));
    };
    i += 1;
    let (next_i, generics) = parse_generic_params(tokens, i)?;
    i = next_i;
    if i >= len || tokens[i].token != LexToken::Punct('(') {
        return Err(CaptureError::UnsupportedMir(format!(
            "expected parameter list in `fn {fn_name}`"
        )));
    }
    i = skip_balanced_delim(tokens, i, '(', ')')?;
    while i < len && tokens[i].token != LexToken::Punct('{') {
        if let LexToken::Ident(kw) = &tokens[i].token
            && kw == "where"
        {
            return Err(CaptureError::UnsupportedMir(
                "`where` clauses are not supported".to_string(),
            ));
        }
        i += 1;
    }
    if i >= len {
        return Err(CaptureError::UnsupportedMir(format!(
            "expected body `{}` for `fn {fn_name}`",
            "{ ... }"
        )));
    }
    let end_i = skip_balanced_delim(tokens, i, '{', '}')?;
    Ok((end_i, fn_name, generics))
}

/// Canonical correlation key linking a constant's lowered MIR body to its use
/// sites (`_N = const ...;`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ConstKey {
    /// Associated constant on a trait implementation (`<SelfTy as
    /// Trait<...>>::CONST`).
    TraitAssoc {
        self_ty_kind: SelfTyKind,
        trait_name: String,
        const_name: String,
    },
    /// Inline `const { ... }` block (`fn_name::{constant#N}`).
    Inline { fn_name: String, index: usize },
    /// Top-level `const NAME: () = ...;` item.
    TopLevel { name: String },
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

/// Parse the textual `Runtime(PostCleanup)` MIR emitted by `rustc --emit=mir`
/// along with crate-level [`SourceMetadata`].
pub fn parse_emitted_mir_with_metadata(
    mir_text: &str,
    meta: &SourceMetadata,
) -> Result<Vec<CapturedFunction>, CaptureError> {
    struct RawParsedFn {
        func: CapturedFunction,
        raw_consts: Vec<(ConstKey, Vec<CapturedTy>)>,
    }

    let mut const_defs: BTreeMap<ConstKey, CapturedFunction> = BTreeMap::new();
    let mut raw_fns: Vec<RawParsedFn> = Vec::new();
    let mut seen_fn_names: BTreeSet<String> = BTreeSet::new();
    let mut lines = mir_text.lines().peekable();

    let default_generics = vec!["Src".to_string(), "Dst".to_string()];

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

        let (name, arg_tys, ret_ty, const_key, active_generics) =
            if (line.starts_with("const ") || line.contains("::{constant#"))
                && line.ends_with(": () = {")
            {
                let (key, generics) =
                    parse_const_header(line, meta, &default_generics)?;
                (
                    "pme_assert_const".to_string(),
                    Vec::new(),
                    CapturedTy::Unit,
                    Some(key),
                    generics,
                )
            } else if let Some(fn_rest) = line.strip_prefix("fn ") {
                let (n, raw_generics) =
                    resolve_fn_generics(fn_rest, meta, &default_generics)?;
                let (parsed_name, args, ret) =
                    parse_fn_header(fn_rest, &raw_generics)?;
                debug_assert_eq!(n, parsed_name);
                if !seen_fn_names.insert(parsed_name.clone()) {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "duplicate MIR function body `{parsed_name}`"
                    )));
                }
                (parsed_name, args, ret, None, raw_generics)
            } else {
                return Err(CaptureError::UnsupportedMir(format!(
                    "unexpected top-level MIR line: `{line}`"
                )));
            };

        let mut max_local = arg_tys.len();
        let mut blocks = Vec::new();
        let mut raw_required_consts: Vec<(ConstKey, Vec<CapturedTy>)> =
            Vec::new();

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
            // Skip nested `scope N { ... }` blocks by tracking brace depth.
            if body_line.starts_with("scope ") && body_line.ends_with('{') {
                let mut scope_depth = 1usize;
                for scope_line in lines.by_ref() {
                    let trimmed = scope_line.trim();
                    if trimmed.starts_with("scope ") && trimmed.ends_with('{') {
                        scope_depth += 1;
                    } else if trimmed == "}" {
                        scope_depth -= 1;
                        if scope_depth == 0 {
                            break;
                        }
                    }
                }
                if scope_depth != 0 {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "unterminated scope block in `{name}`"
                    )));
                }
                continue;
            }
            if body_line == "}" {
                break;
            }
            if let Some(decl_rest) = body_line.strip_prefix("let ") {
                let (local_idx, ty) =
                    parse_local_decl(decl_rest, &active_generics)?;
                if local_idx == 0 && ty != ret_ty {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "return local _0 type {ty:?} does not match header \
                         {ret_ty:?}"
                    )));
                }
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
                            "statement after terminator in bb{bb_idx}: \
                             `{stmt_line}`"
                        )));
                    }
                    let (parsed, maybe_const) = parse_stmt_or_terminator(
                        stmt_line,
                        &name,
                        &active_generics,
                        meta,
                    )?;
                    if let Some(const_ref) = maybe_const
                        && !raw_required_consts.contains(&const_ref)
                    {
                        raw_required_consts.push(const_ref);
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
            if meta.nonzero_field_pub_safe.is_none()
                || arg_tys != vec![CapturedTy::Usize]
                || ret_ty != CapturedTy::Adt(0)
            {
                return Err(CaptureError::UnsupportedMir(format!(
                    "unsupported `unsafe fn {name}` signature or missing \
                     `NonZeroUsize` ADT"
                )));
            }
            CapturedFnKind::PubUnsafeNewUnchecked
        } else {
            CapturedFnKind::PubSafe
        };

        let is_const = const_key.is_some();
        let func = CapturedFunction {
            name,
            arg_tys,
            ret_ty,
            local_count: max_local + 1,
            blocks,
            spec: meta.spec,
            is_const,
            required_consts: Vec::new(),
            kind,
        };
        if let Some(key) = const_key {
            if const_defs.insert(key.clone(), func).is_some() {
                return Err(CaptureError::UnsupportedMir(format!(
                    "duplicate constant MIR body for {key:?}"
                )));
            }
        } else {
            raw_fns.push(RawParsedFn {
                func,
                raw_consts: raw_required_consts,
            });
        }
    }

    // Correlate each referenced `ConstKey` against `const_defs`, failing closed
    // if any referenced constant has no captured MIR body.
    let mut const_name_map: BTreeMap<ConstKey, String> = BTreeMap::new();
    let mut ordered_consts: Vec<CapturedFunction> = Vec::new();

    for rf in &mut raw_fns {
        // Validate every `Call1` callee against `seen_fn_names`.
        for block in &rf.func.blocks {
            if let CapturedTerminator::Call1 { callee_name, .. } =
                &block.terminator
                && !seen_fn_names.contains(callee_name)
            {
                return Err(CaptureError::UnsupportedMir(format!(
                    "call to unknown or uncaptured function `{callee_name}`"
                )));
            }
        }
        for (key, tys) in &rf.raw_consts {
            let Some(const_fn) = const_defs.get(key) else {
                return Err(CaptureError::UnsupportedMir(format!(
                    "referenced constant {key:?} has no captured MIR body"
                )));
            };
            let assigned_name =
                if let Some(existing) = const_name_map.get(key) {
                    existing.clone()
                } else {
                    let next_name = if ordered_consts.is_empty() {
                        "pme_assert_const".to_string()
                    } else {
                        format!("pme_assert_const_{}", ordered_consts.len())
                    };
                    let mut named_const = const_fn.clone();
                    named_const.name = next_name.clone();
                    ordered_consts.push(named_const);
                    const_name_map.insert(key.clone(), next_name.clone());
                    next_name
                };
            rf.func.required_consts.push((assigned_name, tys.clone()));
        }
    }

    let mut items = ordered_consts;
    items.extend(raw_fns.into_iter().map(|rf| rf.func));
    Ok(items)
}

/// Parse a MIR constant body header emitted by `rustc`'s MIR pretty-printer
/// (`compiler/rustc_middle/src/mir/pretty.rs` in
/// `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`), returning its
/// canonical [`ConstKey`] and generic type parameter names in declaration
/// order.
///
/// Handles the three constant header shapes emitted by `rustc --emit=mir`:
/// 1. Trait associated constants (`const <impl at path:L1:C1: L2:C2>::NAME: ()
///    = {`), correlated by source line span with [`SourceMetadata::impl_consts`].
/// 2. Inline `const { ... }` blocks (`<fn_name>::{constant#N}: () = {`),
///    inheriting the enclosing function's generic type parameters.
/// 3. Top-level constants (`const NAME: () = {`).
fn parse_const_header(
    line: &str,
    meta: &SourceMetadata,
    default_generics: &[String],
) -> Result<(ConstKey, Vec<String>), CaptureError> {
    let without_suffix = line.strip_suffix(": () = {").ok_or_else(|| {
        CaptureError::UnsupportedMir(format!("malformed const header `{line}`"))
    })?;
    let trimmed = without_suffix
        .strip_prefix("const ")
        .unwrap_or(without_suffix)
        .trim();

    // Case 1: `const <impl at path:L1:C1: L2:C2>::CONST_NAME: () = {`
    if let Some(impl_rest) = trimmed.strip_prefix("<impl at ") {
        let (span_part, const_name) =
            impl_rest.split_once(">::").ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "malformed impl const header `{line}`"
                ))
            })?;
        let const_name = const_name.trim().to_string();
        if !meta.impl_consts.is_empty() {
            let start_line = parse_impl_span_start_line(span_part)?;
            let matched = meta
                .impl_consts
                .iter()
                .find(|ic| {
                    ic.const_name == const_name
                        && ic.start_line <= start_line
                        && start_line <= ic.end_line
                })
                .ok_or_else(|| {
                    CaptureError::UnsupportedMir(format!(
                        "cannot correlate impl const `{const_name}` at line \
                         {start_line}"
                    ))
                })?;
            return Ok((
                ConstKey::TraitAssoc {
                    self_ty_kind: matched.self_ty_kind.clone(),
                    trait_name: matched.trait_name.clone(),
                    const_name,
                },
                matched.impl_params.clone(),
            ));
        }
        return Ok((
            ConstKey::TraitAssoc {
                self_ty_kind: SelfTyKind::Unit,
                trait_name: "SizeEq".to_string(),
                const_name,
            },
            default_generics.to_vec(),
        ));
    }

    // Case 2: `<fn_name>::{constant#N}: () = {`
    if let Some((raw_fn, idx_part)) = trimmed.split_once("::{constant#")
        && let Some(idx_str) = idx_part.strip_suffix('}')
    {
        let index = idx_str.parse::<usize>().map_err(|_| {
            CaptureError::UnsupportedMir(format!(
                "invalid inline constant index in `{line}`"
            ))
        })?;
        let fn_name = raw_fn
            .strip_prefix("anneal_target::")
            .unwrap_or(raw_fn)
            .trim()
            .to_string();
        if fn_name.contains("::") {
            return Err(CaptureError::UnsupportedMir(format!(
                "unsupported module-qualified inline constant `{trimmed}`"
            )));
        }
        let generics = meta
            .fn_generics
            .get(&fn_name)
            .cloned()
            .unwrap_or_else(|| default_generics.to_vec());
        return Ok((ConstKey::Inline { fn_name, index }, generics));
    }

    // Case 3: Top-level `const NAME: () = {`
    let name = trimmed
        .strip_prefix("anneal_target::")
        .unwrap_or(trimmed)
        .trim();
    if !name.is_empty()
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Ok((
            ConstKey::TopLevel {
                name: name.to_string(),
            },
            Vec::new(),
        ));
    }

    Err(CaptureError::UnsupportedMir(format!(
        "unsupported constant header `{line}`"
    )))
}

/// Extract the 1-based starting line number `L1` from a `rustc` `impl` span
/// header `<impl at path:L1:C1: L2:C2>`.
fn parse_impl_span_start_line(span_part: &str) -> Result<usize, CaptureError> {
    let (start_loc, _) = span_part.rsplit_once(": ").ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "malformed impl span `{span_part}`"
        ))
    })?;
    let (before_col, _) = start_loc.rsplit_once(':').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "malformed impl start location `{start_loc}`"
        ))
    })?;
    let (_, line_str) = before_col.rsplit_once(':').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "malformed impl start line `{before_col}`"
        ))
    })?;
    line_str.trim().parse::<usize>().map_err(|_| {
        CaptureError::UnsupportedMir(format!(
            "invalid impl start line `{line_str}`"
        ))
    })
}

/// Resolve the unqualified function name and its source-level generic parameter
/// names from a MIR `fn` header line (`fn name(_1: ...) -> ... {`).
fn resolve_fn_generics(
    fn_rest: &str,
    meta: &SourceMetadata,
    default_generics: &[String],
) -> Result<(String, Vec<String>), CaptureError> {
    let header = fn_rest
        .strip_suffix('{')
        .ok_or_else(|| {
            CaptureError::UnsupportedMir(format!(
                "malformed fn header: `{fn_rest}`"
            ))
        })?
        .trim();
    let (name_part, _) = header.split_once('(').ok_or_else(|| {
        CaptureError::UnsupportedMir(format!(
            "missing parameter list in `{header}`"
        ))
    })?;
    let raw_name = name_part.trim();
    let stripped = raw_name
        .strip_prefix("anneal_target::")
        .unwrap_or(raw_name)
        .trim();
    if stripped.contains("::") {
        return Err(CaptureError::UnsupportedMir(format!(
            "unsupported module-qualified or method item `{raw_name}`"
        )));
    }
    let generics = if meta.fn_generics.is_empty() && meta.src_text.is_empty() {
        default_generics.to_vec()
    } else {
        meta.fn_generics
            .get(stripped)
            .cloned()
            .unwrap_or_default()
    };
    Ok((stripped.to_string(), generics))
}

trait BlockHeaderExt {
    fn strip_suffix_or_block(&self) -> Option<&str>;
}

impl BlockHeaderExt for str {
    fn strip_suffix_or_block(&self) -> Option<&str> {
        let before_brace = self.strip_suffix('{')?.trim();
        if before_brace.ends_with("(cleanup):") {
            return None;
        }
        before_brace.strip_suffix(':')
    }
}

/// Parse a MIR function signature header (`<name>(_1: <ty>, ...) -> <ret_ty> {`)
/// printed by `write_mir_fn` in `compiler/rustc_middle/src/mir/pretty.rs`
/// (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`), verifying
/// contiguous 1-based argument local indices (`_1..=_k`).
fn parse_fn_header(
    fn_rest: &str,
    generics: &[String],
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
        .strip_prefix("anneal_target::")
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
            arg_tys.push(parse_ty(ty_str.trim(), generics)?);
        }
    }
    let ret_ty = if let Some(arrow_rest) = ret_part.trim().strip_prefix("->") {
        parse_ty(arrow_rest.trim(), generics)?
    } else if ret_part.trim().is_empty() {
        CapturedTy::Unit
    } else {
        return Err(CaptureError::UnsupportedMir(format!(
            "malformed return type in `{header}`"
        )));
    };
    Ok((name, arg_tys, ret_ty))
}

/// Parse a MIR local declaration (`let [mut] _<n>: <ty>;`) corresponding to an
/// entry in `rustc_middle::mir::Body::local_decls`
/// (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).
fn parse_local_decl(
    decl_rest: &str,
    generics: &[String],
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
    let ty = parse_ty(ty_str.trim(), generics)?;
    Ok((idx, ty))
}

/// Parse a local variable token `_<n>` (`rustc_middle::mir::Local`).
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

/// Parse a basic block identifier `bb<n>` (`rustc_middle::mir::BasicBlock`).
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

/// Parse a textual MIR type (`usize`, `bool`, `()`, `!`, `NonZeroUsize`, a
/// generic type parameter `T`, or a shared reference `&T`) into [`CapturedTy`],
/// failing closed on any other type.
fn parse_ty(
    ty_str: &str,
    generics: &[String],
) -> Result<CapturedTy, CaptureError> {
    let trimmed = ty_str.trim();
    match trimmed {
        "usize" => Ok(CapturedTy::Usize),
        "bool" => Ok(CapturedTy::Bool),
        "()" | "!" => Ok(CapturedTy::Unit),
        "NonZeroUsize" => Ok(CapturedTy::Adt(0)),
        _ => {
            if let Some(inner) = trimmed.strip_prefix('&') {
                let inner_trimmed = inner.trim();
                if let Some(idx) =
                    generics.iter().position(|g| g == inner_trimmed)
                {
                    return Ok(CapturedTy::RefParam(idx));
                }
            }
            if let Some(idx) = generics.iter().position(|g| g == trimmed) {
                return Ok(CapturedTy::Param(idx));
            }
            Err(CaptureError::UnsupportedMir(format!(
                "unsupported MIR type `{trimmed}`"
            )))
        }
    }
}

enum StmtOrTerm {
    Stmt(CapturedStmt),
    Term(CapturedTerminator),
}

/// Parse a single basic-block body line as either a [`CapturedStmt`] or a
/// [`CapturedTerminator`] (`rustc_middle::mir::StatementKind` and
/// `rustc_middle::mir::TerminatorKind` in
/// `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`), returning any
/// referenced PME constant `(ConstKey, Vec<CapturedTy>)` alongside the parsed
/// node.
fn parse_stmt_or_terminator(
    line: &str,
    enclosing_fn: &str,
    generics: &[String],
    meta: &SourceMetadata,
) -> Result<(StmtOrTerm, Option<(ConstKey, Vec<CapturedTy>)>), CaptureError> {
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
                    let ty = parse_ty(ty_str.trim(), generics)?;
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
                    let src_ty = parse_ty(src_ty_str.trim(), generics)?;
                    let dst_ty = parse_ty(dst_ty_str.trim(), generics)?;
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
                    let callee_raw = callee_raw.trim();
                    if callee_raw.starts_with('<') || callee_raw.contains(" as ")
                    {
                        return Err(CaptureError::UnsupportedMir(format!(
                            "trait method calls are not supported: `{line}`"
                        )));
                    }
                    let (callee_base, type_args) = if let Some((
                        base,
                        turbo_rest,
                    )) =
                        callee_raw.split_once("::<")
                    {
                        let inner_tys =
                            turbo_rest.strip_suffix('>').ok_or_else(|| {
                                CaptureError::UnsupportedMir(format!(
                                    "malformed turbofish in call `{line}`"
                                ))
                            })?;
                        let mut parsed_tys = Vec::new();
                        if !inner_tys.trim().is_empty() {
                            for t_str in inner_tys.split(',') {
                                parsed_tys
                                    .push(parse_ty(t_str.trim(), generics)?);
                            }
                        }
                        (base.trim(), parsed_tys)
                    } else {
                        (callee_raw, Vec::new())
                    };
                    let callee_name = callee_base
                        .strip_prefix("anneal_target::")
                        .unwrap_or(callee_base)
                        .trim()
                        .to_string();
                    if callee_name.contains("::") {
                        return Err(CaptureError::UnsupportedMir(format!(
                            "unsupported module-qualified call `{callee_base}`"
                        )));
                    }
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
                                type_args,
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

        // Check literal `const ()` or `const <N>_usize` before named/PME
        // constant references.
        if let Ok(op) = parse_operand(rhs) {
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignUse { dst, op }),
                None,
            ));
        }

        // Check named/associated/inline constant reference (`_2 = const ...`).
        if let Some(const_rhs) = rhs.strip_prefix("const ") {
            let (key, type_args) = parse_const_use_site(
                const_rhs.trim(),
                enclosing_fn,
                generics,
                meta,
            )?;
            return Ok((
                StmtOrTerm::Stmt(CapturedStmt::AssignUse {
                    dst,
                    op: CapturedOperand::ConstUnit,
                }),
                Some((key, type_args)),
            ));
        }
    }
    Err(CaptureError::UnsupportedMir(format!(
        "unsupported MIR statement or terminator: `{line}`"
    )))
}

/// Parse a MIR constant use site (`_dst = const <const_rhs>;`) and resolve both
/// its [`ConstKey`] and its instantiated [`CapturedTy`] arguments in the
/// constant definition's generic parameter order.
fn parse_const_use_site(
    const_rhs: &str,
    enclosing_fn: &str,
    generics: &[String],
    meta: &SourceMetadata,
) -> Result<(ConstKey, Vec<CapturedTy>), CaptureError> {
    // Case 1: `<SelfTy as Trait<Arg1, ...>>::CONST_NAME`
    if let Some(inner) = const_rhs.strip_prefix('<')
        && let Some((proj_part, const_name)) = inner.rsplit_once(">::")
        && let Some((self_ty_raw, trait_raw)) = proj_part.split_once(" as ")
    {
        let self_ty_str = self_ty_raw.trim();
        let self_ty_kind = if self_ty_str == "()" {
            SelfTyKind::Unit
        } else if generics.iter().any(|g| g == self_ty_str) {
            SelfTyKind::Param
        } else {
            SelfTyKind::Named(self_ty_str.to_string())
        };
        let (trait_base, use_trait_args) = if let Some((t_name, args_rest)) =
            trait_raw.trim().split_once('<')
        {
            let args_inner = args_rest.strip_suffix('>').ok_or_else(|| {
                CaptureError::UnsupportedMir(format!(
                    "malformed trait arguments in const `{const_rhs}`"
                ))
            })?;
            let mut tys = Vec::new();
            if !args_inner.trim().is_empty() {
                for a in args_inner.split(',') {
                    tys.push(parse_ty(a.trim(), generics)?);
                }
            }
            (t_name.trim(), tys)
        } else {
            (trait_raw.trim(), Vec::new())
        };
        let trait_name = trait_base
            .strip_prefix("anneal_target::")
            .unwrap_or(trait_base)
            .trim()
            .to_string();
        let const_name = const_name.trim().to_string();

        // Map the use-site type arguments into the `impl` block's generic
        // parameter order if metadata is present.
        let type_args = if let Some(ic) = meta.impl_consts.iter().find(|ic| {
            ic.self_ty_kind == self_ty_kind
                && ic.trait_name == trait_name
                && ic.const_name == const_name
        }) {
            if use_trait_args.len() != ic.trait_args.len() {
                return Err(CaptureError::UnsupportedMir(format!(
                    "trait argument count mismatch at `{const_rhs}`"
                )));
            }
            let mut mapped = Vec::with_capacity(ic.impl_params.len());
            for param in &ic.impl_params {
                if param == &ic.self_ty_name {
                    mapped.push(parse_ty(self_ty_str, generics)?);
                } else if let Some(pos) =
                    ic.trait_args.iter().position(|ta| ta == param)
                {
                    mapped.push(use_trait_args[pos]);
                } else {
                    return Err(CaptureError::UnsupportedMir(format!(
                        "unmapped impl parameter `{param}` in `{const_rhs}`"
                    )));
                }
            }
            mapped
        } else {
            let mut fallback = Vec::new();
            if self_ty_kind == SelfTyKind::Param {
                fallback.push(parse_ty(self_ty_str, generics)?);
            }
            fallback.extend(use_trait_args);
            fallback
        };

        return Ok((
            ConstKey::TraitAssoc {
                self_ty_kind,
                trait_name,
                const_name,
            },
            type_args,
        ));
    }

    // Case 2: `<fn_name>::<Arg1, ...>::{constant#N}` or
    // `<fn_name>::{constant#N}`
    if let Some((before_const, idx_part)) =
        const_rhs.split_once("::{constant#")
        && let Some(idx_str) = idx_part.strip_suffix('}')
    {
        let index = idx_str.parse::<usize>().map_err(|_| {
            CaptureError::UnsupportedMir(format!(
                "invalid inline const index in `{const_rhs}`"
            ))
        })?;
        let (raw_fn, type_args) =
            if let Some((fn_base, args_rest)) = before_const.split_once("::<")
            {
                let args_inner = args_rest.strip_suffix('>').ok_or_else(|| {
                    CaptureError::UnsupportedMir(format!(
                        "malformed turbofish in inline const `{const_rhs}`"
                    ))
                })?;
                let mut tys = Vec::new();
                if !args_inner.trim().is_empty() {
                    for a in args_inner.split(',') {
                        tys.push(parse_ty(a.trim(), generics)?);
                    }
                }
                (fn_base.trim(), tys)
            } else {
                let inherited: Vec<CapturedTy> =
                    (0..generics.len()).map(CapturedTy::Param).collect();
                (before_const.trim(), inherited)
            };
        let fn_name = raw_fn
            .strip_prefix("anneal_target::")
            .unwrap_or(raw_fn)
            .trim()
            .to_string();
        if fn_name != enclosing_fn {
            return Err(CaptureError::UnsupportedMir(format!(
                "cross-function inline constant reference `{const_rhs}`"
            )));
        }
        return Ok((ConstKey::Inline { fn_name, index }, type_args));
    }

    // Case 3: Top-level `CONST_NAME`
    let name = const_rhs
        .strip_prefix("anneal_target::")
        .unwrap_or(const_rhs)
        .trim();
    if !name.is_empty()
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Ok((
            ConstKey::TopLevel {
                name: name.to_string(),
            },
            Vec::new(),
        ));
    }

    Err(CaptureError::UnsupportedMir(format!(
        "unsupported constant reference `{const_rhs}`"
    )))
}

/// Parse a MIR operand (`copy _n`, `move _n`, `const ()`, or `const <k>_usize`)
/// corresponding to `rustc_middle::mir::Operand`
/// (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`).
fn parse_operand(rhs: &str) -> Result<CapturedOperand, CaptureError> {
    if let Some(local_str) = rhs.strip_prefix("copy ") {
        return Ok(CapturedOperand::Copy(parse_local_token(local_str.trim())?));
    }
    if let Some(local_str) = rhs.strip_prefix("move ") {
        return Ok(CapturedOperand::Move(parse_local_token(local_str.trim())?));
    }
    if rhs == "const ()" || rhs == "()" {
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

/// Format a slice of rendered Lean expressions as a Lean list literal `[...]`.
fn render_lean_list(items: &[String]) -> String {
    format!("[{}]", items.join(", "))
}

/// Escape an arbitrary UTF-8 string as a double-quoted Lean string literal for
/// embedding `src/lib.rs` into `Trusted.Crate.artifacts`.
fn lean_string_literal(s: &str) -> String {
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
/// `Mir.crate : Trusted.Crate` with crate-level ADT, library invariant, and
/// source artifact metadata.
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
                    .map(|(c, tys)| {
                        let ty_strs: Vec<String> =
                            tys.iter().map(|t| t.to_lean_in_list()).collect();
                        format!("({c}_body, {})", render_lean_list(&ty_strs))
                    })
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
             abbrev newUncheckedSafetyPre (s : Trusted.MirState) : Prop :=\n  \
             ∀ n, s.locals 1 = some (.usize n) → n ≠ 0\n"
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
                "{{ name := \"{}\", prog := {}_body, \
                 kind := Trusted.FnKind.pubUnsafe True newUncheckedSafetyPre, \
                 specs := {} }}",
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
    let src_lit = lean_string_literal(&meta.src_text);
    let artifacts_entry = format!(
        "[{{ path := \"src/lib.rs\", contents := {src_lit}, \
         expected := {src_lit} }}]"
    );

    if let Some(is_pub_safe) = meta.nonzero_field_pub_safe {
        let access_str = if is_pub_safe {
            "Trusted.FieldAccess.pubSafe"
        } else {
            "Trusted.FieldAccess.priv"
        };
        let _ = writeln!(
            out,
            "def crate : Trusted.Crate where\n  \
             adts := [{{ id := 0, fields := [{{ ty := Trusted.MirTy.usize, \
             access := {access_str} }}] }}]\n  \
             adtInv := nonZeroAdtInv\n  \
             functions := {}\n  \
             tcb := {}\n  \
             artifacts := {}\n\n\
             end Mir",
            render_lean_list(&fn_entries),
            render_lean_list(&tcb_entries),
            artifacts_entry,
        );
    } else {
        let _ = writeln!(
            out,
            "def crate : Trusted.Crate where\n  \
             functions := {}\n  \
             tcb := {}\n  \
             artifacts := {}\n\n\
             end Mir",
            render_lean_list(&fn_entries),
            render_lean_list(&tcb_entries),
            artifacts_entry,
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

    #[test]
    fn ignores_anneal_spec_and_spoofed_items_in_strings_and_comments() {
        let src_in_str = "\
pub fn id(x: usize) -> usize {
    let _s = \"// anneal:spec ensures(ret == x) struct NonZeroUsize { pub val: usize }\";
    /* // anneal:spec ensures(ret == x)
       pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize {} */
    x
}
";
        let meta = parse_source_metadata(src_in_str).unwrap();
        assert_eq!(meta.spec, CapturedSpec::WellFormed);
        assert_eq!(meta.nonzero_field_pub_safe, None);
        assert!(meta.unsafe_fns.is_empty());

        let trailing_spec = "\
pub fn id(x: usize) -> usize {
    x
}
/// anneal:spec ensures(ret == x)
";
        assert!(parse_source_metadata(trailing_spec).is_err());
    }

    #[test]
    fn classifies_struct_visibility_and_rejects_unsupported_items() {
        let pub_crate_src = "\
pub struct NonZeroUsize {
    #[allow(dead_code)]
    pub(crate) val: usize,
}
pub fn make_nonzero(x: usize) -> NonZeroUsize {
    NonZeroUsize { val: x }
}
";
        let meta = parse_source_metadata(pub_crate_src).unwrap();
        assert_eq!(meta.nonzero_field_pub_safe, Some(false));

        let pub_attr_src = "\
pub struct NonZeroUsize {
    #[allow(dead_code)]
    pub val: usize,
}
";
        let meta_pub = parse_source_metadata(pub_attr_src).unwrap();
        assert_eq!(meta_pub.nonzero_field_pub_safe, Some(true));

        assert!(parse_source_metadata("pub enum E { A }").is_err());
        assert!(parse_source_metadata("pub struct NonZeroUsize(usize);").is_err());
        assert!(parse_source_metadata("pub unsafe trait Bad {}").is_err());
        assert!(parse_source_metadata(
            "pub struct NonZeroUsize { val: usize }\n\
             impl NonZeroUsize { pub fn f() {} }"
        )
        .is_err());
    }

    #[test]
    fn correlates_consts_by_key_and_rejects_unknown_or_decoy_consts() {
        let src = "\
const DECOY: () = ();
pub trait SizeEq<A, B> {
    const ASSERT: ();
}
impl<A, B> SizeEq<A, B> for () {
    const ASSERT: () = assert!(core::mem::size_of::<A>() == core::mem::size_of::<B>());
}
pub fn transmute_checked<First: Copy, Second: Copy>(x: First) -> Second {
    let () = <() as SizeEq<First, Second>>::ASSERT;
    unsafe { core::mem::transmute_copy(&x) }
}
";
        let meta = parse_source_metadata(src).unwrap();
        assert_eq!(
            meta.fn_generics.get("transmute_checked"),
            Some(&vec!["First".to_string(), "Second".to_string()])
        );
        assert_eq!(meta.impl_consts.len(), 1);

        let mir = "\
const DECOY: () = {
    let mut _0: ();
    bb0: {
        _0 = const ();
        return;
    }
}

const <impl at src/lib.rs:5:1: 7:2>::ASSERT: () = {
    let mut _0: ();
    let mut _1: bool;
    let mut _2: usize;
    let mut _3: usize;
    let mut _4: !;
    bb0: {
        StorageLive(_1);
        StorageLive(_2);
        ConstEvalCounter;
        _2 = std::mem::size_of::<A>() -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageLive(_3);
        ConstEvalCounter;
        _3 = std::mem::size_of::<B>() -> [return: bb2, unwind continue];
    }
    bb2: {
        _1 = Eq(move _2, move _3);
        switchInt(move _1) -> [0: bb4, otherwise: bb3];
    }
    bb3: {
        StorageDead(_3);
        StorageDead(_2);
        _0 = const ();
        StorageDead(_1);
        return;
    }
    bb4: {
        StorageDead(_3);
        StorageDead(_2);
        StorageLive(_4);
        ConstEvalCounter;
        _4 = panic(const \"assertion failed\") -> unwind continue;
    }
}

fn transmute_checked(_1: First) -> Second {
    let mut _0: Second;
    let _2: ();
    let mut _3: &First;
    let _4: &First;
    bb0: {
        StorageLive(_2);
        _2 = const <() as SizeEq<First, Second>>::ASSERT;
        StorageDead(_2);
        StorageLive(_3);
        StorageLive(_4);
        _4 = &_1;
        _3 = &(*_4);
        _0 = transmute_copy::<First, Second>(move _3) -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageDead(_4);
        StorageDead(_3);
        return;
    }
}
";
        let items = parse_emitted_mir_with_metadata(mir, &meta).unwrap();
        assert_eq!(items.len(), 2);
        assert!(items[0].is_const);
        assert_eq!(items[0].name, "pme_assert_const");
        assert_eq!(items[0].blocks.len(), 5);
        assert_eq!(
            items[1].required_consts,
            vec![(
                "pme_assert_const".to_string(),
                vec![CapturedTy::Param(0), CapturedTy::Param(1)]
            )]
        );
    }
}
