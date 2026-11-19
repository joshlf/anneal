// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Owned capture data. Metadata and semantic constructors stay separate so that
//! Rust names and paths never become executable Lean source.

use std::path::PathBuf;

use serde::Serialize;

use crate::compilers::SupportedCompiler;

// Version 2 adds required source identities to every captured Body. Old capture
// subjects must be rejected before proof checking against this model ABI.
pub const SCHEMA_VERSION: u32 = 2;

/// The compiler whose `rustc_private` libraries this driver links.
///
/// `build.rs` identifies `$RUSTC` against the closed table in `compilers.rs`
/// and exports its fields; a build with any other compiler stops there. The
/// driver therefore needs no run-time table search: every check compares
/// against this one compile-time identity.
pub const LINKED_COMPILER: SupportedCompiler = SupportedCompiler {
    mir_dialect: env!("ANNEAL_LINKED_MIR_DIALECT"),
    commit: env!("ANNEAL_LINKED_RUSTC_COMMIT"),
    commit_date: env!("ANNEAL_LINKED_RUSTC_DATE"),
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum EnumTagRepr {
    ZeroSized,
    Scalar {
        bits: u32,
        signed: bool,
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        is_size: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnumTy {
    pub id: u64,
    pub discr_bits: u32,
    pub discr_signed: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub discr_is_size: bool,
    pub tag_repr: EnumTagRepr,
    pub discriminants: Vec<u64>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Ty {
    Bool,
    Unit,
    Never,
    Int {
        bits: u32,
        signed: bool,
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        is_size: bool,
    },
    Enum(EnumTy),
}

impl Ty {
    /// Whether Miri's `RetagMode::Default` (`WithRetag::Yes` on `Rvalue::Use`)
    /// is an operational no-op for values of this type.
    ///
    /// In Miri (`Miri/Interpreter/Rvalue.lean` and `ValidityVisitor.lean`),
    /// `WithRetag::Yes` sets `RetagMode::Default` during `copyOp`, which calls
    /// `retagSafePointer` only inside `ValidityVisitor::checkSafe` on safe
    /// pointers (`&T`, `&mut T`, `Box<T>`). For reference-free scalar, unit,
    /// never, and fieldless-enum types, `WithRetag::Yes` and `WithRetag::No`
    /// have identical semantics. Any future `Ty` variant capable of carrying
    /// references or `Box` must return `false` so capture and Lean emission
    /// fail closed rather than erasing active retags.
    pub fn is_retag_noop(&self) -> bool {
        match self {
            Ty::Bool | Ty::Unit | Ty::Never | Ty::Int { .. } | Ty::Enum(_) => true,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Operand {
    Copy { local: u32 },
    Move { local: u32 },
    Constant { ty: Ty, bits: u64 },
}

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BinOp {
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Add,
    Sub,
    Mul,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Rvalue {
    Unit,
    Use {
        operand: Operand,
        with_retag: bool,
    },
    Binary {
        op: BinOp,
        left: Operand,
        right: Operand,
    },
    Discriminant {
        local: u32,
    },
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Statement {
    Assign { local: u32, value: Rvalue },
    StorageLive { local: u32 },
    StorageDead { local: u32 },
    Nop,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Terminator {
    Goto {
        block: u32,
    },
    SwitchInt {
        operand: Operand,
        targets: Vec<(u64, u32)>,
        otherwise: u32,
    },
    Ret,
    Unreachable,
}

#[derive(Clone, Debug, Serialize)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug, Serialize)]
pub struct Body {
    pub arg_count: usize,
    pub is_unsafe: bool,
    pub local_tys: Vec<Ty>,
    pub blocks: Vec<Block>,
    /// Source contract key, attached to the same body produced for its DefId.
    /// Inventory indices remain navigation metadata; this value enters the
    /// theorem subject and selects the reviewed unsafe caller requirements.
    pub identity: String,
}

/// Preserve scope in the logical subject, not only in a human-readable receipt.
/// A claim about selected bodies must remain distinct from whole-crate coverage.
#[derive(Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum VerificationScope {
    Unit,
    Crate,
}

#[derive(Debug, Serialize)]
pub struct Program {
    pub scope: VerificationScope,
    pub bodies: Vec<Body>,
}

/// The compiler that produced the capture and the executable checked against
/// it. `commit`, `commit_date`, and `mir_dialect` are [`LINKED_COMPILER`];
/// `version` is the linked libraries' own `rustc_version_str()`, which may be
/// a distribution's custom version text.
#[derive(Debug, Serialize)]
pub struct Compiler {
    pub commit: &'static str,
    pub commit_date: &'static str,
    pub version: &'static str,
    pub mir_dialect: &'static str,
    /// The `rustc` whose `--version --verbose` matched the linked compiler.
    pub rustc: PathBuf,
    pub sysroot: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExternFile {
    pub crate_name: String,
    pub path: PathBuf,
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DependencyArtifact {
    pub path: PathBuf,
    pub sha256: String,
}

#[derive(Debug, Serialize)]
pub struct Configuration {
    pub crate_root: PathBuf,
    pub crate_name: String,
    pub edition: String,
    pub target: String,
    pub cfg: Vec<String>,
    pub opt_level: u8,
    pub debug_assertions: bool,
    pub overflow_checks: bool,
    pub pointer_bits: u64,
    pub endian: &'static str,
    pub declared_source_files: Vec<PathBuf>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub externs: Vec<ExternFile>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub dependency_dirs: Vec<PathBuf>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub dependency_artifacts: Vec<DependencyArtifact>,
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Scope {
    SelectedUnit { roots: Vec<String> },
    Crate { roots: Vec<String> },
}

#[derive(Clone, Debug, Serialize)]
pub struct SourceFile {
    pub path: PathBuf,
    pub sha256: String,
    pub read_kind: &'static str,
}

/// Inventory every compiler definition independently of successful translation.
/// Separate required/selected flags expose unsupported unselected items without
/// implying that a selected-unit proof covers them.
#[derive(Debug, Serialize)]
pub struct CensusItem {
    pub def_id: u32,
    pub path: String,
    pub kind: String,
    pub has_body: bool,
    pub selected: bool,
    pub required: bool,
}

#[derive(Debug, Serialize)]
pub struct SelectedBody {
    pub def_id: u32,
    pub path: String,
    pub body_index: usize,
}

#[derive(Debug, Serialize)]
pub struct Unsupported {
    pub def_id: u32,
    pub path: String,
    pub reason: String,
}

/// Bind the proof subject to the compilation and observed input evidence.
/// JSON metadata supports host authentication and coverage checks; only the
/// owned `program` constructors are rendered into the Lean subject.
#[derive(Debug, Serialize)]
pub struct Manifest {
    pub schema_version: u32,
    pub mir_dialect: &'static str,
    pub compiler: Compiler,
    pub configuration: Configuration,
    pub scope: Scope,
    pub source_files: Vec<SourceFile>,
    pub externs: Vec<ExternFile>,
    pub census: Vec<CensusItem>,
    pub selected: Vec<SelectedBody>,
    pub unsupported: Vec<Unsupported>,
    pub program: Program,
}
