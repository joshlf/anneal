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

// Version 2 adds required source identities to every captured Body. Old capture
// subjects must be rejected before proof checking against this model ABI.
pub const SCHEMA_VERSION: u32 = 2;
pub const COMPILER_COMMIT: &str = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1";
pub const COMPILER_VERSION: &str = "1.98.0-nightly (f8a08b688 2026-05-30)";

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Ty {
    Bool,
    Unit,
    Never,
    Int { bits: u32, signed: bool },
    Enum { id: u32, discriminants: Vec<u64> },
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

#[derive(Debug, Serialize)]
pub struct Compiler {
    pub commit: &'static str,
    pub version: &'static str,
    pub sysroot: PathBuf,
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
    pub compiler: Compiler,
    pub configuration: Configuration,
    pub scope: Scope,
    pub source_files: Vec<SourceFile>,
    pub census: Vec<CensusItem>,
    pub selected: Vec<SelectedBody>,
    pub unsupported: Vec<Unsupported>,
    pub program: Program,
}
