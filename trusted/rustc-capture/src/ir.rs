// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Capture-internal representation of a Rust crate.
//!
//! These types mirror the first-order Lean structures in
//! `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean`
//! one-for-one, with `DefIdx` (a `rustc` `DefIndex`) standing in for body and
//! ADT references until `lean.rs` assigns Lean definition names and dense ADT
//! IDs. Keeping this layer free of `rustc` lifetimes lets item classification,
//! body extraction, cross-item checks, and Lean rendering be separate passes.

/// A crate-local definition's `DefIndex::as_u32()`.
pub type DefIdx = u32;

/// A captured crate, ready to render as `Mir.lean`.
pub struct Crate {
    /// Function and constant bodies, in dependency order (each body follows
    /// every body it calls or requires).
    pub bodies: Vec<(DefIdx, Body)>,
    /// Constants (`const`, associated `const`, inline `const { .. }`).
    pub constants: Vec<Constant>,
    /// Free functions (both `pub` roots and private callees).
    pub functions: Vec<Function>,
    /// `#[repr(transparent)]` single-field structs.
    pub adts: Vec<Adt>,
}

/// A constant item or inline `const { .. }` block (`DefKind::Const`,
/// `DefKind::AssocConst`, `DefKind::InlineConst`). Its body is in
/// `Crate::bodies` under `def`.
pub struct Constant {
    pub def: DefIdx,
    /// Human-readable path for the comment in `Mir.lean`.
    pub path: String,
}

/// A free function (`DefKind::Fn`). Its body is in `Crate::bodies` under `def`.
pub struct Function {
    pub def: DefIdx,
    pub name: String,
    pub kind: FnKind,
    /// Postconditions from `/// anneal:spec ...` (only on `PubSafe` /
    /// `PubUnsafe`).
    pub specs: Vec<Spec>,
}

#[derive(PartialEq, Eq)]
pub enum FnKind {
    /// Not exported from the crate. Appears in `Mir.lean` only as a `call1`
    /// callee, not in `Crate.functions`.
    Private,
    /// `pub fn`: verified from `defaultAdtInv` with `safetyPre = none`.
    PubSafe,
    /// `pub unsafe fn`: verified with `requires` as its `CapturedFn.requires`
    /// descriptor (`None` means `safetyPre = none`, i.e. trivially `True`) and
    /// excluded from `CrateTheorem`'s `SafeEntryTheorem` quantified safe-API
    /// surface.
    PubUnsafe { requires: Option<RequiresSpec> },
}

/// A `#[repr(transparent)]` single-field struct (`Trusted.AdtDecl`).
pub struct Adt {
    pub def: DefIdx,
    pub field_ty: Ty,
    pub access: FieldAccess,
    /// From `/// anneal:invariant <field> != <nat>`.
    pub invariant: Option<InvariantSpec>,
}

/// First-order representation invariant descriptor (`Trusted.InvariantSpec`):
/// `field_0 != ne`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvariantSpec {
    pub ne: u128,
}

/// First-order `# Safety` precondition descriptor (`Trusted.RequiresSpec`):
/// `_<arg_local> != ne`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequiresSpec {
    /// 1-based MIR local index (`_1`, `_2`, ...).
    pub arg_local: u32,
    pub ne: u128,
}

/// `Trusted.FieldAccess`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FieldAccess {
    PubSafe,
    Priv,
}

/// A parsed `/// anneal:spec ...` postcondition (`Trusted.PostSpec`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Spec {
    /// `ensures(ret == <param>)`, where `<param>` is the 1-based argument
    /// local (`_1`, `_2`, ...): `Trusted.PostSpec.ensuresEqArg <arg_local>`.
    EnsuresEqArg(u32),
}

/// `Trusted.MirBody`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub arg_tys: Vec<Ty>,
    pub ret_ty: Ty,
    pub local_count: u32,
    pub blocks: Vec<Block>,
    /// `(const_def, type_args)` pairs for `MirBody.requiredConsts`.
    pub required_consts: Vec<(DefIdx, Vec<Ty>)>,
}

/// `Trusted.BasicBlock`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

/// `Trusted.MirTy`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Usize,
    Bool,
    Unit,
    /// `DefIdx` of the struct; mapped to its dense `AdtDecl.id` when
    /// rendering.
    Adt(DefIdx),
    Param(u32),
    Ref(Box<Ty>),
}

/// `Trusted.MirVal` (the literal fragment that can appear in `Operand.constVal`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    Usize(u128),
    Bool(bool),
    Unit,
}

/// `Trusted.PlaceElem`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlaceElem {
    /// Dereference (`*p`).
    Deref,
    /// Struct field projection (`p.idx`).
    Field(u32),
}

/// `Trusted.Place`: a base local variable plus a list of projection elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Place {
    pub loc: u32,
    pub projection: Vec<PlaceElem>,
}

/// `Trusted.Operand`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(Val),
}

/// `Trusted.Rvalue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    Eq(Operand, Operand),
    Aggregate(DefIdx, Operand),
    Ref(Place),
}

/// `Trusted.Stmt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign(Place, Rvalue),
    PlaceMention(Place),
    StorageLive(u32),
    StorageDead(u32),
    Nop,
}

/// `Trusted.Terminator`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminator {
    Return,
    Goto(u32),
    Unreachable,
    Panic,
    Assert {
        cond: Operand,
        expected: bool,
        target: u32,
    },
    SwitchInt {
        discr: Operand,
        false_target: u32,
        true_target: u32,
    },
    SizeOf {
        dst: Place,
        ty: Ty,
        target: u32,
    },
    TransmuteCopy {
        dst: Place,
        src_ty: Ty,
        dst_ty: Ty,
        op: Operand,
        target: u32,
    },
    Call1 {
        dst: Place,
        callee: DefIdx,
        arg: Operand,
        target: u32,
        type_args: Vec<Ty>,
    },
}
