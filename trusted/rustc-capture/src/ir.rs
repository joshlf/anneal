// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The capture's owned intermediate representation (IR).
//!
//! Every type here mirrors one inductive or structure of the Lean vocabulary
//! in `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`, constructor for
//! constructor, so that `lean.rs` can render each value by a one-line table
//! lookup. The IR exists for two reasons:
//!
//! - It owns its data. `rustc`'s MIR (`rustc_middle::mir::Body<'tcx>`) borrows
//!   from the compiler's arenas and cannot outlive the compiler session, while
//!   the capture must translate each body at the moment `rustc` produces it
//!   (see `hook.rs`) and assemble the crate later.
//! - Its type *is* the supported fragment. A value of this IR can only
//!   describe programs that the Lean model can describe; everything `rustc`
//!   produces outside that fragment is rejected during translation
//!   (`extract.rs`, `items.rs`) rather than approximated.
//!
//! The one deviation from the Lean vocabulary is that references to other
//! crate items (`MirTy.adt`, `Terminator.call1`'s callee, and
//! `MirBody.requiredConsts`) name the item by its `rustc` definition index
//! (`DefIdx`). `items.rs` later renumbers ADTs densely and assigns each body a
//! Lean definition name.

/// Crate-local `rustc_span::def_id::DefIndex`, as a plain integer.
///
/// Every captured item is local to the target crate, so the crate number of
/// its `DefId` is always `LOCAL_CRATE` and the index alone identifies it.
pub type DefIdx = u32;

/// `Trusted.MirTy`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Usize,
    Bool,
    Unit,
    /// A crate-local, non-generic, single-field struct.
    Adt(DefIdx),
    /// A function's (or impl's) type parameter, by position among the
    /// item's type parameters. `items.rs` guarantees that the item has no
    /// lifetime or const parameters and no parent generics other than an
    /// impl's, so this position equals `rustc`'s `ParamTy::index`.
    Param(u32),
    /// A shared reference `&T`.
    Ref(Box<Ty>),
}

/// `Trusted.MirVal`, restricted to the values a MIR constant operand can
/// denote. (`MirVal.adt`, `.bytes`, and `.ref` arise only during execution.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    Usize(u128),
    Bool(bool),
    Unit,
}

/// `Trusted.Operand`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Copy(u32),
    Move(u32),
    Const(Val),
}

/// `Trusted.Rvalue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    /// `BinaryOp(BinOp::Eq, ..)`, the only binary operator in the model.
    Eq(Operand, Operand),
    Aggregate(DefIdx, Operand),
    Field0(u32),
    Ref(u32),
    Reborrow(u32),
    CopyDeref(u32),
}

/// `Trusted.Stmt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign(u32, Rvalue),
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
    SwitchInt {
        discr: Operand,
        false_target: u32,
        true_target: u32,
    },
    SizeOf {
        dst: u32,
        ty: Ty,
        target: u32,
    },
    TransmuteCopy {
        dst: u32,
        src_ty: Ty,
        dst_ty: Ty,
        op: Operand,
        target: u32,
    },
    Call1 {
        dst: u32,
        callee: DefIdx,
        arg: Operand,
        target: u32,
        type_args: Vec<Ty>,
    },
}

/// `Trusted.BasicBlock`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

/// `Trusted.MirBody`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub arg_tys: Vec<Ty>,
    pub ret_ty: Ty,
    pub local_count: u32,
    pub blocks: Vec<Block>,
    /// Each entry names a constant body and the type arguments at which this
    /// body requires it to evaluate successfully.
    pub required_consts: Vec<(DefIdx, Vec<Ty>)>,
}

/// `Trusted.FieldAccess`. A field that safe code outside the crate cannot
/// set is `Priv`, whether it is non-public or (under the unstable
/// `unsafe_fields` feature, which the capture rejects anyway) `unsafe`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FieldAccess {
    PubSafe,
    Priv,
}

/// `Trusted.AdtDecl` with its single field, plus the optional representation
/// invariant from the struct's `anneal:invariant` attribute.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Adt {
    pub def: DefIdx,
    pub name: String,
    pub field_ty: Ty,
    pub access: FieldAccess,
    pub invariant: Option<InvariantSpec>,
}

/// Representation invariant of a single-`usize`-field struct: the field is not
/// equal to `ne`. This is the only invariant form the spec grammar accepts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvariantSpec {
    pub ne: u128,
}

/// The role of a captured function.
///
/// Public functions are the roots of `Trusted.Crate.functions`; an `unsafe`
/// one carries `CapturedFn.safetyPre`. Private functions have no entry in
/// `functions` and appear in `Mir.lean` only as `call1` callees: the Lean
/// model verifies them as part of each public caller, at the caller's type
/// arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnKind {
    PubSafe,
    /// `requires` is the safety precondition from `anneal:requires`, if any.
    PubUnsafe {
        requires: Option<RequiresSpec>,
    },
    Private,
}

/// Safety precondition: argument local `arg_local` (a `usize`) is not equal
/// to `ne`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequiresSpec {
    pub arg_local: u32,
    pub ne: u128,
}

/// One entry of `CapturedFn.specs`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Spec {
    /// `Trusted.EnsuresEqArg argLocal`.
    EnsuresEqArg(u32),
}

/// `Trusted.CapturedFn` (for public functions) or a callee body (for private
/// ones).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub def: DefIdx,
    pub name: String,
    pub kind: FnKind,
    pub specs: Vec<Spec>,
}

/// A captured constant body (an inline `const { .. }` block, a free `const`,
/// or an associated `const` in a trait impl). It appears in Lean only as the
/// target of some body's `requiredConsts`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constant {
    pub def: DefIdx,
    /// `rustc`'s path for the item, used only in a Lean comment and in
    /// diagnostics.
    pub path: String,
}

/// `Trusted.Crate` together with every body it references.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Crate {
    /// Every captured body (functions and constants) in dependency order:
    /// each body appears after every body it references, so the emitted Lean
    /// definitions are in scope where they are used.
    pub bodies: Vec<(DefIdx, Body)>,
    pub constants: Vec<Constant>,
    pub functions: Vec<Function>,
    pub adts: Vec<Adt>,
}
