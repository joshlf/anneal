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
}

#[derive(PartialEq, Eq)]
pub enum FnKind {
    /// Not exported from the crate. Appears in `Mir.lean` only as a `call1`
    /// callee, not in `Crate.functions`.
    Private,
    /// Exported from the crate (`pub fn` or `pub unsafe fn`) and verified as a
    /// root in `Crate.functions`. Only `pub unsafe fn` may carry a `requires`
    /// clause (`items::function` enforces this at construction).
    Exported {
        requires: Option<RequiresSpec>,
        specs: Vec<Spec>,
    },
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
    /// First-order safety precondition (`MirBody.requires`), when the body
    /// belongs to an `unsafe fn` with `/// anneal:requires`.
    pub requires: Option<RequiresSpec>,
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
    Isize,
    Uint(u32),
    Int(u32),
    Float(u32),
    Bool,
    Char,
    Str,
    Unit,
    Never,
    /// `DefIdx` of the struct; mapped to its dense `AdtDecl.id` when
    /// rendering.
    Adt(DefIdx),
    Param(u32),
    Ref(Box<Ty>),
    RefMut(Box<Ty>),
    RawPtr(Box<Ty>, bool),
    Array(Box<Ty>, u64),
    Slice(Box<Ty>),
    Tuple(Vec<Ty>),
    FnDef(String),
    FnPtr,
    Unmodeled,
}

/// `Trusted.MirVal` (the literal fragment that can appear in `Operand.constVal`,
/// plus `Uninit` as the fail-closed placeholder for unmodeled constants).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    Uninit,
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
    /// Slice/array dynamic index (`p[_idx]`).
    Index(u32),
    /// Slice/array pattern constant index.
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    /// Slice/array subslice projection.
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    /// Enum/coroutine variant downcast.
    Downcast(u32),
    /// Opaque-type projection cast.
    OpaqueCast(Ty),
    /// Unsafe-binder unwrap projection.
    UnwrapUnsafeBinder(Ty),
}

/// `Trusted.Place`: a base local variable plus a list of projection elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Place {
    pub loc: u32,
    pub projection: Vec<PlaceElem>,
}

/// `Trusted.RuntimeChecks`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeChecks {
    UbChecks,
    ContractChecks,
    OverflowChecks,
}

/// `Trusted.Operand`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(Val),
    RuntimeChecks(RuntimeChecks),
}

/// `Trusted.RawPtrKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RawPtrKind {
    Mut,
    Const,
    FakeForPtrMetadata,
}

/// `Trusted.CastKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastKind {
    PointerExposeProvenance,
    PointerWithExposedProvenance,
    PointerCoercion,
    IntToInt,
    FloatToInt,
    FloatToFloat,
    IntToFloat,
    PtrToPtr,
    FnPtrToPtr,
    Transmute,
    Subtype,
}

/// `Trusted.UnOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
    PtrMetadata,
}

/// `Trusted.BinOp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    AddUnchecked,
    AddWithOverflow,
    Sub,
    SubUnchecked,
    SubWithOverflow,
    Mul,
    MulUnchecked,
    MulWithOverflow,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    ShlUnchecked,
    Shr,
    ShrUnchecked,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    Cmp,
    Offset,
}

/// `Trusted.Rvalue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    Repeat(Operand, u64),
    Ref(Place),
    RefMut(Place),
    RefFake(Place),
    ThreadLocalRef(u32),
    RawPtr(RawPtrKind, Place),
    Cast(CastKind, Operand, Ty),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
    Aggregate(DefIdx, Operand),
    AggregateFields(Vec<Operand>),
    CopyForDeref(Place),
    WrapUnsafeBinder(Operand, Ty),
    Reborrow(Ty, bool, Place),
}

/// `Trusted.NonDivergingIntrinsic`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NonDivergingIntrinsic {
    Assume(Operand),
    CopyNonOverlapping {
        src: Operand,
        dst: Operand,
        count: Operand,
    },
}

/// `Trusted.Stmt`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, u32),
    StorageLive(u32),
    StorageDead(u32),
    PlaceMention(Place),
    AscribeUserType(Place),
    Coverage,
    Intrinsic(NonDivergingIntrinsic),
    ConstEvalCounter,
    Nop,
    BackwardIncompatibleDropHint(Place),
}

/// `Trusted.Terminator`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminator {
    Return,
    Goto(u32),
    Unreachable,
    Panic {
        has_cleanup: bool,
    },
    UnwindResume,
    UnwindTerminate,
    Drop {
        place: Place,
        target: u32,
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: u32,
        has_cleanup: bool,
    },
    SwitchInt {
        discr: Operand,
        false_target: u32,
        true_target: u32,
    },
    SwitchIntGeneral {
        discr: Operand,
        targets: Vec<(u128, u32)>,
        otherwise: u32,
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
    Call {
        dst: Place,
        args: Vec<Operand>,
        target: Option<u32>,
    },
    TailCall {
        args: Vec<Operand>,
    },
    Yield {
        val: Operand,
        resume: u32,
        resume_arg: Place,
    },
    CoroutineDrop,
    FalseEdge {
        real_target: u32,
        imaginary_target: u32,
    },
    FalseUnwind {
        real_target: u32,
    },
    InlineAsm,
}

impl Body {
    /// Direct `Call1` callees of this body.
    pub fn callees(&self) -> impl Iterator<Item = DefIdx> + '_ {
        self.blocks.iter().filter_map(|blk| match &blk.terminator {
            Terminator::Call1 { callee, .. } => Some(*callee),
            _ => None,
        })
    }

    /// Required constants and direct `Call1` callees of this body.
    pub fn deps(&self) -> impl Iterator<Item = DefIdx> + '_ {
        self.required_consts
            .iter()
            .map(|(c, _)| *c)
            .chain(self.callees())
    }
}
