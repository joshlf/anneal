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
    /// Captured struct declarations (`#[repr(Rust)]`, `#[repr(C)]`, or
    /// `#[repr(transparent)]`).
    pub adts: Vec<Adt>,
}

/// A constant item or inline `const { .. }` block (`DefKind::Const`,
/// `DefKind::AssocConst`, `DefKind::InlineConst`). Its body is in
/// `Crate::bodies` under `def`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constant {
    pub def: DefIdx,
    /// Human-readable path for the comment in `Mir.lean`.
    pub path: String,
}

/// A free function (`DefKind::Fn`). Its primary (`release`) body is in
/// `Crate::bodies` under `def`; when the `debug` profile produces a distinct
/// MIR body, that body is stored in `Crate::bodies` under `debug_body`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    pub def: DefIdx,
    pub name: String,
    pub debug_body: Option<DefIdx>,
    pub is_unsafe: bool,
    pub kind: FnKind,
}

/// Layout-quantification waiver tier (`S0`, `S1`, or `S3`) for an exported
/// function.
///
/// The three tiers are mutually exclusive: a function either verifies
/// universally (`Universal`), relies on a compile-time `const` guard to reject
/// non-zero `#[repr(Rust)]` padding (`CompileTimeGuard`), or restricts
/// verification to the pinned compiler's zero-extra-padding layout
/// (`PinnedCompilerCoupled`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutWaiver {
    Universal,
    CompileTimeGuard,
    PinnedCompilerCoupled(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnKind {
    /// Not exported from the crate. Appears in `Mir.lean` only as a `call1`
    /// callee, not in `Crate.functions`.
    Private,
    /// Exported from the crate (`pub fn` or `pub unsafe fn`) and verified as a
    /// root in `Crate.functions`. Both `pub fn` and `pub unsafe fn` may carry a
    /// `requires` clause (`Function::is_unsafe` determines whether `requires`
    /// enters `SafetyPre` or only qualifies `ContractPost`).
    Exported {
        requires: Option<RequiresSpec>,
        specs: Vec<Spec>,
        trusted_reason: Option<String>,
        layout_waiver: LayoutWaiver,
        documented_intents: Vec<String>,
    },
}

/// `Trusted.AdtRepr`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdtRepr {
    Rust,
    Transparent,
    C,
}

/// `Trusted.FieldDecl`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDecl {
    pub ty: Ty,
    pub access: FieldAccess,
}

/// A captured struct (`Trusted.AdtDecl`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Adt {
    pub def: DefIdx,
    pub repr: AdtRepr,
    pub fields: Vec<FieldDecl>,
    /// From `/// anneal:invariant <field> != <nat>`.
    pub invariant: Option<InvariantSpec>,
}

/// First-order representation invariant descriptor (`Trusted.InvariantSpec`):
/// `field_0 != ne`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvariantSpec {
    pub ne: u128,
}

/// First-order precondition descriptor (`Trusted.RequiresSpec`):
/// `_<arg_local> != ne`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequiresSpec {
    /// 1-based MIR local index (`_1`, `_2`, ...).
    pub arg_local: u32,
    pub ne: u128,
}

/// `Trusted.FieldAccess`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
    /// Non-trivial local variable types for `MirBody.requiredLayouts`.
    pub required_layouts: Vec<Ty>,
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

impl Ty {
    /// Peels any outer shared-reference layers (`&T`) and returns the
    /// underlying struct's `DefIdx`, if the innermost type is `Ty::Adt`.
    pub fn referenced_adt(&self) -> Option<DefIdx> {
        let mut cur = self;
        while let Self::Ref(inner) = cur {
            cur = inner;
        }
        match cur {
            Self::Adt(id) => Some(*id),
            _ => None,
        }
    }

    /// Calls `f` on every `Ty::Adt(DefIdx)` appearing anywhere in `self`.
    pub fn for_each_adt(&self, f: &mut impl FnMut(DefIdx)) {
        match self {
            Self::Adt(id) => f(*id),
            Self::Ref(inner)
            | Self::RefMut(inner)
            | Self::RawPtr(inner, _)
            | Self::Array(inner, _)
            | Self::Slice(inner) => inner.for_each_adt(f),
            Self::Tuple(elems) => {
                for elem in elems {
                    elem.for_each_adt(f);
                }
            }
            Self::Usize
            | Self::Isize
            | Self::Uint(_)
            | Self::Int(_)
            | Self::Float(_)
            | Self::Bool
            | Self::Char
            | Self::Str
            | Self::Unit
            | Self::Never
            | Self::Param(_)
            | Self::FnDef(_)
            | Self::FnPtr
            | Self::Unmodeled => {}
        }
    }

    /// Replaces each `Param(i)` in `self` with `args[i]`; `None` is the
    /// identity substitution. An out-of-range index stays a `Param(i)`.
    pub fn subst(&self, args: Option<&[Self]>) -> Self {
        match (self, args) {
            (Self::Param(i), Some(a)) => {
                a.get(*i as usize).cloned().unwrap_or_else(|| self.clone())
            }
            (Self::Ref(inner), _) => Self::Ref(Box::new(inner.subst(args))),
            (Self::RefMut(inner), _) => {
                Self::RefMut(Box::new(inner.subst(args)))
            }
            (Self::RawPtr(inner, m), _) => {
                Self::RawPtr(Box::new(inner.subst(args)), *m)
            }
            (Self::Array(inner, len), _) => {
                Self::Array(Box::new(inner.subst(args)), *len)
            }
            (Self::Slice(inner), _) => Self::Slice(Box::new(inner.subst(args))),
            (Self::Tuple(elems), _) => {
                Self::Tuple(elems.iter().map(|e| e.subst(args)).collect())
            }
            (
                Self::Usize
                | Self::Isize
                | Self::Uint(_)
                | Self::Int(_)
                | Self::Float(_)
                | Self::Bool
                | Self::Char
                | Self::Str
                | Self::Unit
                | Self::Never
                | Self::Adt(_)
                | Self::Param(_)
                | Self::FnDef(_)
                | Self::FnPtr
                | Self::Unmodeled,
                _,
            ) => self.clone(),
        }
    }
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    Transmute(Ty),
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
    AggregateFields(Vec<Operand>, Option<DefIdx>),
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
    EvalConst {
        dst: Place,
        const_def: DefIdx,
        type_args: Vec<Ty>,
    },
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

/// `Trusted.AssertFailKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssertFailKind {
    Unwind,
    Abort,
    Ub,
}

/// `Trusted.LayoutQuery` (`core::mem::size_of` and `core::mem::align_of`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutQuery {
    SizeOf(Ty),
    AlignOf(Ty),
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
        on_fail: AssertFailKind,
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
    CallLayout {
        dst: Place,
        query: LayoutQuery,
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
