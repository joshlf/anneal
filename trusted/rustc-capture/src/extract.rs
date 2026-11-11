// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Translation of one `rustc` MIR body into the capture's IR (`ir.rs`).
//!
//! This module is the only place that reads `rustc_middle::mir` structures.
//! Each function below handles one MIR syntactic category and translates the
//! `Runtime(PostCleanup)` MIR grammar into the corresponding `ir.rs` and
//! `Trusted/MirAst.lean` constructors; semantic restrictions are enforced in
//! `Trusted/MirSemantics.lean`.
//!
//! All `rustc` sources cited below are at the pinned toolchain commit
//! `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (the commit of
//! `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, whose `rustc-src` component
//! ships with the pinned toolchain), at
//! `https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/<path>`.
//! `MIR` below abbreviates `compiler/rustc_middle/src/mir`.

use rustc_hir::def::DefKind;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::{
    self, AggregateKind, BinOp, BorrowKind, CallSource, CastKind, ConstValue,
    MirPhase, NonDivergingIntrinsic, ProjectionElem, RawPtrKind, RuntimeChecks,
    RuntimePhase, StatementKind, TerminatorKind, UnOp, UnwindAction,
};
use rustc_middle::ty::{self, GenericArgKind, Ty, TyCtxt, TypingEnv};
use rustc_span::def_id::{DefId, LOCAL_CRATE, LocalDefId};

use crate::ir;

/// Result of translation: the IR, or a human-readable rejection reason.
pub type Res<T> = Result<T, String>;

fn reject<T>(msg: impl Into<String>) -> Res<T> {
    Err(msg.into())
}

fn is_core_def_path(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    expected: &[&str],
) -> bool {
    if def_id.krate == LOCAL_CRATE
        || tcx.crate_name(def_id.krate).as_str() != "core"
    {
        return false;
    }
    let path = tcx.def_path(def_id);
    if path.data.len() != expected.len() {
        return false;
    }
    path.data.iter().zip(expected).all(|(elem, want)| {
        elem.disambiguator == 0
            && elem.data.get_opt_name().is_some_and(|n| n.as_str() == *want)
    })
}

fn is_core_atomic_usize<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: DefId,
    args: ty::GenericArgsRef<'tcx>,
) -> bool {
    is_core_def_path(tcx, did, &["sync", "atomic", "Atomic"])
        && args.len() == 1
        && args[0]
            .as_type()
            .is_some_and(|t| matches!(t.kind(), ty::Uint(ty::UintTy::Usize)))
}

/// Translates a `rustc` type to `Trusted.MirTy`
/// (`rustc_type_ir::TyKind`, `compiler/rustc_type_ir/src/ty_kind.rs`).
///
/// Types outside the modeled fragment translate to their corresponding
/// `Trusted.MirTy` constructor (or `ir::Ty::Unmodeled` for higher-ranked,
/// closure, coroutine, or foreign/generic ADT types), which
/// `Trusted/MirSemantics.lean` rejects fail-closed whenever evaluated.
pub fn ty<'tcx>(tcx: TyCtxt<'tcx>, t: Ty<'tcx>) -> ir::Ty {
    match *t.kind() {
        ty::Uint(ty::UintTy::Usize) => ir::Ty::Usize,
        ty::Int(ty::IntTy::Isize) => ir::Ty::Isize,
        ty::Uint(u) => ir::Ty::Uint(u.bit_width().unwrap() as u32),
        ty::Int(i) => ir::Ty::Int(i.bit_width().unwrap() as u32),
        ty::Float(f) => ir::Ty::Float(f.bit_width() as u32),
        ty::Bool => ir::Ty::Bool,
        ty::Char => ir::Ty::Char,
        ty::Str => ir::Ty::Str,
        ty::Never => ir::Ty::Never,
        ty::Tuple(elems) if elems.is_empty() => ir::Ty::Unit,
        ty::Tuple(elems) => {
            ir::Ty::Tuple(elems.iter().map(|e| ty(tcx, e)).collect())
        }
        ty::Adt(adt, args) => {
            let did = adt.did();
            if did.is_local() && args.is_empty() && adt.is_struct() {
                ir::Ty::Adt(did.index.as_u32())
            } else if args.is_empty()
                && is_core_def_path(tcx, did, &["sync", "atomic", "Ordering"])
            {
                ir::Ty::AtomicOrdering
            } else {
                ir::Ty::Unmodeled
            }
        }
        ty::Param(p) => ir::Ty::Param(p.index),
        ty::Ref(_, inner, ty::Mutability::Not) => {
            if let ty::Adt(adt, args) = *inner.kind()
                && is_core_atomic_usize(tcx, adt.did(), args)
            {
                ir::Ty::RefAtomicUsize
            } else {
                ir::Ty::Ref(Box::new(ty(tcx, inner)))
            }
        }
        ty::Ref(_, inner, ty::Mutability::Mut) => {
            ir::Ty::RefMut(Box::new(ty(tcx, inner)))
        }
        ty::RawPtr(inner, m) => {
            ir::Ty::RawPtr(Box::new(ty(tcx, inner)), m.is_mut())
        }
        ty::Array(inner, len) => match len.kind() {
            ty::ConstKind::Value(val) => {
                match val
                    .valtree
                    .try_to_leaf()
                    .and_then(|s| u64::try_from(s.to_bits_unchecked()).ok())
                {
                    Some(n) => ir::Ty::Array(Box::new(ty(tcx, inner)), n),
                    None => ir::Ty::Unmodeled,
                }
            }
            _ => ir::Ty::Unmodeled,
        },
        ty::Slice(inner) => ir::Ty::Slice(Box::new(ty(tcx, inner))),
        ty::FnDef(did, _) => ir::Ty::FnDef(format!("{did:?}")),
        ty::FnPtr(..) => ir::Ty::FnPtr,
        _ => ir::Ty::Unmodeled,
    }
}

/// The `core` functions the model gives meaning to, identified by their
/// definition path inside the `core` crate.
///
/// A path in `core` is a structural identity, not text: `tcx.def_path` is
/// `rustc`'s own name for the definition, and the target crate cannot add
/// items to `core`. The only `core` the target crate can link is the pinned
/// sysroot's (the host passes no `--extern` or `-L` flags), and the host
/// authenticates the sysroot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Known {
    /// `core::mem::size_of::<T>()` (`library/core/src/mem/mod.rs#L373`).
    SizeOf,
    /// `core::mem::align_of::<T>()` (`library/core/src/mem/mod.rs#L418`).
    AlignOf,
    /// `core::mem::transmute_copy::<Src, Dst>(&Src)`
    /// (`library/core/src/mem/mod.rs#L1073`).
    TransmuteCopy,
    /// `core::hint::unreachable_unchecked()`, whose safety contract is that
    /// it is never reached: "Reaching this function is *Undefined Behavior*."
    /// (`library/core/src/hint.rs#L16`). The model's `Terminator.unreachable`
    /// has exactly that meaning.
    UnreachableUnchecked,
    /// `core::panicking::panic(&'static str) -> !`
    /// (`library/core/src/panicking.rs#L138`), which `assert!(cond)` expands
    /// to. The model's `Terminator.panic` abstracts away the message.
    Panic,
    /// `core::sync::atomic::Atomic::<usize>::load(&self, order: Ordering) -> usize`
    /// (`library/core/src/sync/atomic.rs#L2868`).
    AtomicUsizeLoad,
}

const KNOWN_CORE_FNS: &[(&[&str], Known)] = &[
    (&["mem", "size_of"], Known::SizeOf),
    (&["mem", "align_of"], Known::AlignOf),
    (&["mem", "transmute_copy"], Known::TransmuteCopy),
    (&["hint", "unreachable_unchecked"], Known::UnreachableUnchecked),
    (&["panicking", "panic"], Known::Panic),
];

fn known_core_fn(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Known> {
    if def_id.krate == LOCAL_CRATE
        || tcx.crate_name(def_id.krate).as_str() != "core"
    {
        return None;
    }
    if tcx.def_kind(def_id) == DefKind::AssocFn
        && tcx.item_name(def_id).as_str() == "load"
    {
        let parent = tcx.parent(def_id);
        if matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: false })
            && let ty::Adt(adt, args) =
                *tcx.type_of(parent).skip_binder().kind()
            && is_core_atomic_usize(tcx, adt.did(), args)
        {
            return Some(Known::AtomicUsizeLoad);
        }
    }
    let path = tcx.def_path(def_id);
    let mut names = Vec::new();
    for elem in &path.data {
        // A nonzero disambiguator means two definitions share a name at this
        // level; none of the known functions are in that situation, so treat
        // it as unknown rather than guess.
        if elem.disambiguator != 0 {
            return None;
        }
        names.push(elem.data.get_opt_name()?.to_string());
    }
    KNOWN_CORE_FNS
        .iter()
        .find(|(p, _)| {
            p.len() == names.len() && p.iter().zip(&names).all(|(a, b)| a == b)
        })
        .map(|(_, k)| *k)
}

/// Translates one MIR body.
///
/// `body` must be the result of `mir_drops_elaborated_and_const_checked`,
/// which `hook.rs` guarantees. That query ends with
/// `run_analysis_to_runtime_passes`, which asserts that the body has reached
/// `MirPhase::Runtime(RuntimePhase::PostCleanup)`
/// (`compiler/rustc_mir_transform/src/lib.rs#L596-L598`):
///
/// > ```text
/// > debug!("runtime_mir_cleanup({:?})", did);
/// > run_runtime_cleanup_passes(tcx, body);
/// > assert!(body.phase == MirPhase::Runtime(RuntimePhase::PostCleanup));
/// > ```
///
/// This is the phase `Trusted/MirAst.lean` models. It is checked again here
/// so the claim does not rest on the hook's placement alone.
pub fn body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    body: &mir::Body<'tcx>,
) -> Res<ir::Body> {
    if body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup) {
        return reject(format!(
            "body is in phase {:?}, not Runtime(PostCleanup)",
            body.phase
        ));
    }
    if body.tainted_by_errors.is_some() {
        return reject("body is tainted by compilation errors");
    }
    if body.coroutine.is_some() {
        return reject("coroutines (async fn, gen blocks) are not supported");
    }
    // `Body::required_consts` (`MIR/mod.rs#L264-L271`):
    //
    // > Constants that are required to evaluate successfully for this MIR to
    // > be well-formed. [...] This is soundness-critical, we make a guarantee
    // > that all consts syntactically mentioned in a function have
    // > successfully evaluated if the function ever gets executed at runtime.
    //
    // `mir_promoted` computes it before any of the passes that produce this
    // phase (`compiler/rustc_mir_transform/src/lib.rs#L460-L462`), so `None`
    // here would mean the body did not come from the normal pipeline.
    let Some(required) = body.required_consts.as_deref() else {
        return reject("body has no computed required_consts");
    };

    let locals = &body.local_decls;
    let arg_tys = (1..=body.arg_count)
        .map(|i| ty(tcx, locals[mir::Local::from_usize(i)].ty))
        .collect::<Vec<_>>();
    let ret_ty = ty(tcx, locals[mir::RETURN_PLACE].ty);

    let mut required_layouts = Vec::new();
    for i in (body.arg_count + 1)..locals.len() {
        let local_ty = ty(tcx, locals[mir::Local::from_usize(i)].ty);
        if needs_layout_check(&local_ty, &arg_tys, &ret_ty)
            && !required_layouts.contains(&local_ty)
        {
            required_layouts.push(local_ty);
        }
    }

    let typing_env = TypingEnv::post_analysis(tcx, def);
    let mut expected_consts = Vec::new();
    for c in required {
        expected_consts.push(required_const(tcx, typing_env, &c.const_)?);
    }

    let cx = BodyCx {
        tcx,
        typing_env,
        body,
        required,
    };
    let mut blocks = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        // Cleanup (unwind) blocks only arise from drop glue or explicit
        // cleanup paths, neither of which the model has.
        if data.is_cleanup {
            return reject(format!("{bb:?} is a cleanup block"));
        }
        let stmts = data
            .statements
            .iter()
            .map(|s| cx.stmt(&s.kind))
            .collect::<Res<Vec<_>>>()
            .map_err(|e| format!("{bb:?}: {e}"))?;
        let terminator = cx
            .terminator(&data.terminator().kind)
            .map_err(|e| format!("{bb:?} terminator: {e}"))?;
        blocks.push(ir::Block { stmts, terminator });
    }

    for (req_def, req_args) in &expected_consts {
        let emitted = blocks.iter().any(|blk| {
            blk.stmts.iter().any(|s| {
                matches!(
                    s,
                    ir::Stmt::EvalConst {
                        const_def,
                        type_args,
                        ..
                    } if const_def == req_def && type_args == req_args
                )
            })
        });
        if !emitted {
            return reject(
                "required constant in `Body::required_consts` was not emitted \
                 as an `EvalConst` statement",
            );
        }
    }

    Ok(ir::Body {
        arg_tys,
        ret_ty,
        local_count: u32::try_from(locals.len())
            .map_err(|_| "too many locals")?,
        blocks,
        required_layouts,
    })
}

/// Whether a temporary local's type `t` requires an explicit entry in
/// `MirBody.requiredLayouts` beyond `argTys` and `retTy` (which
/// `LocalLayoutsAdmitted` already checks).
fn needs_layout_check(
    t: &ir::Ty,
    arg_tys: &[ir::Ty],
    ret_ty: &ir::Ty,
) -> bool {
    if matches!(
        t,
        ir::Ty::Usize
            | ir::Ty::Bool
            | ir::Ty::Unit
            | ir::Ty::Never
            | ir::Ty::RefAtomicUsize
            | ir::Ty::AtomicOrdering
    ) {
        return false;
    }
    if arg_tys.contains(t) || ret_ty == t {
        return false;
    }
    if let ir::Ty::Ref(inner) = t
        && (matches!(
            **inner,
            ir::Ty::Usize | ir::Ty::Bool | ir::Ty::Unit
        ) || arg_tys.contains(inner)
            || ret_ty == &**inner)
    {
        return false;
    }
    true
}

/// Translates one entry of `Body::required_consts` to the constant body it
/// requires and the type arguments at which it is required.
///
/// Every entry is `Const::Unevaluated` (`is_required_const`,
/// `MIR/consts.rs#L271-L280`, admits only unevaluated constants) naming a
/// definition and generic arguments (`UnevaluatedConst`,
/// `MIR/consts.rs#L459-L466`). The definition may be a trait's associated
/// constant (`<() as SizeEq<..>>::ASSERT`), whose body lives in whichever impl
/// trait resolution selects, so the capture asks `rustc` to resolve it with
/// `Instance::try_resolve` (`compiler/rustc_middle/src/ty/instance.rs`).
/// Resolution fails, and the capture rejects, when the impl depends on a type
/// parameter of the enclosing body: the model cannot choose an impl per
/// instantiation.
///
/// For an inline `const { .. }` block, `rustc` appends one synthetic argument,
/// the block's type, to the enclosing item's arguments (`InlineConstArgs`,
/// `compiler/rustc_middle/src/ty/sty.rs#L232-L236`): "Generic parameters from
/// the enclosing item, concatenated with the inferred type of the constant."
/// The block's body uses the enclosing item's parameter indices, so the type
/// arguments the model needs are the enclosing item's, without the synthetic
/// last one.
fn required_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    c: &mir::Const<'tcx>,
) -> Res<(ir::DefIdx, Vec<ir::Ty>)> {
    let mir::Const::Unevaluated(uv, const_ty) = *c else {
        return reject(format!(
            "required constant `{c:?}` is not an unevaluated constant"
        ));
    };
    if uv.promoted.is_some() {
        return reject("promoted constants are not supported");
    }
    // The model gives every required constant type `()`: a required constant
    // only contributes the obligation that it evaluates successfully.
    if ty(tcx, const_ty) != ir::Ty::Unit {
        return reject(format!(
            "required constant `{c:?}` does not have type `()`"
        ));
    }
    let instance =
        match ty::Instance::try_resolve(tcx, typing_env, uv.def, uv.args) {
            Ok(Some(i)) => i,
            _ => {
                return reject(format!(
                    "cannot resolve required constant `{c:?}` to a single body \
                 (constants selected by a generic trait impl are unsupported)"
                ));
            }
        };
    let ty::InstanceKind::Item(target) = instance.def else {
        return reject(format!(
            "required constant `{c:?}` resolves to a compiler shim"
        ));
    };
    if !target.is_local() {
        return reject(format!(
            "required constant `{c:?}` is defined outside this crate"
        ));
    }
    let mut args: Vec<_> = instance.args.iter().collect();
    if tcx.def_kind(target) == DefKind::InlineConst {
        args.pop();
    }
    let type_args = args
        .into_iter()
        .map(|a| match a.kind() {
            GenericArgKind::Type(t) => Ok(ty(tcx, t)),
            _ => reject("required constant has a non-type generic argument"),
        })
        .collect::<Res<Vec<_>>>()?;
    Ok((target.index.as_u32(), type_args))
}

/// Per-body context for translating statements and terminators.
struct BodyCx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &'a mir::Body<'tcx>,
    required: &'a [mir::ConstOperand<'tcx>],
}

fn local_index(l: mir::Local) -> u32 {
    l.as_u32()
}

fn runtime_checks(chk: RuntimeChecks) -> ir::RuntimeChecks {
    match chk {
        RuntimeChecks::UbChecks => ir::RuntimeChecks::UbChecks,
        RuntimeChecks::ContractChecks => ir::RuntimeChecks::ContractChecks,
        RuntimeChecks::OverflowChecks => ir::RuntimeChecks::OverflowChecks,
    }
}

fn raw_ptr_kind(k: RawPtrKind) -> ir::RawPtrKind {
    match k {
        RawPtrKind::Mut => ir::RawPtrKind::Mut,
        RawPtrKind::Const => ir::RawPtrKind::Const,
        RawPtrKind::FakeForPtrMetadata => ir::RawPtrKind::FakeForPtrMetadata,
    }
}

fn cast_kind(k: CastKind, src_ty: ir::Ty) -> ir::CastKind {
    match k {
        CastKind::PointerExposeProvenance => {
            ir::CastKind::PointerExposeProvenance
        }
        CastKind::PointerWithExposedProvenance => {
            ir::CastKind::PointerWithExposedProvenance
        }
        CastKind::PointerCoercion(..) => ir::CastKind::PointerCoercion,
        CastKind::IntToInt => ir::CastKind::IntToInt,
        CastKind::FloatToInt => ir::CastKind::FloatToInt,
        CastKind::FloatToFloat => ir::CastKind::FloatToFloat,
        CastKind::IntToFloat => ir::CastKind::IntToFloat,
        CastKind::PtrToPtr => ir::CastKind::PtrToPtr,
        CastKind::FnPtrToPtr => ir::CastKind::FnPtrToPtr,
        CastKind::Transmute => ir::CastKind::Transmute(src_ty),
        CastKind::Subtype => ir::CastKind::Subtype,
    }
}

fn un_op(op: UnOp) -> ir::UnOp {
    match op {
        UnOp::Not => ir::UnOp::Not,
        UnOp::Neg => ir::UnOp::Neg,
        UnOp::PtrMetadata => ir::UnOp::PtrMetadata,
    }
}

fn bin_op(op: BinOp) -> ir::BinOp {
    match op {
        BinOp::Add => ir::BinOp::Add,
        BinOp::AddUnchecked => ir::BinOp::AddUnchecked,
        BinOp::AddWithOverflow => ir::BinOp::AddWithOverflow,
        BinOp::Sub => ir::BinOp::Sub,
        BinOp::SubUnchecked => ir::BinOp::SubUnchecked,
        BinOp::SubWithOverflow => ir::BinOp::SubWithOverflow,
        BinOp::Mul => ir::BinOp::Mul,
        BinOp::MulUnchecked => ir::BinOp::MulUnchecked,
        BinOp::MulWithOverflow => ir::BinOp::MulWithOverflow,
        BinOp::Div => ir::BinOp::Div,
        BinOp::Rem => ir::BinOp::Rem,
        BinOp::BitXor => ir::BinOp::BitXor,
        BinOp::BitAnd => ir::BinOp::BitAnd,
        BinOp::BitOr => ir::BinOp::BitOr,
        BinOp::Shl => ir::BinOp::Shl,
        BinOp::ShlUnchecked => ir::BinOp::ShlUnchecked,
        BinOp::Shr => ir::BinOp::Shr,
        BinOp::ShrUnchecked => ir::BinOp::ShrUnchecked,
        BinOp::Eq => ir::BinOp::Eq,
        BinOp::Lt => ir::BinOp::Lt,
        BinOp::Le => ir::BinOp::Le,
        BinOp::Ne => ir::BinOp::Ne,
        BinOp::Ge => ir::BinOp::Ge,
        BinOp::Gt => ir::BinOp::Gt,
        BinOp::Cmp => ir::BinOp::Cmp,
        BinOp::Offset => ir::BinOp::Offset,
    }
}

impl<'a, 'tcx> BodyCx<'a, 'tcx> {
    /// Translates a `mir::Place` 1-to-1 into `ir::Place` (`loc` + `projection`).
    ///
    /// All 8 `ProjectionElem` variants (`MIR/syntax.rs#L1192-L1278`) are
    /// translated directly into `ir::PlaceElem`.
    fn place(&self, p: &mir::Place<'tcx>) -> ir::Place {
        let projection = p
            .projection
            .iter()
            .map(|elem| match elem {
                ProjectionElem::Deref => ir::PlaceElem::Deref,
                ProjectionElem::Field(f, _) => ir::PlaceElem::Field(f.as_u32()),
                ProjectionElem::Index(v) => {
                    ir::PlaceElem::Index(local_index(v))
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => ir::PlaceElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                },
                ProjectionElem::Subslice { from, to, from_end } => {
                    ir::PlaceElem::Subslice { from, to, from_end }
                }
                ProjectionElem::Downcast(_, v) => {
                    ir::PlaceElem::Downcast(v.as_u32())
                }
                ProjectionElem::OpaqueCast(t) => {
                    ir::PlaceElem::OpaqueCast(ty(self.tcx, t))
                }
                ProjectionElem::UnwrapUnsafeBinder(t) => {
                    ir::PlaceElem::UnwrapUnsafeBinder(ty(self.tcx, t))
                }
            })
            .collect();
        ir::Place {
            loc: local_index(p.local),
            projection,
        }
    }

    /// Translates a MIR constant operand to a `Trusted.MirVal`.
    ///
    /// `mir::Const` has three forms (`MIR/consts.rs#L212-L233`):
    ///
    /// - `Val(Scalar(Int(i)), ty)` with `ty` `usize`, `bool`, or
    ///   `core::sync::atomic::Ordering`, and `Val(ZeroSized, ())`: an
    ///   already-evaluated literal, which is its own value.
    /// - `Unevaluated(uv, ())` assigned as a statement (`_d = const ...`):
    ///   translated in `stmt` to `ir::Stmt::EvalConst`, which evaluates the
    ///   constant body in order at its statement position; an unevaluated `()`
    ///   constant appearing in any other operand position is rejected here.
    /// - Any other constant translates to `ir::Val::Uninit`, which
    ///   `Trusted.evalOperand` rejects fail-closed (`isFullyInit = false`) if
    ///   evaluated.
    fn constant(&self, c: &mir::ConstOperand<'tcx>) -> Res<ir::Val> {
        match c.const_ {
            mir::Const::Val(ConstValue::Scalar(Scalar::Int(int)), t) => {
                match ty(self.tcx, t) {
                    ir::Ty::Usize => {
                        Ok(ir::Val::Usize(int.to_bits_unchecked()))
                    }
                    ir::Ty::Bool => {
                        Ok(ir::Val::Bool(int.to_bits_unchecked() != 0))
                    }
                    ir::Ty::AtomicOrdering => match int.to_bits_unchecked() {
                        0 => Ok(ir::Val::Ordering(ir::AtomicOrdering::Relaxed)),
                        2 => Ok(ir::Val::Ordering(ir::AtomicOrdering::Acquire)),
                        _ => Ok(ir::Val::Uninit),
                    },
                    _ => Ok(ir::Val::Uninit),
                }
            }
            mir::Const::Val(ConstValue::ZeroSized, t)
                if ty(self.tcx, t) == ir::Ty::Unit =>
            {
                Ok(ir::Val::Unit)
            }
            mir::Const::Unevaluated(_, t) if ty(self.tcx, t) == ir::Ty::Unit => {
                reject(format!(
                    "unevaluated `()` constant `{c:?}` is only supported as a \
                     statement assignment"
                ))
            }
            _ => Ok(ir::Val::Uninit),
        }
    }

    /// Translates an operand 1-to-1 into `ir::Operand` (`MIR/syntax.rs#L1303-L1335`).
    fn operand(&self, op: &mir::Operand<'tcx>) -> Res<ir::Operand> {
        match op {
            mir::Operand::Copy(p) => Ok(ir::Operand::Copy(self.place(p))),
            mir::Operand::Move(p) => Ok(ir::Operand::Move(self.place(p))),
            mir::Operand::Constant(c) => {
                Ok(ir::Operand::Const(self.constant(c)?))
            }
            mir::Operand::RuntimeChecks(chk) => {
                Ok(ir::Operand::RuntimeChecks(runtime_checks(*chk)))
            }
        }
    }

    /// Translates an rvalue 1-to-1 into `ir::Rvalue` (`MIR/syntax.rs#L1363-L1488`).
    fn rvalue(&self, rv: &mir::Rvalue<'tcx>) -> Res<ir::Rvalue> {
        match rv {
            mir::Rvalue::Use(op, _retag) => {
                Ok(ir::Rvalue::Use(self.operand(op)?))
            }
            mir::Rvalue::Repeat(op, c) => Ok(ir::Rvalue::Repeat(
                self.operand(op)?,
                c.try_to_target_usize(self.tcx).unwrap_or(0),
            )),
            mir::Rvalue::Ref(_, BorrowKind::Shared, p) => {
                Ok(ir::Rvalue::Ref(self.place(p)))
            }
            mir::Rvalue::Ref(_, BorrowKind::Mut { .. }, p) => {
                Ok(ir::Rvalue::RefMut(self.place(p)))
            }
            mir::Rvalue::Ref(_, BorrowKind::Fake(_), p) => {
                Ok(ir::Rvalue::RefFake(self.place(p)))
            }
            mir::Rvalue::ThreadLocalRef(did) => {
                Ok(ir::Rvalue::ThreadLocalRef(did.index.as_u32()))
            }
            mir::Rvalue::RawPtr(k, p) => {
                Ok(ir::Rvalue::RawPtr(raw_ptr_kind(*k), self.place(p)))
            }
            mir::Rvalue::Cast(k, op, t) => {
                let src_ty = ty(self.tcx, op.ty(&self.body.local_decls, self.tcx));
                Ok(ir::Rvalue::Cast(
                    cast_kind(*k, src_ty),
                    self.operand(op)?,
                    ty(self.tcx, *t),
                ))
            }
            mir::Rvalue::BinaryOp(op, ops) => Ok(ir::Rvalue::BinaryOp(
                bin_op(*op),
                self.operand(&ops.0)?,
                self.operand(&ops.1)?,
            )),
            mir::Rvalue::UnaryOp(op, opnd) => {
                Ok(ir::Rvalue::UnaryOp(un_op(*op), self.operand(opnd)?))
            }
            mir::Rvalue::Discriminant(p) => {
                Ok(ir::Rvalue::Discriminant(self.place(p)))
            }
            mir::Rvalue::Aggregate(kind, ops) => match **kind {
                AggregateKind::Adt(did, variant, args, None, None)
                    if args.is_empty()
                        && ops.is_empty()
                        && is_core_def_path(
                            self.tcx,
                            did,
                            &["sync", "atomic", "Ordering"],
                        ) =>
                {
                    match variant.as_u32() {
                        0 => Ok(ir::Rvalue::Use(ir::Operand::Const(
                            ir::Val::Ordering(ir::AtomicOrdering::Relaxed),
                        ))),
                        2 => Ok(ir::Rvalue::Use(ir::Operand::Const(
                            ir::Val::Ordering(ir::AtomicOrdering::Acquire),
                        ))),
                        _ => Ok(ir::Rvalue::Use(ir::Operand::Const(
                            ir::Val::Uninit,
                        ))),
                    }
                }
                AggregateKind::Adt(did, variant, args, None, None)
                    if did.is_local()
                        && variant.as_u32() == 0
                        && args.is_empty()
                        && self.tcx.adt_def(did).is_struct() =>
                {
                    if ops.len() == 1 {
                        let op =
                            ops.iter().next().expect("length checked above");
                        Ok(ir::Rvalue::Aggregate(
                            did.index.as_u32(),
                            self.operand(op)?,
                        ))
                    } else {
                        let fields = ops
                            .iter()
                            .map(|o| self.operand(o))
                            .collect::<Res<Vec<_>>>()?;
                        Ok(ir::Rvalue::AggregateFields(
                            fields,
                            Some(did.index.as_u32()),
                        ))
                    }
                }
                _ => {
                    let fields = ops
                        .iter()
                        .map(|o| self.operand(o))
                        .collect::<Res<Vec<_>>>()?;
                    Ok(ir::Rvalue::AggregateFields(fields, None))
                }
            },
            mir::Rvalue::CopyForDeref(p) => {
                Ok(ir::Rvalue::CopyForDeref(self.place(p)))
            }
            mir::Rvalue::WrapUnsafeBinder(op, t) => Ok(
                ir::Rvalue::WrapUnsafeBinder(self.operand(op)?, ty(self.tcx, *t)),
            ),
            mir::Rvalue::Reborrow(t, m, p) => Ok(ir::Rvalue::Reborrow(
                ty(self.tcx, *t),
                m.is_mut(),
                self.place(p),
            )),
        }
    }

    /// Translates a statement 1-to-1 into `ir::Stmt` (`MIR/syntax.rs#L305-L456`).
    fn stmt(&self, s: &StatementKind<'tcx>) -> Res<ir::Stmt> {
        match s {
            StatementKind::Assign(b) => {
                let (place, rv) = &**b;
                if let mir::Rvalue::Use(mir::Operand::Constant(c), _) = rv
                    && let mir::Const::Unevaluated(_, t) = c.const_
                    && ty(self.tcx, t) == ir::Ty::Unit
                {
                    if !self.required.iter().any(|r| r.const_ == c.const_) {
                        return reject(format!(
                            "constant `{c:?}` is not listed in required_consts"
                        ));
                    }
                    let (const_def, type_args) = required_const(
                        self.tcx,
                        self.typing_env,
                        &c.const_,
                    )?;
                    return Ok(ir::Stmt::EvalConst {
                        dst: self.place(place),
                        const_def,
                        type_args,
                    });
                }
                Ok(ir::Stmt::Assign(self.place(place), self.rvalue(rv)?))
            }
            StatementKind::FakeRead(b) => {
                Ok(ir::Stmt::FakeRead(self.place(&b.1)))
            }
            StatementKind::SetDiscriminant { place, variant_index } => {
                Ok(ir::Stmt::SetDiscriminant(
                    self.place(place),
                    variant_index.as_u32(),
                ))
            }
            StatementKind::StorageLive(l) => {
                Ok(ir::Stmt::StorageLive(local_index(*l)))
            }
            StatementKind::StorageDead(l) => {
                Ok(ir::Stmt::StorageDead(local_index(*l)))
            }
            StatementKind::PlaceMention(place) => {
                Ok(ir::Stmt::PlaceMention(self.place(place)))
            }
            StatementKind::AscribeUserType(b, _) => {
                Ok(ir::Stmt::AscribeUserType(self.place(&b.0)))
            }
            StatementKind::Coverage(_) => Ok(ir::Stmt::Coverage),
            StatementKind::Intrinsic(intr) => {
                let intr = match &**intr {
                    NonDivergingIntrinsic::Assume(op) => {
                        ir::NonDivergingIntrinsic::Assume(self.operand(op)?)
                    }
                    NonDivergingIntrinsic::CopyNonOverlapping(c) => {
                        ir::NonDivergingIntrinsic::CopyNonOverlapping {
                            src: self.operand(&c.src)?,
                            dst: self.operand(&c.dst)?,
                            count: self.operand(&c.count)?,
                        }
                    }
                };
                Ok(ir::Stmt::Intrinsic(intr))
            }
            StatementKind::ConstEvalCounter => Ok(ir::Stmt::ConstEvalCounter),
            StatementKind::Nop => Ok(ir::Stmt::Nop),
            StatementKind::BackwardIncompatibleDropHint { place, .. } => {
                Ok(ir::Stmt::BackwardIncompatibleDropHint(self.place(place)))
            }
        }
    }

    /// Translates a terminator 1-to-1 into `ir::Terminator`
    /// (`MIR/syntax.rs#L692-L981`).
    fn terminator(&self, t: &TerminatorKind<'tcx>) -> Res<ir::Terminator> {
        match t {
            TerminatorKind::Return => Ok(ir::Terminator::Return),
            TerminatorKind::Goto { target } => {
                Ok(ir::Terminator::Goto(target.as_u32()))
            }
            TerminatorKind::Unreachable => Ok(ir::Terminator::Unreachable),
            TerminatorKind::UnwindResume => Ok(ir::Terminator::UnwindResume),
            TerminatorKind::UnwindTerminate(_) => {
                Ok(ir::Terminator::UnwindTerminate)
            }
            TerminatorKind::Drop { place, target, .. } => {
                Ok(ir::Terminator::Drop {
                    place: self.place(place),
                    target: target.as_u32(),
                })
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                msg,
            } => {
                let on_fail = if matches!(unwind, UnwindAction::Unreachable)
                    || matches!(
                        **msg,
                        mir::AssertKind::MisalignedPointerDereference { .. }
                            | mir::AssertKind::NullPointerDereference
                            | mir::AssertKind::InvalidEnumConstruction(_)
                    ) {
                    ir::AssertFailKind::Ub
                } else if matches!(
                    unwind,
                    UnwindAction::Continue | UnwindAction::Cleanup(_)
                ) {
                    ir::AssertFailKind::Unwind
                } else {
                    ir::AssertFailKind::Abort
                };
                Ok(ir::Terminator::Assert {
                    cond: self.operand(cond)?,
                    expected: *expected,
                    target: target.as_u32(),
                    on_fail,
                    has_cleanup: !matches!(unwind, UnwindAction::Continue),
                })
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let values: Vec<_> = targets.iter().collect();
                if discr.ty(&self.body.local_decls, self.tcx).is_bool()
                    && let [(0, false_bb)] = values.as_slice()
                {
                    return Ok(ir::Terminator::SwitchInt {
                        discr: self.operand(discr)?,
                        false_target: false_bb.as_u32(),
                        true_target: targets.otherwise().as_u32(),
                    });
                }
                Ok(ir::Terminator::SwitchIntGeneral {
                    discr: self.operand(discr)?,
                    targets: values
                        .into_iter()
                        .map(|(v, b)| (v, b.as_u32()))
                        .collect(),
                    otherwise: targets.otherwise().as_u32(),
                })
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                ..
            } => {
                self.call(func, args, destination, *target, unwind, call_source)
            }
            TerminatorKind::TailCall { args, .. } => {
                let args = args
                    .iter()
                    .map(|a| self.operand(&a.node))
                    .collect::<Res<Vec<_>>>()?;
                Ok(ir::Terminator::TailCall { args })
            }
            TerminatorKind::Yield { value, resume, resume_arg, .. } => {
                Ok(ir::Terminator::Yield {
                    val: self.operand(value)?,
                    resume: resume.as_u32(),
                    resume_arg: self.place(resume_arg),
                })
            }
            TerminatorKind::CoroutineDrop => Ok(ir::Terminator::CoroutineDrop),
            TerminatorKind::FalseEdge { real_target, imaginary_target } => {
                Ok(ir::Terminator::FalseEdge {
                    real_target: real_target.as_u32(),
                    imaginary_target: imaginary_target.as_u32(),
                })
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                Ok(ir::Terminator::FalseUnwind {
                    real_target: real_target.as_u32(),
                })
            }
            TerminatorKind::InlineAsm { .. } => Ok(ir::Terminator::InlineAsm),
        }
    }

    /// Translates a `Call` terminator (`MIR/syntax.rs#L800-L822`).
    ///
    /// Recognized calls to `KNOWN_CORE_FNS` and 1-argument crate-local
    /// `DefKind::Fn` definitions translate to their specialized
    /// `Trusted.Terminator` constructors; all other calls translate to the
    /// general `ir::Terminator::Call` constructor, which
    /// `Trusted/MirSemantics.lean` rejects fail-closed if reached.
    fn call(
        &self,
        func: &mir::Operand<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        destination: &mir::Place<'tcx>,
        target: Option<mir::BasicBlock>,
        unwind: &UnwindAction,
        call_source: &CallSource,
    ) -> Res<ir::Terminator> {
        let dst = self.place(destination);
        let op_args = args
            .iter()
            .map(|a| self.operand(&a.node))
            .collect::<Res<Vec<_>>>()?;
        let ret_target = target.map(|b| b.as_u32());
        let fallback = || ir::Terminator::Call {
            dst: dst.clone(),
            args: op_args.clone(),
            target: ret_target,
        };

        if !matches!(call_source, CallSource::Normal) {
            return Ok(fallback());
        }
        let Some((callee, gargs)) = func.const_fn_def() else {
            return Ok(fallback());
        };
        let mut type_args = Vec::with_capacity(gargs.len());
        for a in gargs {
            match a.kind() {
                GenericArgKind::Type(t) => type_args.push(ty(self.tcx, t)),
                _ => return Ok(fallback()),
            }
        }
        let has_cleanup = !matches!(unwind, UnwindAction::Continue);

        if let Some(known) = known_core_fn(self.tcx, callee) {
            return Ok(match (
                known,
                type_args.as_slice(),
                op_args.as_slice(),
                ret_target,
                has_cleanup,
            ) {
                (Known::SizeOf, [t], [], Some(target), false) => {
                    ir::Terminator::CallLayout {
                        dst,
                        query: ir::LayoutQuery::SizeOf(t.clone()),
                        target,
                    }
                }
                (Known::AlignOf, [t], [], Some(target), false) => {
                    ir::Terminator::CallLayout {
                        dst,
                        query: ir::LayoutQuery::AlignOf(t.clone()),
                        target,
                    }
                }
                (
                    Known::TransmuteCopy,
                    [src_ty, dst_ty],
                    [op],
                    Some(target),
                    false,
                ) => ir::Terminator::TransmuteCopy {
                    dst,
                    src_ty: src_ty.clone(),
                    dst_ty: dst_ty.clone(),
                    op: op.clone(),
                    target,
                },
                (Known::UnreachableUnchecked, [], [], None, false) => {
                    ir::Terminator::Unreachable
                }
                (Known::Panic, [], [_msg], None, has_cleanup) => {
                    ir::Terminator::Panic { has_cleanup }
                }
                (
                    Known::AtomicUsizeLoad,
                    [],
                    [ptr, ord],
                    Some(target),
                    false,
                ) => ir::Terminator::CallAtomicLoad {
                    dst,
                    ptr: ptr.clone(),
                    ord: ord.clone(),
                    target,
                },
                _ => fallback(),
            });
        }

        if has_cleanup {
            return Ok(fallback());
        }

        if callee.is_local()
            && self.tcx.def_kind(callee) == DefKind::Fn
            && let ([arg], Some(target)) = (op_args.as_slice(), ret_target)
        {
            return Ok(ir::Terminator::Call1 {
                dst,
                callee: callee.index.as_u32(),
                arg: arg.clone(),
                target,
                type_args,
            });
        }

        Ok(fallback())
    }
}
