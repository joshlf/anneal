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
//! Each function below handles one MIR syntactic category and has a direct
//! 1-to-1 mapping to the corresponding Lean constructor; every other variant is
//! rejected. The translation is therefore a partial function whose domain is
//! the supported fragment, and the rejection message names the construct
//! `rustc` produced.
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
    self, AggregateKind, BinOp, BorrowKind, CallSource, ConstValue, MirPhase,
    ProjectionElem, RuntimePhase, StatementKind, TerminatorKind, UnwindAction,
};
use rustc_middle::ty::{self, GenericArgKind, Ty, TyCtxt, TypingEnv};
use rustc_span::def_id::{DefId, LOCAL_CRATE, LocalDefId};

use crate::ir;

/// Result of translation: the IR, or a human-readable rejection reason.
pub type Res<T> = Result<T, String>;

fn reject<T>(msg: impl Into<String>) -> Res<T> {
    Err(msg.into())
}

/// Translates a `rustc` type to `Trusted.MirTy`.
///
/// The accepted types are the value-type constructors of `MirTy`
/// (`rustc_type_ir::TyKind`, `compiler/rustc_type_ir/src/ty_kind.rs`):
///
/// - `Uint(Usize)` is `.usize`. The Lean model fixes `usize` at 8 bytes;
///   `items.rs` checks that the target's pointer size is 8 bytes.
/// - `Bool` is `.bool`, and the empty `Tuple` (the unit type `()`) is
///   `.unit`.
/// - `Adt(def, args)` is `.adt` when `def` is a struct of the target crate and
///   `args` is empty: the model's `MirTy.adt` carries no type arguments.
///   `items.rs` checks that the struct itself is in the fragment (one field,
///   no generics, matching layout).
/// - `Param(p)` is `.param p.index`. `items.rs` guarantees that every generic
///   item it accepts has only type parameters, so `p.index` is the position
///   among the item's type parameters, which is how `MirTy.param` indexes the
///   type arguments of a call or a required constant.
/// - `Ref(_, inner, Not)` (a shared reference `&T`) is `.ref`. The region is
///   erased in post-borrowck MIR and is irrelevant to the model.
///
/// Everything else is rejected, including other integer types, `char`, `str`,
/// slices, arrays, raw pointers, `&mut`, function pointers and items, closures,
/// `dyn` types, the never type `!` (accepted only for unused call
/// destinations; see `local_ty`), and non-empty tuples.
pub fn ty<'tcx>(t: Ty<'tcx>) -> Res<ir::Ty> {
    match *t.kind() {
        ty::Uint(ty::UintTy::Usize) => Ok(ir::Ty::Usize),
        ty::Bool => Ok(ir::Ty::Bool),
        ty::Tuple(elems) if elems.is_empty() => Ok(ir::Ty::Unit),
        ty::Adt(adt, args) => {
            let did = adt.did();
            if !did.is_local() || !args.is_empty() || !adt.is_struct() {
                return reject(format!(
                    "unsupported type `{t}`: only non-generic structs of this \
                     crate are supported"
                ));
            }
            Ok(ir::Ty::Adt(did.index.as_u32()))
        }
        ty::Param(p) => Ok(ir::Ty::Param(p.index)),
        ty::Ref(_, inner, ty::Mutability::Not) => {
            Ok(ir::Ty::Ref(Box::new(ty(inner)?)))
        }
        _ => reject(format!("unsupported type `{t}`")),
    }
}

/// Translates the type of a local that is never read: either a normal type
/// or the never type `!`.
///
/// `rustc` gives the destination of a call to a diverging function (such as
/// `core::hint::unreachable_unchecked`) type `!`. Such a local is never
/// assigned or read, and the model never sees its type, so `!` is accepted
/// here but not in signatures or operands.
fn local_ty<'tcx>(t: Ty<'tcx>) -> Res<()> {
    if t.is_never() { Ok(()) } else { ty(t).map(|_| ()) }
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
}

const KNOWN_CORE_FNS: &[(&[&str], Known)] = &[
    (&["mem", "size_of"], Known::SizeOf),
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
    for (local, decl) in locals.iter_enumerated() {
        local_ty(decl.ty).map_err(|e| format!("local {local:?}: {e}"))?;
    }
    let arg_tys = (1..=body.arg_count)
        .map(|i| ty(locals[mir::Local::from_usize(i)].ty))
        .collect::<Res<Vec<_>>>()?;
    let ret_ty = ty(locals[mir::RETURN_PLACE].ty)?;

    let typing_env = TypingEnv::post_analysis(tcx, def);
    let mut required_consts = Vec::new();
    for c in required {
        required_consts.push(required_const(tcx, typing_env, &c.const_)?);
    }

    let cx = BodyCx { tcx, body, required };
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

    Ok(ir::Body {
        arg_tys,
        ret_ty,
        local_count: u32::try_from(locals.len())
            .map_err(|_| "too many locals")?,
        blocks,
        required_consts,
    })
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
    if ty(const_ty)? != ir::Ty::Unit {
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
            GenericArgKind::Type(t) => ty(t),
            _ => reject("required constant has a non-type generic argument"),
        })
        .collect::<Res<Vec<_>>>()?;
    Ok((target.index.as_u32(), type_args))
}

/// Per-body context for translating statements and terminators.
struct BodyCx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    required: &'a [mir::ConstOperand<'tcx>],
}

fn local_index(l: mir::Local) -> u32 {
    l.as_u32()
}

impl<'a, 'tcx> BodyCx<'a, 'tcx> {
    /// Translates a `mir::Place` 1-to-1 into `ir::Place` (`loc` + `projection`).
    ///
    /// Supported projection elements (`MIR/syntax.rs#L1185-L1256`):
    /// - `ProjectionElem::Deref` on a shared reference (`&T`) -> `PlaceElem::Deref`.
    /// - `ProjectionElem::Field(f, field_ty)` on a crate-local struct ->
    ///   `PlaceElem::Field(f.as_u32())`.
    fn place(&self, p: &mir::Place<'tcx>) -> Res<ir::Place> {
        let mut cur_ty = self.body.local_decls[p.local].ty;
        let mut projection = Vec::with_capacity(p.projection.len());
        for elem in p.projection {
            match (elem, cur_ty.kind()) {
                (
                    ProjectionElem::Deref,
                    ty::Ref(_, inner, ty::Mutability::Not),
                ) => {
                    projection.push(ir::PlaceElem::Deref);
                    cur_ty = *inner;
                }
                (ProjectionElem::Field(f, field_ty), ty::Adt(adt, _))
                    if adt.did().is_local() && adt.is_struct() =>
                {
                    projection.push(ir::PlaceElem::Field(f.as_u32()));
                    cur_ty = field_ty;
                }
                _ => {
                    return reject(format!("unsupported place `{p:?}`"));
                }
            }
        }
        Ok(ir::Place {
            loc: local_index(p.local),
            projection,
        })
    }

    /// Translates a MIR constant operand to a `Trusted.MirVal`.
    ///
    /// `mir::Const` has three forms (`MIR/consts.rs#L212-L233`). Only two are
    /// accepted:
    ///
    /// - `Val(Scalar(Int(i)), ty)` with `ty` `usize` or `bool`, and
    ///   `Val(ZeroSized, ())`: an already-evaluated literal, which is its own
    ///   value.
    /// - `Unevaluated(uv, ())` that is listed in the body's `required_consts`:
    ///   the value of a successfully evaluated `()` constant is `()`, and the
    ///   success obligation is carried by `MirBody.requiredConsts`, which the
    ///   model checks before the body runs.
    ///
    /// `Ty` constants (from the type system, such as const generic
    /// parameters) and unevaluated constants of any other type are rejected:
    /// their value is not known without evaluating them.
    fn constant(&self, c: &mir::ConstOperand<'tcx>) -> Res<ir::Val> {
        match c.const_ {
            mir::Const::Val(ConstValue::Scalar(Scalar::Int(int)), t) => {
                match ty(t)? {
                    ir::Ty::Usize => {
                        Ok(ir::Val::Usize(int.to_bits_unchecked()))
                    }
                    ir::Ty::Bool => {
                        Ok(ir::Val::Bool(int.to_bits_unchecked() != 0))
                    }
                    other => reject(format!(
                        "unsupported scalar constant of type {other:?}"
                    )),
                }
            }
            mir::Const::Val(ConstValue::ZeroSized, t)
                if ty(t)? == ir::Ty::Unit =>
            {
                Ok(ir::Val::Unit)
            }
            mir::Const::Unevaluated(_, t) if ty(t)? == ir::Ty::Unit => {
                if self.required.iter().any(|r| r.const_ == c.const_) {
                    Ok(ir::Val::Unit)
                } else {
                    reject(format!(
                        "constant `{c:?}` is not listed in required_consts"
                    ))
                }
            }
            _ => reject(format!("unsupported constant `{c:?}`")),
        }
    }

    /// Translates an operand 1-to-1 into `ir::Operand`.
    ///
    /// `Operand` (`MIR/syntax.rs#L1303-L1330`) is `Copy(place)` ("Creates a
    /// value by loading the given place"), `Move(place)` (the same load,
    /// which "*may* additionally overwrite the place with `uninit` bytes"),
    /// or `Constant`.
    fn operand(&self, op: &mir::Operand<'tcx>) -> Res<ir::Operand> {
        match op {
            mir::Operand::Copy(p) => Ok(ir::Operand::Copy(self.place(p)?)),
            mir::Operand::Move(p) => Ok(ir::Operand::Move(self.place(p)?)),
            mir::Operand::Constant(c) => {
                Ok(ir::Operand::Const(self.constant(c)?))
            }
            mir::Operand::RuntimeChecks(_) => {
                reject("runtime-check operands are not supported")
            }
        }
    }

    /// Translates an rvalue 1-to-1 into `ir::Rvalue`.
    ///
    /// `Rvalue` is at `MIR/syntax.rs#L1363-L1470`. The accepted forms:
    ///
    /// - `Use(op, _retag)`: "Yields the operand unchanged, except for a
    ///   potential retag." The model has no aliasing model (only shared
    ///   references, no `&mut` or raw pointers), so the `WithRetag` flag is
    ///   irrelevant to it and both values are accepted.
    /// - `BinaryOp(Eq, (a, b))` is `binaryOp .eq`.
    /// - `Aggregate(Adt(S, 0, [], None, None), [op])` with `S` a crate-local
    ///   struct is `aggregate`: construction of the single-field struct `S`.
    ///   (`Aggregate` remains in runtime MIR for structs; the `RuntimePhase`
    ///   docs at `MIR/syntax.rs#L122-L141` list the kinds that are
    ///   disallowed.)
    /// - `Ref(_, Shared, place)` is `ref place` (including reborrows `&*_l`).
    ///
    /// Every other rvalue (casts, unary operators, other binary operators,
    /// raw pointers, `&mut`, repeat, discriminant, thread locals, ...) is
    /// rejected.
    fn rvalue(&self, rv: &mir::Rvalue<'tcx>) -> Res<ir::Rvalue> {
        match rv {
            mir::Rvalue::Use(op, _retag) => {
                Ok(ir::Rvalue::Use(self.operand(op)?))
            }
            mir::Rvalue::BinaryOp(BinOp::Eq, ops) => {
                Ok(ir::Rvalue::Eq(self.operand(&ops.0)?, self.operand(&ops.1)?))
            }
            mir::Rvalue::Aggregate(kind, ops) => match **kind {
                AggregateKind::Adt(did, variant, args, None, None)
                    if did.is_local()
                        && variant.as_u32() == 0
                        && args.is_empty()
                        && self.tcx.adt_def(did).is_struct()
                        && ops.len() == 1 =>
                {
                    let op = ops.iter().next().expect("length checked above");
                    Ok(ir::Rvalue::Aggregate(
                        did.index.as_u32(),
                        self.operand(op)?,
                    ))
                }
                _ => reject(format!("unsupported aggregate `{rv:?}`")),
            },
            mir::Rvalue::Ref(_, BorrowKind::Shared, p) => {
                Ok(ir::Rvalue::Ref(self.place(p)?))
            }
            _ => reject(format!("unsupported rvalue `{rv:?}`")),
        }
    }

    /// Translates a statement 1-to-1 into `ir::Stmt`.
    ///
    /// `StatementKind` is at `MIR/syntax.rs#L305-L470`. Accepted:
    ///
    /// - `Assign(place, rv)`.
    /// - `PlaceMention(place)`.
    /// - `StorageLive(_l)`, `StorageDead(_l)`.
    /// - `ConstEvalCounter` ("Other than in the const eval interpreter, this
    ///   is a no-op") and `Nop` ("No-op") are both `Stmt.nop`.
    fn stmt(&self, s: &StatementKind<'tcx>) -> Res<ir::Stmt> {
        match s {
            StatementKind::Assign(b) => {
                let (place, rv) = &**b;
                Ok(ir::Stmt::Assign(self.place(place)?, self.rvalue(rv)?))
            }
            StatementKind::PlaceMention(place) => {
                Ok(ir::Stmt::PlaceMention(self.place(place)?))
            }
            StatementKind::StorageLive(l) => {
                Ok(ir::Stmt::StorageLive(local_index(*l)))
            }
            StatementKind::StorageDead(l) => {
                Ok(ir::Stmt::StorageDead(local_index(*l)))
            }
            StatementKind::ConstEvalCounter | StatementKind::Nop => {
                Ok(ir::Stmt::Nop)
            }
            _ => reject(format!("unsupported statement `{s:?}`")),
        }
    }

    /// Translates a terminator.
    ///
    /// `TerminatorKind` is at `MIR/syntax.rs#L692-L998`. Accepted:
    ///
    /// - `Return`, `Goto`, and `Unreachable` ("Executing this terminator is
    ///   UB") map to the Lean constructors of the same names.
    /// - `Assert { cond, expected, target, unwind: UnwindAction::Continue, .. }`
    ///   (`MIR/syntax.rs#L755-L767`: "Jumps to the target if the condition has
    ///   the expected value, otherwise panics") maps to `Terminator.assert`.
    /// - `SwitchInt { discr, targets }` on a `bool` with exactly one target
    ///   value, `0`, is `switchInt discr falseTarget trueTarget`: "if the list
    ///   of switch targets contains the computed value, continues execution
    ///   at the associated basic block. Otherwise, continues execution at the
    ///   'otherwise' basic block." So value `0` (false) selects the listed
    ///   block and every other value (true) selects `otherwise`.
    /// - `Call` to one of the `core` functions in `KNOWN_CORE_FNS`, or to a
    ///   one-argument function of this crate (`call1`); see `call`.
    ///
    /// Rejected: `Drop`, `TailCall`, `InlineAsm`, unwinding terminators
    /// (including `Assert` with a non-`Continue` unwind action), and coroutine
    /// terminators.
    fn terminator(&self, t: &TerminatorKind<'tcx>) -> Res<ir::Terminator> {
        match t {
            TerminatorKind::Return => Ok(ir::Terminator::Return),
            TerminatorKind::Goto { target } => {
                Ok(ir::Terminator::Goto(target.as_u32()))
            }
            TerminatorKind::Unreachable => Ok(ir::Terminator::Unreachable),
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind: UnwindAction::Continue,
                ..
            } => Ok(ir::Terminator::Assert {
                cond: self.operand(cond)?,
                expected: *expected,
                target: target.as_u32(),
            }),
            TerminatorKind::SwitchInt { discr, targets } => {
                if !discr.ty(&self.body.local_decls, self.tcx).is_bool() {
                    return reject("switchInt on a non-bool discriminant");
                }
                let values: Vec<_> = targets.iter().collect();
                match values.as_slice() {
                    [(0, false_bb)] => Ok(ir::Terminator::SwitchInt {
                        discr: self.operand(discr)?,
                        false_target: false_bb.as_u32(),
                        true_target: targets.otherwise().as_u32(),
                    }),
                    _ => reject(format!(
                        "unsupported switchInt targets {values:?}"
                    )),
                }
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
            _ => reject(format!("unsupported terminator `{t:?}`")),
        }
    }

    /// Translates a `Call` terminator (`MIR/syntax.rs#L800-L822`).
    ///
    /// The callee must be a constant of function-item type (`FnDef`), so the
    /// called definition is static. Calls through function pointers or trait
    /// objects are rejected. `unwind` must be `Continue` (a panic in the
    /// callee propagates to this function's caller, which is how the model
    /// treats `.panic`); `Cleanup`, `Terminate`, and `Unreachable` unwind
    /// actions are rejected. `call_source` must be `Normal`, which excludes
    /// calls `rustc` synthesizes for overloaded operators and `match`
    /// comparisons.
    fn call(
        &self,
        func: &mir::Operand<'tcx>,
        args: &[rustc_span::Spanned<mir::Operand<'tcx>>],
        destination: &mir::Place<'tcx>,
        target: Option<mir::BasicBlock>,
        unwind: &UnwindAction,
        call_source: &CallSource,
    ) -> Res<ir::Terminator> {
        if !matches!(unwind, UnwindAction::Continue) {
            return reject(format!("unsupported unwind action {unwind:?}"));
        }
        if !matches!(call_source, CallSource::Normal) {
            return reject(format!("unsupported call source {call_source:?}"));
        }
        let Some((callee, gargs)) = func.const_fn_def() else {
            return reject(format!(
                "call through a non-constant callee `{func:?}`"
            ));
        };
        let type_args = gargs
            .iter()
            .map(|a| match a.kind() {
                GenericArgKind::Type(t) => ty(t),
                // Late-bound and erased regions do not appear in `FnDef`
                // arguments of the functions accepted by `items.rs`, which
                // have only type parameters. Reject anything else.
                _ => reject("call with a non-type generic argument"),
            })
            .collect::<Res<Vec<_>>>()?;
        let args: Vec<_> = args.iter().map(|a| &a.node).collect();
        let dst = || self.place(destination);
        let ret_target = |t: Option<mir::BasicBlock>| {
            t.map(|b| b.as_u32())
                .ok_or_else(|| "call has no return target".to_string())
        };

        if let Some(known) = known_core_fn(self.tcx, callee) {
            return match (known, type_args.as_slice(), args.as_slice()) {
                (Known::SizeOf, [t], []) => Ok(ir::Terminator::SizeOf {
                    dst: dst()?,
                    ty: t.clone(),
                    target: ret_target(target)?,
                }),
                // Whether a type-parameter source or destination is
                // allowed depends on which kind of body this is, so
                // `items::check_transmutes` decides it.
                (Known::TransmuteCopy, [src_ty, dst_ty], [op]) => {
                    Ok(ir::Terminator::TransmuteCopy {
                        dst: dst()?,
                        src_ty: src_ty.clone(),
                        dst_ty: dst_ty.clone(),
                        op: self.operand(op)?,
                        target: ret_target(target)?,
                    })
                }
                (Known::UnreachableUnchecked, [], []) if target.is_none() => {
                    Ok(ir::Terminator::Unreachable)
                }
                (Known::Panic, [], [_msg]) if target.is_none() => {
                    Ok(ir::Terminator::Panic)
                }
                _ => reject(format!(
                    "unsupported call shape for `{}`",
                    self.tcx.def_path_str(callee)
                )),
            };
        }

        if callee.is_local() && self.tcx.def_kind(callee) == DefKind::Fn {
            let [arg] = args.as_slice() else {
                return reject(format!(
                    "call to `{}` with {} arguments: only one-argument calls are modeled",
                    self.tcx.def_path_str(callee),
                    args.len()
                ));
            };
            return Ok(ir::Terminator::Call1 {
                dst: dst()?,
                callee: callee.index.as_u32(),
                arg: self.operand(arg)?,
                target: ret_target(target)?,
                type_args,
            });
        }

        reject(format!(
            "call to unsupported function `{}`",
            self.tcx.def_path_str(callee)
        ))
    }
}
