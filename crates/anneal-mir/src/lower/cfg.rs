//! Basic-block terminators: static lowering ([`lower_terminator`]) and fuel-bounded
//! multi-block control-flow evaluation ([`eval_lowered_body_cfg`]), whose single steps are
//! [`eval_lowered_terminator`] (one terminator in an [`UnwindState`], yielding a [`CfgStep`]).
//!
//! # Control-flow semantics
//!
//! Execution starts in `bb0` (which must not be a cleanup block) with
//! [`StatementEvalState::from_body`]. Every executed basic block consumes one unit of fuel
//! *before* it runs, so `fuel == 0` immediately yields [`CfgEvalOutcome::OutOfFuel`] and an
//! infinite loop (`bb0: goto bb0`) terminates cleanly. A block runs its statements in order and
//! then its terminator:
//! - `Goto` jumps; `SwitchInt` jumps on the discriminant's bits (`bool` as `0`/`1`, `char` as
//!   its code point, integers as their bit pattern, which must fit their width), first
//!   matching value first;
//! - `Return` reads `_0`, which must be fully initialized (no `PartialShell`; initialization is
//!   tracked per local, so this also applies to a zero-sized `_0`), and returns it;
//! - `Unreachable` is undefined behavior ([`CfgEvalError::UnreachableReached`]);
//! - `Drop` checks that the place is live and well-formed and jumps to its target: Anneal's
//!   types have no drop glue, so dropping is a no-op that leaves the place's value (and an
//!   uninitialized place) unchanged;
//! - `Assert` jumps to its target when `cond == expected`, otherwise it panics with the
//!   evaluated message;
//! - `Call` evaluates the callee and arguments left to right (a `Move` of a bare local
//!   deinitializes it), checks the destination place, and then runs the callee: a function
//!   item of an inline intrinsic ([`CallTarget::Intrinsic`], see [`IntrinsicOp`]) executes in
//!   the calling frame ([`eval_intrinsic_call`]); a function item of a symbol linked in a
//!   [`CallTable`] runs the callee's body in a new frame (under
//!   [`eval_cfg_in_state_with_call_table`], [`eval_lowered_body_cfg_with_call_table`], or
//!   [`eval_lowered_body_cfg_with_call_table_and_calls`]); any other callee goes to the
//!   caller-supplied call handler (a [`CallHandler`], or an [`ExternalCallHandler`] given the
//!   [`ExternalCall`] under a call table; without a handler: [`CfgEvalError::UnsupportedCall`],
//!   or [`CfgEvalError::UnknownCallee`] for an unlinked symbol). A returned value must be well
//!   formed and of the destination's type, and is written to the destination before jumping
//!   to `target` (a return from a call without `target` is undefined behavior); a panicking
//!   call leaves the destination unchanged. `UnreachableUnchecked` is undefined behavior
//!   ([`CfgEvalError::UnreachableReached`]), `Abort` ends the evaluation with
//!   [`CfgEvalOutcome::Terminated`] without running any cleanup block, and `PanicUnwind`
//!   panics.
//!
//! A panic (failed `Assert`, a handler reporting [`CallOutcome::Panic`], a `PanicUnwind`
//! call, or a panicking linked callee) follows the
//! terminator's [`UnwindAction`]: `Continue` leaves the body ([`CfgEvalOutcome::Panicked`]),
//! `Terminate` aborts ([`CfgEvalOutcome::Terminated`]), `Unreachable` is undefined behavior
//! ([`CfgEvalError::UnwindIntoUnreachable`], the panic unwinds into an edge that must never
//! unwind), and `Cleanup(bb)` enters *unwinding mode* at cleanup block `bb`. In unwinding mode
//! only cleanup blocks execute (still consuming fuel), `UnwindResume` ends the body with
//! [`CfgEvalOutcome::Panicked`] for the original panic, `UnwindTerminate` with
//! [`CfgEvalOutcome::Terminated`], and a panic inside a cleanup block may only `Terminate` (or
//! is undefined behavior with `Unreachable`). Edges that break the cleanup discipline are
//! rejected by [`lower_terminator`], and again (for hand-built bodies) at runtime with
//! [`CfgEvalError::InvalidEdge`] / [`CfgEvalError::InvalidUnwind`].
//!
//! # Linked calls
//!
//! [`eval_cfg_in_state_with_call_table`], [`eval_lowered_body_cfg_with_call_table`], and
//! [`eval_lowered_body_cfg_with_call_table_and_calls`] run the callees of a [`CallTable`] on an
//! explicit frame stack that shares one fuel counter and is bounded by
//! [`CallTable::max_call_depth`]; see [`CallTable`] for argument passing, outcome propagation
//! across frames, and frame isolation. [`eval_cfg_in_state`] is the single-frame special case
//! (no table).

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    AssertMessage, BinOp, Body, CallTarget, CalleeSymbol, IntrinsicOp, Operand, Place,
    PointerValue, Provenance, PtrWidth, Safety, SwitchTargets, Terminator, Ty, UintTy,
    UnwindAction,
};
use crate::lower::cast::{CastEvalError, LoweredCast, reify_target};
use crate::lower::intrinsic::{
    IntrinsicOutcome, IntrinsicTypeError, check_intrinsic_call_types, eval_intrinsic_call,
};
use crate::lower::rvalue::{
    LocalSlotState, LoweredBasicBlock, LoweredBody, LoweredRvalue, LoweredStatement, MirValue,
    RvalueEvalError, RvalueLowerError, StatementEvalState, check_value_well_formed,
    eval_lowered_statement, lower_layout_error, lower_operand_ty, mir_value_matches_ty,
    resolve_place_ty,
};

/// Terminator-specific static lowering error (wrapped in
/// [`RvalueLowerError::InvalidTerminator`] with the block index).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TerminatorLowerError {
    /// Jump target is not a basic block of the body.
    InvalidTarget { target: usize, num_blocks: usize },
    /// Edge violating the cleanup discipline (a normal edge between a cleanup and a
    /// non-cleanup block, or an unwind edge into a non-cleanup block).
    InvalidEdge { target: usize, reason: &'static str },
    /// Unwind action not allowed here (`Cleanup` or `Continue` inside a cleanup block).
    InvalidUnwindAction {
        unwind: UnwindAction,
        reason: &'static str,
    },
    /// `SwitchInt` discriminant is not a `bool`, `char`, or integer.
    InvalidSwitchDiscrType(Ty),
    /// `SwitchTargets` has a different number of values and targets.
    SwitchTargetsLengthMismatch { values: usize, targets: usize },
    /// `SwitchTargets` lists the same value twice.
    DuplicateSwitchValue(u128),
    /// `SwitchTargets` value is not a valid bit pattern of the discriminant's type.
    SwitchValueOutOfRange { value: u128, discr_ty: Ty },
    /// `Assert` condition is not a `bool`.
    InvalidAssertCondType(Ty),
    /// `AssertMessage` operand has the wrong type.
    InvalidAssertMessageOperand { expected: &'static str, got: Ty },
    /// `Return` in a body without a return place `_0`.
    MissingReturnPlace,
    /// `Return` of an uninhabited return place type (`-> !` functions cannot return).
    UninhabitedReturnPlace(Ty),
    /// `Return` in a cleanup block.
    ReturnInCleanupBlock,
    /// `UnwindResume` / `UnwindTerminate` outside a cleanup block.
    UnwindTerminatorOutsideCleanup,
    /// `Call` with a `target` although its destination type is uninhabited.
    CallToUninhabitedDestinationWithTarget(Ty),
    /// The entry block `bb0` is a cleanup block.
    CleanupEntryBlock,
    /// `Call` of the inline intrinsic `op` whose argument or destination types do not match
    /// `op`'s signature (see [`IntrinsicOp`] and [`check_intrinsic_call_types`]).
    InvalidIntrinsicCall {
        op: IntrinsicOp,
        reason: &'static str,
    },
    /// Indirect `Call` through a function pointer (`Ty::FnPtr { inputs, output, .. }`) whose
    /// argument types differ from `inputs` or whose destination type differs from `output`.
    InvalidFnPtrCall { reason: &'static str },
}

impl std::fmt::Display for TerminatorLowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TerminatorLowerError::InvalidTarget { target, num_blocks } => {
                write!(
                    f,
                    "jump target bb{target} out of range for {num_blocks} blocks"
                )
            }
            TerminatorLowerError::InvalidEdge { target, reason } => {
                write!(f, "invalid edge to bb{target}: {reason}")
            }
            TerminatorLowerError::InvalidUnwindAction { unwind, reason } => {
                write!(f, "invalid unwind action {unwind:?}: {reason}")
            }
            TerminatorLowerError::InvalidSwitchDiscrType(ty) => {
                write!(
                    f,
                    "SwitchInt discriminant must be bool, char, or an integer, got {ty:?}"
                )
            }
            TerminatorLowerError::SwitchTargetsLengthMismatch { values, targets } => {
                write!(f, "SwitchTargets has {values} values but {targets} targets")
            }
            TerminatorLowerError::DuplicateSwitchValue(value) => {
                write!(f, "SwitchTargets lists value {value:#x} twice")
            }
            TerminatorLowerError::SwitchValueOutOfRange { value, discr_ty } => {
                write!(
                    f,
                    "SwitchTargets value {value:#x} is not a valid {discr_ty:?}"
                )
            }
            TerminatorLowerError::InvalidAssertCondType(ty) => {
                write!(f, "Assert condition must be bool, got {ty:?}")
            }
            TerminatorLowerError::InvalidAssertMessageOperand { expected, got } => {
                write!(f, "Assert message operand must be {expected}, got {got:?}")
            }
            TerminatorLowerError::MissingReturnPlace => {
                write!(f, "Return without a return place _0")
            }
            TerminatorLowerError::UninhabitedReturnPlace(ty) => {
                write!(f, "Return of uninhabited return place type {ty:?}")
            }
            TerminatorLowerError::ReturnInCleanupBlock => write!(f, "Return in a cleanup block"),
            TerminatorLowerError::UnwindTerminatorOutsideCleanup => {
                write!(f, "UnwindResume/UnwindTerminate outside a cleanup block")
            }
            TerminatorLowerError::CallToUninhabitedDestinationWithTarget(ty) => {
                write!(
                    f,
                    "Call returning uninhabited type {ty:?} must not have a target"
                )
            }
            TerminatorLowerError::CleanupEntryBlock => {
                write!(f, "entry block bb0 is a cleanup block")
            }
            TerminatorLowerError::InvalidIntrinsicCall { op, reason } => {
                write!(f, "ill-typed call of intrinsic {op}: {reason}")
            }
            TerminatorLowerError::InvalidFnPtrCall { reason } => {
                write!(f, "ill-typed call through a function pointer: {reason}")
            }
        }
    }
}

impl std::error::Error for TerminatorLowerError {}

/// Lowered, type-checked basic-block terminator (see [`Terminator`] for the meaning of each
/// variant). Every variant carries the static types its runtime checks compare against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweredTerminator {
    /// `Goto`.
    Goto { target: usize },
    /// `SwitchInt` on a `discr` of type `discr_ty` (`bool`, `char`, or an integer).
    SwitchInt {
        discr: Operand,
        discr_ty: Ty,
        targets: SwitchTargets,
    },
    /// `Return` of `_0`, whose declared type is `ret_ty`.
    Return { ret_ty: Ty },
    /// `Unreachable`.
    Unreachable,
    /// `Drop` of `place`, whose declared type is `place_ty`.
    Drop {
        place: Place,
        place_ty: Ty,
        target: usize,
        unwind: UnwindAction,
    },
    /// `Assert` of a `bool` condition.
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertMessage,
        target: usize,
        unwind: UnwindAction,
    },
    /// `Call` with the static types of the callee, the arguments, and the destination.
    Call {
        func: Operand,
        func_ty: Ty,
        args: Vec<Operand>,
        arg_tys: Vec<Ty>,
        destination: Place,
        dest_ty: Ty,
        target: Option<usize>,
        unwind: UnwindAction,
    },
    /// `UnwindResume` (cleanup blocks only).
    UnwindResume,
    /// `UnwindTerminate` (cleanup blocks only).
    UnwindTerminate,
}

impl LoweredTerminator {
    /// Direct [`CallTarget`] if this terminator is a `Call` of a [`Constant::FnDef`] function
    /// item (`None` for indirect `Call`s and non-`Call` terminators).
    ///
    /// [`Constant::FnDef`]: crate::ir::Constant::FnDef
    pub fn call_target(&self) -> Option<&CallTarget> {
        match self {
            LoweredTerminator::Call { func, .. } => func.call_target(),
            _ => None,
        }
    }
}

/// Lowers the terminator `term` of basic block `bb` of `body` under `ptr_width`.
///
/// Checks every jump target against the body's blocks and `rustc`'s cleanup discipline (normal
/// edges stay within cleanup or non-cleanup blocks; `UnwindAction::Cleanup(t)` only from a
/// non-cleanup block into a cleanup block `t`; no `UnwindAction::Continue` in cleanup blocks;
/// `Return` only outside and `UnwindResume`/`UnwindTerminate` only inside cleanup blocks; the
/// entry block is not a cleanup block), and type-checks the operands and places: a `SwitchInt`
/// discriminant of type `bool`/`char`/integer with distinct values valid for that type, an
/// `Assert` condition of type `bool` and well-typed message operands, a well-formed `Drop`
/// place, a `Call` whose destination is inhabited when it has a target, and an inhabited
/// return place `_0` for `Return`. A `Call` of an inline intrinsic
/// ([`CallTarget::Intrinsic`]) must also match the intrinsic's signature
/// ([`check_intrinsic_call_types`]: [`TerminatorLowerError::InvalidIntrinsicCall`], or the
/// layout error of a pointee without an exact layout).
pub fn lower_terminator(
    term: &Terminator,
    bb: usize,
    body: &Body,
    ptr_width: PtrWidth,
) -> Result<LoweredTerminator, RvalueLowerError> {
    let invalid = |error: TerminatorLowerError| RvalueLowerError::InvalidTerminator { bb, error };
    let num_blocks = body.basic_blocks.len();
    let Some(block) = body.basic_blocks.get(bb) else {
        return Err(invalid(TerminatorLowerError::InvalidTarget {
            target: bb,
            num_blocks,
        }));
    };
    let is_cleanup = block.is_cleanup;
    if bb == 0 && is_cleanup {
        return Err(invalid(TerminatorLowerError::CleanupEntryBlock));
    }
    let local_decls = &body.local_decls;
    let check_normal_edge = |target: usize| -> Result<(), RvalueLowerError> {
        let Some(target_block) = body.basic_blocks.get(target) else {
            return Err(invalid(TerminatorLowerError::InvalidTarget {
                target,
                num_blocks,
            }));
        };
        if target_block.is_cleanup != is_cleanup {
            return Err(invalid(TerminatorLowerError::InvalidEdge {
                target,
                reason: "normal edge between a cleanup and a non-cleanup block",
            }));
        }
        Ok(())
    };
    let check_unwind = |unwind: UnwindAction| -> Result<(), RvalueLowerError> {
        match unwind {
            UnwindAction::Cleanup(target) => {
                if is_cleanup {
                    return Err(invalid(TerminatorLowerError::InvalidUnwindAction {
                        unwind,
                        reason: "UnwindAction::Cleanup in a cleanup block",
                    }));
                }
                let Some(target_block) = body.basic_blocks.get(target) else {
                    return Err(invalid(TerminatorLowerError::InvalidTarget {
                        target,
                        num_blocks,
                    }));
                };
                if !target_block.is_cleanup {
                    return Err(invalid(TerminatorLowerError::InvalidEdge {
                        target,
                        reason: "unwind edge into a non-cleanup block",
                    }));
                }
                Ok(())
            }
            UnwindAction::Continue if is_cleanup => {
                Err(invalid(TerminatorLowerError::InvalidUnwindAction {
                    unwind,
                    reason: "UnwindAction::Continue in a cleanup block",
                }))
            }
            UnwindAction::Continue | UnwindAction::Terminate | UnwindAction::Unreachable => Ok(()),
        }
    };
    match term {
        Terminator::Goto { target } => {
            check_normal_edge(*target)?;
            Ok(LoweredTerminator::Goto { target: *target })
        }
        Terminator::SwitchInt { discr, targets } => {
            let discr_ty = lower_operand_ty(discr, local_decls, ptr_width)?;
            if !matches!(discr_ty, Ty::Bool | Ty::Char | Ty::Int(_) | Ty::Uint(_)) {
                return Err(invalid(TerminatorLowerError::InvalidSwitchDiscrType(
                    discr_ty,
                )));
            }
            if targets.values.len() != targets.targets.len() {
                return Err(invalid(TerminatorLowerError::SwitchTargetsLengthMismatch {
                    values: targets.values.len(),
                    targets: targets.targets.len(),
                }));
            }
            let mut seen = BTreeSet::new();
            for value in &targets.values {
                if !seen.insert(*value) {
                    return Err(invalid(TerminatorLowerError::DuplicateSwitchValue(*value)));
                }
                if !discr_ty.is_valid_scalar_bits(*value, ptr_width) {
                    return Err(invalid(TerminatorLowerError::SwitchValueOutOfRange {
                        value: *value,
                        discr_ty,
                    }));
                }
            }
            for target in targets.all_targets() {
                check_normal_edge(target)?;
            }
            Ok(LoweredTerminator::SwitchInt {
                discr: discr.clone(),
                discr_ty,
                targets: targets.clone(),
            })
        }
        Terminator::Return => {
            if is_cleanup {
                return Err(invalid(TerminatorLowerError::ReturnInCleanupBlock));
            }
            let Some(ret_ty) = local_decls.first() else {
                return Err(invalid(TerminatorLowerError::MissingReturnPlace));
            };
            if !ret_ty.is_inhabited_for(ptr_width) {
                return Err(invalid(TerminatorLowerError::UninhabitedReturnPlace(
                    ret_ty.clone(),
                )));
            }
            Ok(LoweredTerminator::Return {
                ret_ty: ret_ty.clone(),
            })
        }
        Terminator::Unreachable => Ok(LoweredTerminator::Unreachable),
        Terminator::Drop {
            place,
            target,
            unwind,
        } => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            check_normal_edge(*target)?;
            check_unwind(*unwind)?;
            Ok(LoweredTerminator::Drop {
                place: place.clone(),
                place_ty,
                target: *target,
                unwind: *unwind,
            })
        }
        Terminator::Assert {
            cond,
            expected,
            msg,
            target,
            unwind,
        } => {
            let cond_ty = lower_operand_ty(cond, local_decls, ptr_width)?;
            if cond_ty != Ty::Bool {
                return Err(invalid(TerminatorLowerError::InvalidAssertCondType(
                    cond_ty,
                )));
            }
            let operand = |op: &Operand,
                           expected: &'static str,
                           ok: &dyn Fn(&Ty) -> bool|
             -> Result<Ty, RvalueLowerError> {
                let ty = lower_operand_ty(op, local_decls, ptr_width)?;
                if !ok(&ty) {
                    return Err(invalid(TerminatorLowerError::InvalidAssertMessageOperand {
                        expected,
                        got: ty,
                    }));
                }
                Ok(ty)
            };
            let is_usize = |ty: &Ty| *ty == Ty::Uint(UintTy::Usize);
            match msg {
                AssertMessage::BoundsCheck { len, index } => {
                    operand(len, "usize", &is_usize)?;
                    operand(index, "usize", &is_usize)?;
                }
                AssertMessage::Overflow(op, lhs, rhs) => {
                    let lhs_ty = operand(lhs, "an integer", &Ty::is_integral)?;
                    let rhs_ty = operand(rhs, "an integer", &Ty::is_integral)?;
                    let shift = matches!(
                        op,
                        BinOp::Shl | BinOp::Shr | BinOp::ShlUnchecked | BinOp::ShrUnchecked
                    );
                    if !shift && lhs_ty != rhs_ty {
                        return Err(invalid(TerminatorLowerError::InvalidAssertMessageOperand {
                            expected: "an integer of the left operand's type",
                            got: rhs_ty,
                        }));
                    }
                }
                AssertMessage::OverflowNeg(op) => {
                    operand(op, "a signed integer", &Ty::is_signed_int)?;
                }
                AssertMessage::DivisionByZero(op)
                | AssertMessage::RemainderByZero(op)
                | AssertMessage::InvalidEnumConstruction(op) => {
                    operand(op, "an integer", &Ty::is_integral)?;
                }
                AssertMessage::MisalignedPointerDereference { required, found } => {
                    operand(required, "usize", &is_usize)?;
                    operand(found, "usize", &is_usize)?;
                }
                AssertMessage::NullPointerDereference | AssertMessage::Custom(_) => {}
            }
            check_normal_edge(*target)?;
            check_unwind(*unwind)?;
            Ok(LoweredTerminator::Assert {
                cond: cond.clone(),
                expected: *expected,
                msg: msg.clone(),
                target: *target,
                unwind: *unwind,
            })
        }
        Terminator::Call {
            func,
            args,
            destination,
            target,
            unwind,
        } => {
            let func_ty = lower_operand_ty(func, local_decls, ptr_width)?;
            let arg_tys = args
                .iter()
                .map(|arg| lower_operand_ty(arg, local_decls, ptr_width))
                .collect::<Result<Vec<_>, _>>()?;
            let dest_ty = resolve_place_ty(destination, local_decls)?;
            if let Some(target) = target {
                if !dest_ty.is_inhabited_for(ptr_width) {
                    return Err(invalid(
                        TerminatorLowerError::CallToUninhabitedDestinationWithTarget(dest_ty),
                    ));
                }
                check_normal_edge(*target)?;
            }
            check_unwind(*unwind)?;
            if let Some(CallTarget::Intrinsic(op)) = call_target_of(func) {
                check_intrinsic_call_types(*op, &arg_tys, &dest_ty, ptr_width).map_err(|err| {
                    match err {
                        IntrinsicTypeError::Signature(reason) => {
                            invalid(TerminatorLowerError::InvalidIntrinsicCall { op: *op, reason })
                        }
                        IntrinsicTypeError::Layout { ty, error } => lower_layout_error(&ty, error),
                    }
                })?;
            }
            // An indirect call through a function pointer passes exactly its parameter types
            // and returns its output type.
            if let Ty::FnPtr { inputs, output, .. } = &func_ty {
                if arg_tys.len() != inputs.len() {
                    return Err(invalid(TerminatorLowerError::InvalidFnPtrCall {
                        reason: "argument count differs from the function pointer's parameter count",
                    }));
                }
                if arg_tys[..] != inputs[..] {
                    return Err(invalid(TerminatorLowerError::InvalidFnPtrCall {
                        reason: "argument types differ from the function pointer's parameter types",
                    }));
                }
                if dest_ty != **output {
                    return Err(invalid(TerminatorLowerError::InvalidFnPtrCall {
                        reason: "destination type differs from the function pointer's return type",
                    }));
                }
            }
            Ok(LoweredTerminator::Call {
                func: func.clone(),
                func_ty,
                args: args.clone(),
                arg_tys,
                destination: destination.clone(),
                dest_ty,
                target: *target,
                unwind: *unwind,
            })
        }
        Terminator::UnwindResume | Terminator::UnwindTerminate => {
            if !is_cleanup {
                return Err(invalid(
                    TerminatorLowerError::UnwindTerminatorOutsideCleanup,
                ));
            }
            Ok(if matches!(term, Terminator::UnwindResume) {
                LoweredTerminator::UnwindResume
            } else {
                LoweredTerminator::UnwindTerminate
            })
        }
    }
}

/// Evaluated panic message of a failed `Assert` (the [`AssertMessage`] with its operands
/// evaluated), or `Custom` for a panicking call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PanicMessage {
    /// Index out of bounds.
    BoundsCheck { len: MirValue, index: MirValue },
    /// Arithmetic overflow of `lhs op rhs`.
    Overflow(BinOp, MirValue, MirValue),
    /// Overflow negating the minimum signed value.
    OverflowNeg(MirValue),
    /// Division of the operand by zero.
    DivisionByZero(MirValue),
    /// Remainder of the operand by zero.
    RemainderByZero(MirValue),
    /// Misaligned pointer dereference.
    MisalignedPointerDereference { required: MirValue, found: MirValue },
    /// Null pointer dereference.
    NullPointerDereference,
    /// Invalid enum discriminant.
    InvalidEnumConstruction(MirValue),
    /// Free-form message.
    Custom(String),
    /// A call of the diverging entry point `op` ([`IntrinsicOp::PanicUnwind`] panics,
    /// [`IntrinsicOp::Abort`] aborts); its arguments are not interpreted.
    Intrinsic(IntrinsicOp),
}

/// Clean (non-UB) result of a control-flow evaluation.
///
/// Block indices refer to the evaluated body: an outcome that a linked callee frame produced
/// (see [`CallTable`]) is attributed to the caller's calling block, with its message unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgEvalOutcome {
    /// `Return` with the initialized return value `_0`.
    Returned(MirValue),
    /// A panic in block `bb` unwound out of the body (`UnwindAction::Continue`, or a cleanup
    /// path ending in `UnwindResume`).
    Panicked { bb: usize, msg: PanicMessage },
    /// A panic in block `bb` aborted the program (`UnwindAction::Terminate`, or a cleanup path
    /// ending in `UnwindTerminate`), or block `bb` called [`IntrinsicOp::Abort`].
    Terminated { bb: usize, msg: PanicMessage },
    /// Fuel ran out before block `bb` could execute; `state` is the state at that point, from
    /// which [`eval_cfg_in_state`] (or [`eval_cfg_in_state_with_call_table`]) can resume unless
    /// `bb` is a cleanup block (the unwinding panic is not part of `state`). When fuel runs out
    /// inside a linked callee, `bb` is the evaluated body's calling block and `state` the body's
    /// state when that block was entered (callee frames are discarded, and resuming re-executes
    /// the block and the call).
    OutOfFuel {
        bb: usize,
        state: StatementEvalState,
    },
}

/// Undefined behavior or ill-formed body encountered during control-flow evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgEvalError {
    /// The arguments do not match the body's parameter types.
    InvalidArguments(RvalueEvalError),
    /// Statement `index` of block `bb` failed.
    Statement {
        bb: usize,
        index: usize,
        error: RvalueEvalError,
    },
    /// The terminator of block `bb` failed while evaluating an operand or place.
    Terminator { bb: usize, error: RvalueEvalError },
    /// Block index `bb` does not exist.
    InvalidBlock { bb: usize },
    /// Control reached `to` from `from` along an edge violating the cleanup discipline (or
    /// started in a cleanup block).
    InvalidEdge { from: usize, to: usize },
    /// Block `bb` has no terminator.
    MissingTerminator { bb: usize },
    /// `Unreachable` was reached in block `bb`, or a call without `target` returned (UB).
    UnreachableReached { bb: usize },
    /// A panic in block `bb` unwound into `UnwindAction::Unreachable` (UB). The message is
    /// boxed to keep `CfgEvalError` small.
    UnwindIntoUnreachable { bb: usize, msg: Box<PanicMessage> },
    /// Block `bb` used an unwinding terminator or action in the wrong mode (`UnwindResume` /
    /// `UnwindTerminate` while not unwinding, `Return` while unwinding, or
    /// `Continue`/`Cleanup` unwinding from a cleanup block).
    InvalidUnwind { bb: usize },
    /// Block `bb` calls a function that is neither an inline intrinsic nor linked, but no
    /// call handler was provided.
    UnsupportedCall { bb: usize },
    /// Block `bb` calls the ordinary function `callee`, which the [`CallTable`] does not link
    /// (and no call handler was provided).
    UnknownCallee { bb: usize, callee: CalleeSymbol },
    /// Block `bb` calls a linked callee while [`CallTable::max_call_depth`] linked callee
    /// frames are already active. This is an evaluation limit (like fuel), not undefined
    /// behavior; it is raised deterministically, before the callee frame is created.
    CallDepthExceeded { bb: usize, max_call_depth: usize },
    /// `error` occurred in a linked callee frame. `call_stack[0]` is the call made by the
    /// evaluated body and `call_stack[i + 1]` the call made by the callee of `call_stack[i]`;
    /// block indices inside `error` refer to the innermost callee's body. (The stack is flat,
    /// so even a deep recursion's error stays shallow.)
    InCallee {
        call_stack: Vec<CallSite>,
        error: Box<CfgEvalError>,
    },
}

impl std::fmt::Display for CfgEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CfgEvalError::InvalidArguments(err) => write!(f, "invalid arguments: {err}"),
            CfgEvalError::Statement { bb, index, error } => {
                write!(f, "bb{bb}[{index}]: {error}")
            }
            CfgEvalError::Terminator { bb, error } => write!(f, "bb{bb} terminator: {error}"),
            CfgEvalError::InvalidBlock { bb } => write!(f, "basic block bb{bb} does not exist"),
            CfgEvalError::InvalidEdge { from, to } => {
                write!(f, "invalid control-flow edge bb{from} -> bb{to}")
            }
            CfgEvalError::MissingTerminator { bb } => write!(f, "bb{bb} has no terminator"),
            CfgEvalError::UnreachableReached { bb } => {
                write!(f, "unreachable code reached in bb{bb} (UB)")
            }
            CfgEvalError::UnwindIntoUnreachable { bb, msg } => {
                write!(
                    f,
                    "panic {msg:?} in bb{bb} unwound into UnwindAction::Unreachable (UB)"
                )
            }
            CfgEvalError::InvalidUnwind { bb } => {
                write!(
                    f,
                    "bb{bb} uses an unwinding terminator or action in the wrong mode"
                )
            }
            CfgEvalError::UnsupportedCall { bb } => {
                write!(
                    f,
                    "bb{bb} calls a function but no call handler was provided"
                )
            }
            CfgEvalError::UnknownCallee { bb, callee } => {
                write!(
                    f,
                    "bb{bb} calls `{callee}`, which is not linked in the call table"
                )
            }
            CfgEvalError::CallDepthExceeded { bb, max_call_depth } => {
                write!(
                    f,
                    "bb{bb} exceeds the maximum depth of {max_call_depth} linked callee frames"
                )
            }
            CfgEvalError::InCallee { call_stack, error } => {
                write!(f, "in callee")?;
                for site in call_stack {
                    write!(f, " -> `{}` (called from bb{})", site.callee, site.bb)?;
                }
                write!(f, ": {error}")
            }
        }
    }
}

impl std::error::Error for CfgEvalError {}

/// Outcome of a call reported by a call handler.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallOutcome {
    /// The callee returned this value.
    Return(MirValue),
    /// The callee panicked with this message.
    Panic(String),
}

/// Caller-supplied call handler: given the calling block, the evaluated callee, and the
/// evaluated arguments, reports the call's outcome (or undefined behavior inside the callee).
pub type CallHandler<'a> =
    dyn FnMut(usize, &MirValue, &[MirValue]) -> Result<CallOutcome, RvalueEvalError> + 'a;

/// Evaluates `body` on `args` with at most `fuel` executed basic blocks, without a call
/// handler (every `Call` of anything but an inline intrinsic is
/// [`CfgEvalError::UnsupportedCall`]). See the module documentation.
pub fn eval_lowered_body_cfg(
    body: &LoweredBody,
    args: &[MirValue],
    fuel: usize,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    let state =
        StatementEvalState::from_body(body, args).map_err(CfgEvalError::InvalidArguments)?;
    eval_cfg_in_state(body, state, 0, fuel, None)
}

/// [`eval_lowered_body_cfg`] with a call handler deciding the outcome of every `Call` that is
/// not an inline intrinsic.
pub fn eval_lowered_body_cfg_with_calls<F>(
    body: &LoweredBody,
    args: &[MirValue],
    fuel: usize,
    mut call_handler: F,
) -> Result<CfgEvalOutcome, CfgEvalError>
where
    F: FnMut(usize, &MirValue, &[MirValue]) -> Result<CallOutcome, RvalueEvalError>,
{
    let state =
        StatementEvalState::from_body(body, args).map_err(CfgEvalError::InvalidArguments)?;
    eval_cfg_in_state(body, state, 0, fuel, Some(&mut call_handler))
}

/// Next step after a panic.
enum PanicFlow {
    /// Continue unwinding at this cleanup block.
    Cleanup(usize),
    /// Evaluation ends with this outcome.
    Done(CfgEvalOutcome),
}

/// Applies the unwind action `unwind` to a panic `msg` raised in block `bb`, validating
/// `unwind` against `basic_blocks` before updating `unwinding` so a failed `Cleanup` edge
/// never leaves `unwinding` partially mutated.
fn start_panic(
    bb: usize,
    msg: PanicMessage,
    unwind: UnwindAction,
    basic_blocks: &[LoweredBasicBlock],
    unwinding: &mut UnwindState,
) -> Result<PanicFlow, CfgEvalError> {
    check_unwind_action(bb, unwind, unwinding.is_some(), basic_blocks)?;
    match unwind {
        UnwindAction::Unreachable => Err(CfgEvalError::UnwindIntoUnreachable {
            bb,
            msg: Box::new(msg),
        }),
        UnwindAction::Terminate => Ok(PanicFlow::Done(CfgEvalOutcome::Terminated { bb, msg })),
        UnwindAction::Continue => Ok(PanicFlow::Done(CfgEvalOutcome::Panicked { bb, msg })),
        UnwindAction::Cleanup(target) => {
            *unwinding = Some((bb, msg));
            Ok(PanicFlow::Cleanup(target))
        }
    }
}

/// Evaluates an `AssertMessage`'s operands into a [`PanicMessage`].
fn eval_panic_message(
    msg: &AssertMessage,
    state: &mut StatementEvalState,
) -> Result<PanicMessage, RvalueEvalError> {
    let ptr_width = state.ptr_width;
    let check_usize = |val: MirValue| -> Result<MirValue, RvalueEvalError> {
        if !mir_value_matches_ty(&val, &Ty::Uint(UintTy::Usize)) {
            return Err(RvalueEvalError::TypeMismatch(
                "AssertMessage operand must evaluate to a usize value",
            ));
        }
        check_value_well_formed(&val, ptr_width)?;
        Ok(val)
    };
    let check_int = |val: MirValue| -> Result<MirValue, RvalueEvalError> {
        if !matches!(val, MirValue::Int { ref ty, .. } if ty.is_integral()) {
            return Err(RvalueEvalError::TypeMismatch(
                "AssertMessage operand must evaluate to an integer value",
            ));
        }
        check_value_well_formed(&val, ptr_width)?;
        Ok(val)
    };
    Ok(match msg {
        AssertMessage::BoundsCheck { len, index } => PanicMessage::BoundsCheck {
            len: check_usize(state.eval_operand(len)?)?,
            index: check_usize(state.eval_operand(index)?)?,
        },
        AssertMessage::Overflow(op, lhs, rhs) => {
            let lhs = check_int(state.eval_operand(lhs)?)?;
            let rhs = check_int(state.eval_operand(rhs)?)?;
            let shift = matches!(
                op,
                BinOp::Shl | BinOp::Shr | BinOp::ShlUnchecked | BinOp::ShrUnchecked
            );
            if !shift && lhs.ty() != rhs.ty() {
                return Err(RvalueEvalError::TypeMismatch(
                    "AssertMessage::Overflow operands must have matching integer types",
                ));
            }
            PanicMessage::Overflow(*op, lhs, rhs)
        }
        AssertMessage::OverflowNeg(op) => {
            let val = state.eval_operand(op)?;
            if !matches!(val, MirValue::Int { ref ty, .. } if ty.is_signed_int()) {
                return Err(RvalueEvalError::TypeMismatch(
                    "AssertMessage::OverflowNeg operand must evaluate to a signed integer",
                ));
            }
            check_value_well_formed(&val, ptr_width)?;
            PanicMessage::OverflowNeg(val)
        }
        AssertMessage::DivisionByZero(op) => {
            PanicMessage::DivisionByZero(check_int(state.eval_operand(op)?)?)
        }
        AssertMessage::RemainderByZero(op) => {
            PanicMessage::RemainderByZero(check_int(state.eval_operand(op)?)?)
        }
        AssertMessage::MisalignedPointerDereference { required, found } => {
            PanicMessage::MisalignedPointerDereference {
                required: check_usize(state.eval_operand(required)?)?,
                found: check_usize(state.eval_operand(found)?)?,
            }
        }
        AssertMessage::NullPointerDereference => PanicMessage::NullPointerDereference,
        AssertMessage::InvalidEnumConstruction(op) => {
            PanicMessage::InvalidEnumConstruction(check_int(state.eval_operand(op)?)?)
        }
        AssertMessage::Custom(text) => PanicMessage::Custom(text.clone()),
    })
}

/// Bits a `SwitchInt` discriminant value is matched on. An integer whose bits exceed its
/// type's width is an ill-formed value (`InvalidBitPattern`), never truncated to a valid one.
fn switch_bits(val: &MirValue, ptr_width: PtrWidth) -> Result<u128, RvalueEvalError> {
    match val {
        MirValue::Bool(b) => Ok(u128::from(*b)),
        MirValue::Char(c) => Ok(u128::from(u32::from(*c))),
        MirValue::Int { bits, ty } if ty.is_integral() => {
            if !ty.is_valid_scalar_bits(*bits, ptr_width) {
                return Err(RvalueEvalError::CastEval(
                    CastEvalError::InvalidBitPattern {
                        target_ty: ty.clone(),
                        bits: *bits,
                    },
                ));
            }
            Ok(*bits)
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "SwitchInt discriminant must be a bool, char, or integer value",
        )),
    }
}

/// Validates that `unwind` is well-formed for block `bb` (in or outside cleanup mode).
fn check_unwind_action(
    bb: usize,
    unwind: UnwindAction,
    in_cleanup: bool,
    basic_blocks: &[LoweredBasicBlock],
) -> Result<(), CfgEvalError> {
    match unwind {
        UnwindAction::Unreachable | UnwindAction::Terminate => Ok(()),
        UnwindAction::Continue if in_cleanup => Err(CfgEvalError::InvalidUnwind { bb }),
        UnwindAction::Continue => Ok(()),
        UnwindAction::Cleanup(_) if in_cleanup => Err(CfgEvalError::InvalidUnwind { bb }),
        UnwindAction::Cleanup(target) => match basic_blocks.get(target) {
            None => Err(CfgEvalError::InvalidBlock { bb: target }),
            Some(target_block) if !target_block.is_cleanup => Err(CfgEvalError::InvalidEdge {
                from: bb,
                to: target,
            }),
            Some(_) => Ok(()),
        },
    }
}

/// Execution mode between basic blocks: `None` in normal execution, or `Some((bb, msg))` while
/// unwinding the panic `msg` raised in block `bb` (in which mode only cleanup blocks run).
pub type UnwindState = Option<(usize, PanicMessage)>;

/// Next control-flow step after a basic block's terminator ([`eval_lowered_terminator`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgStep {
    /// Continue at this block, which exists and is a cleanup block iff the evaluation is (now)
    /// unwinding.
    Goto(usize),
    /// The body finished cleanly (`Returned`, `Panicked`, or `Terminated`).
    Done(CfgEvalOutcome),
}

/// Evaluates the terminator `term` of block `bb` of `body` (whose statements have run) in
/// `state` and unwinding mode `unwinding`, executing an inline intrinsic `Call` in place and
/// using `call_handler` (if any) for any other `Call` (this single-frame step never enters a
/// linked callee); see the module documentation. `state` must match `body` (`ptr_width`, `local_decls`, one slot per
/// local: `InvalidArguments`), and `bb` must be a block of `body` that is a cleanup block iff
/// the evaluation is unwinding (`InvalidBlock` / `InvalidUnwind`). A panic updates `unwinding`
/// when it enters a cleanup block, and `UnwindResume`/`UnwindTerminate` end the unwinding. A
/// [`CfgStep::Goto`] target is checked to be a block of `body` that is a cleanup block iff the
/// evaluation is unwinding afterwards (`InvalidBlock` / `InvalidEdge`), so consecutive steps
/// preserve the entry requirement. Values crossing the body boundary (the returned `_0`, a
/// callee and its arguments, a call's result, and evaluated panic-message operands) must be
/// well formed.
///
/// One iteration of [`eval_cfg_in_state`] is one unit of fuel, the statements of a block, and
/// this function on its terminator.
pub fn eval_lowered_terminator(
    body: &LoweredBody,
    bb: usize,
    term: &LoweredTerminator,
    state: &mut StatementEvalState,
    unwinding: &mut UnwindState,
    mut call_handler: Option<&mut CallHandler<'_>>,
) -> Result<CfgStep, CfgEvalError> {
    let in_cleanup = check_terminator_entry(body, bb, state, unwinding)?;
    let ptr_width = state.ptr_width;
    let term_err = |error: RvalueEvalError| CfgEvalError::Terminator { bb, error };
    let next = match term {
        LoweredTerminator::Goto { target } => *target,
        LoweredTerminator::SwitchInt {
            discr,
            discr_ty,
            targets,
        } => {
            if targets.values.len() != targets.targets.len() {
                return Err(term_err(RvalueEvalError::TypeMismatch(
                    "SwitchInt targets length mismatch",
                )));
            }
            let val = state.eval_operand(discr).map_err(term_err)?;
            if !mir_value_matches_ty(&val, discr_ty) {
                return Err(term_err(RvalueEvalError::TypeMismatch(
                    "SwitchInt discriminant runtime type does not match lowered type",
                )));
            }
            let bits = switch_bits(&val, ptr_width).map_err(term_err)?;
            let mut seen = BTreeSet::new();
            for value in &targets.values {
                if !seen.insert(*value) || !discr_ty.is_valid_scalar_bits(*value, ptr_width) {
                    return Err(term_err(RvalueEvalError::TypeMismatch(
                        "SwitchInt targets contain duplicate or out-of-range values",
                    )));
                }
            }
            targets.target_for_value(bits)
        }
        LoweredTerminator::Return { ret_ty } => {
            if in_cleanup {
                return Err(CfgEvalError::InvalidUnwind { bb });
            }
            if state.local_decls.first() != Some(ret_ty) || !ret_ty.is_inhabited_for(ptr_width) {
                return Err(term_err(RvalueEvalError::TypeMismatch(
                    "Return requires an inhabited return place _0 of the lowered type",
                )));
            }
            let ret_val = state.read_place(&Place::from_local(0)).map_err(term_err)?;
            check_value_well_formed(&ret_val, ptr_width).map_err(term_err)?;
            return Ok(CfgStep::Done(CfgEvalOutcome::Returned(ret_val)));
        }
        LoweredTerminator::Unreachable => {
            return Err(CfgEvalError::UnreachableReached { bb });
        }
        LoweredTerminator::Drop {
            place,
            place_ty,
            target,
            unwind,
        } => {
            // No drop glue: the place must be live and well-formed; its value is unchanged.
            state
                .check_place_access(place, place_ty)
                .map_err(term_err)?;
            check_unwind_action(bb, *unwind, in_cleanup, &body.basic_blocks)?;
            *target
        }
        LoweredTerminator::Assert {
            cond,
            expected,
            msg,
            target,
            unwind,
        } => {
            let MirValue::Bool(actual) = state.eval_operand(cond).map_err(term_err)? else {
                return Err(term_err(RvalueEvalError::TypeMismatch(
                    "Assert condition must be a bool value",
                )));
            };
            if actual == *expected {
                check_unwind_action(bb, *unwind, in_cleanup, &body.basic_blocks)?;
                *target
            } else {
                let panic_msg = eval_panic_message(msg, state).map_err(term_err)?;
                match start_panic(bb, panic_msg, *unwind, &body.basic_blocks, unwinding)? {
                    PanicFlow::Cleanup(target) => target,
                    PanicFlow::Done(outcome) => return Ok(CfgStep::Done(outcome)),
                }
            }
        }
        LoweredTerminator::Call {
            func,
            func_ty,
            args,
            arg_tys,
            destination,
            dest_ty,
            target,
            unwind,
        } => {
            let PreparedCall {
                func_val,
                arg_vals,
                dest_place,
            } = prepare_call(
                bb,
                func,
                func_ty,
                args,
                arg_tys,
                destination,
                dest_ty,
                *target,
                state,
            )?;
            if let Some(CallTarget::Intrinsic(op)) = call_target_of(func) {
                let op = *op;
                match eval_intrinsic_call(op, &arg_vals, arg_tys, dest_ty, state)
                    .map_err(term_err)?
                {
                    IntrinsicOutcome::Return(ret_val) => complete_call_return(
                        body,
                        bb,
                        in_cleanup,
                        CallReturn {
                            ret_val,
                            destination: &dest_place,
                            dest_ty,
                            target: *target,
                            unwind: *unwind,
                            cross_frame_limit: None,
                        },
                        state,
                    )?,
                    IntrinsicOutcome::Unreachable => {
                        return Err(CfgEvalError::UnreachableReached { bb });
                    }
                    // An abort ends the program at once: no cleanup block runs, whatever the
                    // call's `target` and `unwind` (`Trusted`'s `retOutcome .abort`). As for
                    // every completed call, an ill-formed unwind action of a hand-built body
                    // is still rejected.
                    IntrinsicOutcome::Abort => {
                        check_unwind_action(bb, *unwind, in_cleanup, &body.basic_blocks)?;
                        return Ok(CfgStep::Done(CfgEvalOutcome::Terminated {
                            bb,
                            msg: PanicMessage::Intrinsic(op),
                        }));
                    }
                    IntrinsicOutcome::Panic => {
                        match start_panic(
                            bb,
                            PanicMessage::Intrinsic(op),
                            *unwind,
                            &body.basic_blocks,
                            unwinding,
                        )? {
                            PanicFlow::Cleanup(target) => target,
                            PanicFlow::Done(outcome) => return Ok(CfgStep::Done(outcome)),
                        }
                    }
                }
            } else {
                let Some(handler) = call_handler.as_mut() else {
                    return Err(CfgEvalError::UnsupportedCall { bb });
                };
                match handler(bb, &func_val, &arg_vals).map_err(term_err)? {
                    CallOutcome::Return(ret_val) => complete_call_return(
                        body,
                        bb,
                        in_cleanup,
                        CallReturn {
                            ret_val,
                            destination: &dest_place,
                            dest_ty,
                            target: *target,
                            unwind: *unwind,
                            cross_frame_limit: None,
                        },
                        state,
                    )?,
                    CallOutcome::Panic(text) => {
                        match start_panic(
                            bb,
                            PanicMessage::Custom(text),
                            *unwind,
                            &body.basic_blocks,
                            unwinding,
                        )? {
                            PanicFlow::Cleanup(target) => target,
                            PanicFlow::Done(outcome) => return Ok(CfgStep::Done(outcome)),
                        }
                    }
                }
            }
        }
        LoweredTerminator::UnwindResume => {
            let Some((panic_bb, msg)) = unwinding.take() else {
                return Err(CfgEvalError::InvalidUnwind { bb });
            };
            return Ok(CfgStep::Done(CfgEvalOutcome::Panicked {
                bb: panic_bb,
                msg,
            }));
        }
        LoweredTerminator::UnwindTerminate => {
            let Some((panic_bb, msg)) = unwinding.take() else {
                return Err(CfgEvalError::InvalidUnwind { bb });
            };
            return Ok(CfgStep::Done(CfgEvalOutcome::Terminated {
                bb: panic_bb,
                msg,
            }));
        }
    };
    check_goto(body, bb, next, unwinding).map(CfgStep::Goto)
}

/// Checks that `next` is a block of `body` that is a cleanup block iff the evaluation is
/// unwinding (`InvalidBlock` / `InvalidEdge` from `from`), and returns it.
fn check_goto(
    body: &LoweredBody,
    from: usize,
    next: usize,
    unwinding: &UnwindState,
) -> Result<usize, CfgEvalError> {
    match body.basic_blocks.get(next) {
        None => Err(CfgEvalError::InvalidBlock { bb: next }),
        Some(next_block) if next_block.is_cleanup != unwinding.is_some() => {
            Err(CfgEvalError::InvalidEdge { from, to: next })
        }
        Some(_) => Ok(next),
    }
}

/// The call target of a function-item callee operand ([`Constant::FnDef`]).
///
/// [`Constant::FnDef`]: crate::ir::Constant::FnDef
fn call_target_of(func: &Operand) -> Option<&CallTarget> {
    func.call_target()
}

/// A call's evaluated callee, arguments, and destination (see [`prepare_call`]).
struct PreparedCall {
    func_val: MirValue,
    arg_vals: Vec<MirValue>,
    /// The destination evaluated before the call, without `Deref` or `Index` steps.
    dest_place: Place,
}

/// Evaluates the callee and then the arguments of a `Call` in block `bb` left to right (a
/// `Move` of a bare local deinitializes it), checking each value against its lowered type
/// and for well-formedness, then evaluates the destination place for a whole-place write
/// (reading its pointers and index operands now, so the result is written to the place as
/// evaluated before the call, see [`StatementEvalState::check_place_write_access`]) and
/// checks that a call with a `target` has an inhabited destination type. Shared by every
/// kind of callee (intrinsic, call handler, or linked), so all of them observe the same
/// operand evaluation order and faults before the callee runs.
///
/// `Trusted`'s `evalTerminator` evaluates the destination only when it writes the returned
/// value (`writePlaceValue` on the post-argument locals). No callee that `Trusted` models
/// changes the caller's frame (linked callees are frame-isolated and value intrinsics are
/// pure), so both orders write the same place; they differ only for an invalid destination,
/// which faults here even when the call never returns (it panics, aborts, or diverges), as
/// with MiniRust's eager `eval_place`: an extra error, never a different outcome.
#[allow(clippy::too_many_arguments)]
fn prepare_call(
    bb: usize,
    func: &Operand,
    func_ty: &Ty,
    args: &[Operand],
    arg_tys: &[Ty],
    destination: &Place,
    dest_ty: &Ty,
    target: Option<usize>,
    state: &mut StatementEvalState,
) -> Result<PreparedCall, CfgEvalError> {
    let ptr_width = state.ptr_width;
    let term_err = |error: RvalueEvalError| CfgEvalError::Terminator { bb, error };
    let func_val = state.eval_operand(func).map_err(term_err)?;
    if !mir_value_matches_ty(&func_val, func_ty) || args.len() != arg_tys.len() {
        return Err(term_err(RvalueEvalError::TypeMismatch(
            "Call callee runtime type does not match lowered type",
        )));
    }
    check_value_well_formed(&func_val, ptr_width).map_err(term_err)?;
    let mut arg_vals = Vec::with_capacity(args.len());
    for (arg, arg_ty) in args.iter().zip(arg_tys) {
        let val = state.eval_operand(arg).map_err(term_err)?;
        if !mir_value_matches_ty(&val, arg_ty) {
            return Err(term_err(RvalueEvalError::TypeMismatch(
                "Call argument runtime type does not match lowered type",
            )));
        }
        check_value_well_formed(&val, ptr_width).map_err(term_err)?;
        arg_vals.push(val);
    }
    // The destination place is evaluated before the call, as a whole-place write evaluates
    // it (a final `Deref` may overwrite a leaf union field).
    let dest_place = state
        .resolve_write_place(destination, dest_ty)
        .map_err(term_err)?;
    if target.is_some() && !dest_ty.is_inhabited_for(ptr_width) {
        return Err(term_err(RvalueEvalError::TypeMismatch(
            "Call with an uninhabited destination type must not have a return target",
        )));
    }
    Ok(PreparedCall {
        func_val,
        arg_vals,
        dest_place,
    })
}

/// The value a call returned and where it goes (see [`complete_call_return`]).
struct CallReturn<'c> {
    ret_val: MirValue,
    destination: &'c Place,
    dest_ty: &'c Ty,
    target: Option<usize>,
    unwind: UnwindAction,
    /// `Some(limit)` when the value crosses a frame boundary (a linked callee's `_0`): it must
    /// not hold a pointer into a frame-local synthetic allocation (`alloc_id` in `1..=limit`).
    cross_frame_limit: Option<usize>,
}

/// Completes a call in block `bb` (a cleanup block iff `in_cleanup`) that returned: checks
/// the call's unwind action, requires a return target (a call without one must not return:
/// `UnreachableReached`), checks the returned value for well-formedness (and frame
/// isolation), and writes it to the destination. Returns the target block.
fn complete_call_return(
    body: &LoweredBody,
    bb: usize,
    in_cleanup: bool,
    ret: CallReturn<'_>,
    state: &mut StatementEvalState,
) -> Result<usize, CfgEvalError> {
    let term_err = |error: RvalueEvalError| CfgEvalError::Terminator { bb, error };
    check_unwind_action(bb, ret.unwind, in_cleanup, &body.basic_blocks)?;
    let Some(target) = ret.target else {
        return Err(CfgEvalError::UnreachableReached { bb });
    };
    check_value_well_formed(&ret.ret_val, state.ptr_width).map_err(term_err)?;
    if let Some(limit) = ret.cross_frame_limit
        && frame_local_pointer(&ret.ret_val, limit).is_some()
    {
        return Err(term_err(RvalueEvalError::UnsupportedMemoryAccess(
            CROSS_FRAME_POINTER,
        )));
    }
    let mut ret_val = ret.ret_val;
    if let Some(limit) = ret.cross_frame_limit {
        restore_caller_exposed_provenance(&mut ret_val, state, limit);
    }
    state
        .write_place(ret.destination, ret.dest_ty, ret_val)
        .map_err(term_err)?;
    Ok(target)
}

/// Reason a value crossing a linked call boundary is rejected (see [`CallTable`]).
const CROSS_FRAME_POINTER: &str = "a pointer into a frame-local synthetic allocation cannot cross \
     a linked call boundary (every frame has its own synthetic address space)";

/// The first pointer in `val` (at any depth) whose provenance names a synthetic local
/// allocation of a frame with at most `limit` locals (allocation ids `1..=limit`, i.e. local
/// `alloc_id - 1`).
fn frame_local_pointer(val: &MirValue, limit: usize) -> Option<PointerValue> {
    match val {
        MirValue::Ptr { ptr, .. } | MirValue::WidePtr { data: ptr, .. } => ptr
            .provenance
            .filter(|prov| usize::try_from(prov.alloc_id).is_ok_and(|id| id >= 1 && id <= limit))
            .map(|_| *ptr),
        MirValue::Array { elements, .. } => elements
            .iter()
            .find_map(|element| frame_local_pointer(element, limit)),
        MirValue::Tuple(fields)
        | MirValue::Adt {
            active_field: None,
            fields,
            ..
        } => fields
            .iter()
            .find_map(|field| frame_local_pointer(field, limit)),
        MirValue::Adt {
            active_field: Some(active),
            fields,
            ..
        } => {
            let active_val = if fields.len() == 1 {
                fields.first()
            } else {
                fields.get(*active)
            };
            active_val.and_then(|field| frame_local_pointer(field, limit))
        }
        // A function pointer's provenance is global (never a frame-local allocation).
        MirValue::Int { .. }
        | MirValue::Bool(_)
        | MirValue::Char(_)
        | MirValue::Unit
        | MirValue::FnPtr { .. } => None,
    }
}

/// Checks the entry requirements of [`eval_lowered_terminator`] for block `bb`: `state`
/// matches `body` (`InvalidArguments`), `bb` exists (`InvalidBlock`), and it is a cleanup
/// block iff the evaluation is unwinding (`InvalidUnwind`). Returns whether `bb` is a cleanup
/// block.
fn check_terminator_entry(
    body: &LoweredBody,
    bb: usize,
    state: &StatementEvalState,
    unwinding: &UnwindState,
) -> Result<bool, CfgEvalError> {
    check_state_matches_body(body, state)?;
    let Some(block) = body.basic_blocks.get(bb) else {
        return Err(CfgEvalError::InvalidBlock { bb });
    };
    if block.is_cleanup != unwinding.is_some() {
        return Err(CfgEvalError::InvalidUnwind { bb });
    }
    Ok(block.is_cleanup)
}

/// `InvalidArguments` unless `state` matches `body` (`ptr_width`, `local_decls`, one slot per
/// local, and a page-aligned `frame_addr_base`).
fn check_state_matches_body(
    body: &LoweredBody,
    state: &StatementEvalState,
) -> Result<(), CfgEvalError> {
    if state.ptr_width != body.ptr_width
        || state.local_decls != body.local_decls
        || state.slots.len() != body.local_decls.len()
        || !state.frame_addr_base.is_multiple_of(0x1000)
    {
        return Err(CfgEvalError::InvalidArguments(
            RvalueEvalError::TypeMismatch(
                "StatementEvalState local_decls, slots, ptr_width, or frame_addr_base do not match LoweredBody",
            ),
        ));
    }
    Ok(())
}

/// Evaluates `body` from block `start_bb` in `state` with at most `fuel` executed basic blocks,
/// using `call_handler` (if any) for `Call` terminators. See the module documentation.
///
/// Each executed block consumes one unit of fuel, runs its statements, and then its
/// terminator with [`eval_lowered_terminator`], until a [`CfgStep::Done`] outcome, an error, or
/// [`CfgEvalOutcome::OutOfFuel`] at the block that would run next.
pub fn eval_cfg_in_state(
    body: &LoweredBody,
    state: StatementEvalState,
    start_bb: usize,
    fuel: usize,
    call_handler: Option<&mut CallHandler<'_>>,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    match call_handler {
        None => eval_frames(body, state, start_bb, fuel, None, None),
        Some(handler) => {
            let mut external = |call: &ExternalCall<'_>| handler(call.bb, call.func, call.args);
            eval_frames(body, state, start_bb, fuel, None, Some(&mut external))
        }
    }
}

/// Default [`CallTable::max_call_depth`].
pub const DEFAULT_MAX_CALL_DEPTH: usize = 64;

/// A linked callee of a [`CallTable`]: its lowered body and its number of parameters
/// (`_1..=arg_count`, which a call initializes with its arguments; `_0` is the return place and
/// every other local starts storage-dead, as in [`StatementEvalState::from_body`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkedCallee {
    /// Number of parameters.
    pub arg_count: usize,
    /// The callee's lowered body.
    pub body: LoweredBody,
    /// Whether the callee is an `unsafe fn` (which cannot be reified to, or called through, a
    /// safe function pointer).
    pub safety: Safety,
}

impl LinkedCallee {
    /// Checks that this callee, linked as `symbol`, can be reified to or called through a
    /// function pointer of type `fn_ptr_ty` (`Trusted`'s `checkCalleeSig`): its parameter
    /// count, parameter types (`_1..=arg_count`), and return type (`_0`) must be the function
    /// pointer's, and an `unsafe fn` needs an `unsafe` function pointer
    /// ([`RvalueEvalError::FnPtrSignatureMismatch`] otherwise, undefined behavior).
    pub fn check_fn_ptr_signature(
        &self,
        symbol: &CalleeSymbol,
        fn_ptr_ty: &Ty,
    ) -> Result<(), RvalueEvalError> {
        let Ty::FnPtr {
            inputs,
            output,
            safety,
        } = fn_ptr_ty
        else {
            return Err(RvalueEvalError::TypeMismatch(
                "function pointer signature check requires a function pointer type",
            ));
        };
        let mismatch = |reason: &'static str| RvalueEvalError::FnPtrSignatureMismatch {
            callee: symbol.clone(),
            reason,
        };
        if self.arg_count != inputs.len() {
            return Err(mismatch(
                "the callee's parameter count differs from the function pointer's",
            ));
        }
        let decls = &self.body.local_decls;
        if decls.get(1..=self.arg_count) != Some(&inputs[..]) {
            return Err(mismatch(
                "the callee's parameter types differ from the function pointer's",
            ));
        }
        if decls.first() != Some(&**output) {
            return Err(mismatch(
                "the callee's return type differs from the function pointer's",
            ));
        }
        if self.safety == Safety::Unsafe && *safety == Safety::Safe {
            return Err(mismatch(
                "an unsafe function cannot be reified to or called through a safe function pointer",
            ));
        }
        Ok(())
    }
}

/// Multi-callee call table: the linked intra-crate callees of an evaluation, keyed by
/// [`CalleeSymbol`], and the maximum depth of nested callee frames.
///
/// [`eval_cfg_in_state_with_call_table`] runs a `Call` whose callee is the function item of a
/// linked symbol ([`CallTarget::Fn`]) in a new frame of that callee's body, on an explicit
/// (heap-allocated) frame stack, so neither self nor mutual recursion can overflow the Rust
/// stack:
/// - **Arguments.** After the caller has evaluated the callee, the arguments, and the
///   destination exactly as for any call, the callee frame starts with `_1..=arg_count` set to
///   the arguments, which must match the parameter types and be well formed; the argument
///   count must be `arg_count`, the callee's return type must match the destination's type (or,
///   on a diverging `target: None` call, be uninhabited, e.g. `-> !` coerced into an inhabited
///   caller destination), and its pointer width must match the caller's (`Terminator` errors of
///   the calling block otherwise).
/// - **Fuel.** All frames share one fuel counter: every block executed in any frame consumes
///   one unit, so the whole call tree executes at most `fuel` blocks; when it runs out inside a
///   callee, the evaluation ends with [`CfgEvalOutcome::OutOfFuel`] at the evaluated body's
///   calling block (see there).
/// - **Depth.** A call made while `max_call_depth` callee frames are active fails with
///   [`CfgEvalError::CallDepthExceeded`] (`0` forbids linked calls altogether).
/// - **Outcomes.** A callee's `Returned(val)` completes the call like a handler's return:
///   the caller's unwind action is checked, a call without `target` is undefined behavior
///   (`UnreachableReached`), and `val` is written to the destination before jumping to
///   `target`. A callee's `Panicked` panic continues in the caller along the call's
///   `UnwindAction` (`Cleanup` enters the caller's cleanup block, `Continue` unwinds further,
///   `Terminate` aborts, `Unreachable` is `UnwindIntoUnreachable`), and a callee's
///   `Terminated` ends the whole evaluation at once (no caller cleanup block runs). Outcomes are
///   re-attributed to the caller's calling block with their messages unchanged, and an error
///   inside a callee is reported as [`CfgEvalError::InCallee`] with the call stack.
/// - **Frame isolation.** Every frame has its own locals and synthetic stack allocations
///   (provenance `alloc_id = local + 1`); it inherits the caller's transmute policy and
///   `ub_checks`. Of the caller's exposed provenances, those of storage-dead caller locals are
///   dropped, external ones with `alloc_id > max(caller_locals, callee_locals)` are inherited
///   unchanged, and the others (live caller locals, and externals whose `alloc_id` would name a
///   callee local) become one opaque non-local provenance, so `with_exposed_provenance`
///   pointer arithmetic stays defined without aliasing callee locals. When the callee returns
///   or unwinds, the external provenances it exposed outside
///   `1..=max(caller_locals, callee_locals)` become exposed in the caller, and a returned
///   pointer with the opaque provenance gets the caller's live exposed local containing its
///   address, else a hidden external, else any live exposed local (unless the caller itself
///   holds an outer frame's opaque provenance, which the pointer then keeps). A callee
///   frame's allocations lie above all of its caller's
///   ([`StatementEvalState::frame_addr_base`]; a frame that does not fit the address space is
///   `UnsupportedMemoryAccess`), so the addresses of distinct active frames never coincide, not
///   even as exposed integers. Because a synthetic pointer's provenance is only meaningful in
///   its own frame, an argument or returned value holding a pointer whose provenance names a
///   synthetic local allocation of either frame (`alloc_id` in
///   `1..=max(caller_locals, callee_locals)`) is rejected with `UnsupportedMemoryAccess`
///   (never reinterpreted as a pointer into the other frame); pointers without provenance, or
///   with any other provenance, cross unchanged (but for the opaque provenance of a returned
///   pointer, as above).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallTable {
    callees: BTreeMap<CalleeSymbol, LinkedCallee>,
    max_call_depth: usize,
}

impl Default for CallTable {
    fn default() -> Self {
        CallTable::new()
    }
}

impl CallTable {
    /// An empty table with [`DEFAULT_MAX_CALL_DEPTH`].
    pub fn new() -> Self {
        CallTable {
            callees: BTreeMap::new(),
            max_call_depth: DEFAULT_MAX_CALL_DEPTH,
        }
    }

    /// This table with a maximum of `max_call_depth` nested callee frames.
    pub fn with_max_call_depth(mut self, max_call_depth: usize) -> Self {
        self.max_call_depth = max_call_depth;
        self
    }

    /// This table with `body` (taking `arg_count` parameters) linked as `symbol`.
    pub fn with_callee(
        mut self,
        symbol: impl Into<CalleeSymbol>,
        arg_count: usize,
        body: LoweredBody,
    ) -> Self {
        self.insert(symbol, arg_count, body);
        self
    }

    /// This table with the `unsafe fn` `body` (taking `arg_count` parameters) linked as
    /// `symbol`.
    pub fn with_unsafe_callee(
        mut self,
        symbol: impl Into<CalleeSymbol>,
        arg_count: usize,
        body: LoweredBody,
    ) -> Self {
        self.insert_with_safety(symbol, arg_count, body, Safety::Unsafe);
        self
    }

    /// Maximum number of nested callee frames.
    pub fn max_call_depth(&self) -> usize {
        self.max_call_depth
    }

    /// Sets the maximum number of nested callee frames.
    pub fn set_max_call_depth(&mut self, max_call_depth: usize) {
        self.max_call_depth = max_call_depth;
    }

    /// Links the safe `body` (taking `arg_count` parameters) as `symbol`, returning the callee
    /// it replaces.
    pub fn insert(
        &mut self,
        symbol: impl Into<CalleeSymbol>,
        arg_count: usize,
        body: LoweredBody,
    ) -> Option<LinkedCallee> {
        self.insert_with_safety(symbol, arg_count, body, Safety::Safe)
    }

    /// Links `body` (taking `arg_count` parameters, an `unsafe fn` iff `safety` is
    /// [`Safety::Unsafe`]) as `symbol`, returning the callee it replaces.
    pub fn insert_with_safety(
        &mut self,
        symbol: impl Into<CalleeSymbol>,
        arg_count: usize,
        body: LoweredBody,
        safety: Safety,
    ) -> Option<LinkedCallee> {
        self.callees.insert(
            symbol.into(),
            LinkedCallee {
                arg_count,
                body,
                safety,
            },
        )
    }

    /// The callee linked as `symbol`.
    pub fn get(&self, symbol: &CalleeSymbol) -> Option<&LinkedCallee> {
        self.callees.get(symbol)
    }

    /// Returns true if `symbol` is linked.
    pub fn contains(&self, symbol: &CalleeSymbol) -> bool {
        self.callees.contains_key(symbol)
    }

    /// Number of linked callees.
    pub fn len(&self) -> usize {
        self.callees.len()
    }

    /// Returns true if no callee is linked.
    pub fn is_empty(&self) -> bool {
        self.callees.is_empty()
    }

    /// The linked callees in symbol order.
    pub fn iter(&self) -> impl Iterator<Item = (&CalleeSymbol, &LinkedCallee)> {
        self.callees.iter()
    }
}

/// A call of a linked callee that is in progress: the caller's calling block and the callee.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CallSite {
    /// The calling block (in the caller's body).
    pub bb: usize,
    /// The linked callee.
    pub callee: CalleeSymbol,
}

/// A `Call` that a call-table evaluation hands to its [`ExternalCallHandler`]: one whose
/// callee is neither an inline intrinsic nor linked in the [`CallTable`], made in any frame.
///
/// It identifies the call like `Trusted`'s `MirCallReq` (whose `defPath` is
/// [`ExternalCall::callee`]): a block index alone is ambiguous across frames, and a function
/// item evaluates to `MirValue::Unit` whatever it names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExternalCall<'a> {
    /// The linked calls in progress, outermost first (empty for a call made by the evaluated
    /// body itself).
    pub call_stack: &'a [CallSite],
    /// The calling block, in the body of the innermost frame.
    pub bb: usize,
    /// The unlinked symbol the call names: a direct `Constant::FnDef(CallTarget::Fn(_))`
    /// callee, or the target of the function pointer an indirect call evaluated its callee to
    /// (`None` for any other callee, e.g. a pointer constant).
    pub callee: Option<&'a CalleeSymbol>,
    /// The evaluated callee operand.
    pub func: &'a MirValue,
    /// The evaluated arguments.
    pub args: &'a [MirValue],
}

/// Caller-supplied handler of the [`ExternalCall`]s of a call-table evaluation (`Trusted`'s
/// `ExternalCallHandler`): reports the call's outcome (or undefined behavior inside the callee),
/// exactly like a [`CallHandler`].
pub type ExternalCallHandler<'a> =
    dyn FnMut(&ExternalCall<'_>) -> Result<CallOutcome, RvalueEvalError> + 'a;

/// [`eval_cfg_in_state`] with the linked callees of `table` (see [`CallTable`]): a `Call` of
/// a linked [`CallTarget::Fn`] symbol runs the callee's body in a new frame; inline intrinsics
/// run in the calling frame; every other call (in any frame) goes to `call_handler` as an
/// [`ExternalCall`], or fails with [`CfgEvalError::UnknownCallee`] (an unlinked symbol) or
/// [`CfgEvalError::UnsupportedCall`] without one. `fuel` bounds the blocks executed across all
/// frames.
pub fn eval_cfg_in_state_with_call_table(
    body: &LoweredBody,
    state: StatementEvalState,
    start_bb: usize,
    fuel: usize,
    table: &CallTable,
    call_handler: Option<&mut ExternalCallHandler<'_>>,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    eval_frames(body, state, start_bb, fuel, Some(table), call_handler)
}

/// [`eval_lowered_body_cfg`] with the linked callees of `table` (see
/// [`eval_cfg_in_state_with_call_table`]; without a call handler).
pub fn eval_lowered_body_cfg_with_call_table(
    body: &LoweredBody,
    args: &[MirValue],
    fuel: usize,
    table: &CallTable,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    let state =
        StatementEvalState::from_body(body, args).map_err(CfgEvalError::InvalidArguments)?;
    eval_frames(body, state, 0, fuel, Some(table), None)
}

/// [`eval_lowered_body_cfg_with_call_table`] with `call_handler` deciding every
/// [`ExternalCall`] (an unlinked or indirect `Call` in any frame), mirroring
/// `Trusted.VerificationResult.mirHandledTreeWithCallees`.
pub fn eval_lowered_body_cfg_with_call_table_and_calls<F>(
    body: &LoweredBody,
    args: &[MirValue],
    fuel: usize,
    table: &CallTable,
    mut call_handler: F,
) -> Result<CfgEvalOutcome, CfgEvalError>
where
    F: FnMut(&ExternalCall<'_>) -> Result<CallOutcome, RvalueEvalError>,
{
    let state =
        StatementEvalState::from_body(body, args).map_err(CfgEvalError::InvalidArguments)?;
    eval_frames(body, state, 0, fuel, Some(table), Some(&mut call_handler))
}

/// A linked call waiting in its caller's frame.
struct PendingCall {
    site: CallSite,
    /// The destination as evaluated before the call (see [`prepare_call`]).
    destination: Place,
    dest_ty: Ty,
    target: Option<usize>,
    unwind: UnwindAction,
}

/// One activation on the frame stack of [`eval_frames`].
struct Frame<'a> {
    body: &'a LoweredBody,
    state: StatementEvalState,
    /// The block to execute next (or, while `pending`, the calling block).
    bb: usize,
    unwinding: UnwindState,
    /// The linked call this frame waits for (every frame but the top one has one).
    pending: Option<PendingCall>,
}

/// Result of executing one block of the top frame ([`run_block`]).
enum BlockStep<'a> {
    /// The frame continues at its (updated) `bb`.
    Continue,
    /// The frame calls a linked callee.
    Call {
        callee: &'a LinkedCallee,
        args: Vec<MirValue>,
        pending: PendingCall,
    },
    /// The frame finished.
    Done(CfgEvalOutcome),
}

/// Returns true if the terminator of `frame`'s current block may call a linked callee of
/// `table`: a direct call of a linked symbol, or an indirect call through a function pointer
/// (whose target is only known once the block's statements have run).
fn may_call_linked(frame: &Frame<'_>, table: &CallTable) -> bool {
    let Some(LoweredTerminator::Call { func, func_ty, .. }) = frame
        .body
        .basic_blocks
        .get(frame.bb)
        .and_then(|block| block.terminator.as_ref())
    else {
        return false;
    };
    match call_target_of(func) {
        Some(CallTarget::Fn(symbol)) => table.contains(symbol),
        Some(CallTarget::Intrinsic(_)) => false,
        None => func_ty.is_fn_ptr() && !table.is_empty(),
    }
}

/// Executes the statements and the terminator of the current block of `frame` (consuming no
/// fuel), stopping before a linked call is entered. `callers` are the frames below `frame`.
fn run_block<'a>(
    frame: &mut Frame<'a>,
    callers: &[Frame<'_>],
    table: Option<&'a CallTable>,
    call_handler: Option<&mut ExternalCallHandler<'_>>,
) -> Result<BlockStep<'a>, CfgEvalError> {
    let body = frame.body;
    let bb = frame.bb;
    let Some(block) = body.basic_blocks.get(bb) else {
        return Err(CfgEvalError::InvalidBlock { bb });
    };
    for (index, stmt) in block.statements.iter().enumerate() {
        if let Some(table) = table {
            check_reify_signature(stmt, table)
                .map_err(|error| CfgEvalError::Statement { bb, index, error })?;
        }
        eval_lowered_statement(stmt, &mut frame.state)
            .map_err(|error| CfgEvalError::Statement { bb, index, error })?;
    }
    let Some(term) = &block.terminator else {
        return Err(CfgEvalError::MissingTerminator { bb });
    };
    let unlinked_symbol: Option<CalleeSymbol> = match term {
        LoweredTerminator::Call {
            func,
            func_ty,
            args,
            arg_tys,
            destination,
            dest_ty,
            target,
            unwind,
        } => {
            // The linked symbol a direct call names, or that the function pointer an indirect
            // call reads designates (peeked without side effects; `prepare_call` evaluates
            // the callee operand for real, faulting on an invalid one).
            let (symbol, indirect) = match call_target_of(func) {
                Some(CallTarget::Fn(symbol)) => (Some(symbol.clone()), false),
                Some(CallTarget::Intrinsic(_)) => (None, false),
                None if func_ty.is_fn_ptr() => match peek_operand(func, &frame.state) {
                    Some(MirValue::FnPtr { target, .. }) => (Some(target), true),
                    _ => (None, true),
                },
                None => (None, false),
            };
            match (table, symbol) {
                (Some(table), Some(symbol)) => {
                    if let Some(callee) = table.get(&symbol) {
                        check_terminator_entry(body, bb, &frame.state, &frame.unwinding)?;
                        let PreparedCall {
                            func_val,
                            arg_vals,
                            dest_place,
                        } = prepare_call(
                            bb,
                            func,
                            func_ty,
                            args,
                            arg_tys,
                            destination,
                            dest_ty,
                            *target,
                            &mut frame.state,
                        )?;
                        if indirect {
                            // The evaluated function pointer must still designate `symbol`,
                            // and the linked callee must have its signature.
                            if !matches!(&func_val, MirValue::FnPtr { target, .. } if *target == symbol)
                            {
                                return Err(CfgEvalError::Terminator {
                                    bb,
                                    error: RvalueEvalError::TypeMismatch(
                                        "indirect callee changed while evaluating the call",
                                    ),
                                });
                            }
                            callee
                                .check_fn_ptr_signature(&symbol, func_ty)
                                .map_err(|error| CfgEvalError::Terminator { bb, error })?;
                        }
                        return Ok(BlockStep::Call {
                            callee,
                            args: arg_vals,
                            pending: PendingCall {
                                site: CallSite {
                                    bb,
                                    callee: symbol,
                                },
                                destination: dest_place,
                                dest_ty: dest_ty.clone(),
                                target: *target,
                                unwind: *unwind,
                            },
                        });
                    }
                    Some(symbol)
                }
                _ => None,
            }
        }
        _ => None,
    };
    // Any other `Call` reaching the handler is an `ExternalCall` of this frame.
    let mut external_call;
    let call_handler: Option<&mut CallHandler<'_>> = match call_handler {
        None => None,
        Some(handler) => {
            let callee = match term {
                LoweredTerminator::Call { func, .. } => {
                    func.call_target().and_then(CallTarget::as_callee)
                }
                _ => None,
            };
            external_call = move |bb: usize, func: &MirValue, args: &[MirValue]| {
                let call_stack: Vec<CallSite> = callers
                    .iter()
                    .filter_map(|caller| caller.pending.as_ref().map(|p| p.site.clone()))
                    .collect();
                // An indirect call names the target of the function pointer it evaluated.
                let callee = callee.or(match func {
                    MirValue::FnPtr { target, .. } => Some(target),
                    _ => None,
                });
                handler(&ExternalCall {
                    call_stack: &call_stack,
                    bb,
                    callee,
                    func,
                    args,
                })
            };
            Some(&mut external_call)
        }
    };
    match eval_lowered_terminator(
        body,
        bb,
        term,
        &mut frame.state,
        &mut frame.unwinding,
        call_handler,
    ) {
        Ok(CfgStep::Goto(next)) => {
            frame.bb = next;
            Ok(BlockStep::Continue)
        }
        Ok(CfgStep::Done(outcome)) => Ok(BlockStep::Done(outcome)),
        Err(CfgEvalError::UnsupportedCall { bb }) => Err(match unlinked_symbol {
            Some(symbol) => CfgEvalError::UnknownCallee {
                bb,
                callee: symbol,
            },
            None => CfgEvalError::UnsupportedCall { bb },
        }),
        Err(error) => Err(error),
    }
}

/// The value of the operand `op` in `state` if it can be read without side effects (a
/// `Copy` or `Move` place is read, not moved, and a failed read is `None`).
fn peek_operand(op: &Operand, state: &StatementEvalState) -> Option<MirValue> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => state.read_place(place).ok(),
        Operand::Constant(_) => None,
    }
}

/// Under a call table, checks that a statement reifying a linked function item or closure
/// into a function pointer (`ReifyFnPointer*` / `ClosureFnPointer*`) gives it the callee's
/// signature ([`LinkedCallee::check_fn_ptr_signature`]): creating a function pointer of
/// another signature is undefined behavior. Unlinked callees are not checked.
fn check_reify_signature(stmt: &LoweredStatement, table: &CallTable) -> Result<(), RvalueEvalError> {
    let LoweredStatement::Assign {
        rvalue:
            LoweredRvalue::Cast {
                cast:
                    LoweredCast::PointerCoercion {
                        coercion,
                        src_ty,
                        target_ty,
                        operand,
                    },
                ..
            },
        ..
    } = stmt
    else {
        return Ok(());
    };
    if !coercion.is_reify() && !coercion.is_closure_reify() {
        return Ok(());
    }
    let Ok(symbol) = reify_target(*coercion, operand, src_ty) else {
        return Ok(());
    };
    match table.get(&symbol) {
        Some(callee) => callee.check_fn_ptr_signature(&symbol, target_ty),
        None => Ok(()),
    }
}

/// `error`, raised in `frames[frame_index]`, with the linked call stack leading to that frame.
fn in_frames(frames: &[Frame<'_>], frame_index: usize, error: CfgEvalError) -> CfgEvalError {
    if frame_index == 0 {
        return error;
    }
    let call_stack = frames[..frame_index]
        .iter()
        .filter_map(|frame| frame.pending.as_ref().map(|pending| pending.site.clone()))
        .collect();
    CfgEvalError::InCallee {
        call_stack,
        error: Box::new(error),
    }
}

/// Synthetic non-local `alloc_id` representing an exposed allocation from an outer caller
/// frame inside a linked callee's [`ExposedProvenanceTracker`]: keeps `with_exposed_provenance`
/// and `BinOp::Offset` defined across call boundaries without colliding with any frame-local
/// allocation id (`1..=local_decls.len()`).
const CALLER_EXPOSED_ALLOC_ID: u64 = u64::MAX;

/// Restores [`CALLER_EXPOSED_ALLOC_ID`] provenances in `val` when a linked callee returns to
/// `caller_state`: pointers matching one of `caller_state`'s live exposed locals recover that
/// local's provenance (so dereferencing, `copy_nonoverlapping`, and `write_bytes` in the caller
/// observe the local allocation); if the caller itself holds an outer frame's
/// [`CALLER_EXPOSED_ALLOC_ID`], any other pointer keeps it until it reaches that frame;
/// otherwise it recovers a shielded external provenance (`alloc_id` in
/// `(caller_locals + 1)..=limit`), or else any live exposed local's provenance (the last resort
/// of `with_exposed_provenance` prediction in a single frame).
fn restore_caller_exposed_provenance(
    val: &mut MirValue,
    caller_state: &StatementEvalState,
    limit: usize,
) {
    match val {
        MirValue::Ptr { ptr, ty } | MirValue::WidePtr { data: ptr, ty, .. } => {
            restore_caller_exposed_pointer(ptr, ty, caller_state, limit);
        }
        MirValue::Array { elements, .. } => {
            for element in elements {
                restore_caller_exposed_provenance(element, caller_state, limit);
            }
        }
        MirValue::Tuple(fields)
        | MirValue::Adt {
            active_field: None,
            fields,
            ..
        } => {
            for field in fields {
                restore_caller_exposed_provenance(field, caller_state, limit);
            }
        }
        MirValue::Adt {
            active_field: Some(active),
            fields,
            ..
        } => {
            let active_val = if fields.len() == 1 {
                fields.first_mut()
            } else {
                fields.get_mut(*active)
            };
            if let Some(field) = active_val {
                restore_caller_exposed_provenance(field, caller_state, limit);
            }
        }
        MirValue::Int { .. }
        | MirValue::Bool(_)
        | MirValue::Char(_)
        | MirValue::Unit
        | MirValue::FnPtr { .. } => {}
    }
}

/// [`restore_caller_exposed_provenance`] of one (thin or data) pointer `ptr` of type `ty`.
fn restore_caller_exposed_pointer(
    ptr: &mut PointerValue,
    ty: &Ty,
    caller_state: &StatementEvalState,
    limit: usize,
) {
    if !ptr
        .provenance
        .is_some_and(|prov| prov.alloc_id == CALLER_EXPOSED_ALLOC_ID)
    {
        return;
    }
    if let Some(local_prov) = caller_state.match_exposed_local_provenance(u128::from(ptr.addr), ty)
    {
        ptr.provenance = Some(local_prov);
    } else if caller_state
        .tracker
        .exposed
        .iter()
        .any(|prov| prov.alloc_id == CALLER_EXPOSED_ALLOC_ID)
    {
        // Keep `CALLER_EXPOSED_ALLOC_ID` for an outer caller frame lower on the stack.
    } else if let Some(&ext_prov) = caller_state.tracker.exposed.iter().find(|prov| {
        usize::try_from(prov.alloc_id)
            .is_ok_and(|id| id > caller_state.local_decls.len() && id <= limit)
    }) {
        ptr.provenance = Some(ext_prov);
    } else {
        ptr.provenance = caller_state.tracker.exposed.iter().copied().find(|prov| {
            prov.alloc_id
                .checked_sub(1)
                .and_then(|i| usize::try_from(i).ok())
                .is_some_and(|loc| {
                    loc < caller_state.local_decls.len()
                        && !matches!(caller_state.slots.get(loc), Some(LocalSlotState::Dead))
                })
        });
    }
}

/// Creates the state of a frame of the linked `callee` called from `caller` with `args`
/// (into a destination of type `dest_ty`, with a return target iff `has_return_target`); see
/// [`CallTable`].
fn enter_callee(
    caller: &Frame<'_>,
    callee: &LinkedCallee,
    args: &[MirValue],
    dest_ty: &Ty,
    has_return_target: bool,
) -> Result<StatementEvalState, RvalueEvalError> {
    if callee.body.ptr_width != caller.body.ptr_width {
        return Err(RvalueEvalError::TypeMismatch(
            "linked callee targets a different pointer width than its caller",
        ));
    }
    if args.len() != callee.arg_count {
        return Err(RvalueEvalError::TypeMismatch(
            "argument count does not match the linked callee's arg_count",
        ));
    }
    let Some(callee_ret_ty) = callee.body.local_decls.first() else {
        return Err(RvalueEvalError::TypeMismatch(
            "linked callee body has no return local _0",
        ));
    };
    let ret_ty_compatible = callee_ret_ty == dest_ty
        || (!has_return_target && !callee_ret_ty.is_inhabited_for(caller.body.ptr_width));
    if !ret_ty_compatible {
        return Err(RvalueEvalError::TypeMismatch(
            "linked callee return type does not match the call destination type",
        ));
    }
    let limit = caller
        .state
        .local_decls
        .len()
        .max(callee.body.local_decls.len());
    if args
        .iter()
        .any(|arg| frame_local_pointer(arg, limit).is_some())
    {
        return Err(RvalueEvalError::UnsupportedMemoryAccess(
            CROSS_FRAME_POINTER,
        ));
    }
    let mut state = StatementEvalState::from_body(&callee.body, args)?;
    state.policy = caller.state.policy;
    state.ub_checks = caller.state.ub_checks;
    for &prov in &caller.state.tracker.exposed {
        if prov
            .alloc_id
            .checked_sub(1)
            .and_then(|i| usize::try_from(i).ok())
            .is_some_and(|loc| {
                loc < caller.state.local_decls.len()
                    && matches!(caller.state.slots.get(loc), Some(LocalSlotState::Dead))
            })
        {
            continue;
        }
        let mapped = if usize::try_from(prov.alloc_id).is_ok_and(|id| id >= 1 && id <= limit) {
            Provenance {
                alloc_id: CALLER_EXPOSED_ALLOC_ID,
                tag: 0,
            }
        } else {
            prov
        };
        state.tracker.expose(mapped);
    }
    // The callee's synthetic allocations lie above all of its caller's, so addresses of
    // distinct active frames never coincide (also through exposed addresses).
    state.frame_addr_base = caller.state.frame_addr_end()?;
    state.frame_addr_end()?;
    Ok(state)
}

/// The out-of-fuel outcome for `frames` (see [`CfgEvalOutcome::OutOfFuel`]): the top frame's
/// next block and state when it is the evaluated body's frame, and otherwise the body's calling
/// block with its state on entry to that block (`root_call_entry`).
fn out_of_fuel(
    mut frames: Vec<Frame<'_>>,
    root_call_entry: Option<StatementEvalState>,
) -> CfgEvalOutcome {
    let has_callees = frames.len() > 1;
    let root = frames.swap_remove(0);
    match (has_callees, root.pending, root_call_entry) {
        (true, Some(pending), Some(state)) => CfgEvalOutcome::OutOfFuel {
            bb: pending.site.bb,
            state,
        },
        _ => CfgEvalOutcome::OutOfFuel {
            bb: root.bb,
            state: root.state,
        },
    }
}

/// The fuel-bounded evaluation loop over an explicit frame stack shared by
/// [`eval_cfg_in_state`] (no table: a single frame) and
/// [`eval_cfg_in_state_with_call_table`].
fn eval_frames<'a>(
    body: &'a LoweredBody,
    state: StatementEvalState,
    start_bb: usize,
    mut fuel: usize,
    table: Option<&'a CallTable>,
    mut call_handler: Option<&mut ExternalCallHandler<'_>>,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    check_state_matches_body(body, &state)?;
    match body.basic_blocks.get(start_bb) {
        None => return Err(CfgEvalError::InvalidBlock { bb: start_bb }),
        Some(block) if block.is_cleanup => {
            return Err(CfgEvalError::InvalidEdge {
                from: start_bb,
                to: start_bb,
            });
        }
        Some(_) => {}
    }
    let mut frames = vec![Frame {
        body,
        state,
        bb: start_bb,
        unwinding: None,
        pending: None,
    }];
    // The root frame's state on entry to the block of its pending linked call: the resumption
    // point reported when fuel runs out inside a callee.
    let mut root_call_entry: Option<StatementEvalState> = None;
    loop {
        if fuel == 0 {
            return Ok(out_of_fuel(frames, root_call_entry));
        }
        fuel -= 1;
        let top = frames.len() - 1;
        let (callers, top_frame) = frames.split_at_mut(top);
        let frame = &mut top_frame[0];
        if top == 0
            && let Some(table) = table
            && may_call_linked(frame, table)
        {
            root_call_entry = Some(frame.state.clone());
        }
        match run_block(frame, callers, table, call_handler.as_deref_mut()) {
            Err(error) => return Err(in_frames(&frames, top, error)),
            Ok(BlockStep::Continue) => {}
            Ok(BlockStep::Call {
                callee,
                args,
                pending,
            }) => {
                let max_call_depth = table.map_or(0, CallTable::max_call_depth);
                if top >= max_call_depth {
                    return Err(in_frames(
                        &frames,
                        top,
                        CfgEvalError::CallDepthExceeded {
                            bb: pending.site.bb,
                            max_call_depth,
                        },
                    ));
                }
                let callee_state = match enter_callee(
                    &frames[top],
                    callee,
                    &args,
                    &pending.dest_ty,
                    pending.target.is_some(),
                ) {
                    Ok(callee_state) => callee_state,
                    Err(error) => {
                        let bb = pending.site.bb;
                        return Err(in_frames(
                            &frames,
                            top,
                            CfgEvalError::Terminator { bb, error },
                        ));
                    }
                };
                frames[top].pending = Some(pending);
                let entry_error = match callee.body.basic_blocks.first() {
                    None => Some(CfgEvalError::InvalidBlock { bb: 0 }),
                    Some(block) if block.is_cleanup => {
                        Some(CfgEvalError::InvalidEdge { from: 0, to: 0 })
                    }
                    Some(_) => None,
                };
                if let Some(error) = entry_error {
                    return Err(in_frames(&frames, top + 1, error));
                }
                frames.push(Frame {
                    body: &callee.body,
                    state: callee_state,
                    bb: 0,
                    unwinding: None,
                    pending: None,
                });
            }
            Ok(BlockStep::Done(mut outcome)) => loop {
                if frames.len() == 1 {
                    return Ok(outcome);
                }
                let callee_frame = frames.pop().expect("a callee frame is above the root");
                let callee_locals = callee_frame.state.local_decls.len();
                let callee_exposed = callee_frame.state.tracker.exposed;
                let caller_index = frames.len() - 1;
                if caller_index == 0 {
                    root_call_entry = None;
                }
                let Some(pending) = frames[caller_index].pending.take() else {
                    let bb = frames[caller_index].bb;
                    return Err(in_frames(
                        &frames,
                        caller_index,
                        CfgEvalError::InvalidUnwind { bb },
                    ));
                };
                let caller = &mut frames[caller_index];
                let bb = pending.site.bb;
                let limit = caller.state.local_decls.len().max(callee_locals);
                if matches!(
                    outcome,
                    CfgEvalOutcome::Returned(_) | CfgEvalOutcome::Panicked { .. }
                ) {
                    for prov in callee_exposed {
                        if prov.alloc_id != CALLER_EXPOSED_ALLOC_ID
                            && !usize::try_from(prov.alloc_id)
                                .is_ok_and(|id| id >= 1 && id <= limit)
                        {
                            caller.state.tracker.expose(prov);
                        }
                    }
                }
                let resumed: Result<Option<CfgEvalOutcome>, CfgEvalError> = match outcome {
                    CfgEvalOutcome::Returned(ret_val) => {
                        let in_cleanup = caller
                            .body
                            .basic_blocks
                            .get(bb)
                            .is_some_and(|block| block.is_cleanup);
                        complete_call_return(
                            caller.body,
                            bb,
                            in_cleanup,
                            CallReturn {
                                ret_val,
                                destination: &pending.destination,
                                dest_ty: &pending.dest_ty,
                                target: pending.target,
                                unwind: pending.unwind,
                                cross_frame_limit: Some(limit),
                            },
                            &mut caller.state,
                        )
                        .and_then(|next| check_goto(caller.body, bb, next, &caller.unwinding))
                        .map(|next| {
                            caller.bb = next;
                            None
                        })
                    }
                    CfgEvalOutcome::Panicked { msg, .. } => {
                        match start_panic(
                            bb,
                            msg,
                            pending.unwind,
                            &caller.body.basic_blocks,
                            &mut caller.unwinding,
                        ) {
                            Ok(PanicFlow::Cleanup(cleanup)) => {
                                check_goto(caller.body, bb, cleanup, &caller.unwinding).map(
                                    |next| {
                                        caller.bb = next;
                                        None
                                    },
                                )
                            }
                            Ok(PanicFlow::Done(done)) => Ok(Some(done)),
                            Err(error) => Err(error),
                        }
                    }
                    // An abort ends the program: no caller cleanup block runs (an ill-formed
                    // unwind action of a hand-built caller is still rejected, as for every
                    // completed call).
                    CfgEvalOutcome::Terminated { msg, .. } => check_unwind_action(
                        bb,
                        pending.unwind,
                        caller.unwinding.is_some(),
                        &caller.body.basic_blocks,
                    )
                    .map(|()| Some(CfgEvalOutcome::Terminated { bb, msg })),
                    // Frames never finish out of fuel (the loop checks fuel before each block).
                    CfgEvalOutcome::OutOfFuel { .. } => Ok(Some(outcome)),
                };
                match resumed {
                    Ok(None) => break,
                    Ok(Some(done)) => outcome = done,
                    Err(error) => return Err(in_frames(&frames, caller_index, error)),
                }
            },
        }
    }
}
