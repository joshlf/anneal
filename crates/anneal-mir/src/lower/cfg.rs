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
//!   deinitializes it), checks the destination place, and asks the caller-supplied call
//!   handler for the outcome (without a handler: [`CfgEvalError::UnsupportedCall`]); a
//!   returned value must be well formed and of the destination's type, and is written to the
//!   destination before jumping to `target` (a return from a call without `target` is
//!   undefined behavior); a panicking call leaves the destination unchanged.
//!
//! A panic (failed `Assert`, or a handler reporting [`CallOutcome::Panic`]) follows the
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

use std::collections::BTreeSet;

use crate::ir::{
    AssertMessage, BinOp, Body, Operand, Place, PtrWidth, SwitchTargets, Terminator, Ty, UintTy,
    UnwindAction,
};
use crate::lower::cast::CastEvalError;
use crate::lower::rvalue::{
    LoweredBasicBlock, LoweredBody, MirValue, RvalueEvalError, RvalueLowerError,
    StatementEvalState, check_value_well_formed, eval_lowered_statement, lower_operand_ty,
    mir_value_matches_ty, resolve_place_ty,
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
/// return place `_0` for `Return`.
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
}

/// Clean (non-UB) result of a control-flow evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgEvalOutcome {
    /// `Return` with the initialized return value `_0`.
    Returned(MirValue),
    /// A panic in block `bb` unwound out of the body (`UnwindAction::Continue`, or a cleanup
    /// path ending in `UnwindResume`).
    Panicked { bb: usize, msg: PanicMessage },
    /// A panic in block `bb` aborted the program (`UnwindAction::Terminate`, or a cleanup path
    /// ending in `UnwindTerminate`).
    Terminated { bb: usize, msg: PanicMessage },
    /// Fuel ran out before block `bb` could execute; `state` is the state at that point.
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
    /// Block `bb` calls a function, but no call handler was provided.
    UnsupportedCall { bb: usize },
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
/// handler (every `Call` is [`CfgEvalError::UnsupportedCall`]). See the module documentation.
pub fn eval_lowered_body_cfg(
    body: &LoweredBody,
    args: &[MirValue],
    fuel: usize,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    let state =
        StatementEvalState::from_body(body, args).map_err(CfgEvalError::InvalidArguments)?;
    eval_cfg_in_state(body, state, 0, fuel, None)
}

/// [`eval_lowered_body_cfg`] with a call handler deciding the outcome of every `Call`.
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

/// Applies the unwind action `unwind` to a panic `msg` raised in block `bb`.
fn start_panic(
    bb: usize,
    msg: PanicMessage,
    unwind: UnwindAction,
    unwinding: &mut UnwindState,
) -> Result<PanicFlow, CfgEvalError> {
    match unwind {
        UnwindAction::Unreachable => Err(CfgEvalError::UnwindIntoUnreachable {
            bb,
            msg: Box::new(msg),
        }),
        UnwindAction::Terminate => Ok(PanicFlow::Done(CfgEvalOutcome::Terminated { bb, msg })),
        UnwindAction::Continue | UnwindAction::Cleanup(_) if unwinding.is_some() => {
            Err(CfgEvalError::InvalidUnwind { bb })
        }
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
    let check_usize = |val: MirValue| -> Result<MirValue, RvalueEvalError> {
        if val.ty() != Ty::Uint(UintTy::Usize) {
            return Err(RvalueEvalError::TypeMismatch(
                "AssertMessage operand must evaluate to a usize value",
            ));
        }
        Ok(val)
    };
    let check_int = |val: MirValue| -> Result<MirValue, RvalueEvalError> {
        if !val.ty().is_integral() {
            return Err(RvalueEvalError::TypeMismatch(
                "AssertMessage operand must evaluate to an integer value",
            ));
        }
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
            if !val.ty().is_signed_int() {
                return Err(RvalueEvalError::TypeMismatch(
                    "AssertMessage::OverflowNeg operand must evaluate to a signed integer",
                ));
            }
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
            Some(target_block) if !target_block.is_cleanup => {
                Err(CfgEvalError::InvalidEdge { from: bb, to: target })
            }
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
/// `state` and unwinding mode `unwinding`, using `call_handler` (if any) for a `Call`; see the
/// module documentation. A panic updates `unwinding` when it enters a cleanup block, and
/// `UnwindResume`/`UnwindTerminate` end the unwinding. A [`CfgStep::Goto`] target is checked
/// to be a block of `body` that is a cleanup block iff the evaluation is unwinding afterwards
/// (`InvalidBlock` / `InvalidEdge`).
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
    let Some(block) = body.basic_blocks.get(bb) else {
        return Err(CfgEvalError::InvalidBlock { bb });
    };
    let ptr_width = state.ptr_width;
    let in_cleanup = block.is_cleanup || unwinding.is_some();
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
                match start_panic(bb, panic_msg, *unwind, unwinding)? {
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
            let func_val = state.eval_operand(func).map_err(term_err)?;
            if !mir_value_matches_ty(&func_val, func_ty) || args.len() != arg_tys.len() {
                return Err(term_err(RvalueEvalError::TypeMismatch(
                    "Call callee runtime type does not match lowered type",
                )));
            }
            let mut arg_vals = Vec::with_capacity(args.len());
            for (arg, arg_ty) in args.iter().zip(arg_tys) {
                let val = state.eval_operand(arg).map_err(term_err)?;
                if !mir_value_matches_ty(&val, arg_ty) {
                    return Err(term_err(RvalueEvalError::TypeMismatch(
                        "Call argument runtime type does not match lowered type",
                    )));
                }
                arg_vals.push(val);
            }
            state
                .check_place_access(destination, dest_ty)
                .map_err(term_err)?;
            if target.is_some() && !dest_ty.is_inhabited_for(ptr_width) {
                return Err(term_err(RvalueEvalError::TypeMismatch(
                    "Call with an uninhabited destination type must not have a return target",
                )));
            }
            let Some(handler) = call_handler.as_mut() else {
                return Err(CfgEvalError::UnsupportedCall { bb });
            };
            match handler(bb, &func_val, &arg_vals).map_err(term_err)? {
                CallOutcome::Return(ret_val) => {
                    check_unwind_action(bb, *unwind, in_cleanup, &body.basic_blocks)?;
                    let Some(target) = target else {
                        return Err(CfgEvalError::UnreachableReached { bb });
                    };
                    check_value_well_formed(&ret_val, ptr_width).map_err(term_err)?;
                    state
                        .write_place(destination, dest_ty, ret_val)
                        .map_err(term_err)?;
                    *target
                }
                CallOutcome::Panic(text) => {
                    match start_panic(bb, PanicMessage::Custom(text), *unwind, unwinding)? {
                        PanicFlow::Cleanup(target) => target,
                        PanicFlow::Done(outcome) => return Ok(CfgStep::Done(outcome)),
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
    match body.basic_blocks.get(next) {
        None => Err(CfgEvalError::InvalidBlock { bb: next }),
        Some(next_block) if next_block.is_cleanup != unwinding.is_some() => {
            Err(CfgEvalError::InvalidEdge { from: bb, to: next })
        }
        Some(_) => Ok(CfgStep::Goto(next)),
    }
}

/// Evaluates `body` from block `start_bb` in `state` with at most `fuel` executed basic blocks,
/// using `call_handler` (if any) for `Call` terminators. See the module documentation.
///
/// Each executed block consumes one unit of fuel, runs its statements, and then its
/// terminator with [`eval_lowered_terminator`], until a [`CfgStep::Done`] outcome, an error, or
/// [`CfgEvalOutcome::OutOfFuel`] at the block that would run next.
pub fn eval_cfg_in_state(
    body: &LoweredBody,
    mut state: StatementEvalState,
    start_bb: usize,
    mut fuel: usize,
    mut call_handler: Option<&mut CallHandler<'_>>,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    if state.ptr_width != body.ptr_width
        || state.local_decls != body.local_decls
        || state.slots.len() != body.local_decls.len()
    {
        return Err(CfgEvalError::InvalidArguments(
            RvalueEvalError::TypeMismatch(
                "StatementEvalState local_decls, slots, or ptr_width do not match LoweredBody",
            ),
        ));
    }
    let mut bb = start_bb;
    match body.basic_blocks.get(bb) {
        None => return Err(CfgEvalError::InvalidBlock { bb }),
        Some(block) if block.is_cleanup => {
            return Err(CfgEvalError::InvalidEdge { from: bb, to: bb });
        }
        Some(_) => {}
    }
    let mut unwinding: UnwindState = None;
    loop {
        if fuel == 0 {
            return Ok(CfgEvalOutcome::OutOfFuel { bb, state });
        }
        fuel -= 1;
        let block = &body.basic_blocks[bb];
        for (index, stmt) in block.statements.iter().enumerate() {
            eval_lowered_statement(stmt, &mut state).map_err(|error| CfgEvalError::Statement {
                bb,
                index,
                error,
            })?;
        }
        let Some(term) = &block.terminator else {
            return Err(CfgEvalError::MissingTerminator { bb });
        };
        match eval_lowered_terminator(
            body,
            bb,
            term,
            &mut state,
            &mut unwinding,
            call_handler.as_deref_mut(),
        )? {
            CfgStep::Goto(next) => bb = next,
            CfgStep::Done(outcome) => return Ok(outcome),
        }
    }
}
