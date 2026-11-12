//! Inline compiler intrinsics and diverging entry points ([`IntrinsicOp`]): static call typing
//! ([`check_intrinsic_call_types`]), pure value semantics ([`eval_intrinsic`]), and stateful
//! call semantics ([`eval_intrinsic_call`]), which `Terminator::Call` uses for a callee
//! [`Constant::FnDef`](crate::ir::Constant::FnDef) naming
//! [`CallTarget::Intrinsic`](crate::ir::CallTarget::Intrinsic).
//!
//! The semantics mirror `Trusted.Rustc.V2026_06_01.MirSemantics.evalNonSelectIntrinsicCall`
//! and its `Scalars.lean` evaluators (`evalCtlz`, `evalCttz`, `evalCtpop`, `evalBswap`,
//! `evalBitreverse`, `evalExactDiv`, `evalWrapping*`, `evalSaturating*`, `evalUnchecked*`,
//! `evalThreeWayCompare`, `evalArithOffset`, `ubChecks`, `sizeOfVal`, `alignOfVal`),
//! generalized from `Trusted`'s 64-bit target to both [`PtrWidth`]s (`isize`/`usize` have
//! `ptr_width` bits, and pointer arithmetic wraps modulo `2^ptr_width.bit_width()`), and
//! restricted to well-typed calls: where `Trusted` steps to `unsupported` because it cannot
//! resolve a signedness (or faults on a malformed argument list), Anneal rejects the call
//! statically (`TerminatorLowerError::InvalidIntrinsicCall`) or at runtime (`TypeMismatch`).
//!
//! Every precondition violation is undefined behavior. Preconditions that an intrinsic shares
//! with a [`BinOp`] report exactly that `BinOp`'s error, so that `unchecked_add(x, y)` and
//! `BinOp::AddUnchecked` (and likewise `unchecked_sub`/`mul`/`div`/`rem`/`shl`/`shr` and
//! `exact_div`'s division checks) can never disagree; the remaining ones (`ctlz_nonzero(0)`,
//! `cttz_nonzero(0)`, `exact_div` with a remainder) are [`RvalueEvalError::IntrinsicUb`].

use std::cmp::Ordering;

use crate::ir::{
    AdtKind, BinOp, IntTy, IntrinsicOp, LayoutError, Mutability, PointerValue, PtrWidth, ScalarTy,
    Ty, TyLayout, UintTy, sign_extend_bits, width_mask,
};
use crate::lower::cast::cast_eval_layout_error;
use crate::lower::rvalue::{
    MirValue, RvalueEvalError, StatementEvalState, check_value_well_formed, checked_ptr_addr,
    compare_mir_values, compute_int_arith_with_overflow, copy_nonoverlapping_values, eval_binop,
    mir_value_matches_ty, write_bytes_values,
};

/// Static typing failure of an intrinsic call (see [`check_intrinsic_call_types`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntrinsicTypeError {
    /// The argument or destination types do not match the intrinsic's signature.
    Signature(&'static str),
    /// A pointee type the intrinsic needs the layout of has no exact layout.
    Layout { ty: Ty, error: LayoutError },
}

impl IntrinsicTypeError {
    /// The runtime error reported when a hand-built call fails this check: `TypeMismatch` for a
    /// signature mismatch, and the `CastEval` layout error for a pointee layout.
    pub fn into_eval_error(self) -> RvalueEvalError {
        match self {
            IntrinsicTypeError::Signature(reason) => RvalueEvalError::TypeMismatch(reason),
            IntrinsicTypeError::Layout { ty, error } => {
                RvalueEvalError::CastEval(cast_eval_layout_error(&ty, error))
            }
        }
    }
}

impl std::fmt::Display for IntrinsicTypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntrinsicTypeError::Signature(reason) => f.write_str(reason),
            IntrinsicTypeError::Layout { ty, error } => {
                write!(f, "pointee type {ty:?} has no exact layout: {error}")
            }
        }
    }
}

impl std::error::Error for IntrinsicTypeError {}

/// Outcome of an inline intrinsic call ([`eval_intrinsic_call`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntrinsicOutcome {
    /// The intrinsic returned this value (written to the call's destination).
    Return(MirValue),
    /// [`IntrinsicOp::UnreachableUnchecked`] was reached (undefined behavior).
    Unreachable,
    /// [`IntrinsicOp::Abort`]: the program aborts without unwinding (no cleanup runs).
    Abort,
    /// [`IntrinsicOp::PanicUnwind`]: the call panics and unwinds along its `UnwindAction`.
    Panic,
}

const WRONG_ARITY: &str = "intrinsic called with the wrong number of arguments";
const NOT_INTEGER: &str = "intrinsic argument must be an integer";
const MISMATCHED_OPERANDS: &str = "intrinsic arguments must have the same integer type";
const COUNT_RESULT: &str = "ctlz/cttz/ctpop must return u32";
const SAME_TYPE_RESULT: &str = "intrinsic must return its first argument's type";
const COMPARE_OPERANDS: &str =
    "three_way_compare arguments must be integers or chars of the same type";
const COMPARE_RESULT: &str = "three_way_compare must return i8 or an Ordering-shaped enum";
const UB_CHECKS_SIGNATURE: &str = "ub_checks takes no arguments and returns bool";
const NOT_POINTER: &str = "pointer intrinsic argument must be a raw pointer or reference";
const ARITH_OFFSET_COUNT: &str = "arith_offset count must be an isize";
const ARITH_OFFSET_RESULT: &str =
    "arith_offset must return a raw pointer to its argument's pointee type";
const SIZE_ALIGN_RESULT: &str = "size_of_val/align_of_val must return usize";
const COPY_SIGNATURE: &str =
    "copy_nonoverlapping requires (*const T | &T, *mut T | &mut T, usize) -> ()";
const WRITE_BYTES_SIGNATURE: &str = "write_bytes requires (*mut T | &mut T, u8, usize) -> ()";

/// Variant of the `Ordering`-shaped enum `ty` whose discriminant is `code`: a valid 1-byte
/// `#[repr(i8)]` enum (`TyLayout { size: 1, align: 1 }`) with explicit `i8` tag, no niche
/// range, and exactly three fieldless variants whose signed discriminants are `-1`, `0`, and
/// `1` (as `core::cmp::Ordering`, `#[repr(i8)] enum { Less = -1, Equal = 0, Greater = 1 }`).
/// `None` if `ty` is not such an enum. The shape is recognized structurally, never by
/// `DefPath`.
pub fn ordering_variant(ty: &Ty, code: i8, ptr_width: PtrWidth) -> Option<usize> {
    let Ty::Adt(def) = ty else {
        return None;
    };
    let AdtKind::Enum { tag_ty, variants } = &def.kind else {
        return None;
    };
    if *tag_ty != Some(ScalarTy::Int(IntTy::I8))
        || variants.len() != 3
        || variants.iter().any(|v| !v.fields.is_empty())
    {
        return None;
    }
    if ty.layout_for(ptr_width) != Ok(TyLayout { size: 1, align: 1 }) {
        return None;
    }
    let values: Vec<i128> = def
        .discriminants(ptr_width)
        .ok()?
        .iter()
        .map(|bits| sign_extend_bits(*bits, 8))
        .collect();
    let mut sorted = values.clone();
    sorted.sort_unstable();
    if sorted != [-1, 0, 1] {
        return None;
    }
    values.iter().position(|value| *value == i128::from(code))
}

/// Checks that a call of `op` with arguments of types `arg_tys` writing a destination of type
/// `dest_ty` is well typed under `ptr_width` (see [`IntrinsicOp`] for the signatures), and that
/// every pointee whose layout `op` uses (`ArithOffset`'s stride, `SizeOfVal`/`AlignOfVal`,
/// and the element type of `CopyNonOverlapping`/`WriteBytes`) has an exact layout.
pub fn check_intrinsic_call_types(
    op: IntrinsicOp,
    arg_tys: &[Ty],
    dest_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<(), IntrinsicTypeError> {
    use IntrinsicTypeError::Signature;
    let arity = |n: usize| {
        if arg_tys.len() == n {
            Ok(())
        } else {
            Err(Signature(WRONG_ARITY))
        }
    };
    let integral = |ty: &Ty| {
        if ty.is_integral() {
            Ok(())
        } else {
            Err(Signature(NOT_INTEGER))
        }
    };
    let exact_layout = |ty: &Ty| -> Result<TyLayout, IntrinsicTypeError> {
        ty.layout_for(ptr_width)
            .map_err(|error| IntrinsicTypeError::Layout {
                ty: ty.clone(),
                error,
            })
    };
    let expect = |ok: bool, reason: &'static str| if ok { Ok(()) } else { Err(Signature(reason)) };
    match op {
        IntrinsicOp::Ctlz
        | IntrinsicOp::CtlzNonzero
        | IntrinsicOp::Cttz
        | IntrinsicOp::CttzNonzero
        | IntrinsicOp::Ctpop => {
            arity(1)?;
            integral(&arg_tys[0])?;
            expect(*dest_ty == Ty::Uint(UintTy::U32), COUNT_RESULT)
        }
        IntrinsicOp::Bswap | IntrinsicOp::Bitreverse => {
            arity(1)?;
            integral(&arg_tys[0])?;
            expect(*dest_ty == arg_tys[0], SAME_TYPE_RESULT)
        }
        IntrinsicOp::ExactDiv
        | IntrinsicOp::WrappingAdd
        | IntrinsicOp::WrappingSub
        | IntrinsicOp::WrappingMul
        | IntrinsicOp::SaturatingAdd
        | IntrinsicOp::SaturatingSub
        | IntrinsicOp::UncheckedAdd
        | IntrinsicOp::UncheckedSub
        | IntrinsicOp::UncheckedMul
        | IntrinsicOp::UncheckedDiv
        | IntrinsicOp::UncheckedRem => {
            arity(2)?;
            integral(&arg_tys[0])?;
            expect(arg_tys[1] == arg_tys[0], MISMATCHED_OPERANDS)?;
            expect(*dest_ty == arg_tys[0], SAME_TYPE_RESULT)
        }
        IntrinsicOp::UncheckedShl | IntrinsicOp::UncheckedShr => {
            arity(2)?;
            integral(&arg_tys[0])?;
            integral(&arg_tys[1])?;
            expect(*dest_ty == arg_tys[0], SAME_TYPE_RESULT)
        }
        IntrinsicOp::ThreeWayCompare => {
            arity(2)?;
            expect(
                (arg_tys[0].is_integral() || arg_tys[0] == Ty::Char) && arg_tys[1] == arg_tys[0],
                COMPARE_OPERANDS,
            )?;
            expect(
                *dest_ty == Ty::Int(IntTy::I8) || ordering_variant(dest_ty, 0, ptr_width).is_some(),
                COMPARE_RESULT,
            )
        }
        IntrinsicOp::UbChecks => expect(
            arg_tys.is_empty() && *dest_ty == Ty::Bool,
            UB_CHECKS_SIGNATURE,
        ),
        IntrinsicOp::ArithOffset => {
            arity(2)?;
            let pointee = arg_tys[0].pointee_ty().ok_or(Signature(NOT_POINTER))?;
            expect(arg_tys[1] == Ty::Int(IntTy::Isize), ARITH_OFFSET_COUNT)?;
            expect(
                matches!(dest_ty, Ty::RawPtr(dest_pointee, _) if **dest_pointee == *pointee),
                ARITH_OFFSET_RESULT,
            )?;
            exact_layout(pointee).map(|_| ())
        }
        IntrinsicOp::SizeOfVal | IntrinsicOp::AlignOfVal => {
            arity(1)?;
            let pointee = arg_tys[0].pointee_ty().ok_or(Signature(NOT_POINTER))?;
            expect(*dest_ty == Ty::Uint(UintTy::Usize), SIZE_ALIGN_RESULT)?;
            exact_layout(pointee).map(|_| ())
        }
        IntrinsicOp::CopyNonOverlapping => {
            arity(3)?;
            let elem_ty = match (&arg_tys[0], &arg_tys[1]) {
                (
                    Ty::RawPtr(src_pointee, _) | Ty::Ref(src_pointee, _),
                    Ty::RawPtr(dst_pointee, Mutability::Mut)
                    | Ty::Ref(dst_pointee, Mutability::Mut),
                ) if src_pointee == dst_pointee => &**src_pointee,
                _ => return Err(Signature(COPY_SIGNATURE)),
            };
            expect(
                arg_tys[2] == Ty::Uint(UintTy::Usize) && dest_ty.is_unit(),
                COPY_SIGNATURE,
            )?;
            exact_layout(elem_ty).map(|_| ())
        }
        IntrinsicOp::WriteBytes => {
            arity(3)?;
            let elem_ty = match &arg_tys[0] {
                Ty::RawPtr(pointee, Mutability::Mut) | Ty::Ref(pointee, Mutability::Mut) => {
                    &**pointee
                }
                _ => return Err(Signature(WRITE_BYTES_SIGNATURE)),
            };
            expect(
                arg_tys[1] == Ty::Uint(UintTy::U8)
                    && arg_tys[2] == Ty::Uint(UintTy::Usize)
                    && dest_ty.is_unit(),
                WRITE_BYTES_SIGNATURE,
            )?;
            exact_layout(elem_ty).map(|_| ())
        }
        IntrinsicOp::UnreachableUnchecked | IntrinsicOp::Abort | IntrinsicOp::PanicUnwind => Ok(()),
    }
}

/// Evaluates a value intrinsic (every [`IntrinsicOp`] except the memory intrinsics
/// `CopyNonOverlapping` / `WriteBytes` and the diverging entry points, which need a call's
/// evaluation state: [`eval_intrinsic_call`]) on the arguments `args` returning `dest_ty`
/// under `ptr_width`.
///
/// The argument types are the arguments' runtime types, which must satisfy
/// [`check_intrinsic_call_types`] (`TypeMismatch`, or the `CastEval` layout error); every
/// argument and the result must be well formed (`InvalidBitPattern`). `UbChecks` returns
/// `true` (`Trusted`'s `ubChecks`), and every other intrinsic behaves exactly as in
/// [`eval_intrinsic_call`].
pub fn eval_intrinsic(
    op: IntrinsicOp,
    args: &[MirValue],
    dest_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    if op.is_diverging() || op.accesses_memory() {
        return Err(RvalueEvalError::TypeMismatch(
            "eval_intrinsic evaluates value intrinsics only (see eval_intrinsic_call)",
        ));
    }
    let arg_tys: Vec<Ty> = args.iter().map(MirValue::ty).collect();
    check_intrinsic_call_types(op, &arg_tys, dest_ty, ptr_width)
        .map_err(IntrinsicTypeError::into_eval_error)?;
    for arg in args {
        check_value_well_formed(arg, ptr_width)?;
    }
    let val = eval_value_intrinsic(op, args, dest_ty, ptr_width, true)?;
    check_value_well_formed(&val, ptr_width)?;
    Ok(val)
}

/// Evaluates a call of the inline intrinsic `op` on the evaluated arguments `args` (of the
/// static types `arg_tys`) writing a destination of type `dest_ty`, in `state`.
///
/// The call must be well typed ([`check_intrinsic_call_types`]: `TypeMismatch`, or the
/// `CastEval` layout error), every argument value must match its type (`TypeMismatch`) and be
/// well formed (`InvalidBitPattern`). Then:
/// - the diverging entry points report their outcome without touching `state`
///   ([`IntrinsicOutcome::Unreachable`], [`IntrinsicOutcome::Abort`],
///   [`IntrinsicOutcome::Panic`]);
/// - `CopyNonOverlapping` performs `Statement::CopyNonOverlapping`'s checks and copy on the
///   evaluated operands, and `WriteBytes` the analogous checks and byte write (both return
///   `()`);
/// - `UbChecks` returns `state.ub_checks` (the value of `NullOp::UbChecks` in `state`,
///   `true` by default as in `Trusted`'s `ubChecks`);
/// - every other intrinsic returns its value or fails with its precondition's
///   undefined-behavior error (see the module documentation).
pub fn eval_intrinsic_call(
    op: IntrinsicOp,
    args: &[MirValue],
    arg_tys: &[Ty],
    dest_ty: &Ty,
    state: &mut StatementEvalState,
) -> Result<IntrinsicOutcome, RvalueEvalError> {
    let ptr_width = state.ptr_width;
    check_intrinsic_call_types(op, arg_tys, dest_ty, ptr_width)
        .map_err(IntrinsicTypeError::into_eval_error)?;
    if args.len() != arg_tys.len()
        || args
            .iter()
            .zip(arg_tys)
            .any(|(arg, ty)| !mir_value_matches_ty(arg, ty))
    {
        return Err(RvalueEvalError::TypeMismatch(
            "intrinsic argument values do not match their static types",
        ));
    }
    for arg in args {
        check_value_well_formed(arg, ptr_width)?;
    }
    match op {
        IntrinsicOp::UnreachableUnchecked => Ok(IntrinsicOutcome::Unreachable),
        IntrinsicOp::Abort => Ok(IntrinsicOutcome::Abort),
        IntrinsicOp::PanicUnwind => Ok(IntrinsicOutcome::Panic),
        IntrinsicOp::CopyNonOverlapping => {
            let (elem_ty, layout) = pointee_layout(&arg_tys[0], ptr_width)?;
            copy_nonoverlapping_values(
                state,
                &args[0],
                &args[1],
                &args[2],
                elem_ty,
                layout.size,
                layout.align,
            )?;
            Ok(IntrinsicOutcome::Return(MirValue::Unit))
        }
        IntrinsicOp::WriteBytes => {
            let (elem_ty, layout) = pointee_layout(&arg_tys[0], ptr_width)?;
            write_bytes_values(
                state,
                &args[0],
                &args[1],
                &args[2],
                elem_ty,
                layout.size,
                layout.align,
            )?;
            Ok(IntrinsicOutcome::Return(MirValue::Unit))
        }
        _ => {
            let val = eval_value_intrinsic(op, args, dest_ty, ptr_width, state.ub_checks)?;
            check_value_well_formed(&val, ptr_width)?;
            Ok(IntrinsicOutcome::Return(val))
        }
    }
}

/// Pointee type of the pointer type `ptr_ty` and its exact layout.
fn pointee_layout(ptr_ty: &Ty, ptr_width: PtrWidth) -> Result<(&Ty, TyLayout), RvalueEvalError> {
    let pointee = ptr_ty
        .pointee_ty()
        .ok_or(RvalueEvalError::TypeMismatch(NOT_POINTER))?;
    let layout = pointee
        .layout_for(ptr_width)
        .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(pointee, err)))?;
    Ok((pointee, layout))
}

/// Bits (masked to the type's width), type, and bit width of an integer argument.
fn int_arg(val: &MirValue, ptr_width: PtrWidth) -> Result<(u128, &Ty, u32), RvalueEvalError> {
    match val {
        MirValue::Int { bits, ty } if ty.is_integral() => {
            let width = ty
                .scalar_bit_width(ptr_width)
                .ok_or(RvalueEvalError::TypeMismatch(NOT_INTEGER))?;
            Ok((*bits & width_mask(width), ty, width))
        }
        _ => Err(RvalueEvalError::TypeMismatch(NOT_INTEGER)),
    }
}

/// Value semantics of the non-memory, non-diverging intrinsics on well-typed, well-formed
/// arguments (`ub_checks` is the value `UbChecks` returns).
fn eval_value_intrinsic(
    op: IntrinsicOp,
    args: &[MirValue],
    dest_ty: &Ty,
    ptr_width: PtrWidth,
    ub_checks: bool,
) -> Result<MirValue, RvalueEvalError> {
    let int_result = |bits: u128, ty: &Ty| MirValue::Int {
        bits,
        ty: ty.clone(),
    };
    match op {
        IntrinsicOp::Ctlz
        | IntrinsicOp::CtlzNonzero
        | IntrinsicOp::Cttz
        | IntrinsicOp::CttzNonzero
        | IntrinsicOp::Ctpop => {
            let (bits, _, width) = int_arg(&args[0], ptr_width)?;
            if bits == 0 && matches!(op, IntrinsicOp::CtlzNonzero | IntrinsicOp::CttzNonzero) {
                return Err(RvalueEvalError::IntrinsicUb {
                    op,
                    reason: "the argument is zero",
                });
            }
            // `bits` has no bit at or above `width`, so these counts lie in `0..=width`.
            let count = match op {
                IntrinsicOp::Ctlz | IntrinsicOp::CtlzNonzero => {
                    bits.leading_zeros() - (128 - width)
                }
                IntrinsicOp::Cttz | IntrinsicOp::CttzNonzero => bits.trailing_zeros().min(width),
                _ => bits.count_ones(),
            };
            Ok(MirValue::unsigned(
                u128::from(count),
                UintTy::U32,
                ptr_width,
            ))
        }
        IntrinsicOp::Bswap => {
            let (bits, ty, width) = int_arg(&args[0], ptr_width)?;
            Ok(int_result(bits.swap_bytes() >> (128 - width), ty))
        }
        IntrinsicOp::Bitreverse => {
            let (bits, ty, width) = int_arg(&args[0], ptr_width)?;
            Ok(int_result(bits.reverse_bits() >> (128 - width), ty))
        }
        IntrinsicOp::ExactDiv => {
            let (a, ty, width) = int_arg(&args[0], ptr_width)?;
            let (b, _, _) = int_arg(&args[1], ptr_width)?;
            let remainder = RvalueEvalError::IntrinsicUb {
                op,
                reason: "the division has a non-zero remainder",
            };
            match ty {
                Ty::Uint(_) => {
                    if b == 0 {
                        return Err(RvalueEvalError::DivisionByZero);
                    }
                    if a % b != 0 {
                        return Err(remainder);
                    }
                    Ok(int_result(a / b, ty))
                }
                Ty::Int(it) => {
                    let sa = it.sign_extend(a, ptr_width);
                    let sb = it.sign_extend(b, ptr_width);
                    if sb == 0 {
                        return Err(RvalueEvalError::DivisionByZero);
                    }
                    let min_val = it.min_value(ptr_width);
                    if sa == min_val && sb == -1 {
                        return Err(RvalueEvalError::SignedDivisionOverflow {
                            min_val,
                            bit_width: width,
                        });
                    }
                    if sa % sb != 0 {
                        return Err(remainder);
                    }
                    Ok(int_result(it.truncate_signed(sa / sb, ptr_width), ty))
                }
                _ => Err(RvalueEvalError::TypeMismatch(NOT_INTEGER)),
            }
        }
        IntrinsicOp::WrappingAdd | IntrinsicOp::WrappingSub | IntrinsicOp::WrappingMul => {
            let (a, ty, _) = int_arg(&args[0], ptr_width)?;
            let (b, _, _) = int_arg(&args[1], ptr_width)?;
            let binop = match op {
                IntrinsicOp::WrappingAdd => BinOp::Add,
                IntrinsicOp::WrappingSub => BinOp::Sub,
                _ => BinOp::Mul,
            };
            let (wrapped, _) = compute_int_arith_with_overflow(binop, a, b, ty, ptr_width)?;
            Ok(int_result(wrapped, ty))
        }
        IntrinsicOp::SaturatingAdd | IntrinsicOp::SaturatingSub => {
            let (a, ty, _) = int_arg(&args[0], ptr_width)?;
            let (b, _, _) = int_arg(&args[1], ptr_width)?;
            let add = op == IntrinsicOp::SaturatingAdd;
            let binop = if add { BinOp::Add } else { BinOp::Sub };
            let (wrapped, overflowed) =
                compute_int_arith_with_overflow(binop, a, b, ty, ptr_width)?;
            if !overflowed {
                return Ok(int_result(wrapped, ty));
            }
            let bound = match ty {
                // Unsigned addition can only overflow upwards, subtraction downwards.
                Ty::Uint(ut) => {
                    if add {
                        ut.max_value(ptr_width)
                    } else {
                        0
                    }
                }
                // Signed `a + b` overflows only when both operands have `a`'s sign, and
                // `a - b` only when `b` has the opposite sign: either way towards `a`'s sign.
                Ty::Int(it) => {
                    let toward = if it.sign_extend(a, ptr_width) < 0 {
                        it.min_value(ptr_width)
                    } else {
                        it.max_value(ptr_width)
                    };
                    it.truncate_signed(toward, ptr_width)
                }
                _ => return Err(RvalueEvalError::TypeMismatch(NOT_INTEGER)),
            };
            Ok(int_result(bound, ty))
        }
        IntrinsicOp::UncheckedAdd => eval_binop(BinOp::AddUnchecked, &args[0], &args[1], ptr_width),
        IntrinsicOp::UncheckedSub => eval_binop(BinOp::SubUnchecked, &args[0], &args[1], ptr_width),
        IntrinsicOp::UncheckedMul => eval_binop(BinOp::MulUnchecked, &args[0], &args[1], ptr_width),
        IntrinsicOp::UncheckedDiv => eval_binop(BinOp::Div, &args[0], &args[1], ptr_width),
        IntrinsicOp::UncheckedRem => eval_binop(BinOp::Rem, &args[0], &args[1], ptr_width),
        IntrinsicOp::UncheckedShl => eval_binop(BinOp::ShlUnchecked, &args[0], &args[1], ptr_width),
        IntrinsicOp::UncheckedShr => eval_binop(BinOp::ShrUnchecked, &args[0], &args[1], ptr_width),
        IntrinsicOp::ThreeWayCompare => {
            if !matches!(&args[0], MirValue::Int { .. } | MirValue::Char(_)) {
                return Err(RvalueEvalError::TypeMismatch(COMPARE_OPERANDS));
            }
            let code: i8 = match compare_mir_values(&args[0], &args[1], ptr_width, false)? {
                Ordering::Less => -1,
                Ordering::Equal => 0,
                Ordering::Greater => 1,
            };
            if *dest_ty == Ty::Int(IntTy::I8) {
                return Ok(MirValue::signed(i128::from(code), IntTy::I8, ptr_width));
            }
            match (dest_ty, ordering_variant(dest_ty, code, ptr_width)) {
                (Ty::Adt(def), Some(variant)) => Ok(MirValue::adt(def, variant, Vec::new())),
                _ => Err(RvalueEvalError::TypeMismatch(COMPARE_RESULT)),
            }
        }
        IntrinsicOp::UbChecks => Ok(MirValue::Bool(ub_checks)),
        IntrinsicOp::ArithOffset => {
            let MirValue::Ptr { ptr, ty: ptr_ty } = &args[0] else {
                return Err(RvalueEvalError::TypeMismatch(NOT_POINTER));
            };
            let (_, layout) = pointee_layout(ptr_ty, ptr_width)?;
            let MirValue::Int {
                bits: count_bits,
                ty: Ty::Int(IntTy::Isize),
            } = &args[1]
            else {
                return Err(RvalueEvalError::TypeMismatch(ARITH_OFFSET_COUNT));
            };
            if !matches!(dest_ty, Ty::RawPtr(..)) {
                return Err(RvalueEvalError::TypeMismatch(ARITH_OFFSET_RESULT));
            }
            let count = IntTy::Isize.sign_extend(*count_bits, ptr_width);
            let addr = checked_ptr_addr(ptr, ptr_ty, ptr_width)?;
            // `|count| <= 2^63` and `size <= isize::MAX < 2^63`, so neither the byte delta nor
            // the sum can overflow `i128`; the address then wraps modulo `2^bits`.
            let modulus = 1i128 << ptr_width.bit_width();
            let delta = count * layout.size as i128;
            let new_addr = (addr as i128 + delta).rem_euclid(modulus);
            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: new_addr as u64,
                    provenance: ptr.provenance,
                },
                ty: dest_ty.clone(),
            })
        }
        IntrinsicOp::SizeOfVal | IntrinsicOp::AlignOfVal => {
            let MirValue::Ptr { ty: ptr_ty, .. } = &args[0] else {
                return Err(RvalueEvalError::TypeMismatch(NOT_POINTER));
            };
            let (_, layout) = pointee_layout(ptr_ty, ptr_width)?;
            let bytes = if op == IntrinsicOp::SizeOfVal {
                layout.size
            } else {
                layout.align
            };
            Ok(MirValue::unsigned(bytes as u128, UintTy::Usize, ptr_width))
        }
        IntrinsicOp::CopyNonOverlapping
        | IntrinsicOp::WriteBytes
        | IntrinsicOp::UnreachableUnchecked
        | IntrinsicOp::Abort
        | IntrinsicOp::PanicUnwind => Err(RvalueEvalError::TypeMismatch(
            "memory and diverging intrinsics have no value semantics",
        )),
    }
}
