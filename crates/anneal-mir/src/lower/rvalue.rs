//! Lowering and dynamic evaluation for core MIR `Rvalue`, `Statement`, and `Body` forms.
//!
//! Covers:
//! - Place and operand static type resolution (`resolve_place_ty`, `resolve_operand_ty`)
//! - `Rvalue::BinaryOp` and `Rvalue::CheckedBinaryOp` (wrapping, checked, and unchecked
//!   signed/unsigned arithmetic, divisions, shifts, bitwise operations, comparisons,
//!   three-way `Cmp`, and pointer `Offset`)
//! - `Rvalue::UnaryOp` (`Not`, `Neg`, `PtrMetadata`)
//! - `Rvalue::Aggregate` (`Array`, `Tuple`, `Adt` structs/enums/unions, `Closure`, `RawPtr`)
//! - Place/operand rvalues (`Use`, `Repeat`, `Ref`, `RawPtr`, `Len`, `Cast`, `Discriminant`,
//!   `CopyForDeref`) and `Statement` / `Body` lowering.

use std::cmp::Ordering;

use crate::ir::{
    AggregateKind, BasicBlockData, BinOp, Body, Constant, IntTy, Local, Mutability, Operand, Place,
    PointerValue, ProjectionElem, PtrWidth, Rvalue, Statement, Ty, UintTy, UnOp,
};
use crate::lower::cast::{
    AbstractByte, CastEvalError, CastLowerError, ExposedProvenanceTracker, LoweredCast,
    TransmutePolicy, TransmuteValue, decode_int_bytes, decode_ptr_bytes, encode_int_bytes,
    encode_ptr_bytes, eval_int_to_int, eval_int_to_ptr_with_ptr_width,
    eval_ptr_to_int_with_ptr_width, eval_transmute, lower_cast_rvalue_with_ptr_width,
};

/// Maximum number of array elements the evaluator materializes in a single `MirValue::Array`.
const MAX_EVAL_ARRAY_LEN: usize = 1 << 20;

/// Errors encountered during MIR rvalue, statement, or body lowering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RvalueLowerError {
    /// Local index is out of bounds for `local_decls`.
    UnknownLocal(Local),
    /// Projection step is invalid for the current place type.
    InvalidProjection {
        place: Place,
        current_ty: Ty,
        elem: ProjectionElem,
    },
    /// Array index local does not have type `usize` (`Ty::Uint(UintTy::Usize)`).
    InvalidIndexType(Ty),
    /// `Rvalue::Len` applied to a non-array type.
    InvalidLenTarget(Ty),
    /// Underlying `Rvalue::Cast` failed to lower.
    CastError(CastLowerError),
    /// Incompatible operand types for `Rvalue::BinaryOp` or `Rvalue::CheckedBinaryOp`.
    BinaryTypeMismatch {
        op: BinOp,
        lhs_ty: Ty,
        rhs_ty: Ty,
    },
    /// Invalid operand type for `Rvalue::UnaryOp`.
    InvalidUnaryOp {
        op: UnOp,
        operand_ty: Ty,
    },
    /// Array aggregate element type does not match declared element type.
    AggregateElementTypeMismatch {
        expected: Ty,
        got: Ty,
    },
    /// Invalid operand count or types for `Rvalue::Aggregate`.
    InvalidAggregateOperands {
        kind: AggregateKind,
        count: usize,
        reason: &'static str,
    },
    /// Left-hand place type and lowered rvalue type do not match in `Statement::Assign`.
    AssignmentTypeMismatch {
        place_ty: Ty,
        rvalue_ty: Ty,
    },
    /// Uninhabited type in a context requiring an inhabited type.
    UninhabitedType(Ty),
    /// Ill-formed `Operand::Constant` (wrong type, out-of-range bits, or null `&T`).
    InvalidConstant {
        constant: Constant,
        reason: &'static str,
    },
    /// `Rvalue::CopyForDeref` applied to a place whose type is not dereferenceable
    /// (`RawPtr` or `Ref`).
    InvalidCopyForDeref(Ty),
    /// Type's layout is not representable on the target pointer width (see
    /// [`Ty::layout_size_for`]).
    LayoutTooLarge(Ty),
}

impl std::fmt::Display for RvalueLowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RvalueLowerError::UnknownLocal(loc) => {
                write!(f, "unknown local _{}", loc.0)
            }
            RvalueLowerError::InvalidProjection {
                place,
                current_ty,
                elem,
            } => {
                write!(
                    f,
                    "invalid projection {elem:?} on type {current_ty:?} in place {place:?}"
                )
            }
            RvalueLowerError::InvalidIndexType(ty) => {
                write!(f, "array index local must have type usize, got {ty:?}")
            }
            RvalueLowerError::InvalidLenTarget(ty) => {
                write!(f, "Rvalue::Len requires array place, got {ty:?}")
            }
            RvalueLowerError::CastError(err) => write!(f, "cast lowering error: {err}"),
            RvalueLowerError::BinaryTypeMismatch { op, lhs_ty, rhs_ty } => {
                write!(
                    f,
                    "binary op {op:?} type mismatch: lhs={lhs_ty:?}, rhs={rhs_ty:?}"
                )
            }
            RvalueLowerError::InvalidUnaryOp { op, operand_ty } => {
                write!(f, "invalid unary op {op:?} for operand type {operand_ty:?}")
            }
            RvalueLowerError::AggregateElementTypeMismatch { expected, got } => {
                write!(
                    f,
                    "array aggregate element type mismatch: expected {expected:?}, got {got:?}"
                )
            }
            RvalueLowerError::InvalidAggregateOperands {
                kind,
                count,
                reason,
            } => {
                write!(
                    f,
                    "invalid aggregate {kind:?} with {count} operands: {reason}"
                )
            }
            RvalueLowerError::AssignmentTypeMismatch {
                place_ty,
                rvalue_ty,
            } => {
                write!(
                    f,
                    "assignment type mismatch: place has type {place_ty:?}, rvalue has type {rvalue_ty:?}"
                )
            }
            RvalueLowerError::UninhabitedType(ty) => {
                write!(f, "uninhabited type {ty:?}")
            }
            RvalueLowerError::InvalidConstant { constant, reason } => {
                write!(f, "invalid constant {constant:?}: {reason}")
            }
            RvalueLowerError::InvalidCopyForDeref(ty) => {
                write!(f, "CopyForDeref requires a RawPtr or Ref place, got {ty:?}")
            }
            RvalueLowerError::LayoutTooLarge(ty) => {
                write!(f, "type {ty:?} is too large for the target architecture")
            }
        }
    }
}

impl std::error::Error for RvalueLowerError {}

impl From<CastLowerError> for RvalueLowerError {
    fn from(err: CastLowerError) -> Self {
        RvalueLowerError::CastError(err)
    }
}

/// Lowered, type-checked representation of a MIR `Rvalue`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweredRvalue {
    Use {
        operand: Operand,
        ty: Ty,
    },
    Repeat {
        operand: Operand,
        count: usize,
        elem_ty: Ty,
        ty: Ty,
    },
    Ref {
        mutability: Mutability,
        place: Place,
        ty: Ty,
    },
    RawPtr {
        mutability: Mutability,
        place: Place,
        ty: Ty,
    },
    Len {
        place: Place,
        static_len: usize,
        ty: Ty,
    },
    Cast {
        cast: LoweredCast,
        ty: Ty,
    },
    BinaryOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
        lhs_ty: Ty,
        rhs_ty: Ty,
        ty: Ty,
        pointee_size: Option<usize>,
    },
    CheckedBinaryOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
        lhs_ty: Ty,
        rhs_ty: Ty,
        ty: Ty,
    },
    UnaryOp {
        op: UnOp,
        operand: Operand,
        operand_ty: Ty,
        ty: Ty,
    },
    Discriminant {
        place: Place,
        place_ty: Ty,
        ty: Ty,
    },
    Aggregate {
        kind: AggregateKind,
        operands: Vec<Operand>,
        operand_tys: Vec<Ty>,
        ty: Ty,
    },
    CopyForDeref {
        place: Place,
        ty: Ty,
    },
}

impl LoweredRvalue {
    /// Returns the static result `Ty` of the lowered rvalue.
    pub fn ty(&self) -> &Ty {
        match self {
            LoweredRvalue::Use { ty, .. }
            | LoweredRvalue::Repeat { ty, .. }
            | LoweredRvalue::Ref { ty, .. }
            | LoweredRvalue::RawPtr { ty, .. }
            | LoweredRvalue::Len { ty, .. }
            | LoweredRvalue::Cast { ty, .. }
            | LoweredRvalue::BinaryOp { ty, .. }
            | LoweredRvalue::CheckedBinaryOp { ty, .. }
            | LoweredRvalue::UnaryOp { ty, .. }
            | LoweredRvalue::Discriminant { ty, .. }
            | LoweredRvalue::Aggregate { ty, .. }
            | LoweredRvalue::CopyForDeref { ty, .. } => ty,
        }
    }
}

/// Lowered representation of a MIR `Statement`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweredStatement {
    Assign {
        place: Place,
        place_ty: Ty,
        rvalue: LoweredRvalue,
    },
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}

/// Lowered representation of a MIR basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredBasicBlock {
    pub statements: Vec<LoweredStatement>,
    pub is_cleanup: bool,
}

/// Lowered representation of a complete MIR body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredBody {
    pub local_decls: Vec<Ty>,
    pub basic_blocks: Vec<LoweredBasicBlock>,
    pub ptr_width: PtrWidth,
}

/// Resolves the static `Ty` of a `Place` against `local_decls`, validating all projections.
///
/// Mirrors `rustc`'s MIR validator: `Deref` requires a `RawPtr`/`Ref`; `Field(i, ty)`
/// requires a tuple whose field `i` has exactly type `ty` (arrays have no fields);
/// `Index`/`ConstantIndex`/`Subslice` require an array (and a `usize` index local / in-bounds
/// constant offsets); `Downcast(_)` selects an ADT variant, which Anneal models as the tuple of
/// that variant's fields, so it leaves the tuple type unchanged and subsequent `Field`
/// projections are still fully type-checked.
pub fn resolve_place_ty(place: &Place, local_decls: &[Ty]) -> Result<Ty, RvalueLowerError> {
    let Some(base_ty) = local_decls.get(place.local.0) else {
        return Err(RvalueLowerError::UnknownLocal(place.local));
    };
    let mut cur_ty = base_ty.clone();

    for elem in &place.projection {
        let invalid = |current_ty: Ty| RvalueLowerError::InvalidProjection {
            place: place.clone(),
            current_ty,
            elem: elem.clone(),
        };
        cur_ty = match (elem, cur_ty) {
            (ProjectionElem::Deref, Ty::RawPtr(inner, _) | Ty::Ref(inner, _)) => *inner,
            (ProjectionElem::Field(idx, field_ty), Ty::Tuple(fields)) => {
                if fields.get(*idx) != Some(field_ty) {
                    return Err(invalid(Ty::Tuple(fields)));
                }
                field_ty.clone()
            }
            (ProjectionElem::Index(idx_local), Ty::Array(elem_ty, _)) => {
                let Some(idx_ty) = local_decls.get(idx_local.0) else {
                    return Err(RvalueLowerError::UnknownLocal(*idx_local));
                };
                if *idx_ty != Ty::Uint(UintTy::Usize) {
                    return Err(RvalueLowerError::InvalidIndexType(idx_ty.clone()));
                }
                *elem_ty
            }
            (
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                },
                Ty::Array(elem_ty, len),
            ) => {
                let len_u64 = len as u64;
                let valid_bounds = len_u64 >= *min_length
                    && if *from_end {
                        *offset >= 1 && *offset <= len_u64
                    } else {
                        *offset < len_u64
                    };
                if !valid_bounds {
                    return Err(invalid(Ty::Array(elem_ty, len)));
                }
                *elem_ty
            }
            (ProjectionElem::Subslice { from, to, from_end }, Ty::Array(elem_ty, len)) => {
                let len_u64 = len as u64;
                let new_len = if *from_end {
                    match from.checked_add(*to) {
                        Some(total) if total <= len_u64 => len_u64 - total,
                        _ => return Err(invalid(Ty::Array(elem_ty, len))),
                    }
                } else if *from <= *to && *to <= len_u64 {
                    *to - *from
                } else {
                    return Err(invalid(Ty::Array(elem_ty, len)));
                };
                Ty::Array(elem_ty, new_len as usize)
            }
            (ProjectionElem::Downcast(_), Ty::Tuple(fields)) => Ty::Tuple(fields),
            (_, other) => return Err(invalid(other)),
        };
    }

    Ok(cur_ty)
}

/// Resolves the static `Ty` of an `Operand` against `local_decls`.
pub fn resolve_operand_ty(operand: &Operand, local_decls: &[Ty]) -> Result<Ty, RvalueLowerError> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => resolve_place_ty(place, local_decls),
        Operand::Constant(constant) => Ok(constant.ty()),
    }
}

/// Checks that a MIR constant is well-formed under `ptr_width`:
/// - `Constant::Int(bits, ty)` requires an `Int`/`Uint` type and `bits` within the type's
///   width (signed constants may also be given in sign-extended `i128` form, e.g.
///   `u128::MAX` for `-1i8`);
/// - `Constant::Ptr(ptr, ty)` requires a `RawPtr`/`Ref` type, an address within the target
///   pointer width, and a non-null address for references.
fn check_constant(constant: &Constant, ptr_width: PtrWidth) -> Result<(), &'static str> {
    match constant {
        Constant::Int(bits, ty) => {
            let in_range = match ty {
                Ty::Uint(ut) => *bits <= ut.mask(ptr_width),
                Ty::Int(it) => {
                    let sign_extended = *bits as i128;
                    *bits <= it.mask(ptr_width)
                        || (sign_extended < 0 && sign_extended >= it.min_value(ptr_width))
                }
                _ => return Err("Constant::Int must carry an Int or Uint type"),
            };
            if in_range {
                Ok(())
            } else {
                Err("Constant::Int bits exceed the width of its type")
            }
        }
        Constant::Ptr(ptr, ty) => {
            if !ty.is_any_ptr() {
                return Err("Constant::Ptr must carry a RawPtr or Ref type");
            }
            if u128::from(ptr.addr) > ptr_width.mask() {
                return Err("Constant::Ptr address exceeds the target pointer width");
            }
            if ty.is_ref() && ptr.addr == 0 {
                return Err("Constant::Ptr of reference type must be non-null");
            }
            Ok(())
        }
        Constant::Bool(_) | Constant::Char(_) | Constant::Unit => Ok(()),
    }
}

/// Resolves an operand's type during lowering, additionally validating constants.
fn lower_operand_ty(
    operand: &Operand,
    local_decls: &[Ty],
    ptr_width: PtrWidth,
) -> Result<Ty, RvalueLowerError> {
    if let Operand::Constant(constant) = operand {
        check_constant(constant, ptr_width).map_err(|reason| RvalueLowerError::InvalidConstant {
            constant: constant.clone(),
            reason,
        })?;
    }
    resolve_operand_ty(operand, local_decls)
}

/// Returns `ty` if its layout is representable under `ptr_width`, else `LayoutTooLarge`.
fn check_layout(ty: Ty, ptr_width: PtrWidth) -> Result<Ty, RvalueLowerError> {
    if ty.layout_size_for(ptr_width).is_none() {
        return Err(RvalueLowerError::LayoutTooLarge(ty));
    }
    Ok(ty)
}

/// Validates operand types for `BinOp` and returns `(result_ty, pointee_size)`.
fn validate_binop_types(
    op: BinOp,
    lhs_ty: &Ty,
    rhs_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<(Ty, Option<usize>), RvalueLowerError> {
    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::AddUnchecked
        | BinOp::SubUnchecked
        | BinOp::MulUnchecked
        | BinOp::Div
        | BinOp::Rem => {
            if lhs_ty != rhs_ty || !lhs_ty.is_integral() {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            }
            Ok((lhs_ty.clone(), None))
        }
        BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow => {
            if lhs_ty != rhs_ty || !lhs_ty.is_integral() {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            }
            Ok((Ty::Tuple(vec![lhs_ty.clone(), Ty::Bool]), None))
        }
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
            let valid = lhs_ty == rhs_ty && (*lhs_ty == Ty::Bool || lhs_ty.is_integral());
            if !valid {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            }
            Ok((lhs_ty.clone(), None))
        }
        BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked => {
            // In rustc MIR, LHS must be integral and RHS may be any integral type
            // (signed or unsigned, possibly different width from LHS).
            if !lhs_ty.is_integral() || !rhs_ty.is_integral() {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            }
            Ok((lhs_ty.clone(), None))
        }
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            if lhs_ty != rhs_ty || !lhs_ty.is_scalar() {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            }
            Ok((Ty::Bool, None))
        }
        BinOp::Cmp => {
            // Three-way comparison (`Cmp`) requires matching Int, Uint, Bool, or Char (rejects pointers).
            let valid_scalar =
                lhs_ty.is_integral() || matches!(lhs_ty, Ty::Bool | Ty::Char);
            if lhs_ty != rhs_ty || !valid_scalar {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            }
            Ok((Ty::Int(IntTy::I8), None))
        }
        BinOp::Offset => {
            let Some(pointee) = lhs_ty.pointee_ty() else {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            };
            if !rhs_ty.is_integral() {
                return Err(RvalueLowerError::BinaryTypeMismatch {
                    op,
                    lhs_ty: lhs_ty.clone(),
                    rhs_ty: rhs_ty.clone(),
                });
            }
            // The stride is the pointee's layout size, which is well-defined even for
            // uninhabited pointees (`*const !` has stride 0, `*const (!, u32)` stride 4).
            let stride = pointee
                .layout_size_for(ptr_width)
                .ok_or_else(|| RvalueLowerError::LayoutTooLarge(pointee.clone()))?;
            Ok((lhs_ty.clone(), Some(stride)))
        }
    }
}

/// Lowers an `Rvalue` against `local_decls` under `ptr_width` and `policy`.
pub fn lower_rvalue_with_policy(
    rvalue: &Rvalue,
    local_decls: &[Ty],
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredRvalue, RvalueLowerError> {
    match rvalue {
        Rvalue::Use(operand) => {
            let ty = lower_operand_ty(operand, local_decls, ptr_width)?;
            Ok(LoweredRvalue::Use {
                operand: operand.clone(),
                ty,
            })
        }
        Rvalue::Repeat(operand, count) => {
            let elem_ty = lower_operand_ty(operand, local_decls, ptr_width)?;
            let ty = check_layout(Ty::Array(Box::new(elem_ty.clone()), *count), ptr_width)?;
            Ok(LoweredRvalue::Repeat {
                operand: operand.clone(),
                count: *count,
                elem_ty,
                ty,
            })
        }
        Rvalue::Ref(mutability, place) => {
            let pointee_ty = resolve_place_ty(place, local_decls)?;
            let ty = Ty::Ref(Box::new(pointee_ty), *mutability);
            Ok(LoweredRvalue::Ref {
                mutability: *mutability,
                place: place.clone(),
                ty,
            })
        }
        Rvalue::RawPtr(mutability, place) => {
            let pointee_ty = resolve_place_ty(place, local_decls)?;
            let ty = Ty::RawPtr(Box::new(pointee_ty), *mutability);
            Ok(LoweredRvalue::RawPtr {
                mutability: *mutability,
                place: place.clone(),
                ty,
            })
        }
        Rvalue::Len(place) => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            match place_ty {
                Ty::Array(_, len) if (len as u128) <= ptr_width.max_usize() => {
                    Ok(LoweredRvalue::Len {
                        place: place.clone(),
                        static_len: len,
                        ty: Ty::Uint(UintTy::Usize),
                    })
                }
                Ty::Array(_, _) => Err(RvalueLowerError::LayoutTooLarge(place_ty)),
                other => Err(RvalueLowerError::InvalidLenTarget(other)),
            }
        }
        Rvalue::Cast(kind, operand, target_ty) => {
            let src_ty = lower_operand_ty(operand, local_decls, ptr_width)?;
            let cast = lower_cast_rvalue_with_ptr_width(
                *kind,
                operand,
                &src_ty,
                target_ty,
                ptr_width,
                policy,
            )?;
            Ok(LoweredRvalue::Cast {
                cast,
                ty: target_ty.clone(),
            })
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let lhs_ty = lower_operand_ty(lhs, local_decls, ptr_width)?;
            let rhs_ty = lower_operand_ty(rhs, local_decls, ptr_width)?;
            let (ty, pointee_size) = validate_binop_types(*op, &lhs_ty, &rhs_ty, ptr_width)?;
            Ok(LoweredRvalue::BinaryOp {
                op: *op,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                lhs_ty,
                rhs_ty,
                ty,
                pointee_size,
            })
        }
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let lhs_ty = lower_operand_ty(lhs, local_decls, ptr_width)?;
            let rhs_ty = lower_operand_ty(rhs, local_decls, ptr_width)?;
            match op {
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::AddWithOverflow
                | BinOp::SubWithOverflow
                | BinOp::MulWithOverflow => {
                    if lhs_ty != rhs_ty || !lhs_ty.is_integral() {
                        return Err(RvalueLowerError::BinaryTypeMismatch {
                            op: *op,
                            lhs_ty,
                            rhs_ty,
                        });
                    }
                }
                BinOp::Shl | BinOp::Shr => {
                    if !lhs_ty.is_integral() || !rhs_ty.is_integral() {
                        return Err(RvalueLowerError::BinaryTypeMismatch {
                            op: *op,
                            lhs_ty,
                            rhs_ty,
                        });
                    }
                }
                _ => {
                    return Err(RvalueLowerError::BinaryTypeMismatch {
                        op: *op,
                        lhs_ty,
                        rhs_ty,
                    });
                }
            }
            let ty = Ty::Tuple(vec![lhs_ty.clone(), Ty::Bool]);
            Ok(LoweredRvalue::CheckedBinaryOp {
                op: *op,
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                lhs_ty,
                rhs_ty,
                ty,
            })
        }
        Rvalue::UnaryOp(op, operand) => {
            let operand_ty = lower_operand_ty(operand, local_decls, ptr_width)?;
            let ty = match op {
                UnOp::Not => {
                    if operand_ty == Ty::Bool || operand_ty.is_integral() {
                        operand_ty.clone()
                    } else {
                        return Err(RvalueLowerError::InvalidUnaryOp {
                            op: *op,
                            operand_ty,
                        });
                    }
                }
                UnOp::Neg => {
                    // UnOp::Neg is valid on signed Int(_) ONLY (must reject Uint, Bool, Char, pointers).
                    if operand_ty.is_signed_int() {
                        operand_ty.clone()
                    } else {
                        return Err(RvalueLowerError::InvalidUnaryOp {
                            op: *op,
                            operand_ty,
                        });
                    }
                }
                UnOp::PtrMetadata => {
                    if operand_ty.is_any_ptr() {
                        Ty::unit()
                    } else {
                        return Err(RvalueLowerError::InvalidUnaryOp {
                            op: *op,
                            operand_ty,
                        });
                    }
                }
            };
            Ok(LoweredRvalue::UnaryOp {
                op: *op,
                operand: operand.clone(),
                operand_ty,
                ty,
            })
        }
        Rvalue::Discriminant(place) => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            if !place_ty.is_inhabited() {
                return Err(RvalueLowerError::UninhabitedType(place_ty));
            }
            Ok(LoweredRvalue::Discriminant {
                place: place.clone(),
                place_ty,
                ty: Ty::Int(IntTy::Isize),
            })
        }
        Rvalue::Aggregate(kind, operands) => {
            let mut operand_tys = Vec::with_capacity(operands.len());
            for op in operands {
                operand_tys.push(lower_operand_ty(op, local_decls, ptr_width)?);
            }
            let invalid = |reason: &'static str| RvalueLowerError::InvalidAggregateOperands {
                kind: kind.clone(),
                count: operands.len(),
                reason,
            };
            let ty = match kind {
                AggregateKind::Array(elem_ty) => {
                    for op_ty in &operand_tys {
                        if op_ty != elem_ty {
                            return Err(RvalueLowerError::AggregateElementTypeMismatch {
                                expected: elem_ty.clone(),
                                got: op_ty.clone(),
                            });
                        }
                    }
                    check_layout(Ty::Array(Box::new(elem_ty.clone()), operands.len()), ptr_width)?
                }
                AggregateKind::Tuple => check_layout(Ty::Tuple(operand_tys.clone()), ptr_width)?,
                AggregateKind::Adt {
                    variant_idx,
                    active_field,
                    ..
                } => {
                    if active_field.is_some() {
                        // `rustc` MIR validation: union initializers have exactly one operand and
                        // always use `FIRST_VARIANT` (unions are single-variant ADTs).
                        if operands.len() != 1 {
                            return Err(invalid(
                                "union aggregate initialization requires exactly 1 operand",
                            ));
                        }
                        if *variant_idx != 0 {
                            return Err(invalid("union aggregate initialization must use variant 0"));
                        }
                    }
                    check_layout(Ty::Tuple(operand_tys.clone()), ptr_width)?
                }
                AggregateKind::Closure => check_layout(Ty::Tuple(operand_tys.clone()), ptr_width)?,
                AggregateKind::RawPtr {
                    pointee,
                    mutability,
                } => {
                    if operands.len() != 2 {
                        return Err(invalid(
                            "RawPtr aggregate requires 2 operands (data_ptr_or_addr, unit_metadata)",
                        ));
                    }
                    // `rustc` MIR validation: the data pointer is a thin raw pointer whose
                    // mutability matches the constructed pointer's; Anneal additionally accepts a
                    // `usize` address (yielding a pointer without provenance).
                    let data_ok = match &operand_tys[0] {
                        Ty::RawPtr(_, data_mutability) => data_mutability == mutability,
                        Ty::Uint(UintTy::Usize) => true,
                        _ => false,
                    };
                    if !data_ok {
                        return Err(invalid(
                            "RawPtr aggregate first operand must be a raw pointer of matching mutability or a usize address",
                        ));
                    }
                    if !operand_tys[1].is_unit() {
                        return Err(invalid(
                            "thin RawPtr aggregate second operand must be unit metadata ()",
                        ));
                    }
                    Ty::RawPtr(Box::new(pointee.clone()), *mutability)
                }
            };
            Ok(LoweredRvalue::Aggregate {
                kind: kind.clone(),
                operands: operands.clone(),
                operand_tys,
                ty,
            })
        }
        Rvalue::CopyForDeref(place) => {
            let ty = resolve_place_ty(place, local_decls)?;
            // `rustc` only emits `CopyForDeref` for places of dereferenceable type.
            if !ty.is_any_ptr() {
                return Err(RvalueLowerError::InvalidCopyForDeref(ty));
            }
            Ok(LoweredRvalue::CopyForDeref {
                place: place.clone(),
                ty,
            })
        }
    }
}

/// Lowers an `Rvalue` against `local_decls` using `ptr_width` and `TransmutePolicy::RejectPtrToInt`.
pub fn lower_rvalue(
    rvalue: &Rvalue,
    local_decls: &[Ty],
    ptr_width: PtrWidth,
) -> Result<LoweredRvalue, RvalueLowerError> {
    lower_rvalue_with_policy(rvalue, local_decls, ptr_width, TransmutePolicy::RejectPtrToInt)
}

/// Lowers a single MIR `Statement` under `ptr_width` and `policy`.
pub fn lower_statement_with_policy(
    stmt: &Statement,
    local_decls: &[Ty],
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredStatement, RvalueLowerError> {
    match stmt {
        Statement::Assign(place, rvalue) => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            let lowered = lower_rvalue_with_policy(rvalue, local_decls, ptr_width, policy)?;
            let rvalue_ty = lowered.ty();

            let compatible = if let LoweredRvalue::Aggregate {
                kind:
                    AggregateKind::Adt {
                        active_field: Some(field_idx),
                        ..
                    },
                operand_tys,
                ..
            } = &lowered
            {
                // Union initialization: Anneal models a union-typed place as the tuple of the
                // union's declared field types, so the destination must declare field
                // `field_idx` with exactly the initializing operand's type (`rustc`: "union
                // field has the wrong type" otherwise). Checking this before `&place_ty == rvalue_ty`
                // ensures out-of-bounds `field_idx` on a 1-field union is rejected.
                matches!(
                    &place_ty,
                    Ty::Tuple(fields)
                        if operand_tys.len() == 1 && fields.get(*field_idx) == Some(&operand_tys[0])
                )
            } else {
                &place_ty == rvalue_ty
            };

            if !compatible {
                return Err(RvalueLowerError::AssignmentTypeMismatch {
                    place_ty,
                    rvalue_ty: rvalue_ty.clone(),
                });
            }

            Ok(LoweredStatement::Assign {
                place: place.clone(),
                place_ty,
                rvalue: lowered,
            })
        }
        Statement::StorageLive(loc) => {
            if loc.0 >= local_decls.len() {
                return Err(RvalueLowerError::UnknownLocal(*loc));
            }
            Ok(LoweredStatement::StorageLive(*loc))
        }
        Statement::StorageDead(loc) => {
            if loc.0 >= local_decls.len() {
                return Err(RvalueLowerError::UnknownLocal(*loc));
            }
            Ok(LoweredStatement::StorageDead(*loc))
        }
        Statement::Nop => Ok(LoweredStatement::Nop),
    }
}

/// Lowers a single MIR `Statement` under `ptr_width` using `TransmutePolicy::RejectPtrToInt`.
pub fn lower_statement(
    stmt: &Statement,
    local_decls: &[Ty],
    ptr_width: PtrWidth,
) -> Result<LoweredStatement, RvalueLowerError> {
    lower_statement_with_policy(stmt, local_decls, ptr_width, TransmutePolicy::RejectPtrToInt)
}

/// Lowers a complete MIR `Body` under `ptr_width` and `policy`.
///
/// Every local's declared type must be representable on the target
/// ([`Ty::layout_size_for`]), otherwise `RvalueLowerError::LayoutTooLarge` is returned.
pub fn lower_body_with_policy(
    body: &Body,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredBody, RvalueLowerError> {
    for local_ty in &body.local_decls {
        check_layout(local_ty.clone(), ptr_width)?;
    }
    let mut basic_blocks = Vec::with_capacity(body.basic_blocks.len());
    for BasicBlockData {
        statements,
        is_cleanup,
    } in &body.basic_blocks
    {
        let mut lowered_stmts = Vec::with_capacity(statements.len());
        for stmt in statements {
            lowered_stmts.push(lower_statement_with_policy(
                stmt,
                &body.local_decls,
                ptr_width,
                policy,
            )?);
        }
        basic_blocks.push(LoweredBasicBlock {
            statements: lowered_stmts,
            is_cleanup: *is_cleanup,
        });
    }
    Ok(LoweredBody {
        local_decls: body.local_decls.clone(),
        basic_blocks,
        ptr_width,
    })
}

/// Lowers a complete MIR `Body` under `ptr_width` using `TransmutePolicy::RejectPtrToInt`.
pub fn lower_body(body: &Body, ptr_width: PtrWidth) -> Result<LoweredBody, RvalueLowerError> {
    lower_body_with_policy(body, ptr_width, TransmutePolicy::RejectPtrToInt)
}

/// Runtime value representation for dynamic evaluation of lowered MIR rvalues.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MirValue {
    /// Two's-complement or unsigned integer scalar value paired with its `Ty`.
    Int { bits: u128, ty: Ty },
    /// Boolean scalar.
    Bool(bool),
    /// Unicode scalar value (`char`).
    Char(char),
    /// Machine pointer with optional provenance.
    Ptr { ptr: PointerValue, ty: Ty },
    /// Unit value `()`.
    Unit,
    /// Fixed-size homogeneous array value.
    Array { elements: Vec<MirValue>, elem_ty: Ty },
    /// Heterogeneous tuple or closure capture value.
    Tuple(Vec<MirValue>),
    /// Algebraic data type (struct, enum variant, or union) value.
    Adt {
        def_path: String,
        variant_idx: usize,
        active_field: Option<usize>,
        fields: Vec<MirValue>,
    },
}

/// Type alias for `MirValue`.
pub type RvalueValue = MirValue;

impl MirValue {
    /// Constructs an unsigned integer `MirValue` masked to `uint_ty` under `ptr_width`.
    pub fn unsigned(val: u128, uint_ty: UintTy, ptr_width: PtrWidth) -> Self {
        MirValue::Int {
            bits: val & uint_ty.mask(ptr_width),
            ty: Ty::Uint(uint_ty),
        }
    }

    /// Constructs a signed two's-complement integer `MirValue` masked to `int_ty` under `ptr_width`.
    pub fn signed(val: i128, int_ty: IntTy, ptr_width: PtrWidth) -> Self {
        MirValue::Int {
            bits: int_ty.truncate_signed(val, ptr_width),
            ty: Ty::Int(int_ty),
        }
    }

    /// Constructs a pointer `MirValue`.
    pub fn ptr(ptr: PointerValue, ty: Ty) -> Self {
        MirValue::Ptr { ptr, ty }
    }

    /// Returns true if this value represents `()` (`MirValue::Unit` or empty `MirValue::Tuple`).
    pub fn is_unit(&self) -> bool {
        matches!(self, MirValue::Unit)
            || matches!(self, MirValue::Tuple(fields) if fields.is_empty())
    }

    /// Extracts the raw bit pattern if `self` is `Int`, `Bool`, or `Char`.
    pub fn as_bits(&self) -> Option<u128> {
        match self {
            MirValue::Int { bits, .. } => Some(*bits),
            MirValue::Bool(b) => Some(u128::from(*b)),
            MirValue::Char(c) => Some(u32::from(*c) as u128),
            _ => None,
        }
    }

    /// Extracts the sign-extended `i128` value if `self` is a signed `MirValue::Int`.
    pub fn as_signed(&self, ptr_width: PtrWidth) -> Option<i128> {
        match self {
            MirValue::Int {
                bits,
                ty: Ty::Int(it),
            } => Some(it.sign_extend(*bits, ptr_width)),
            _ => None,
        }
    }

    /// Extracts the boolean value if `self` is `MirValue::Bool`.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            MirValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Extracts the `PointerValue` if `self` is `MirValue::Ptr`.
    pub fn as_ptr(&self) -> Option<PointerValue> {
        match self {
            MirValue::Ptr { ptr, .. } => Some(*ptr),
            _ => None,
        }
    }

    /// Extracts `(wrapped_bits, overflowed)` from a checked binary operation tuple `(T, bool)`.
    pub fn as_checked_pair(&self) -> Option<(u128, bool)> {
        match self {
            MirValue::Tuple(fields) if fields.len() == 2 => {
                let bits = fields[0].as_bits()?;
                let overflowed = fields[1].as_bool()?;
                Some((bits, overflowed))
            }
            _ => None,
        }
    }

    /// Returns the runtime `Ty` of this value.
    pub fn ty(&self) -> Ty {
        match self {
            MirValue::Int { ty, .. } => ty.clone(),
            MirValue::Bool(_) => Ty::Bool,
            MirValue::Char(_) => Ty::Char,
            MirValue::Ptr { ty, .. } => ty.clone(),
            MirValue::Unit => Ty::unit(),
            MirValue::Array { elements, elem_ty } => {
                Ty::Array(Box::new(elem_ty.clone()), elements.len())
            }
            MirValue::Tuple(fields) => Ty::Tuple(fields.iter().map(MirValue::ty).collect()),
            MirValue::Adt { fields, .. } => Ty::Tuple(fields.iter().map(MirValue::ty).collect()),
        }
    }
}

/// Errors encountered during dynamic evaluation of MIR rvalues.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RvalueEvalError {
    /// Division or remainder by zero (`x / 0` or `x % 0`).
    DivisionByZero,
    /// Signed two's-complement division or remainder overflow (`INT_MIN / -1` or `INT_MIN % -1`).
    SignedDivisionOverflow {
        min_val: i128,
        bit_width: u32,
    },
    /// Unchecked arithmetic overflow (`AddUnchecked`, `SubUnchecked`, `MulUnchecked`).
    ArithmeticOverflow {
        op: BinOp,
    },
    /// Unchecked shift amount out of bounds (`rhs < 0` or `rhs >= lhs_bit_width`).
    ShiftOverflow {
        shift_bits: u128,
        rhs_signed: Option<i128>,
        lhs_bit_width: u32,
    },
    /// Pointer offset overflowed target address space or `isize` bounds.
    PointerOffsetOverflow {
        base_addr: u64,
        offset: i128,
        pointee_size: usize,
    },
    /// Underlying cast evaluation error.
    CastEval(CastEvalError),
    /// Dynamic type mismatch.
    TypeMismatch(&'static str),
    /// Non-zero pointer `Offset` on a pointer without provenance: `ptr::offset`/`ptr::add`
    /// require the pointer to be derived from an allocation unless the byte offset is `0`.
    PointerArithmeticWithoutProvenance {
        addr: u64,
        byte_offset: i128,
    },
    /// Place projection that cannot be evaluated without a memory model (only bare locals,
    /// and `&(*p)` / `&raw (*p)` reborrows, are supported).
    UnsupportedPlaceProjection(Place),
    /// Ill-formed `Constant` (wrong type, out-of-range bits, or null `&T`).
    InvalidConstant(&'static str),
    /// Array value too large for the evaluator to materialize.
    EvaluationLimit {
        len: usize,
    },
}

impl std::fmt::Display for RvalueEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RvalueEvalError::DivisionByZero => write!(f, "division or remainder by zero (UB)"),
            RvalueEvalError::SignedDivisionOverflow { min_val, bit_width } => {
                write!(
                    f,
                    "signed {bit_width}-bit division/remainder overflow on INT_MIN ({min_val}) / -1 (UB)"
                )
            }
            RvalueEvalError::ArithmeticOverflow { op } => {
                write!(f, "unchecked arithmetic overflow in {op:?} (UB)")
            }
            RvalueEvalError::ShiftOverflow {
                shift_bits,
                rhs_signed,
                lhs_bit_width,
            } => {
                write!(
                    f,
                    "unchecked shift overflow: shift={shift_bits:#x} (signed={rhs_signed:?}) for {lhs_bit_width}-bit LHS (UB)"
                )
            }
            RvalueEvalError::PointerOffsetOverflow {
                base_addr,
                offset,
                pointee_size,
            } => {
                write!(
                    f,
                    "pointer offset overflow: base={base_addr:#x}, offset={offset}, pointee_size={pointee_size}"
                )
            }
            RvalueEvalError::CastEval(err) => write!(f, "cast evaluation error: {err}"),
            RvalueEvalError::TypeMismatch(msg) => write!(f, "rvalue type mismatch: {msg}"),
            RvalueEvalError::PointerArithmeticWithoutProvenance { addr, byte_offset } => {
                write!(
                    f,
                    "pointer offset by {byte_offset} bytes on pointer {addr:#x} without provenance (UB)"
                )
            }
            RvalueEvalError::UnsupportedPlaceProjection(place) => {
                write!(f, "place {place:?} requires a memory model to evaluate")
            }
            RvalueEvalError::InvalidConstant(reason) => write!(f, "invalid constant: {reason}"),
            RvalueEvalError::EvaluationLimit { len } => {
                write!(f, "array of {len} elements exceeds the evaluator's materialization limit")
            }
        }
    }
}

impl std::error::Error for RvalueEvalError {}

impl From<CastEvalError> for RvalueEvalError {
    fn from(err: CastEvalError) -> Self {
        RvalueEvalError::CastEval(err)
    }
}

/// Evaluates a `Constant` into a `MirValue` under `ptr_width`.
///
/// Rejects ill-formed constants (see `check_constant`) instead of silently truncating them:
/// e.g. a `Constant::Int` whose bits exceed its type's width, or a null `&T` constant.
pub fn eval_constant(constant: &Constant, ptr_width: PtrWidth) -> Result<MirValue, RvalueEvalError> {
    check_constant(constant, ptr_width).map_err(RvalueEvalError::InvalidConstant)?;
    match constant {
        Constant::Int(bits, ty) => match ty {
            Ty::Int(it) => Ok(MirValue::Int {
                bits: *bits & it.mask(ptr_width),
                ty: ty.clone(),
            }),
            Ty::Uint(ut) => Ok(MirValue::Int {
                bits: *bits & ut.mask(ptr_width),
                ty: ty.clone(),
            }),
            _ => Err(RvalueEvalError::InvalidConstant(
                "Constant::Int must carry an Int or Uint type",
            )),
        },
        Constant::Bool(b) => Ok(MirValue::Bool(*b)),
        Constant::Char(c) => Ok(MirValue::Char(*c)),
        Constant::Ptr(ptr, ty) => Ok(MirValue::Ptr {
            ptr: *ptr,
            ty: ty.clone(),
        }),
        Constant::Unit => Ok(MirValue::Unit),
    }
}

/// Computes `(wrapped_bits, overflowed)` for integer `Add`, `Sub`, or `Mul` (plus `*WithOverflow` / `*Unchecked`).
fn compute_int_arith_with_overflow(
    op: BinOp,
    lhs_bits: u128,
    rhs_bits: u128,
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<(u128, bool), RvalueEvalError> {
    match ty {
        Ty::Uint(ut) => {
            let mask = ut.mask(ptr_width);
            let a = lhs_bits & mask;
            let b = rhs_bits & mask;
            match op {
                BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked => {
                    let (sum128, ov128) = a.overflowing_add(b);
                    let overflowed = ov128 || sum128 > mask;
                    Ok((sum128 & mask, overflowed))
                }
                BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                    let overflowed = a < b;
                    let wrapped = a.wrapping_sub(b) & mask;
                    Ok((wrapped, overflowed))
                }
                BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                    let (prod128, ov128) = a.overflowing_mul(b);
                    let overflowed = ov128 || prod128 > mask;
                    Ok((prod128 & mask, overflowed))
                }
                _ => Err(RvalueEvalError::TypeMismatch("unsupported arithmetic op")),
            }
        }
        Ty::Int(it) => {
            let mask = it.mask(ptr_width);
            let min_val = it.min_value(ptr_width);
            let max_val = it.max_value(ptr_width);
            let a = it.sign_extend(lhs_bits, ptr_width);
            let b = it.sign_extend(rhs_bits, ptr_width);
            match op {
                BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked => {
                    let (sum, ov128) = a.overflowing_add(b);
                    let overflowed = ov128 || sum < min_val || sum > max_val;
                    Ok(((sum as u128) & mask, overflowed))
                }
                BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                    let (diff, ov128) = a.overflowing_sub(b);
                    let overflowed = ov128 || diff < min_val || diff > max_val;
                    Ok(((diff as u128) & mask, overflowed))
                }
                BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                    let (prod, ov128) = a.overflowing_mul(b);
                    let overflowed = ov128 || prod < min_val || prod > max_val;
                    Ok(((prod as u128) & mask, overflowed))
                }
                _ => Err(RvalueEvalError::TypeMismatch("unsupported arithmetic op")),
            }
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "integer arithmetic requires Int or Uint type",
        )),
    }
}

/// Computes `(shifted_bits, overflowed)` for `Shl`, `ShlUnchecked`, `Shr`, or `ShrUnchecked`.
fn compute_shift_with_overflow(
    op: BinOp,
    lhs_bits: u128,
    lhs_ty: &Ty,
    rhs_bits: u128,
    rhs_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<(u128, bool, Option<i128>, u32), RvalueEvalError> {
    let lhs_w = match lhs_ty {
        Ty::Int(it) => it.bit_width_for(ptr_width),
        Ty::Uint(ut) => ut.bit_width_for(ptr_width),
        _ => {
            return Err(RvalueEvalError::TypeMismatch(
                "shift LHS must be Int or Uint",
            ));
        }
    };
    let lhs_mask = lhs_ty.scalar_mask(ptr_width);
    let rhs_masked = rhs_bits & rhs_ty.scalar_mask(ptr_width);

    let (overflowed, rhs_signed) = match rhs_ty {
        Ty::Int(rhs_it) => {
            let signed = rhs_it.sign_extend(rhs_masked, ptr_width);
            let ov = signed < 0 || (signed as u128) >= (lhs_w as u128);
            (ov, Some(signed))
        }
        Ty::Uint(_) => (rhs_masked >= (lhs_w as u128), None),
        _ => {
            return Err(RvalueEvalError::TypeMismatch(
                "shift RHS must be Int or Uint",
            ));
        }
    };

    let shift_amt = (rhs_masked & ((lhs_w as u128) - 1)) as u32;
    let shifted = match op {
        BinOp::Shl | BinOp::ShlUnchecked => ((lhs_bits & lhs_mask) << shift_amt) & lhs_mask,
        BinOp::Shr | BinOp::ShrUnchecked => match lhs_ty {
            Ty::Uint(_) => ((lhs_bits & lhs_mask) >> shift_amt) & lhs_mask,
            Ty::Int(lhs_it) => {
                let signed_lhs = lhs_it.sign_extend(lhs_bits, ptr_width);
                let shifted_signed = signed_lhs >> shift_amt;
                (shifted_signed as u128) & lhs_mask
            }
            _ => unreachable!(),
        },
        _ => unreachable!(),
    };

    Ok((shifted, overflowed, rhs_signed, lhs_w))
}

/// Compares two matching scalar/pointer `MirValue`s under `ptr_width`.
fn compare_mir_values(
    lhs: &MirValue,
    rhs: &MirValue,
    ptr_width: PtrWidth,
    allow_pointers: bool,
) -> Result<Ordering, RvalueEvalError> {
    match (lhs, rhs) {
        (MirValue::Bool(a), MirValue::Bool(b)) => Ok(a.cmp(b)),
        (MirValue::Char(a), MirValue::Char(b)) => Ok(a.cmp(b)),
        (
            MirValue::Int {
                bits: a,
                ty: lhs_ty,
            },
            MirValue::Int {
                bits: b,
                ty: rhs_ty,
            },
        ) if lhs_ty == rhs_ty => match lhs_ty {
            Ty::Uint(ut) => {
                let mask = ut.mask(ptr_width);
                Ok((a & mask).cmp(&(b & mask)))
            }
            Ty::Int(it) => {
                let sa = it.sign_extend(*a, ptr_width);
                let sb = it.sign_extend(*b, ptr_width);
                Ok(sa.cmp(&sb))
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "MirValue::Int must carry Int or Uint type",
            )),
        },
        (
            MirValue::Ptr {
                ptr: pa,
                ty: lhs_ty,
            },
            MirValue::Ptr {
                ptr: pb,
                ty: rhs_ty,
            },
        ) if allow_pointers && lhs_ty == rhs_ty && lhs_ty.is_any_ptr() => {
            let mask = ptr_width.mask();
            let aa = (pa.addr as u128) & mask;
            let ab = (pb.addr as u128) & mask;
            if lhs_ty.is_ref() && (aa == 0 || ab == 0) {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: lhs_ty.clone(),
                    bits: 0,
                }));
            }
            Ok(aa.cmp(&ab))
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "comparison operands must have matching scalar types",
        )),
    }
}

/// Evaluates a checked binary operation (`Rvalue::CheckedBinaryOp` or `*WithOverflow`),
/// returning `(wrapped_bits, overflowed)`.
pub fn eval_checked_binop(
    op: BinOp,
    lhs: &MirValue,
    rhs: &MirValue,
    ptr_width: PtrWidth,
) -> Result<(u128, bool), RvalueEvalError> {
    let MirValue::Int {
        bits: lhs_bits,
        ty: lhs_ty,
    } = lhs
    else {
        return Err(RvalueEvalError::TypeMismatch(
            "checked binary op LHS must be MirValue::Int",
        ));
    };
    let MirValue::Int {
        bits: rhs_bits,
        ty: rhs_ty,
    } = rhs
    else {
        return Err(RvalueEvalError::TypeMismatch(
            "checked binary op RHS must be MirValue::Int",
        ));
    };

    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::AddWithOverflow
        | BinOp::SubWithOverflow
        | BinOp::MulWithOverflow => {
            if lhs_ty != rhs_ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "checked arithmetic LHS and RHS types must match",
                ));
            }
            compute_int_arith_with_overflow(op, *lhs_bits, *rhs_bits, lhs_ty, ptr_width)
        }
        BinOp::Shl | BinOp::Shr => {
            let (shifted, overflowed, _, _) = compute_shift_with_overflow(
                op, *lhs_bits, lhs_ty, *rhs_bits, rhs_ty, ptr_width,
            )?;
            Ok((shifted, overflowed))
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "unsupported BinOp for CheckedBinaryOp",
        )),
    }
}

/// Evaluates a MIR `BinOp` on two runtime `MirValue` operands under `ptr_width`.
pub fn eval_binop(
    op: BinOp,
    lhs: &MirValue,
    rhs: &MirValue,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul => {
            let (MirValue::Int { bits: a, ty: lt }, MirValue::Int { bits: b, ty: rt }) = (lhs, rhs)
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "arithmetic operands must be MirValue::Int",
                ));
            };
            if lt != rt {
                return Err(RvalueEvalError::TypeMismatch(
                    "arithmetic LHS and RHS types must match",
                ));
            }
            let (wrapped, _) = compute_int_arith_with_overflow(op, *a, *b, lt, ptr_width)?;
            Ok(MirValue::Int {
                bits: wrapped,
                ty: lt.clone(),
            })
        }
        BinOp::AddUnchecked | BinOp::SubUnchecked | BinOp::MulUnchecked => {
            let (MirValue::Int { bits: a, ty: lt }, MirValue::Int { bits: b, ty: rt }) = (lhs, rhs)
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "unchecked arithmetic operands must be MirValue::Int",
                ));
            };
            if lt != rt {
                return Err(RvalueEvalError::TypeMismatch(
                    "unchecked arithmetic LHS and RHS types must match",
                ));
            }
            let (wrapped, overflowed) = compute_int_arith_with_overflow(op, *a, *b, lt, ptr_width)?;
            if overflowed {
                return Err(RvalueEvalError::ArithmeticOverflow { op });
            }
            Ok(MirValue::Int {
                bits: wrapped,
                ty: lt.clone(),
            })
        }
        BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow => {
            let (MirValue::Int { bits: a, ty: lt }, MirValue::Int { bits: b, ty: rt }) = (lhs, rhs)
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "checked arithmetic operands must be MirValue::Int",
                ));
            };
            if lt != rt {
                return Err(RvalueEvalError::TypeMismatch(
                    "checked arithmetic LHS and RHS types must match",
                ));
            }
            let (wrapped, overflowed) = compute_int_arith_with_overflow(op, *a, *b, lt, ptr_width)?;
            Ok(MirValue::Tuple(vec![
                MirValue::Int {
                    bits: wrapped,
                    ty: lt.clone(),
                },
                MirValue::Bool(overflowed),
            ]))
        }
        BinOp::Div | BinOp::Rem => {
            let (MirValue::Int { bits: a, ty: lt }, MirValue::Int { bits: b, ty: rt }) = (lhs, rhs)
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Div/Rem operands must be MirValue::Int",
                ));
            };
            if lt != rt {
                return Err(RvalueEvalError::TypeMismatch(
                    "Div/Rem LHS and RHS types must match",
                ));
            }
            match lt {
                Ty::Uint(ut) => {
                    let mask = ut.mask(ptr_width);
                    let ua = *a & mask;
                    let ub = *b & mask;
                    if ub == 0 {
                        return Err(RvalueEvalError::DivisionByZero);
                    }
                    let res = if op == BinOp::Div { ua / ub } else { ua % ub };
                    Ok(MirValue::Int {
                        bits: res & mask,
                        ty: lt.clone(),
                    })
                }
                Ty::Int(it) => {
                    let mask = it.mask(ptr_width);
                    let sa = it.sign_extend(*a, ptr_width);
                    let sb = it.sign_extend(*b, ptr_width);
                    if sb == 0 {
                        return Err(RvalueEvalError::DivisionByZero);
                    }
                    let min_val = it.min_value(ptr_width);
                    if sa == min_val && sb == -1 {
                        return Err(RvalueEvalError::SignedDivisionOverflow {
                            min_val,
                            bit_width: it.bit_width_for(ptr_width),
                        });
                    }
                    let res = if op == BinOp::Div { sa / sb } else { sa % sb };
                    Ok(MirValue::Int {
                        bits: (res as u128) & mask,
                        ty: lt.clone(),
                    })
                }
                _ => Err(RvalueEvalError::TypeMismatch(
                    "Div/Rem requires Int or Uint type",
                )),
            }
        }
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => match (lhs, rhs) {
            (MirValue::Bool(a), MirValue::Bool(b)) => {
                let res = match op {
                    BinOp::BitAnd => *a & *b,
                    BinOp::BitOr => *a | *b,
                    BinOp::BitXor => *a ^ *b,
                    _ => unreachable!(),
                };
                Ok(MirValue::Bool(res))
            }
            (MirValue::Int { bits: a, ty: lt }, MirValue::Int { bits: b, ty: rt })
                if lt == rt && lt.is_integral() =>
            {
                let mask = lt.scalar_mask(ptr_width);
                let res = match op {
                    BinOp::BitAnd => (*a & *b) & mask,
                    BinOp::BitOr => (*a | *b) & mask,
                    BinOp::BitXor => (*a ^ *b) & mask,
                    _ => unreachable!(),
                };
                Ok(MirValue::Int {
                    bits: res,
                    ty: lt.clone(),
                })
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "bitwise op requires matching Bool or integral operands",
            )),
        },
        BinOp::Shl | BinOp::Shr => {
            let (MirValue::Int { bits: a, ty: lt }, MirValue::Int { bits: b, ty: rt }) = (lhs, rhs)
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "shift operands must be MirValue::Int",
                ));
            };
            let (shifted, _, _, _) = compute_shift_with_overflow(op, *a, lt, *b, rt, ptr_width)?;
            Ok(MirValue::Int {
                bits: shifted,
                ty: lt.clone(),
            })
        }
        BinOp::ShlUnchecked | BinOp::ShrUnchecked => {
            let (MirValue::Int { bits: a, ty: lt }, MirValue::Int { bits: b, ty: rt }) = (lhs, rhs)
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "unchecked shift operands must be MirValue::Int",
                ));
            };
            let (shifted, overflowed, rhs_signed, lhs_bit_width) =
                compute_shift_with_overflow(op, *a, lt, *b, rt, ptr_width)?;
            if overflowed {
                return Err(RvalueEvalError::ShiftOverflow {
                    shift_bits: *b & rt.scalar_mask(ptr_width),
                    rhs_signed,
                    lhs_bit_width,
                });
            }
            Ok(MirValue::Int {
                bits: shifted,
                ty: lt.clone(),
            })
        }
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let ord = compare_mir_values(lhs, rhs, ptr_width, true)?;
            let res = match op {
                BinOp::Eq => ord == Ordering::Equal,
                BinOp::Ne => ord != Ordering::Equal,
                BinOp::Lt => ord == Ordering::Less,
                BinOp::Le => ord != Ordering::Greater,
                BinOp::Gt => ord == Ordering::Greater,
                BinOp::Ge => ord != Ordering::Less,
                _ => unreachable!(),
            };
            Ok(MirValue::Bool(res))
        }
        BinOp::Cmp => {
            let ord = compare_mir_values(lhs, rhs, ptr_width, false)?;
            let code: i128 = match ord {
                Ordering::Less => -1,
                Ordering::Equal => 0,
                Ordering::Greater => 1,
            };
            Ok(MirValue::signed(code, IntTy::I8, ptr_width))
        }
        BinOp::Offset => {
            let MirValue::Ptr { ptr, ty: ptr_ty } = lhs else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Offset LHS must be MirValue::Ptr",
                ));
            };
            let Some(pointee) = ptr_ty.pointee_ty() else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Offset LHS type must be RawPtr or Ref",
                ));
            };
            let MirValue::Int {
                bits: count_bits,
                ty: rhs_ty,
            } = rhs
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Offset RHS must be MirValue::Int",
                ));
            };
            // The stride is the pointee's layout size (well-defined even when uninhabited).
            let Some(pointee_size) = pointee.layout_size_for(ptr_width) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Offset pointee layout is too large for the target",
                ));
            };
            let base_addr = u128::from(ptr.addr) & ptr_width.mask();
            if ptr_ty.is_ref() && base_addr == 0 {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: ptr_ty.clone(),
                    bits: 0,
                }));
            }
            let overflow = |offset: i128| RvalueEvalError::PointerOffsetOverflow {
                base_addr: ptr.addr,
                offset,
                pointee_size,
            };

            // `ptr::offset` (signed count) / `ptr::add` (unsigned count): the byte offset
            // `count * size_of::<T>()`, computed on mathematical integers, must fit in `isize`.
            let (count, byte_delta) = match rhs_ty {
                Ty::Int(it) => {
                    let count = it.sign_extend(*count_bits, ptr_width);
                    let delta = count
                        .checked_mul(pointee_size as i128)
                        .ok_or_else(|| overflow(count))?;
                    (count, delta)
                }
                Ty::Uint(ut) => {
                    let count_unsigned = *count_bits & ut.mask(ptr_width);
                    let count = i128::try_from(count_unsigned).unwrap_or(i128::MAX);
                    let delta = count_unsigned
                        .checked_mul(pointee_size as u128)
                        .filter(|delta| *delta <= ptr_width.max_object_size())
                        .ok_or_else(|| overflow(count))?;
                    (count, delta as i128)
                }
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Offset RHS must have Int or Uint type",
                    ));
                }
            };
            if byte_delta < ptr_width.min_isize() || byte_delta > ptr_width.max_isize() {
                return Err(overflow(count));
            }
            // The resulting address must not wrap around the target address space.
            let new_addr = base_addr as i128 + byte_delta;
            if new_addr < 0 || (new_addr as u128) > ptr_width.mask() {
                return Err(overflow(count));
            }
            if ptr_ty.is_ref() && new_addr == 0 {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: ptr_ty.clone(),
                    bits: 0,
                }));
            }
            // A non-zero offset requires a pointer derived from an allocation, i.e. one that
            // carries provenance (offsetting by 0 bytes is always allowed).
            if byte_delta != 0 && ptr.provenance.is_none() {
                return Err(RvalueEvalError::PointerArithmeticWithoutProvenance {
                    addr: ptr.addr,
                    byte_offset: byte_delta,
                });
            }

            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: new_addr as u64,
                    provenance: ptr.provenance,
                },
                ty: ptr_ty.clone(),
            })
        }
    }
}

/// Evaluates a MIR `UnOp` on a runtime `MirValue` operand under `ptr_width`.
pub fn eval_unop(
    op: UnOp,
    val: &MirValue,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    match op {
        UnOp::Not => match val {
            MirValue::Bool(b) => Ok(MirValue::Bool(!b)),
            MirValue::Int { bits, ty } if ty.is_integral() => {
                let mask = ty.scalar_mask(ptr_width);
                Ok(MirValue::Int {
                    bits: (!*bits) & mask,
                    ty: ty.clone(),
                })
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "UnOp::Not requires Bool or integral operand",
            )),
        },
        UnOp::Neg => match val {
            MirValue::Int {
                bits,
                ty: Ty::Int(it),
            } => {
                let signed = it.sign_extend(*bits, ptr_width);
                let negated = signed.wrapping_neg();
                Ok(MirValue::Int {
                    bits: it.truncate_signed(negated, ptr_width),
                    ty: Ty::Int(*it),
                })
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "UnOp::Neg requires signed IntTy operand",
            )),
        },
        UnOp::PtrMetadata => match val {
            MirValue::Ptr { ptr, ty } if ty.is_any_ptr() => {
                if ty.is_ref() && (u128::from(ptr.addr) & ptr_width.mask()) == 0 {
                    return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                        target_ty: ty.clone(),
                        bits: 0,
                    }));
                }
                Ok(MirValue::Unit)
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "UnOp::PtrMetadata requires pointer or reference operand",
            )),
        },
    }
}

/// Evaluates an `AggregateKind` construction from evaluated `operands` under `ptr_width`.
pub fn eval_aggregate(
    kind: &AggregateKind,
    operands: Vec<MirValue>,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    match kind {
        AggregateKind::Array(elem_ty) => {
            for op in &operands {
                if op.ty() != *elem_ty {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array aggregate element type mismatch",
                    ));
                }
            }
            Ok(MirValue::Array {
                elements: operands,
                elem_ty: elem_ty.clone(),
            })
        }
        AggregateKind::Tuple | AggregateKind::Closure => Ok(MirValue::Tuple(operands)),
        AggregateKind::Adt {
            def_path,
            variant_idx,
            active_field,
        } => {
            if active_field.is_some() {
                if operands.len() != 1 {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union Adt aggregate with active_field requires exactly 1 operand",
                    ));
                }
                if *variant_idx != 0 {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union Adt aggregate with active_field must use variant 0",
                    ));
                }
            }
            Ok(MirValue::Adt {
                def_path: def_path.clone(),
                variant_idx: *variant_idx,
                active_field: *active_field,
                fields: operands,
            })
        }
        AggregateKind::RawPtr {
            pointee,
            mutability,
        } => {
            if operands.len() != 2 {
                return Err(RvalueEvalError::TypeMismatch(
                    "RawPtr aggregate requires 2 operands (data_ptr_or_addr, unit_metadata)",
                ));
            }
            if !operands[1].is_unit() {
                return Err(RvalueEvalError::TypeMismatch(
                    "thin RawPtr aggregate second operand must be unit metadata",
                ));
            }
            let ptr = match &operands[0] {
                MirValue::Ptr {
                    ptr,
                    ty: Ty::RawPtr(_, data_mutability),
                } if data_mutability == mutability => PointerValue {
                    addr: (u128::from(ptr.addr) & ptr_width.mask()) as u64,
                    provenance: ptr.provenance,
                },
                MirValue::Int {
                    bits,
                    ty: Ty::Uint(UintTy::Usize),
                } => PointerValue {
                    addr: (*bits & ptr_width.mask()) as u64,
                    provenance: None,
                },
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "RawPtr aggregate data operand must be a raw pointer of matching mutability or a usize address",
                    ));
                }
            };
            Ok(MirValue::Ptr {
                ptr,
                ty: Ty::RawPtr(Box::new(pointee.clone()), *mutability),
            })
        }
    }
}

/// Encodes `val` as the canonical byte image of type `ty` (see
/// [`Ty::has_canonical_byte_layout`]), validating that the value's shape and scalar types
/// match `ty`. Pointer bytes carry provenance fragments (MiniRust `encode_ptr`).
fn encode_mir_value(
    val: &MirValue,
    ty: &Ty,
    ptr_width: PtrWidth,
    out: &mut Vec<AbstractByte>,
) -> Result<(), RvalueEvalError> {
    match (ty, val) {
        (Ty::Bool, MirValue::Bool(b)) => out.push(AbstractByte::new(u8::from(*b))),
        (Ty::Char, MirValue::Char(c)) => out.extend(encode_int_bytes(u128::from(u32::from(*c)), 4)),
        (Ty::Int(_) | Ty::Uint(_), MirValue::Int { bits, ty: val_ty }) if val_ty == ty => {
            if !ty.is_valid_scalar_bits(*bits, ptr_width) {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: ty.clone(),
                    bits: *bits,
                }));
            }
            out.extend(encode_int_bytes(*bits, ty.byte_size_for(ptr_width)));
        }
        (Ty::RawPtr(_, _) | Ty::Ref(_, _), MirValue::Ptr { ptr, ty: val_ty }) if val_ty == ty => {
            let addr_bits = u128::from(ptr.addr) & ptr_width.mask();
            if !ty.is_valid_scalar_bits(addr_bits, ptr_width) {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: ty.clone(),
                    bits: addr_bits,
                }));
            }
            out.extend(encode_ptr_bytes(*ptr, ptr_width));
        }
        (
            Ty::Array(elem, count),
            MirValue::Array {
                elements,
                elem_ty,
            },
        ) if **elem == *elem_ty && elements.len() == *count => {
            for element in elements {
                encode_mir_value(element, elem, ptr_width, out)?;
            }
        }
        (Ty::Tuple(fields), MirValue::Unit) if fields.is_empty() => {}
        (Ty::Tuple(fields), MirValue::Tuple(values)) if values.len() == fields.len() => {
            for (value, field) in values.iter().zip(fields) {
                encode_mir_value(value, field, ptr_width, out)?;
            }
        }
        _ => {
            return Err(RvalueEvalError::TypeMismatch(
                "transmute operand value does not match its source type (ADT values have no modeled byte layout)",
            ));
        }
    }
    Ok(())
}

/// Validates `val` against `ty` for an identity transmute: like `encode_mir_value` (shape,
/// scalar types, and leaf validity such as non-null `&T`), but also accepts struct/enum
/// `MirValue::Adt` values, which Anneal types as the tuple of their fields.
fn encode_or_validate_identity(
    val: &MirValue,
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<(), RvalueEvalError> {
    match (ty, val) {
        (
            Ty::Tuple(fields),
            MirValue::Adt {
                active_field: None,
                fields: values,
                ..
            },
        )
        | (Ty::Tuple(fields), MirValue::Tuple(values))
            if values.len() == fields.len() =>
        {
            values
                .iter()
                .zip(fields)
                .try_for_each(|(value, field)| encode_or_validate_identity(value, field, ptr_width))
        }
        (
            Ty::Array(elem, count),
            MirValue::Array {
                elements,
                elem_ty,
            },
        ) if **elem == *elem_ty && elements.len() == *count => elements
            .iter()
            .try_for_each(|element| encode_or_validate_identity(element, elem, ptr_width)),
        _ => encode_mir_value(val, ty, ptr_width, &mut Vec::new()),
    }
}

/// Decodes the canonical byte image `bytes` (exactly `ty`'s size, already validated by
/// `eval_transmute`) into a structured `MirValue` of type `ty`.
fn decode_mir_value(
    bytes: &[AbstractByte],
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    let invalid = |bits: u128| {
        RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ty.clone(),
            bits,
        })
    };
    match ty {
        Ty::Bool => match decode_int_bytes(bytes) {
            0 => Ok(MirValue::Bool(false)),
            1 => Ok(MirValue::Bool(true)),
            bits => Err(invalid(bits)),
        },
        Ty::Char => {
            let bits = decode_int_bytes(bytes);
            u32::try_from(bits)
                .ok()
                .and_then(char::from_u32)
                .map(MirValue::Char)
                .ok_or_else(|| invalid(bits))
        }
        Ty::Int(_) | Ty::Uint(_) => Ok(MirValue::Int {
            bits: decode_int_bytes(bytes),
            ty: ty.clone(),
        }),
        Ty::RawPtr(_, _) | Ty::Ref(_, _) => {
            let ptr = decode_ptr_bytes(bytes);
            if !ty.is_valid_scalar_bits(u128::from(ptr.addr), ptr_width) {
                return Err(invalid(u128::from(ptr.addr)));
            }
            Ok(MirValue::Ptr {
                ptr,
                ty: ty.clone(),
            })
        }
        Ty::Array(elem, count) => {
            if *count > MAX_EVAL_ARRAY_LEN {
                return Err(RvalueEvalError::EvaluationLimit { len: *count });
            }
            let elem_size = elem.byte_size_for(ptr_width);
            let elements = (0..*count)
                .map(|i| decode_mir_value(&bytes[i * elem_size..(i + 1) * elem_size], elem, ptr_width))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(MirValue::Array {
                elements,
                elem_ty: (**elem).clone(),
            })
        }
        Ty::Tuple(fields) if fields.is_empty() => Ok(MirValue::Unit),
        Ty::Tuple(fields) => {
            let mut offset = 0usize;
            let mut values = Vec::with_capacity(fields.len());
            for field in fields {
                let size = field.byte_size_for(ptr_width);
                values.push(decode_mir_value(&bytes[offset..offset + size], field, ptr_width)?);
                offset += size;
            }
            Ok(MirValue::Tuple(values))
        }
        Ty::Never => Err(RvalueEvalError::CastEval(CastEvalError::UninhabitedTarget {
            target_ty: Ty::Never,
        })),
    }
}

/// Evaluates a `LoweredCast` on an evaluated `MirValue` operand under `ptr_width` and `policy`.
pub fn eval_lowered_cast(
    cast: &LoweredCast,
    val: &MirValue,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<MirValue, RvalueEvalError> {
    match cast {
        LoweredCast::PtrToInt {
            src_ty, target_ty, ..
        } => {
            let MirValue::Ptr { ptr, ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "PtrToInt requires pointer value",
                ));
            };
            // `lower_ptr_to_int` accepts raw pointers *and* references as sources.
            if ty != src_ty || !src_ty.is_any_ptr() {
                return Err(RvalueEvalError::TypeMismatch(
                    "PtrToInt operand type must match pointer or reference source type",
                ));
            }
            if src_ty.is_ref() && (u128::from(ptr.addr) & ptr_width.mask()) == 0 {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: src_ty.clone(),
                    bits: 0,
                }));
            }
            let bits = eval_ptr_to_int_with_ptr_width(*ptr, target_ty, ptr_width, tracker)?;
            Ok(MirValue::Int {
                bits,
                ty: target_ty.clone(),
            })
        }
        LoweredCast::IntToPtr {
            src_ty,
            target_ty,
            pick_exposed_provenance,
            ..
        } => {
            let MirValue::Int { bits: addr, ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "IntToPtr requires integer value",
                ));
            };
            if ty != src_ty || !ty.is_integral() {
                return Err(RvalueEvalError::TypeMismatch(
                    "IntToPtr operand type must match integral source type",
                ));
            }
            let addr_bits = match ty {
                Ty::Int(it) => (it.sign_extend(*addr, ptr_width) as u128) & ptr_width.mask(),
                Ty::Uint(ut) => (*addr & ut.mask(ptr_width)) & ptr_width.mask(),
                _ => unreachable!(),
            };
            // MiniRust `int2ptr` angelically predicts either no provenance or a previously
            // exposed one. Anneal's evaluator has no allocation bounds, so every exposed
            // provenance satisfies every later provenance-dependent check (e.g. non-zero
            // `Offset`) equally well; we deterministically predict the least exposed
            // provenance, and `None` only when nothing has been exposed (or picking is
            // disabled). Predicting `None` despite exposed provenance would make valid
            // `ptr::with_exposed_provenance(addr).add(n)` programs report UB.
            let predicted = if *pick_exposed_provenance {
                tracker.exposed.first().copied()
            } else {
                None
            };
            let ptr = eval_int_to_ptr_with_ptr_width(
                addr_bits, target_ty, ptr_width, tracker, predicted,
            )?;
            Ok(MirValue::Ptr {
                ptr,
                ty: target_ty.clone(),
            })
        }
        LoweredCast::IntToInt {
            src_ty, target_ty, ..
        } => {
            if val.ty() != *src_ty || src_ty.is_any_ptr() {
                return Err(RvalueEvalError::TypeMismatch(
                    "IntToInt operand type must match non-pointer scalar source type",
                ));
            }
            let Some(src_bits) = val.as_bits() else {
                return Err(RvalueEvalError::TypeMismatch(
                    "IntToInt requires scalar value",
                ));
            };
            let bits = eval_int_to_int(src_bits, src_ty, target_ty, ptr_width)?;
            if *target_ty == Ty::Char {
                let c = char::from_u32(bits as u32).ok_or(CastEvalError::InvalidBitPattern {
                    target_ty: Ty::Char,
                    bits,
                })?;
                Ok(MirValue::Char(c))
            } else {
                Ok(MirValue::Int {
                    bits,
                    ty: target_ty.clone(),
                })
            }
        }
        LoweredCast::PtrToPtr {
            src_ty, target_ty, ..
        } => {
            let MirValue::Ptr { ptr, ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "PtrToPtr requires pointer value",
                ));
            };
            if ty != src_ty || !src_ty.is_raw_ptr() || !target_ty.is_raw_ptr() {
                return Err(RvalueEvalError::TypeMismatch(
                    "PtrToPtr requires raw pointer source and target types matching operand",
                ));
            }
            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: (ptr.addr as u128 & ptr_width.mask()) as u64,
                    provenance: ptr.provenance,
                },
                ty: target_ty.clone(),
            })
        }
        LoweredCast::Transmute {
            src_ty, target_ty, ..
        } => {
            if src_ty == target_ty && !src_ty.has_canonical_byte_layout(ptr_width) {
                // Identity transmute through a layout without a canonical byte image (e.g. a
                // padded tuple): `T.decode(T.encode(v)) == v` for every valid `v`, so validate
                // the operand against `T` and return it unchanged.
                if !src_ty.is_inhabited() {
                    return Err(RvalueEvalError::CastEval(CastEvalError::UninhabitedTarget {
                        target_ty: target_ty.clone(),
                    }));
                }
                if src_ty.layout_size_for(ptr_width).is_none() {
                    return Err(RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge {
                        ty: src_ty.clone(),
                    }));
                }
                encode_or_validate_identity(val, src_ty, ptr_width)?;
                return Ok(val.clone());
            }
            let tv_in = match val {
                MirValue::Ptr { ptr, ty } if ty == src_ty => TransmuteValue::Ptr(*ptr),
                MirValue::Int { bits, ty } if ty == src_ty => TransmuteValue::Scalar(*bits),
                MirValue::Bool(b) if *src_ty == Ty::Bool => TransmuteValue::Scalar(u128::from(*b)),
                MirValue::Char(c) if *src_ty == Ty::Char => {
                    TransmuteValue::Scalar(u128::from(u32::from(*c)))
                }
                MirValue::Ptr { .. } | MirValue::Int { .. } | MirValue::Bool(_) | MirValue::Char(_) => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "transmute operand value does not match its source type",
                    ));
                }
                MirValue::Unit | MirValue::Array { .. } | MirValue::Tuple(_) | MirValue::Adt { .. } => {
                    let mut bytes = Vec::with_capacity(src_ty.byte_size_for(ptr_width));
                    encode_mir_value(val, src_ty, ptr_width, &mut bytes)?;
                    TransmuteValue::AbstractBytes(bytes)
                }
            };
            let tv_out = eval_transmute(tv_in, src_ty, target_ty, ptr_width, policy, tracker)?;
            match tv_out {
                TransmuteValue::Ptr(ptr) => Ok(MirValue::Ptr {
                    ptr,
                    ty: target_ty.clone(),
                }),
                TransmuteValue::Scalar(bits) => {
                    let size = target_ty.byte_size_for(ptr_width);
                    let bytes: Vec<AbstractByte> = encode_int_bytes(bits, size).collect();
                    decode_mir_value(&bytes, target_ty, ptr_width)
                }
                TransmuteValue::Bytes(raw) => {
                    let bytes: Vec<AbstractByte> = raw.into_iter().map(AbstractByte::new).collect();
                    decode_mir_value(&bytes, target_ty, ptr_width)
                }
                TransmuteValue::AbstractBytes(bytes) => decode_mir_value(&bytes, target_ty, ptr_width),
            }
        }
    }
}

/// Evaluates a `LoweredRvalue` given a slice mapping `Local`s to `MirValue`s.
///
/// There is no memory model: operands, `Discriminant`, and `CopyForDeref` may only read bare
/// locals; `Ref`/`RawPtr` of a bare local yield a synthetic per-local address with a fresh
/// provenance, and `Ref`/`RawPtr` of `(*p)` reborrow `p`'s address and provenance. Any other
/// projection returns `RvalueEvalError::UnsupportedPlaceProjection`.
pub fn eval_lowered_rvalue(
    rvalue: &LoweredRvalue,
    locals: &[MirValue],
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<MirValue, RvalueEvalError> {
    let read_local = |local: Local| -> Result<MirValue, RvalueEvalError> {
        locals
            .get(local.0)
            .cloned()
            .ok_or(RvalueEvalError::TypeMismatch("local index out of bounds"))
    };
    let read_place = |place: &Place| -> Result<MirValue, RvalueEvalError> {
        if !place.projection.is_empty() {
            return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
        }
        read_local(place.local)
    };
    let eval_op = |op: &Operand| -> Result<MirValue, RvalueEvalError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => read_place(place),
            Operand::Constant(c) => eval_constant(c, ptr_width),
        }
    };

    match rvalue {
        LoweredRvalue::Use { operand, .. } => eval_op(operand),
        LoweredRvalue::Repeat {
            operand,
            count,
            elem_ty,
            ..
        } => {
            if *count > MAX_EVAL_ARRAY_LEN {
                return Err(RvalueEvalError::EvaluationLimit { len: *count });
            }
            let v = eval_op(operand)?;
            Ok(MirValue::Array {
                elements: vec![v; *count],
                elem_ty: elem_ty.clone(),
            })
        }
        LoweredRvalue::Ref {
            place, ty: ref_ty, ..
        }
        | LoweredRvalue::RawPtr {
            place, ty: ref_ty, ..
        } => {
            let ptr = match place.projection.as_slice() {
                [] => {
                    // Synthetic, page-aligned per-local allocation with a fresh provenance.
                    let addr = ((place.local.0 as u128 + 1) * 0x1000) & ptr_width.mask();
                    PointerValue::with_provenance(addr as u64, place.local.0 as u64 + 1, 1)
                }
                [ProjectionElem::Deref] => match read_local(place.local)? {
                    // `&(*p)` / `&raw const (*p)`: reborrow keeps p's address and provenance.
                    MirValue::Ptr { ptr, ty } => {
                        if !ty.is_any_ptr() || ty.pointee_ty() != ref_ty.pointee_ty() {
                            return Err(RvalueEvalError::TypeMismatch(
                                "Deref projection requires a pointer value with matching pointee type",
                            ));
                        }
                        let masked_addr = (u128::from(ptr.addr) & ptr_width.mask()) as u64;
                        if ty.is_ref() && masked_addr == 0 {
                            return Err(RvalueEvalError::CastEval(
                                CastEvalError::InvalidBitPattern {
                                    target_ty: ty,
                                    bits: 0,
                                },
                            ));
                        }
                        PointerValue {
                            addr: masked_addr,
                            provenance: ptr.provenance,
                        }
                    }
                    _ => {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Deref projection requires a pointer value",
                        ));
                    }
                },
                _ => return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone())),
            };
            if ref_ty.is_ref() && ptr.addr == 0 {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: ref_ty.clone(),
                    bits: 0,
                }));
            }
            Ok(MirValue::Ptr {
                ptr,
                ty: ref_ty.clone(),
            })
        }
        LoweredRvalue::Len { static_len, .. } => {
            Ok(MirValue::unsigned(*static_len as u128, UintTy::Usize, ptr_width))
        }
        LoweredRvalue::Cast { cast, .. } => {
            let op = match cast {
                LoweredCast::PtrToInt { operand, .. }
                | LoweredCast::IntToPtr { operand, .. }
                | LoweredCast::IntToInt { operand, .. }
                | LoweredCast::PtrToPtr { operand, .. }
                | LoweredCast::Transmute { operand, .. } => operand,
            };
            let v = eval_op(op)?;
            eval_lowered_cast(cast, &v, ptr_width, policy, tracker)
        }
        LoweredRvalue::BinaryOp { op, lhs, rhs, .. } => {
            let lv = eval_op(lhs)?;
            let rv = eval_op(rhs)?;
            eval_binop(*op, &lv, &rv, ptr_width)
        }
        LoweredRvalue::CheckedBinaryOp {
            op,
            lhs,
            rhs,
            lhs_ty,
            ..
        } => {
            let lv = eval_op(lhs)?;
            let rv = eval_op(rhs)?;
            let (wrapped, overflowed) = eval_checked_binop(*op, &lv, &rv, ptr_width)?;
            Ok(MirValue::Tuple(vec![
                MirValue::Int {
                    bits: wrapped,
                    ty: lhs_ty.clone(),
                },
                MirValue::Bool(overflowed),
            ]))
        }
        LoweredRvalue::UnaryOp { op, operand, .. } => {
            let v = eval_op(operand)?;
            eval_unop(*op, &v, ptr_width)
        }
        LoweredRvalue::Discriminant { place, .. } => {
            let discr = match read_place(place)? {
                MirValue::Adt { variant_idx, .. } => variant_idx as i128,
                _ => 0,
            };
            Ok(MirValue::signed(discr, IntTy::Isize, ptr_width))
        }
        LoweredRvalue::Aggregate { kind, operands, .. } => {
            let mut vals = Vec::with_capacity(operands.len());
            for op in operands {
                vals.push(eval_op(op)?);
            }
            eval_aggregate(kind, vals, ptr_width)
        }
        LoweredRvalue::CopyForDeref { place, .. } => read_place(place),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wrapping_checked_unchecked_arithmetic_boundaries() {
        // Unsigned u128::MAX + 1
        let max_u128 = MirValue::unsigned(u128::MAX, UintTy::U128, PtrWidth::Bits64);
        let one_u128 = MirValue::unsigned(1, UintTy::U128, PtrWidth::Bits64);

        let wrapped = eval_binop(BinOp::Add, &max_u128, &one_u128, PtrWidth::Bits64).unwrap();
        assert_eq!(wrapped.as_bits(), Some(0));

        let checked = eval_checked_binop(BinOp::Add, &max_u128, &one_u128, PtrWidth::Bits64).unwrap();
        assert_eq!(checked, (0, true));

        let unchecked_err =
            eval_binop(BinOp::AddUnchecked, &max_u128, &one_u128, PtrWidth::Bits64)
                .expect_err("u128::MAX + 1 unchecked must overflow");
        assert_eq!(
            unchecked_err,
            RvalueEvalError::ArithmeticOverflow {
                op: BinOp::AddUnchecked
            }
        );

        // Signed i128::MIN - 1 and i128::MIN * -1
        let min_i128 = MirValue::signed(i128::MIN, IntTy::I128, PtrWidth::Bits64);
        let one_i128 = MirValue::signed(1, IntTy::I128, PtrWidth::Bits64);
        let neg_one_i128 = MirValue::signed(-1, IntTy::I128, PtrWidth::Bits64);

        let (sub_bits, sub_ov) =
            eval_checked_binop(BinOp::Sub, &min_i128, &one_i128, PtrWidth::Bits64).unwrap();
        assert!(sub_ov);
        assert_eq!(sub_bits, i128::MAX as u128);

        let (mul_bits, mul_ov) =
            eval_checked_binop(BinOp::Mul, &min_i128, &neg_one_i128, PtrWidth::Bits64).unwrap();
        assert!(mul_ov);
        assert_eq!(mul_bits, i128::MIN as u128);

        // 32-bit isize::MIN - 1
        let min_isize32 = MirValue::signed(i32::MIN as i128, IntTy::Isize, PtrWidth::Bits32);
        let one_isize32 = MirValue::signed(1, IntTy::Isize, PtrWidth::Bits32);
        let (isize_bits, isize_ov) =
            eval_checked_binop(BinOp::Sub, &min_isize32, &one_isize32, PtrWidth::Bits32).unwrap();
        assert!(isize_ov);
        assert_eq!(isize_bits, i32::MAX as u128);
    }

    #[test]
    fn test_div_rem_by_zero_and_signed_min_overflow() {
        let min_i8 = MirValue::signed(i8::MIN as i128, IntTy::I8, PtrWidth::Bits64);
        let neg_one_i8 = MirValue::signed(-1, IntTy::I8, PtrWidth::Bits64);
        let zero_i8 = MirValue::signed(0, IntTy::I8, PtrWidth::Bits64);

        assert_eq!(
            eval_binop(BinOp::Div, &min_i8, &zero_i8, PtrWidth::Bits64),
            Err(RvalueEvalError::DivisionByZero)
        );
        assert_eq!(
            eval_binop(BinOp::Rem, &min_i8, &zero_i8, PtrWidth::Bits64),
            Err(RvalueEvalError::DivisionByZero)
        );
        assert_eq!(
            eval_binop(BinOp::Div, &min_i8, &neg_one_i8, PtrWidth::Bits64),
            Err(RvalueEvalError::SignedDivisionOverflow {
                min_val: -128,
                bit_width: 8
            })
        );
        assert_eq!(
            eval_binop(BinOp::Rem, &min_i8, &neg_one_i8, PtrWidth::Bits64),
            Err(RvalueEvalError::SignedDivisionOverflow {
                min_val: -128,
                bit_width: 8
            })
        );

        // Truncation toward zero & dividend sign on remainder: -7i8 / 2 == -3i8, -7i8 % 2 == -1i8
        let neg7 = MirValue::signed(-7, IntTy::I8, PtrWidth::Bits64);
        let pos2 = MirValue::signed(2, IntTy::I8, PtrWidth::Bits64);
        let q = eval_binop(BinOp::Div, &neg7, &pos2, PtrWidth::Bits64).unwrap();
        let r = eval_binop(BinOp::Rem, &neg7, &pos2, PtrWidth::Bits64).unwrap();
        assert_eq!(q.as_signed(PtrWidth::Bits64), Some(-3));
        assert_eq!(r.as_signed(PtrWidth::Bits64), Some(-1));
    }

    #[test]
    fn test_shifts_checked_unchecked_and_arithmetic_shr() {
        let neg_128_i8 = MirValue::signed(-128, IntTy::I8, PtrWidth::Bits64);
        let u8_128 = MirValue::unsigned(128, UintTy::U8, PtrWidth::Bits64);
        let shift_9_u32 = MirValue::unsigned(9, UintTy::U32, PtrWidth::Bits64);
        let shift_neg1_i16 = MirValue::signed(-1, IntTy::I16, PtrWidth::Bits64);

        // Wrapping Shr masks shift count 9 & 7 == 1:
        // arithmetic on i8 (-128 >> 1 == -64), logical on u8 (128 >> 1 == 64)
        let arith_shr = eval_binop(BinOp::Shr, &neg_128_i8, &shift_9_u32, PtrWidth::Bits64).unwrap();
        assert_eq!(arith_shr.as_signed(PtrWidth::Bits64), Some(-64));

        let logic_shr = eval_binop(BinOp::Shr, &u8_128, &shift_9_u32, PtrWidth::Bits64).unwrap();
        assert_eq!(logic_shr.as_bits(), Some(64));

        // ShlUnchecked / ShrUnchecked reject shift >= bit_width and negative signed shift count!
        assert!(matches!(
            eval_binop(BinOp::ShrUnchecked, &neg_128_i8, &shift_9_u32, PtrWidth::Bits64),
            Err(RvalueEvalError::ShiftOverflow { lhs_bit_width: 8, .. })
        ));
        assert!(matches!(
            eval_binop(BinOp::ShlUnchecked, &neg_128_i8, &shift_neg1_i16, PtrWidth::Bits64),
            Err(RvalueEvalError::ShiftOverflow {
                rhs_signed: Some(-1),
                lhs_bit_width: 8,
                ..
            })
        ));
    }

    #[test]
    fn test_unop_neg_rejects_unsigned_and_wraps_int_min() {
        let local_decls = vec![Ty::Uint(UintTy::U32), Ty::Int(IntTy::I8)];
        let neg_u32 = Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::from_local(0)));
        assert!(matches!(
            lower_rvalue(&neg_u32, &local_decls, PtrWidth::Bits64),
            Err(RvalueLowerError::InvalidUnaryOp { op: UnOp::Neg, .. })
        ));

        let neg_i8 = Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::from_local(1)));
        assert!(lower_rvalue(&neg_i8, &local_decls, PtrWidth::Bits64).is_ok());

        let min_i8 = MirValue::signed(i8::MIN as i128, IntTy::I8, PtrWidth::Bits64);
        let negated = eval_unop(UnOp::Neg, &min_i8, PtrWidth::Bits64).unwrap();
        assert_eq!(negated.as_signed(PtrWidth::Bits64), Some(i8::MIN as i128));
    }

    #[test]
    fn test_pointer_offset_negative_isize_and_provenance() {
        let ptr_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U32)), Mutability::Not);
        let ptr_val = MirValue::ptr(PointerValue::with_provenance(0x1000, 42, 7), ptr_ty.clone());
        let neg_two_isize = MirValue::signed(-2, IntTy::Isize, PtrWidth::Bits32);

        let offset_res = eval_binop(BinOp::Offset, &ptr_val, &neg_two_isize, PtrWidth::Bits32)
            .expect("negative isize offset on 32-bit must succeed");
        let out_ptr = offset_res.as_ptr().unwrap();
        assert_eq!(out_ptr.addr, 0x1000 - 2 * 4);
        assert_eq!(out_ptr.provenance, ptr_val.as_ptr().unwrap().provenance);
    }

    #[test]
    fn test_b1_mir_value_byte_codec_roundtrips_nested_canonical_values() {
        let pw = PtrWidth::Bits64;
        let raw = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        // Structural codec over ((u32, u16, u16), [*const u8; 1], [char; 2]). (Canonicality is
        // enforced by `eval_transmute`; this mixed-niche tuple is deliberately not canonical.)
        let ty = Ty::Tuple(vec![
            Ty::Tuple(vec![Ty::Uint(UintTy::U32), Ty::Uint(UintTy::U16), Ty::Uint(UintTy::U16)]),
            Ty::Array(Box::new(raw.clone()), 1),
            Ty::Array(Box::new(Ty::Char), 2),
        ]);
        assert!(!ty.has_canonical_byte_layout(pw));
        let ptr = PointerValue::with_provenance(0xABCD, 1, 2);
        let val = MirValue::Tuple(vec![
            MirValue::Tuple(vec![
                MirValue::unsigned(0x1122_3344, UintTy::U32, pw),
                MirValue::unsigned(0x5566, UintTy::U16, pw),
                MirValue::unsigned(0x7788, UintTy::U16, pw),
            ]),
            MirValue::Array {
                elements: vec![MirValue::ptr(ptr, raw.clone())],
                elem_ty: raw.clone(),
            },
            MirValue::Array {
                elements: vec![MirValue::Char('é'), MirValue::Char('\u{10FFFF}')],
                elem_ty: Ty::Char,
            },
        ]);
        let mut bytes = Vec::new();
        encode_mir_value(&val, &ty, pw, &mut bytes).unwrap();
        assert_eq!(bytes.len(), ty.byte_size_for(pw));
        assert_eq!(bytes.len(), 24);
        assert_eq!(&bytes[..4].iter().map(|b| b.data).collect::<Vec<_>>(), &[0x44, 0x33, 0x22, 0x11]);
        assert!(bytes[8..16].iter().all(|b| b.provenance.is_some()));
        assert_eq!(decode_mir_value(&bytes, &ty, pw), Ok(val));

        // Shape mismatches are rejected rather than silently re-typed.
        let wrong = MirValue::Tuple(vec![MirValue::Unit]);
        assert!(matches!(
            encode_mir_value(&wrong, &ty, pw, &mut Vec::new()),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
        // ADT values have no modeled byte layout.
        let adt = MirValue::Adt {
            def_path: "S".into(),
            variant_idx: 0,
            active_field: None,
            fields: vec![],
        };
        assert!(matches!(
            encode_mir_value(&adt, &Ty::unit(), pw, &mut Vec::new()),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
        // Decoding validates niches: a surrogate is not a char.
        let surrogate: Vec<AbstractByte> = encode_int_bytes(0xD800, 4).collect();
        assert_eq!(
            decode_mir_value(&surrogate, &Ty::Char, pw),
            Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: Ty::Char,
                bits: 0xD800,
            }))
        );
    }
}
