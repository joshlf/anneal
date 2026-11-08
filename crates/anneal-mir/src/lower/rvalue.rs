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
    CastEvalError, CastLowerError, ExposedProvenanceTracker, LoweredCast, TransmutePolicy,
    TransmuteValue, eval_int_to_int, eval_int_to_ptr_with_ptr_width,
    eval_ptr_to_int_with_ptr_width, eval_transmute, lower_cast_rvalue_with_ptr_width,
};

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
pub fn resolve_place_ty(place: &Place, local_decls: &[Ty]) -> Result<Ty, RvalueLowerError> {
    let Some(base_ty) = local_decls.get(place.local.0) else {
        return Err(RvalueLowerError::UnknownLocal(place.local));
    };
    let mut cur_ty = base_ty.clone();
    let mut downcast_active = false;

    for elem in &place.projection {
        match elem {
            ProjectionElem::Deref => {
                downcast_active = false;
                match cur_ty {
                    Ty::RawPtr(inner, _) | Ty::Ref(inner, _) => {
                        cur_ty = *inner;
                    }
                    other => {
                        return Err(RvalueLowerError::InvalidProjection {
                            place: place.clone(),
                            current_ty: other,
                            elem: elem.clone(),
                        });
                    }
                }
            }
            ProjectionElem::Field(idx, field_ty) => match &cur_ty {
                Ty::Tuple(fields) => {
                    if let Some(actual) = fields.get(*idx) {
                        if actual != field_ty && !downcast_active {
                            return Err(RvalueLowerError::InvalidProjection {
                                place: place.clone(),
                                current_ty: cur_ty,
                                elem: elem.clone(),
                            });
                        }
                        downcast_active = false;
                        cur_ty = field_ty.clone();
                    } else if downcast_active {
                        downcast_active = false;
                        cur_ty = field_ty.clone();
                    } else {
                        return Err(RvalueLowerError::InvalidProjection {
                            place: place.clone(),
                            current_ty: cur_ty,
                            elem: elem.clone(),
                        });
                    }
                }
                Ty::Array(elem_ty, len) => {
                    downcast_active = false;
                    if *idx < *len && **elem_ty == *field_ty {
                        cur_ty = field_ty.clone();
                    } else {
                        return Err(RvalueLowerError::InvalidProjection {
                            place: place.clone(),
                            current_ty: cur_ty,
                            elem: elem.clone(),
                        });
                    }
                }
                _ => {
                    return Err(RvalueLowerError::InvalidProjection {
                        place: place.clone(),
                        current_ty: cur_ty,
                        elem: elem.clone(),
                    });
                }
            },
            ProjectionElem::Index(idx_local) => {
                downcast_active = false;
                let Some(idx_ty) = local_decls.get(idx_local.0) else {
                    return Err(RvalueLowerError::UnknownLocal(*idx_local));
                };
                if *idx_ty != Ty::Uint(UintTy::Usize) {
                    return Err(RvalueLowerError::InvalidIndexType(idx_ty.clone()));
                }
                match cur_ty {
                    Ty::Array(elem_ty, _) => {
                        cur_ty = *elem_ty;
                    }
                    other => {
                        return Err(RvalueLowerError::InvalidProjection {
                            place: place.clone(),
                            current_ty: other,
                            elem: elem.clone(),
                        });
                    }
                }
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                downcast_active = false;
                match cur_ty {
                    Ty::Array(elem_ty, len) => {
                        let len_u64 = len as u64;
                        let valid_bounds = len_u64 >= *min_length
                            && if *from_end {
                                *offset >= 1 && *offset <= len_u64
                            } else {
                                *offset < len_u64
                            };
                        if !valid_bounds {
                            return Err(RvalueLowerError::InvalidProjection {
                                place: place.clone(),
                                current_ty: Ty::Array(elem_ty, len),
                                elem: elem.clone(),
                            });
                        }
                        cur_ty = *elem_ty;
                    }
                    other => {
                        return Err(RvalueLowerError::InvalidProjection {
                            place: place.clone(),
                            current_ty: other,
                            elem: elem.clone(),
                        });
                    }
                }
            }
            ProjectionElem::Subslice { from, to, from_end } => {
                downcast_active = false;
                match cur_ty {
                    Ty::Array(elem_ty, len) => {
                        let len_u64 = len as u64;
                        let new_len = if *from_end {
                            match from.checked_add(*to) {
                                Some(total) if total <= len_u64 => (len_u64 - total) as usize,
                                _ => {
                                    return Err(RvalueLowerError::InvalidProjection {
                                        place: place.clone(),
                                        current_ty: Ty::Array(elem_ty, len),
                                        elem: elem.clone(),
                                    });
                                }
                            }
                        } else if *from <= *to && *to <= len_u64 {
                            (*to - *from) as usize
                        } else {
                            return Err(RvalueLowerError::InvalidProjection {
                                place: place.clone(),
                                current_ty: Ty::Array(elem_ty, len),
                                elem: elem.clone(),
                            });
                        };
                        cur_ty = Ty::Array(elem_ty, new_len);
                    }
                    other => {
                        return Err(RvalueLowerError::InvalidProjection {
                            place: place.clone(),
                            current_ty: other,
                            elem: elem.clone(),
                        });
                    }
                }
            }
            ProjectionElem::Downcast(_) => match &cur_ty {
                Ty::Tuple(_) => {
                    downcast_active = true;
                }
                _ => {
                    return Err(RvalueLowerError::InvalidProjection {
                        place: place.clone(),
                        current_ty: cur_ty,
                        elem: elem.clone(),
                    });
                }
            },
        }
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
            if !pointee.is_inhabited() {
                return Err(RvalueLowerError::UninhabitedType(pointee.clone()));
            }
            let stride = pointee.byte_size_for(ptr_width);
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
            let ty = resolve_operand_ty(operand, local_decls)?;
            Ok(LoweredRvalue::Use {
                operand: operand.clone(),
                ty,
            })
        }
        Rvalue::Repeat(operand, count) => {
            let elem_ty = resolve_operand_ty(operand, local_decls)?;
            let ty = Ty::Array(Box::new(elem_ty.clone()), *count);
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
                Ty::Array(_, len) => Ok(LoweredRvalue::Len {
                    place: place.clone(),
                    static_len: len,
                    ty: Ty::Uint(UintTy::Usize),
                }),
                other => Err(RvalueLowerError::InvalidLenTarget(other)),
            }
        }
        Rvalue::Cast(kind, operand, target_ty) => {
            let src_ty = resolve_operand_ty(operand, local_decls)?;
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
            let lhs_ty = resolve_operand_ty(lhs, local_decls)?;
            let rhs_ty = resolve_operand_ty(rhs, local_decls)?;
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
            let lhs_ty = resolve_operand_ty(lhs, local_decls)?;
            let rhs_ty = resolve_operand_ty(rhs, local_decls)?;
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
            let operand_ty = resolve_operand_ty(operand, local_decls)?;
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
                operand_tys.push(resolve_operand_ty(op, local_decls)?);
            }
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
                    Ty::Array(Box::new(elem_ty.clone()), operands.len())
                }
                AggregateKind::Tuple => Ty::Tuple(operand_tys.clone()),
                AggregateKind::Adt { active_field, .. } => {
                    if active_field.is_some() && operands.len() != 1 {
                        return Err(RvalueLowerError::InvalidAggregateOperands {
                            kind: kind.clone(),
                            count: operands.len(),
                            reason: "union aggregate initialization requires exactly 1 operand",
                        });
                    }
                    Ty::Tuple(operand_tys.clone())
                }
                AggregateKind::Closure => Ty::Tuple(operand_tys.clone()),
                AggregateKind::RawPtr {
                    pointee,
                    mutability,
                } => {
                    if operands.len() != 2 {
                        return Err(RvalueLowerError::InvalidAggregateOperands {
                            kind: kind.clone(),
                            count: operands.len(),
                            reason: "RawPtr aggregate requires 2 operands (data_ptr_or_addr, unit_metadata)",
                        });
                    }
                    let data_ty = &operand_tys[0];
                    let meta_ty = &operand_tys[1];
                    if !(data_ty.is_any_ptr() || data_ty.is_integral()) {
                        return Err(RvalueLowerError::InvalidAggregateOperands {
                            kind: kind.clone(),
                            count: operands.len(),
                            reason: "RawPtr aggregate first operand must be a pointer or integer address",
                        });
                    }
                    if !meta_ty.is_unit() {
                        return Err(RvalueLowerError::InvalidAggregateOperands {
                            kind: kind.clone(),
                            count: operands.len(),
                            reason: "thin RawPtr aggregate second operand must be unit metadata ()",
                        });
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

            let compatible = if &place_ty == rvalue_ty {
                true
            } else if let LoweredRvalue::Aggregate {
                kind:
                    AggregateKind::Adt {
                        active_field: Some(field_idx),
                        ..
                    },
                operand_tys,
                ..
            } = &lowered
            {
                // Allow union aggregate initialization to assign to either a single-field tuple,
                // the active field's type directly, or a multi-field tuple representing the union layout.
                operand_tys.len() == 1
                    && (place_ty == operand_tys[0]
                        || matches!(&place_ty, Ty::Tuple(fields) if fields.get(*field_idx) == Some(&operand_tys[0])))
            } else {
                false
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
pub fn lower_body_with_policy(
    body: &Body,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredBody, RvalueLowerError> {
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
pub fn eval_constant(constant: &Constant, ptr_width: PtrWidth) -> Result<MirValue, RvalueEvalError> {
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
            _ => Err(RvalueEvalError::TypeMismatch(
                "Constant::Int must carry Int or Uint type",
            )),
        },
        Constant::Bool(b) => Ok(MirValue::Bool(*b)),
        Constant::Char(c) => Ok(MirValue::Char(*c)),
        Constant::Ptr(ptr, ty) => {
            if !ty.is_any_ptr() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Constant::Ptr must carry RawPtr or Ref type",
                ));
            }
            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: (ptr.addr as u128 & ptr_width.mask()) as u64,
                    provenance: ptr.provenance,
                },
                ty: ty.clone(),
            })
        }
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
        ) if allow_pointers && lhs_ty == rhs_ty => {
            let mask = ptr_width.mask();
            let aa = (pa.addr as u128) & mask;
            let ab = (pb.addr as u128) & mask;
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
            if !pointee.is_inhabited() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Offset pointee type must be inhabited",
                ));
            }
            let MirValue::Int {
                bits: count_bits,
                ty: rhs_ty,
            } = rhs
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Offset RHS must be MirValue::Int",
                ));
            };

            let pointee_size = pointee.byte_size_for(ptr_width);
            let base_addr = (ptr.addr as u128) & ptr_width.mask();

            let new_addr = match rhs_ty {
                Ty::Int(it) => {
                    let count_signed = it.sign_extend(*count_bits, ptr_width);
                    let Some(byte_delta) = count_signed.checked_mul(pointee_size as i128) else {
                        return Err(RvalueEvalError::PointerOffsetOverflow {
                            base_addr: ptr.addr,
                            offset: count_signed,
                            pointee_size,
                        });
                    };
                    if byte_delta < ptr_width.min_isize() || byte_delta > ptr_width.max_isize() {
                        return Err(RvalueEvalError::PointerOffsetOverflow {
                            base_addr: ptr.addr,
                            offset: count_signed,
                            pointee_size,
                        });
                    }
                    let Some(res) = (base_addr as i128).checked_add(byte_delta) else {
                        return Err(RvalueEvalError::PointerOffsetOverflow {
                            base_addr: ptr.addr,
                            offset: count_signed,
                            pointee_size,
                        });
                    };
                    if res < 0 || (res as u128) > ptr_width.mask() {
                        return Err(RvalueEvalError::PointerOffsetOverflow {
                            base_addr: ptr.addr,
                            offset: count_signed,
                            pointee_size,
                        });
                    }
                    res as u64
                }
                Ty::Uint(ut) => {
                    let count_unsigned = *count_bits & ut.mask(ptr_width);
                    let Some(byte_delta) = count_unsigned.checked_mul(pointee_size as u128) else {
                        return Err(RvalueEvalError::PointerOffsetOverflow {
                            base_addr: ptr.addr,
                            offset: count_unsigned as i128,
                            pointee_size,
                        });
                    };
                    let Some(res) = base_addr.checked_add(byte_delta) else {
                        return Err(RvalueEvalError::PointerOffsetOverflow {
                            base_addr: ptr.addr,
                            offset: count_unsigned as i128,
                            pointee_size,
                        });
                    };
                    if res > ptr_width.mask() {
                        return Err(RvalueEvalError::PointerOffsetOverflow {
                            base_addr: ptr.addr,
                            offset: count_unsigned as i128,
                            pointee_size,
                        });
                    }
                    res as u64
                }
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Offset RHS must have Int or Uint type",
                    ));
                }
            };

            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: new_addr,
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
            MirValue::Ptr { .. } => Ok(MirValue::Unit),
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
            if active_field.is_some() && operands.len() != 1 {
                return Err(RvalueEvalError::TypeMismatch(
                    "union Adt aggregate with active_field requires exactly 1 operand",
                ));
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
                MirValue::Ptr { ptr, .. } => PointerValue {
                    addr: (ptr.addr as u128 & ptr_width.mask()) as u64,
                    provenance: ptr.provenance,
                },
                MirValue::Int { bits, .. } => PointerValue {
                    addr: (*bits & ptr_width.mask()) as u64,
                    provenance: None,
                },
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "RawPtr aggregate first operand must be pointer or integer address",
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

/// Evaluates a `LoweredCast` on an evaluated `MirValue` operand under `ptr_width` and `policy`.
pub fn eval_lowered_cast(
    cast: &LoweredCast,
    val: &MirValue,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<MirValue, RvalueEvalError> {
    match cast {
        LoweredCast::PtrToInt { target_ty, .. } => {
            let Some(ptr) = val.as_ptr() else {
                return Err(RvalueEvalError::TypeMismatch(
                    "PtrToInt requires pointer value",
                ));
            };
            let bits = eval_ptr_to_int_with_ptr_width(ptr, target_ty, ptr_width, tracker)?;
            Ok(MirValue::Int {
                bits,
                ty: target_ty.clone(),
            })
        }
        LoweredCast::IntToPtr { target_ty, .. } => {
            let Some(addr) = val.as_bits() else {
                return Err(RvalueEvalError::TypeMismatch(
                    "IntToPtr requires scalar integer value",
                ));
            };
            let ptr = eval_int_to_ptr_with_ptr_width(addr, target_ty, ptr_width, tracker, None)?;
            Ok(MirValue::Ptr {
                ptr,
                ty: target_ty.clone(),
            })
        }
        LoweredCast::IntToInt {
            src_ty, target_ty, ..
        } => {
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
        LoweredCast::PtrToPtr { target_ty, .. } => {
            let Some(ptr) = val.as_ptr() else {
                return Err(RvalueEvalError::TypeMismatch(
                    "PtrToPtr requires pointer value",
                ));
            };
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
            let tv_in = match val {
                MirValue::Ptr { ptr, .. } => TransmuteValue::Ptr(*ptr),
                MirValue::Int { bits, .. } => TransmuteValue::Scalar(*bits),
                MirValue::Bool(b) => TransmuteValue::Scalar(u128::from(*b)),
                MirValue::Char(c) => TransmuteValue::Scalar(u32::from(*c) as u128),
                MirValue::Unit => TransmuteValue::Bytes(Vec::new()),
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "unsupported value for eval_lowered_cast Transmute",
                    ));
                }
            };
            let tv_out = eval_transmute(tv_in, src_ty, target_ty, ptr_width, policy, tracker)?;
            match (tv_out, target_ty) {
                (TransmuteValue::Ptr(ptr), _) => Ok(MirValue::Ptr {
                    ptr,
                    ty: target_ty.clone(),
                }),
                (TransmuteValue::Scalar(bits), Ty::Bool) => Ok(MirValue::Bool(bits != 0)),
                (TransmuteValue::Scalar(bits), Ty::Char) => {
                    let c = char::from_u32(bits as u32).ok_or(CastEvalError::InvalidBitPattern {
                        target_ty: Ty::Char,
                        bits,
                    })?;
                    Ok(MirValue::Char(c))
                }
                (TransmuteValue::Scalar(bits), _) => Ok(MirValue::Int {
                    bits,
                    ty: target_ty.clone(),
                }),
                (TransmuteValue::Bytes(_), Ty::Tuple(fields)) if fields.is_empty() => {
                    Ok(MirValue::Unit)
                }
                (TransmuteValue::Bytes(bytes), Ty::Array(elem_ty, count))
                    if **elem_ty == Ty::Uint(UintTy::U8) && bytes.len() == *count =>
                {
                    let elements = bytes
                        .into_iter()
                        .map(|b| MirValue::Int {
                            bits: b as u128,
                            ty: Ty::Uint(UintTy::U8),
                        })
                        .collect();
                    Ok(MirValue::Array {
                        elements,
                        elem_ty: Ty::Uint(UintTy::U8),
                    })
                }
                (TransmuteValue::Bytes(bytes), _) => {
                    let elements = bytes
                        .into_iter()
                        .map(|b| MirValue::Int {
                            bits: b as u128,
                            ty: Ty::Uint(UintTy::U8),
                        })
                        .collect();
                    Ok(MirValue::Tuple(elements))
                }
            }
        }
    }
}

/// Evaluates a `LoweredRvalue` given a closure/slice mapping `Local`s to `MirValue`s.
pub fn eval_lowered_rvalue(
    rvalue: &LoweredRvalue,
    locals: &[MirValue],
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<MirValue, RvalueEvalError> {
    let eval_op = |op: &Operand| -> Result<MirValue, RvalueEvalError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                if !place.projection.is_empty() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected place evaluation requires memory environment",
                    ));
                }
                locals
                    .get(place.local.0)
                    .cloned()
                    .ok_or(RvalueEvalError::TypeMismatch("local index out of bounds"))
            }
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
            let addr = ((place.local.0 as u128 + 1) * 0x1000) & ptr_width.mask();
            Ok(MirValue::Ptr {
                ptr: PointerValue::with_provenance(addr as u64, place.local.0 as u64 + 1, 1),
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
            let v = locals
                .get(place.local.0)
                .ok_or(RvalueEvalError::TypeMismatch("local index out of bounds"))?;
            let discr = match v {
                MirValue::Adt { variant_idx, .. } => *variant_idx as i128,
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
        LoweredRvalue::CopyForDeref { place, .. } => locals
            .get(place.local.0)
            .cloned()
            .ok_or(RvalueEvalError::TypeMismatch("local index out of bounds")),
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
}
