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
    AggregateKind, BasicBlockData, BinOp, Body, Constant, IntTy, Local, Mutability, NullOp,
    Operand, Place, PointerValue, ProjectionElem, PtrWidth, Rvalue, Statement, Ty, UintTy, UnOp,
};
use crate::lower::cast::{
    AbstractByte, CastEvalError, CastLowerError, ExposedProvenanceTracker, LoweredCast,
    TransmutePolicy, TransmuteValue, decode_int_bytes, decode_ptr_bytes, encode_int_bytes,
    encode_ptr_bytes, eval_char_to_int, eval_int_to_int, eval_int_to_ptr_with_ptr_width,
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
    /// `NullOp::OffsetOf` applied to a type without a canonical byte layout
    /// (see [`Ty::has_canonical_byte_layout`]).
    UnsupportedOffsetOfLayout(Ty),
    /// `NullOp::OffsetOf` step with a non-tuple container, non-zero `variant_idx`, or
    /// out-of-bounds `field_idx`.
    InvalidOffsetOfField {
        container_ty: Ty,
        variant_idx: usize,
        field_idx: usize,
    },
    /// Invalid type parameter for `Rvalue::NullaryOp` (e.g. `NullOp::UbChecks` with non-`bool`).
    InvalidNullaryOpType {
        op: NullOp,
        arg_ty: Ty,
    },
    /// `Statement::SetDiscriminant` applied to a non-aggregate place type.
    InvalidSetDiscriminantTarget(Ty),
    /// `Statement::Assume` applied to a non-`bool` operand.
    InvalidAssumeType(Ty),
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
            RvalueLowerError::UnsupportedOffsetOfLayout(ty) => {
                write!(f, "type {ty:?} has no canonical byte layout for OffsetOf")
            }
            RvalueLowerError::InvalidOffsetOfField {
                container_ty,
                variant_idx,
                field_idx,
            } => {
                write!(
                    f,
                    "invalid OffsetOf step (variant={variant_idx}, field={field_idx}) on type {container_ty:?}"
                )
            }
            RvalueLowerError::InvalidNullaryOpType { op, arg_ty } => {
                write!(f, "invalid type {arg_ty:?} for nullary op {op:?}")
            }
            RvalueLowerError::InvalidSetDiscriminantTarget(ty) => {
                write!(f, "SetDiscriminant requires aggregate tuple/ADT place, got {ty:?}")
            }
            RvalueLowerError::InvalidAssumeType(ty) => {
                write!(f, "Statement::Assume requires bool operand, got {ty:?}")
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
    NullaryOp {
        op: NullOp,
        arg_ty: Ty,
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
            | LoweredRvalue::NullaryOp { ty, .. }
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
    SetDiscriminant {
        place: Place,
        place_ty: Ty,
        variant_index: usize,
    },
    PlaceMention {
        place: Place,
        place_ty: Ty,
    },
    Assume {
        operand: Operand,
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

/// Resolves the byte offset of `fields` (`(variant_idx, field_idx)` chain) inside `arg_ty`
/// under `ptr_width`.
///
/// Requires `arg_ty` to have a representable layout ([`Ty::layout_size_for`]) and every
/// projected container to be a `Ty::Tuple` with a canonical byte layout
/// ([`Ty::has_canonical_byte_layout`]), `variant_idx == 0`, and `field_idx < fields.len()`.
pub fn resolve_offset_of(
    arg_ty: &Ty,
    fields: &[(usize, usize)],
    ptr_width: PtrWidth,
) -> Result<usize, RvalueLowerError> {
    check_layout(arg_ty.clone(), ptr_width)?;
    let mut cur_ty = arg_ty;
    let mut total_offset = 0usize;
    for &(variant_idx, field_idx) in fields {
        let Ty::Tuple(tuple_fields) = cur_ty else {
            return Err(RvalueLowerError::InvalidOffsetOfField {
                container_ty: cur_ty.clone(),
                variant_idx,
                field_idx,
            });
        };
        if variant_idx != 0 || field_idx >= tuple_fields.len() {
            return Err(RvalueLowerError::InvalidOffsetOfField {
                container_ty: cur_ty.clone(),
                variant_idx,
                field_idx,
            });
        }
        if !cur_ty.has_canonical_byte_layout(ptr_width) {
            return Err(RvalueLowerError::UnsupportedOffsetOfLayout(cur_ty.clone()));
        }
        for f in &tuple_fields[..field_idx] {
            let f_size = f
                .layout_size_for(ptr_width)
                .ok_or_else(|| RvalueLowerError::LayoutTooLarge(arg_ty.clone()))?;
            total_offset = total_offset
                .checked_add(f_size)
                .ok_or_else(|| RvalueLowerError::LayoutTooLarge(arg_ty.clone()))?;
        }
        cur_ty = &tuple_fields[field_idx];
    }
    Ok(total_offset)
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
        Rvalue::NullaryOp(op, arg_ty) => {
            let ty = match op {
                NullOp::SizeOf | NullOp::AlignOf => {
                    check_layout(arg_ty.clone(), ptr_width)?;
                    Ty::Uint(UintTy::Usize)
                }
                NullOp::OffsetOf(fields) => {
                    resolve_offset_of(arg_ty, fields, ptr_width)?;
                    Ty::Uint(UintTy::Usize)
                }
                NullOp::UbChecks => {
                    if *arg_ty != Ty::Bool {
                        return Err(RvalueLowerError::InvalidNullaryOpType {
                            op: op.clone(),
                            arg_ty: arg_ty.clone(),
                        });
                    }
                    Ty::Bool
                }
            };
            Ok(LoweredRvalue::NullaryOp {
                op: op.clone(),
                arg_ty: arg_ty.clone(),
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
        Statement::SetDiscriminant {
            place,
            variant_index,
        } => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            if !matches!(place_ty, Ty::Tuple(_)) {
                return Err(RvalueLowerError::InvalidSetDiscriminantTarget(place_ty));
            }
            Ok(LoweredStatement::SetDiscriminant {
                place: place.clone(),
                place_ty,
                variant_index: *variant_index,
            })
        }
        Statement::PlaceMention(place) => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            Ok(LoweredStatement::PlaceMention {
                place: place.clone(),
                place_ty,
            })
        }
        Statement::Assume(operand) => {
            let operand_ty = lower_operand_ty(operand, local_decls, ptr_width)?;
            if operand_ty != Ty::Bool {
                return Err(RvalueLowerError::InvalidAssumeType(operand_ty));
            }
            Ok(LoweredStatement::Assume {
                operand: operand.clone(),
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
    /// Place that cannot be evaluated without a byte-level memory model: a `Deref` read or
    /// write (other than the `&(*p)` / `&raw (*p)` reborrows), the address of a projected
    /// place, or a nested write into an inactive union field.
    UnsupportedPlaceProjection(Place),
    /// Ill-formed `Constant` (wrong type, out-of-range bits, or null `&T`).
    InvalidConstant(&'static str),
    /// Array value too large for the evaluator to materialize.
    EvaluationLimit {
        len: usize,
    },
    /// Out-of-bounds array `Index`, `ConstantIndex`, or `Subslice` projection.
    IndexOutOfBounds {
        index: u128,
        len: usize,
    },
    /// Out-of-bounds tuple or ADT `Field` projection.
    FieldOutOfBounds {
        field_idx: usize,
        field_count: usize,
    },
    /// `Downcast` or `Field` projection on an enum/ADT whose active variant does not match.
    InactiveVariantProjection {
        expected: usize,
        actual: usize,
    },
    /// Union `Field` read on a field other than the union's active field. (A nested write into
    /// an inactive union field is `UnsupportedPlaceProjection` instead: it is defined in Rust
    /// but needs a byte-level memory model.)
    InactiveUnionField {
        active_field: usize,
        requested_field: usize,
    },
    /// Access or assignment to a storage-dead (`LocalSlotState::Dead`) local.
    DeadLocal(Local),
    /// Read or invalid operation on an uninitialized (`LocalSlotState::Uninit` or incomplete
    /// `PartialShell`) local or field.
    UninitializedLocal(Local),
    /// `Statement::SetDiscriminant` on a place holding a non-aggregate runtime value.
    InvalidSetDiscriminant(Place),
    /// `Statement::Assume` evaluated to `false` (immediate undefined behavior).
    AssumeFalse,
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
            RvalueEvalError::IndexOutOfBounds { index, len } => {
                write!(f, "index {index} out of bounds for array of length {len} (UB)")
            }
            RvalueEvalError::FieldOutOfBounds {
                field_idx,
                field_count,
            } => {
                write!(
                    f,
                    "field index {field_idx} out of bounds for aggregate with {field_count} fields (UB)"
                )
            }
            RvalueEvalError::InactiveVariantProjection { expected, actual } => {
                write!(
                    f,
                    "projection on inactive variant: expected variant {expected}, actual variant {actual} (UB)"
                )
            }
            RvalueEvalError::InactiveUnionField {
                active_field,
                requested_field,
            } => {
                write!(
                    f,
                    "read of inactive union field {requested_field} while active field is {active_field} (UB)"
                )
            }
            RvalueEvalError::DeadLocal(loc) => {
                write!(f, "access to storage-dead local _{} (UB)", loc.0)
            }
            RvalueEvalError::UninitializedLocal(loc) => {
                write!(f, "access to uninitialized local _{} (UB)", loc.0)
            }
            RvalueEvalError::InvalidSetDiscriminant(place) => {
                write!(f, "SetDiscriminant on non-aggregate place {place:?} (UB)")
            }
            RvalueEvalError::AssumeFalse => {
                write!(f, "Statement::Assume evaluated to false (UB)")
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

/// Validates and normalizes `val` against `ty` for an identity transmute (`src_ty == target_ty`):
/// checks shape, scalar types, and leaf bit-validity (such as non-null `&T`), masks pointer
/// addresses and integer bits to `ptr_width`, and preserves struct/enum/union `MirValue::Adt`
/// values (which Anneal types as the tuple of their declared fields) across both canonical and
/// non-canonical field layouts.
fn eval_identity_transmute_value(
    val: &MirValue,
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    match (ty, val) {
        (Ty::Bool, MirValue::Bool(b)) => Ok(MirValue::Bool(*b)),
        (Ty::Char, MirValue::Char(c)) => Ok(MirValue::Char(*c)),
        (Ty::Int(_) | Ty::Uint(_), MirValue::Int { bits, ty: val_ty }) if val_ty == ty => {
            if !ty.is_valid_scalar_bits(*bits, ptr_width) {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: ty.clone(),
                    bits: *bits,
                }));
            }
            Ok(MirValue::Int {
                bits: *bits & ty.scalar_mask(ptr_width),
                ty: ty.clone(),
            })
        }
        (Ty::RawPtr(_, _) | Ty::Ref(_, _), MirValue::Ptr { ptr, ty: val_ty }) if val_ty == ty => {
            let addr_bits = u128::from(ptr.addr) & ptr_width.mask();
            if !ty.is_valid_scalar_bits(addr_bits, ptr_width) {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: ty.clone(),
                    bits: addr_bits,
                }));
            }
            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: addr_bits as u64,
                    provenance: ptr.provenance,
                },
                ty: ty.clone(),
            })
        }
        (
            Ty::Array(elem, count),
            MirValue::Array {
                elements,
                elem_ty,
            },
        ) if **elem == *elem_ty && elements.len() == *count => {
            if *count > MAX_EVAL_ARRAY_LEN {
                return Err(RvalueEvalError::EvaluationLimit { len: *count });
            }
            let norm = elements
                .iter()
                .map(|element| eval_identity_transmute_value(element, elem, ptr_width))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(MirValue::Array {
                elements: norm,
                elem_ty: elem_ty.clone(),
            })
        }
        (Ty::Tuple(fields), MirValue::Unit) if fields.is_empty() => Ok(MirValue::Unit),
        (Ty::Tuple(fields), MirValue::Tuple(values)) if values.len() == fields.len() => {
            let norm = values
                .iter()
                .zip(fields)
                .map(|(value, field)| eval_identity_transmute_value(value, field, ptr_width))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(MirValue::Tuple(norm))
        }
        (
            Ty::Tuple(fields),
            MirValue::Adt {
                def_path,
                variant_idx,
                active_field: None,
                fields: values,
            },
        ) if values.len() == fields.len() => {
            let norm = values
                .iter()
                .zip(fields)
                .map(|(value, field)| eval_identity_transmute_value(value, field, ptr_width))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(MirValue::Adt {
                def_path: def_path.clone(),
                variant_idx: *variant_idx,
                active_field: None,
                fields: norm,
            })
        }
        (
            Ty::Tuple(fields),
            MirValue::Adt {
                def_path,
                variant_idx: 0,
                active_field: Some(field_idx),
                fields: values,
            },
        ) if values.len() == 1 => {
            let Some(field_ty) = fields.get(*field_idx) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "union Adt active_field index out of bounds for union type",
                ));
            };
            let norm = eval_identity_transmute_value(&values[0], field_ty, ptr_width)?;
            Ok(MirValue::Adt {
                def_path: def_path.clone(),
                variant_idx: 0,
                active_field: Some(*field_idx),
                fields: vec![norm],
            })
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "transmute operand value does not match its source type",
        )),
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
            src_ty,
            target_ty,
            expose_provenance,
            ..
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
            let mut suppressed = ExposedProvenanceTracker::new();
            let active_tracker = if *expose_provenance {
                tracker
            } else {
                &mut suppressed
            };
            let bits =
                eval_ptr_to_int_with_ptr_width(*ptr, target_ty, ptr_width, active_tracker)?;
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
        LoweredCast::CharToInt { target_ty, .. } => {
            let MirValue::Char(c) = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "CharToInt requires MirValue::Char operand",
                ));
            };
            let codepoint_bits = u128::from(u32::from(*c));
            let bits = eval_char_to_int(codepoint_bits, target_ty, ptr_width)?;
            Ok(MirValue::Int {
                bits,
                ty: target_ty.clone(),
            })
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
            if src_ty == target_ty {
                // Identity transmute (`T.decode(T.encode(v)) == v` for every valid `v`),
                // covering both canonical and non-canonical layouts as well as `MirValue::Adt`
                // struct/enum/union values.
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
                return eval_identity_transmute_value(val, src_ty, ptr_width);
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

/// Checks whether a runtime `MirValue` is structurally compatible with `expected_ty`,
/// accounting for union `MirValue::Adt { active_field: Some(field_idx), .. }` values whose
/// single operand corresponds to `field_tys[field_idx]` of the union's declared tuple type.
fn mir_value_matches_ty(val: &MirValue, expected_ty: &Ty) -> bool {
    match (val, expected_ty) {
        (MirValue::Int { ty, .. }, expected) => ty == expected,
        (MirValue::Bool(_), Ty::Bool) => true,
        (MirValue::Char(_), Ty::Char) => true,
        (MirValue::Ptr { ty, .. }, expected) => ty == expected,
        (MirValue::Unit, Ty::Tuple(fields)) => fields.is_empty(),
        (
            MirValue::Array { elements, elem_ty },
            Ty::Array(expected_elem, expected_len),
        ) => {
            elem_ty == &**expected_elem
                && elements.len() == *expected_len
                && elements.iter().all(|e| mir_value_matches_ty(e, expected_elem))
        }
        (MirValue::Tuple(vals), Ty::Tuple(field_tys)) => {
            vals.len() == field_tys.len()
                && vals
                    .iter()
                    .zip(field_tys)
                    .all(|(v, t)| mir_value_matches_ty(v, t))
        }
        (
            MirValue::Adt {
                active_field: None,
                fields: vals,
                ..
            },
            Ty::Tuple(field_tys),
        ) => {
            vals.len() == field_tys.len()
                && vals
                    .iter()
                    .zip(field_tys)
                    .all(|(v, t)| mir_value_matches_ty(v, t))
        }
        (
            MirValue::Adt {
                variant_idx: 0,
                active_field: Some(field_idx),
                fields: vals,
                ..
            },
            Ty::Tuple(field_tys),
        ) => {
            if vals.len() == 1 {
                field_tys
                    .get(*field_idx)
                    .is_some_and(|ft| mir_value_matches_ty(&vals[0], ft))
            } else {
                vals.len() == field_tys.len()
                    && field_tys
                        .get(*field_idx)
                        .zip(vals.get(*field_idx))
                        .is_some_and(|(ft, v)| mir_value_matches_ty(v, ft))
            }
        }
        _ => false,
    }
}

/// Traverses `proj` on `val` for a value-tree read.
fn read_projected_mir_value(
    val: &MirValue,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<MirValue, RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        return Ok(val.clone());
    };

    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Downcast(expected_variant) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "consecutive Downcast projections without Field",
                ));
            }
            if let Some(next) = rest.first() {
                if matches!(next, ProjectionElem::Deref) {
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(
                        full_place.clone(),
                    ));
                }
                if !matches!(next, ProjectionElem::Field(..)) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast projection must be followed by Field",
                    ));
                }
            }
            match val {
                MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    ..
                } => {
                    if *variant_idx != *expected_variant {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual: *variant_idx,
                        });
                    }
                    read_projected_mir_value(
                        val,
                        rest,
                        read_index,
                        ptr_width,
                        full_place,
                        Some(*expected_variant),
                    )
                }
                MirValue::Tuple(_) | MirValue::Unit => {
                    if *expected_variant != 0 {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual: 0,
                        });
                    }
                    read_projected_mir_value(
                        val,
                        rest,
                        read_index,
                        ptr_width,
                        full_place,
                        Some(0),
                    )
                }
                _ => Err(RvalueEvalError::TypeMismatch(
                    "Downcast requires a non-union Adt or Tuple value",
                )),
            }
        }
        ProjectionElem::Field(idx, expected_ty) => match val {
            MirValue::Tuple(fields) => {
                if let Some(v) = active_downcast {
                    if v != 0 {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: v,
                            actual: 0,
                        });
                    }
                }
                let Some(field_val) = fields.get(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count: fields.len(),
                    });
                };
                if !mir_value_matches_ty(field_val, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected tuple field runtime type does not match expected type",
                    ));
                }
                read_projected_mir_value(field_val, rest, read_index, ptr_width, full_place, None)
            }
            MirValue::Unit => {
                if let Some(v) = active_downcast {
                    if v != 0 {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: v,
                            actual: 0,
                        });
                    }
                }
                Err(RvalueEvalError::FieldOutOfBounds {
                    field_idx: *idx,
                    field_count: 0,
                })
            }
            MirValue::Adt {
                variant_idx,
                active_field: None,
                fields,
                ..
            } => {
                let expected_variant = active_downcast.unwrap_or(0);
                if *variant_idx != expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: expected_variant,
                        actual: *variant_idx,
                    });
                }
                let Some(field_val) = fields.get(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count: fields.len(),
                    });
                };
                if !mir_value_matches_ty(field_val, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected ADT field runtime type does not match expected type",
                    ));
                }
                read_projected_mir_value(field_val, rest, read_index, ptr_width, full_place, None)
            }
            MirValue::Adt {
                variant_idx,
                active_field: Some(active),
                fields,
                ..
            } => {
                if active_downcast.is_some() || *variant_idx != 0 {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT must have variant 0 and cannot be downcast",
                    ));
                }
                if *active != *idx {
                    return Err(RvalueEvalError::InactiveUnionField {
                        active_field: *active,
                        requested_field: *idx,
                    });
                }
                let field_val = if fields.len() == 1 {
                    &fields[0]
                } else {
                    fields.get(*idx).ok_or(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count: fields.len(),
                    })?
                };
                if !mir_value_matches_ty(field_val, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected union field runtime type does not match expected type",
                    ));
                }
                read_projected_mir_value(field_val, rest, read_index, ptr_width, full_place, None)
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "Field projection requires Tuple or Adt value",
            )),
        },
        ProjectionElem::Index(idx_local) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Index projection requires Array value",
                ));
            };
            let idx_bits = read_index(*idx_local)?;
            let Ok(i) = usize::try_from(idx_bits) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: elements.len(),
                });
            };
            let Some(elem_val) = elements.get(i) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: elements.len(),
                });
            };
            if !mir_value_matches_ty(elem_val, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array element runtime type does not match elem_ty",
                ));
            }
            read_projected_mir_value(elem_val, rest, read_index, ptr_width, full_place, None)
        }
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "ConstantIndex projection requires Array value",
                ));
            };
            let len = elements.len() as u64;
            if len < *min_length {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: u128::from(*offset),
                    len: elements.len(),
                });
            }
            let idx = if *from_end {
                if *offset == 0 || *offset > len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(*offset),
                        len: elements.len(),
                    });
                }
                elements.len() - (*offset as usize)
            } else {
                if *offset >= len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(*offset),
                        len: elements.len(),
                    });
                }
                *offset as usize
            };
            let elem_val = &elements[idx];
            if !mir_value_matches_ty(elem_val, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array element runtime type does not match elem_ty",
                ));
            }
            read_projected_mir_value(elem_val, rest, read_index, ptr_width, full_place, None)
        }
        ProjectionElem::Subslice {
            from,
            to,
            from_end,
        } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Subslice projection requires Array value",
                ));
            };
            let len = elements.len() as u64;
            let (start, end) = if *from_end {
                let Some(sum) = from.checked_add(*to) else {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(*from) + u128::from(*to),
                        len: elements.len(),
                    });
                };
                if sum > len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(sum),
                        len: elements.len(),
                    });
                }
                (*from as usize, (len - *to) as usize)
            } else {
                if *from > *to || *to > len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from((*from).max(*to)),
                        len: elements.len(),
                    });
                }
                (*from as usize, *to as usize)
            };
            for elem_val in &elements[start..end] {
                if !mir_value_matches_ty(elem_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
            }
            let sub_val = MirValue::Array {
                elements: elements[start..end].to_vec(),
                elem_ty: elem_ty.clone(),
            };
            read_projected_mir_value(&sub_val, rest, read_index, ptr_width, full_place, None)
        }
    }
}

/// Traverses `proj` on `val` for an in-place value-tree write.
fn write_projected_mir_value(
    val: &mut MirValue,
    proj: &[ProjectionElem],
    new_val: MirValue,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        if let Some(expected_variant) = active_downcast {
            match &new_val {
                MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    ..
                } if *variant_idx == expected_variant => {}
                MirValue::Tuple(_) | MirValue::Unit if expected_variant == 0 => {}
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "written value does not match active Downcast variant",
                    ));
                }
            }
        }
        *val = new_val;
        return Ok(());
    };

    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Downcast(expected_variant) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "consecutive Downcast projections without Field",
                ));
            }
            if let Some(next) = rest.first() {
                if matches!(next, ProjectionElem::Deref) {
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(
                        full_place.clone(),
                    ));
                }
                if !matches!(next, ProjectionElem::Field(..)) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast projection must be followed by Field",
                    ));
                }
            }
            match val {
                MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    ..
                } => {
                    if *variant_idx != *expected_variant {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual: *variant_idx,
                        });
                    }
                    write_projected_mir_value(
                        val,
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        Some(*expected_variant),
                    )
                }
                MirValue::Tuple(_) | MirValue::Unit => {
                    if *expected_variant != 0 {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual: 0,
                        });
                    }
                    write_projected_mir_value(
                        val,
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        Some(0),
                    )
                }
                _ => Err(RvalueEvalError::TypeMismatch(
                    "Downcast requires a non-union Adt or Tuple value",
                )),
            }
        }
        ProjectionElem::Field(idx, expected_ty) => match val {
            MirValue::Tuple(fields) => {
                if let Some(v) = active_downcast {
                    if v != 0 {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: v,
                            actual: 0,
                        });
                    }
                }
                let field_count = fields.len();
                let Some(field_slot) = fields.get_mut(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count,
                    });
                };
                if rest.is_empty() {
                    // Both the replaced field and the written value must have the projected
                    // field type, so a write never changes the tuple's type.
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected tuple field runtime type does not match expected type",
                        ));
                    }
                    if !mir_value_matches_ty(&new_val, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "written tuple field runtime type does not match expected type",
                        ));
                    }
                    *field_slot = new_val;
                    Ok(())
                } else {
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected tuple field runtime type does not match expected type",
                        ));
                    }
                    write_projected_mir_value(
                        field_slot,
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        None,
                    )?;
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "updated tuple field runtime type does not match expected type",
                        ));
                    }
                    Ok(())
                }
            }
            MirValue::Unit => {
                if let Some(v) = active_downcast {
                    if v != 0 {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: v,
                            actual: 0,
                        });
                    }
                }
                Err(RvalueEvalError::FieldOutOfBounds {
                    field_idx: *idx,
                    field_count: 0,
                })
            }
            MirValue::Adt {
                variant_idx,
                active_field: None,
                fields,
                ..
            } => {
                let expected_variant = active_downcast.unwrap_or(0);
                if *variant_idx != expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: expected_variant,
                        actual: *variant_idx,
                    });
                }
                let field_count = fields.len();
                let Some(field_slot) = fields.get_mut(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count,
                    });
                };
                if rest.is_empty() {
                    // Both the replaced field and the written value must have the projected
                    // field type, so a write never changes the ADT variant's field types.
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected ADT field runtime type does not match expected type",
                        ));
                    }
                    if !mir_value_matches_ty(&new_val, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "written ADT field runtime type does not match expected type",
                        ));
                    }
                    *field_slot = new_val;
                    Ok(())
                } else {
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected ADT field runtime type does not match expected type",
                        ));
                    }
                    write_projected_mir_value(
                        field_slot,
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        None,
                    )?;
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "updated ADT field runtime type does not match expected type",
                        ));
                    }
                    Ok(())
                }
            }
            MirValue::Adt {
                variant_idx,
                active_field: Some(active),
                fields,
                ..
            } => {
                if active_downcast.is_some() || *variant_idx != 0 {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT must have variant 0 and cannot be downcast",
                    ));
                }
                if rest.is_empty() {
                    if !mir_value_matches_ty(&new_val, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "written union field runtime type does not match expected type",
                        ));
                    }
                    if fields.len() <= 1 {
                        *active = *idx;
                        *fields = vec![new_val];
                        Ok(())
                    } else if *idx < fields.len() {
                        *active = *idx;
                        fields[*idx] = new_val;
                        Ok(())
                    } else {
                        Err(RvalueEvalError::FieldOutOfBounds {
                            field_idx: *idx,
                            field_count: fields.len(),
                        })
                    }
                } else {
                    if *active != *idx {
                        // A write into a sub-place of an inactive union field (`u.b.0 = x`
                        // while `u.a` is active) is defined in Rust: it overwrites part of the
                        // union's storage. The value tree has no bytes for the inactive field to
                        // update, so this needs a byte-level memory model and is unsupported
                        // rather than undefined behavior.
                        return Err(RvalueEvalError::UnsupportedPlaceProjection(
                            full_place.clone(),
                        ));
                    }
                    let field_count = fields.len();
                    let field_slot = if field_count == 1 {
                        &mut fields[0]
                    } else {
                        fields.get_mut(*idx).ok_or(RvalueEvalError::FieldOutOfBounds {
                            field_idx: *idx,
                            field_count,
                        })?
                    };
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected union field runtime type does not match expected type",
                        ));
                    }
                    write_projected_mir_value(
                        field_slot,
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        None,
                    )?;
                    if !mir_value_matches_ty(field_slot, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "updated union field runtime type does not match expected type",
                        ));
                    }
                    Ok(())
                }
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "Field projection requires Tuple or Adt value",
            )),
        },
        ProjectionElem::Index(idx_local) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Index projection requires Array value",
                ));
            };
            let idx_bits = read_index(*idx_local)?;
            let arr_len = elements.len();
            let Ok(i) = usize::try_from(idx_bits) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: arr_len,
                });
            };
            let Some(elem_slot) = elements.get_mut(i) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: arr_len,
                });
            };
            if rest.is_empty() {
                if !mir_value_matches_ty(&new_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "written Array element runtime type does not match elem_ty",
                    ));
                }
                *elem_slot = new_val;
                Ok(())
            } else {
                if !mir_value_matches_ty(elem_slot, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
                write_projected_mir_value(
                    elem_slot,
                    rest,
                    new_val,
                    read_index,
                    ptr_width,
                    full_place,
                    None,
                )?;
                if !mir_value_matches_ty(elem_slot, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "updated Array element runtime type does not match elem_ty",
                    ));
                }
                Ok(())
            }
        }
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "ConstantIndex projection requires Array value",
                ));
            };
            let arr_len = elements.len();
            let len = arr_len as u64;
            if len < *min_length {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: u128::from(*offset),
                    len: arr_len,
                });
            }
            let idx = if *from_end {
                if *offset == 0 || *offset > len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(*offset),
                        len: arr_len,
                    });
                }
                arr_len - (*offset as usize)
            } else {
                if *offset >= len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(*offset),
                        len: arr_len,
                    });
                }
                *offset as usize
            };
            let elem_slot = &mut elements[idx];
            if rest.is_empty() {
                if !mir_value_matches_ty(&new_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "written Array element runtime type does not match elem_ty",
                    ));
                }
                *elem_slot = new_val;
                Ok(())
            } else {
                if !mir_value_matches_ty(elem_slot, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
                write_projected_mir_value(
                    elem_slot,
                    rest,
                    new_val,
                    read_index,
                    ptr_width,
                    full_place,
                    None,
                )?;
                if !mir_value_matches_ty(elem_slot, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "updated Array element runtime type does not match elem_ty",
                    ));
                }
                Ok(())
            }
        }
        ProjectionElem::Subslice {
            from,
            to,
            from_end,
        } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Subslice projection requires Array value",
                ));
            };
            let arr_len = elements.len();
            let len = arr_len as u64;
            let (start, end) = if *from_end {
                let Some(sum) = from.checked_add(*to) else {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(*from) + u128::from(*to),
                        len: arr_len,
                    });
                };
                if sum > len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from(sum),
                        len: arr_len,
                    });
                }
                (*from as usize, (len - *to) as usize)
            } else {
                if *from > *to || *to > len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: u128::from((*from).max(*to)),
                        len: arr_len,
                    });
                }
                (*from as usize, *to as usize)
            };
            for elem_val in &elements[start..end] {
                if !mir_value_matches_ty(elem_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
            }
            let expected_sub_len = end - start;
            let mut sub_val = MirValue::Array {
                elements: elements[start..end].to_vec(),
                elem_ty: elem_ty.clone(),
            };
            write_projected_mir_value(
                &mut sub_val,
                rest,
                new_val,
                read_index,
                ptr_width,
                full_place,
                None,
            )?;
            let MirValue::Array {
                elements: new_sub_elems,
                elem_ty: new_elem_ty,
            } = sub_val
            else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Subslice write must produce an Array value",
                ));
            };
            if new_elem_ty != *elem_ty || new_sub_elems.len() != expected_sub_len {
                return Err(RvalueEvalError::TypeMismatch(
                    "Subslice write result element type or length mismatch",
                ));
            }
            for elem_val in &new_sub_elems {
                if !mir_value_matches_ty(elem_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Subslice updated element runtime type does not match elem_ty",
                    ));
                }
            }
            elements.splice(start..end, new_sub_elems);
            Ok(())
        }
    }
}

/// Evaluates a value-tree `Place` read over an initialized `locals` slice under `ptr_width`.
///
/// Supports arbitrary chains of `Field`, `Index`, `ConstantIndex`, `Subslice`, and `Downcast`
/// projections over `MirValue::{Tuple, Array, Adt}`. Any `ProjectionElem::Deref` returns
/// `Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()))`.
pub fn eval_place_read(
    place: &Place,
    locals: &[MirValue],
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    if place
        .projection
        .iter()
        .any(|p| matches!(p, ProjectionElem::Deref))
    {
        return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
    }
    let root_val = locals
        .get(place.local.0)
        .ok_or(RvalueEvalError::TypeMismatch("local index out of bounds"))?;
    let read_index = |idx_local: Local| -> Result<u128, RvalueEvalError> {
        let Some(idx_val) = locals.get(idx_local.0) else {
            return Err(RvalueEvalError::TypeMismatch(
                "index local index out of bounds",
            ));
        };
        match idx_val {
            MirValue::Int {
                bits,
                ty: Ty::Uint(UintTy::Usize),
            } if *bits <= ptr_width.max_usize() => Ok(*bits),
            _ => Err(RvalueEvalError::TypeMismatch(
                "array index local must hold a valid usize value",
            )),
        }
    };
    read_projected_mir_value(root_val, &place.projection, &read_index, ptr_width, place, None)
}

/// Evaluates a value-tree `Place` write of `new_val` into an initialized `locals` slice under
/// `ptr_width`.
///
/// Supports arbitrary chains of `Field`, `Index`, `ConstantIndex`, `Subslice`, and `Downcast`
/// projections over `MirValue::{Tuple, Array, Adt}`. Any `ProjectionElem::Deref` returns
/// `Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()))`.
///
/// A projected write never changes the type of a container along `place`: the replaced value
/// and `new_val` must both have the projected field or element type (a union write may switch
/// the active field), and a `Subslice` write must supply an array of the window's exact length
/// and element type. On any error `locals` is left unchanged.
pub fn eval_place_write(
    place: &Place,
    new_val: MirValue,
    locals: &mut [MirValue],
    ptr_width: PtrWidth,
) -> Result<(), RvalueEvalError> {
    if place
        .projection
        .iter()
        .any(|p| matches!(p, ProjectionElem::Deref))
    {
        return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
    }
    if place.local.0 >= locals.len() {
        return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
    }
    // Pre-validate and snapshot any `Index(idx_local)` values before mutably borrowing
    // `locals[place.local.0]`.
    let mut index_cache: Vec<(Local, u128)> = Vec::new();
    for elem in &place.projection {
        if let ProjectionElem::Index(idx_local) = elem {
            let Some(idx_val) = locals.get(idx_local.0) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "index local index out of bounds",
                ));
            };
            let bits = match idx_val {
                MirValue::Int {
                    bits,
                    ty: Ty::Uint(UintTy::Usize),
                } if *bits <= ptr_width.max_usize() => *bits,
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "array index local must hold a valid usize value",
                    ));
                }
            };
            index_cache.push((*idx_local, bits));
        }
    }
    let read_index = |idx_local: Local| -> Result<u128, RvalueEvalError> {
        index_cache
            .iter()
            .find_map(|(loc, bits)| (*loc == idx_local).then_some(*bits))
            .ok_or(RvalueEvalError::TypeMismatch(
                "index local not found in pre-validated cache",
            ))
    };
    let mut updated = locals[place.local.0].clone();
    write_projected_mir_value(
        &mut updated,
        &place.projection,
        new_val,
        &read_index,
        ptr_width,
        place,
        None,
    )?;
    locals[place.local.0] = updated;
    Ok(())
}

/// Evaluates a `NullOp` against `arg_ty` under `ptr_width`.
pub fn eval_nullary_op(
    op: &NullOp,
    arg_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    match op {
        NullOp::SizeOf => {
            let Some(size) = arg_ty.layout_size_for(ptr_width) else {
                return Err(RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge {
                    ty: arg_ty.clone(),
                }));
            };
            Ok(MirValue::unsigned(size as u128, UintTy::Usize, ptr_width))
        }
        NullOp::AlignOf => {
            if arg_ty.layout_size_for(ptr_width).is_none() {
                return Err(RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge {
                    ty: arg_ty.clone(),
                }));
            }
            let align = arg_ty.align_for(ptr_width);
            Ok(MirValue::unsigned(align as u128, UintTy::Usize, ptr_width))
        }
        NullOp::OffsetOf(fields) => {
            let offset = resolve_offset_of(arg_ty, fields, ptr_width).map_err(|err| match err {
                RvalueLowerError::LayoutTooLarge(ty) => {
                    RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge { ty })
                }
                RvalueLowerError::UnsupportedOffsetOfLayout(ty) => {
                    RvalueEvalError::CastEval(CastEvalError::UnsupportedLayout { ty })
                }
                _ => RvalueEvalError::TypeMismatch("invalid OffsetOf field path"),
            })?;
            Ok(MirValue::unsigned(offset as u128, UintTy::Usize, ptr_width))
        }
        NullOp::UbChecks => {
            if *arg_ty != Ty::Bool {
                return Err(RvalueEvalError::TypeMismatch(
                    "NullOp::UbChecks requires Ty::Bool",
                ));
            }
            Ok(MirValue::Bool(true))
        }
    }
}

/// Evaluates a `LoweredRvalue` given a slice mapping `Local`s to `MirValue`s.
///
/// Value-tree projections (`Field`, `Index`, `ConstantIndex`, `Subslice`, `Downcast`) are
/// evaluated via [`eval_place_read`]. `Ref`/`RawPtr` of a bare local yield a synthetic per-local
/// address with a fresh provenance, and `Ref`/`RawPtr` of `(*p)` reborrow `p`'s address and
/// provenance. Any `Deref` read or sub-local address-of returns
/// `RvalueEvalError::UnsupportedPlaceProjection`.
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
        eval_place_read(place, locals, ptr_width)
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
            if !mir_value_matches_ty(&v, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Repeat operand runtime type does not match element type",
                ));
            }
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
        LoweredRvalue::Len {
            place,
            static_len,
            ty,
        } => {
            if *ty != Ty::Uint(UintTy::Usize) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len result type must be usize",
                ));
            }
            if !place.projection.is_empty() || !locals.is_empty() {
                let val = read_place(place)?;
                let MirValue::Array { elements, .. } = val else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Len target runtime value must be MirValue::Array",
                    ));
                };
                if elements.len() != *static_len {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Len target array length does not match static_len",
                    ));
                }
            }
            Ok(MirValue::unsigned(*static_len as u128, UintTy::Usize, ptr_width))
        }
        LoweredRvalue::Cast { cast, .. } => {
            let op = match cast {
                LoweredCast::PtrToInt { operand, .. }
                | LoweredCast::IntToPtr { operand, .. }
                | LoweredCast::IntToInt { operand, .. }
                | LoweredCast::CharToInt { operand, .. }
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
            rhs_ty,
            ..
        } => {
            let lv = eval_op(lhs)?;
            let rv = eval_op(rhs)?;
            if lv.ty() != *lhs_ty || rv.ty() != *rhs_ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "CheckedBinaryOp operand runtime types do not match lowered types",
                ));
            }
            let (wrapped, overflowed) = eval_checked_binop(*op, &lv, &rv, ptr_width)?;
            Ok(MirValue::Tuple(vec![
                MirValue::Int {
                    bits: wrapped,
                    ty: lhs_ty.clone(),
                },
                MirValue::Bool(overflowed),
            ]))
        }
        LoweredRvalue::NullaryOp { op, arg_ty, ty } => {
            let val = eval_nullary_op(op, arg_ty, ptr_width)?;
            if val.ty() != *ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "NullaryOp result type does not match lowered ty",
                ));
            }
            Ok(val)
        }
        LoweredRvalue::UnaryOp { op, operand, .. } => {
            let v = eval_op(operand)?;
            eval_unop(*op, &v, ptr_width)
        }
        LoweredRvalue::Discriminant { place, .. } => {
            let discr = match read_place(place)? {
                MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    ..
                } => variant_idx as i128,
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
        LoweredRvalue::CopyForDeref { place, ty } => match read_place(place)? {
            MirValue::Ptr { ptr, ty: val_ty } if val_ty == *ty && ty.is_any_ptr() => {
                let masked_addr = (u128::from(ptr.addr) & ptr_width.mask()) as u64;
                if ty.is_ref() && masked_addr == 0 {
                    return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                        target_ty: ty.clone(),
                        bits: 0,
                    }));
                }
                Ok(MirValue::Ptr {
                    ptr: PointerValue {
                        addr: masked_addr,
                        provenance: ptr.provenance,
                    },
                    ty: ty.clone(),
                })
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "CopyForDeref requires a pointer value matching the place type",
            )),
        },
    }
}

/// Initialization state of a single field inside a [`PartialAggregate`] (`D13b`).
///
/// Tracks uninitialized sibling fields explicitly so unwritten `()` (`Ty::Tuple(vec![])`)
/// fields are never confused with initialized `MirValue::Unit` values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldSlot {
    /// Field has not yet been written (or has been moved out of).
    Uninit,
    /// Field is itself a partially initialized tuple or ADT shell.
    Partial(PartialAggregate),
    /// Field holds a fully initialized value.
    Init(MirValue),
}

/// Partially initialized tuple, struct, or enum variant shell (`D13b`).
///
/// A shell is created only by field writes into an uninitialized local (or uninitialized
/// tuple field) whose declared type is a `Ty::Tuple`; arrays never get shells, so an element
/// write into an uninitialized array fails closed (`c6d2ad74`).
///
/// Anneal types structs, enums, and unions alike as the `Ty::Tuple` of their fields, so a
/// field-by-field initialization of an uninitialized *union* local also builds a per-field
/// shell. Such a shell keeps every written field instead of modeling the overlapping storage
/// of union fields; union values built by `Rvalue::Aggregate` carry `active_field` and do not
/// have this limitation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialAggregate {
    /// Optional ADT definition path (if known from prior ADT value).
    pub def_path: Option<String>,
    /// Active variant index (`0` for tuples and single-variant structs; `v` when narrowed via
    /// `Downcast(v)` or updated by `SetDiscriminant`).
    pub variant_idx: usize,
    /// True if this shell represents an enum/ADT variant (via `Downcast` or `SetDiscriminant`)
    /// rather than a plain tuple.
    pub is_adt: bool,
    /// True once `Statement::SetDiscriminant` has written this shell's variant tag.
    ///
    /// `rustc` MIR builds enum values in place as `((_1 as V).0) = x; discriminant(_1) = V;`.
    /// Before `SetDiscriminant` runs, the tag bytes are uninitialized, so an enum shell
    /// narrowed only by `Downcast(v)` field writes is never promoted to an initialized
    /// `MirValue::Adt` (a whole-value read fails with `UninitializedLocal`) and cannot answer
    /// `Rvalue::Discriminant`, even when every field of the variant has been written.
    pub discriminant_set: bool,
    /// Per-field initialization states in declaration order.
    pub fields: Vec<FieldSlot>,
}

impl PartialAggregate {
    /// Creates an all-uninitialized tuple/ADT shell with `field_count` fields and an unwritten
    /// variant tag (`discriminant_set == false`).
    pub fn new_uninit(field_count: usize, variant_idx: usize, is_adt: bool) -> Self {
        PartialAggregate {
            def_path: None,
            variant_idx,
            is_adt,
            discriminant_set: false,
            fields: vec![FieldSlot::Uninit; field_count],
        }
    }

    /// Returns `Some(MirValue)` if every field in `self.fields` is `FieldSlot::Init` and, for
    /// an enum/ADT shell (`is_adt`), the variant tag has been written by `SetDiscriminant`.
    pub fn try_into_mir_value(&self) -> Option<MirValue> {
        if self.is_adt && !self.discriminant_set {
            return None;
        }
        let mut init_fields = Vec::with_capacity(self.fields.len());
        for f in &self.fields {
            match f {
                FieldSlot::Init(v) => init_fields.push(v.clone()),
                FieldSlot::Uninit | FieldSlot::Partial(_) => return None,
            }
        }
        if self.is_adt {
            Some(MirValue::Adt {
                def_path: self.def_path.clone().unwrap_or_default(),
                variant_idx: self.variant_idx,
                active_field: None,
                fields: init_fields,
            })
        } else {
            Some(MirValue::Tuple(init_fields))
        }
    }
}

/// Per-local lifecycle and initialization state for statement-level MIR evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalSlotState {
    /// Local storage is not live (before `StorageLive` or after `StorageDead`).
    Dead,
    /// Local storage is live but completely uninitialized.
    Uninit,
    /// Local holds a partially initialized tuple or ADT shell (`D13b`).
    PartialShell(PartialAggregate),
    /// Local holds a fully initialized `MirValue`.
    Init(MirValue),
}

/// Stateful execution environment for [`eval_lowered_statement`] and [`eval_lowered_block`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatementEvalState {
    /// Declared static types of all locals (`_0.._n`).
    pub local_decls: Vec<Ty>,
    /// Current per-local storage and initialization state (`_0.._n`).
    pub slots: Vec<LocalSlotState>,
    /// Target pointer width (`Bits32` or `Bits64`).
    pub ptr_width: PtrWidth,
    /// Policy governing `Ptr -> Int` transmutes.
    pub policy: TransmutePolicy,
    /// Exposed pointer provenance tracker (`IntPtrCast`).
    pub tracker: ExposedProvenanceTracker,
    /// Value returned by `Rvalue::NullaryOp(NullOp::UbChecks, Ty::Bool)` (defaults to `true`).
    pub ub_checks: bool,
}

/// Type alias for [`StatementEvalState`].
pub type LocalFrame = StatementEvalState;

impl StatementEvalState {
    /// Constructs a `StatementEvalState` with explicit `local_decls`, `slots`, and `ptr_width`
    /// using `TransmutePolicy::RejectPtrToInt` and `ub_checks = true`.
    pub fn new(
        local_decls: Vec<Ty>,
        slots: Vec<LocalSlotState>,
        ptr_width: PtrWidth,
    ) -> Self {
        StatementEvalState {
            local_decls,
            slots,
            ptr_width,
            policy: TransmutePolicy::RejectPtrToInt,
            tracker: ExposedProvenanceTracker::new(),
            ub_checks: true,
        }
    }

    /// Constructs a `StatementEvalState` with an explicit `TransmutePolicy`.
    pub fn with_policy(
        local_decls: Vec<Ty>,
        slots: Vec<LocalSlotState>,
        ptr_width: PtrWidth,
        policy: TransmutePolicy,
    ) -> Self {
        StatementEvalState {
            local_decls,
            slots,
            ptr_width,
            policy,
            tracker: ExposedProvenanceTracker::new(),
            ub_checks: true,
        }
    }

    /// Constructs a `StatementEvalState` in which all declared locals start live and `Uninit`.
    pub fn from_local_decls(local_decls: Vec<Ty>, ptr_width: PtrWidth) -> Self {
        let count = local_decls.len();
        Self::new(local_decls, vec![LocalSlotState::Uninit; count], ptr_width)
    }

    /// Constructs a `StatementEvalState` from a `LoweredBody` and function arguments `args`:
    /// `_0` (`RETURN_PLACE`) starts `Uninit`, `_1..=args.len()` start `Init(arg)`, and
    /// remaining temporaries start `Dead` (awaiting `StorageLive`).
    pub fn from_body(body: &LoweredBody, args: &[MirValue]) -> Result<Self, RvalueEvalError> {
        if body.local_decls.is_empty() || args.len() >= body.local_decls.len() {
            return Err(RvalueEvalError::TypeMismatch(
                "body local_decls must contain return place _0 plus all argument locals",
            ));
        }
        let mut slots = vec![LocalSlotState::Dead; body.local_decls.len()];
        slots[0] = LocalSlotState::Uninit;
        for (i, arg) in args.iter().enumerate() {
            let decl_ty = &body.local_decls[i + 1];
            if !mir_value_matches_ty(arg, decl_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "argument runtime value does not match declared parameter type",
                ));
            }
            slots[i + 1] = LocalSlotState::Init(arg.clone());
        }
        Ok(Self::new(
            body.local_decls.clone(),
            slots,
            body.ptr_width,
        ))
    }

    /// Returns the `LocalSlotState` of `local`, if in bounds.
    pub fn get_local(&self, local: Local) -> Option<&LocalSlotState> {
        self.slots.get(local.0)
    }

    /// Returns the initialized `MirValue` of `local`, if it is in state `LocalSlotState::Init`.
    pub fn get_init(&self, local: Local) -> Option<&MirValue> {
        match self.slots.get(local.0) {
            Some(LocalSlotState::Init(v)) => Some(v),
            _ => None,
        }
    }

    /// Reads an index local as a `usize` bit pattern, returning `DeadLocal` or
    /// `UninitializedLocal` if the index local is not initialized.
    fn read_index_local(&self, idx_local: Local) -> Result<u128, RvalueEvalError> {
        match self.slots.get(idx_local.0) {
            None => Err(RvalueEvalError::TypeMismatch(
                "index local index out of bounds",
            )),
            Some(LocalSlotState::Dead) => Err(RvalueEvalError::DeadLocal(idx_local)),
            Some(LocalSlotState::Uninit | LocalSlotState::PartialShell(_)) => {
                Err(RvalueEvalError::UninitializedLocal(idx_local))
            }
            Some(LocalSlotState::Init(MirValue::Int {
                bits,
                ty: Ty::Uint(UintTy::Usize),
            })) if *bits <= self.ptr_width.max_usize() => Ok(*bits),
            Some(LocalSlotState::Init(_)) => Err(RvalueEvalError::TypeMismatch(
                "array index local must hold a valid usize value",
            )),
        }
    }

    /// Reads the value at `place` from `self.slots` without moving it.
    pub fn read_place(&self, place: &Place) -> Result<MirValue, RvalueEvalError> {
        if place
            .projection
            .iter()
            .any(|p| matches!(p, ProjectionElem::Deref))
        {
            return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
        }
        let read_index = |loc: Local| self.read_index_local(loc);
        match self.slots.get(place.local.0) {
            None => Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
            Some(LocalSlotState::Dead) => Err(RvalueEvalError::DeadLocal(place.local)),
            Some(LocalSlotState::Uninit) => Err(RvalueEvalError::UninitializedLocal(place.local)),
            Some(LocalSlotState::Init(root_val)) => read_projected_mir_value(
                root_val,
                &place.projection,
                &read_index,
                self.ptr_width,
                place,
                None,
            ),
            Some(LocalSlotState::PartialShell(shell)) => read_from_partial_shell(
                shell,
                &place.projection,
                &read_index,
                self.ptr_width,
                place.local,
                place,
                None,
            ),
        }
    }

    /// Reads the value at `place` for `Operand::Move`, matching
    /// `Trusted.MirSemantics.evalOperand` on `.move`:
    /// - a bare local (`place.projection` empty) is read and then becomes
    ///   `LocalSlotState::Uninit`;
    /// - a projected place (`_1.0`, `(_1 as V).0`, `_1[_2]`, ...) is read and the root local's
    ///   slot is left unchanged, so the parent aggregate stays initialized.
    ///
    /// `rustc`'s borrow checker rejects every later use of a moved-from place until it is
    /// re-initialized, so keeping projected move sources initialized only differs from a
    /// deinitializing model on MIR that `rustc` does not emit.
    pub fn move_place(&mut self, place: &Place) -> Result<MirValue, RvalueEvalError> {
        let val = self.read_place(place)?;
        if place.projection.is_empty() {
            self.slots[place.local.0] = LocalSlotState::Uninit;
        }
        Ok(val)
    }

    /// Returns the variant index of the enum shell designated by `place` when `place` resolves,
    /// through `Field` / `Downcast`+`Field` steps over partially initialized shells, to a
    /// [`PartialAggregate`] whose variant tag has been written by `SetDiscriminant`.
    ///
    /// `Rvalue::Discriminant` reads only the tag, so it is defined on such a shell even while
    /// some variant fields are still uninitialized.
    fn tagged_shell_variant(&self, place: &Place) -> Option<usize> {
        let Some(LocalSlotState::PartialShell(root)) = self.slots.get(place.local.0) else {
            return None;
        };
        let shell = partial_shell_at(root, &place.projection, None)?;
        (shell.is_adt && shell.discriminant_set).then_some(shell.variant_idx)
    }

    /// Writes `val` to `place` (of declared leaf type `place_ty`), supporting `D13b` nested
    /// tuple/ADT field-shell initialization while rejecting array-element writes on
    /// uninitialized arrays.
    pub fn write_place(
        &mut self,
        place: &Place,
        place_ty: &Ty,
        val: MirValue,
    ) -> Result<(), RvalueEvalError> {
        if place
            .projection
            .iter()
            .any(|p| matches!(p, ProjectionElem::Deref))
        {
            return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
        }
        let Some(base_decl_ty) = self.local_decls.get(place.local.0).cloned() else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        match self.slots.get(place.local.0) {
            None => return Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
            Some(LocalSlotState::Dead) => return Err(RvalueEvalError::DeadLocal(place.local)),
            _ => {}
        }
        if !mir_value_matches_ty(&val, place_ty) {
            return Err(RvalueEvalError::TypeMismatch(
                "assigned value runtime type does not match destination place type",
            ));
        }
        if place.projection.is_empty() {
            if !mir_value_matches_ty(&val, &base_decl_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "assigned value runtime type does not match local declaration type",
                ));
            }
            self.slots[place.local.0] = LocalSlotState::Init(val);
            return Ok(());
        }

        // Pre-validate any `Index(idx_local)` operands before mutating `self.slots[place.local.0]`.
        let mut index_cache: Vec<(Local, u128)> = Vec::new();
        for elem in &place.projection {
            if let ProjectionElem::Index(idx_local) = elem {
                let bits = self.read_index_local(*idx_local)?;
                index_cache.push((*idx_local, bits));
            }
        }
        let read_index = |idx_local: Local| -> Result<u128, RvalueEvalError> {
            index_cache
                .iter()
                .find_map(|(loc, bits)| (*loc == idx_local).then_some(*bits))
                .ok_or(RvalueEvalError::TypeMismatch(
                    "index local not found in pre-validated cache",
                ))
        };

        let mut root_slot = match &self.slots[place.local.0] {
            LocalSlotState::Dead => return Err(RvalueEvalError::DeadLocal(place.local)),
            LocalSlotState::Uninit => FieldSlot::Uninit,
            LocalSlotState::PartialShell(shell) => FieldSlot::Partial(shell.clone()),
            LocalSlotState::Init(v) => FieldSlot::Init(v.clone()),
        };

        write_to_partial_slot(
            &mut root_slot,
            &base_decl_ty,
            &place.projection,
            val,
            &read_index,
            self.ptr_width,
            place.local,
            place,
            None,
        )?;

        self.slots[place.local.0] = match root_slot {
            FieldSlot::Uninit => LocalSlotState::Uninit,
            FieldSlot::Partial(shell) => {
                if let Some(full_val) = shell.try_into_mir_value() {
                    LocalSlotState::Init(full_val)
                } else {
                    LocalSlotState::PartialShell(shell)
                }
            }
            FieldSlot::Init(v) => LocalSlotState::Init(v),
        };
        Ok(())
    }
}

/// Reads a projected value out of a `PartialAggregate` shell.
fn read_from_partial_shell(
    shell: &PartialAggregate,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    base_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<MirValue, RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        if let Some(full_val) = shell.try_into_mir_value() {
            return Ok(full_val);
        }
        return Err(RvalueEvalError::UninitializedLocal(base_local));
    };

    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Downcast(expected_variant) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "consecutive Downcast projections without Field",
                ));
            }
            if let Some(next) = rest.first() {
                if matches!(next, ProjectionElem::Deref) {
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(
                        full_place.clone(),
                    ));
                }
                if !matches!(next, ProjectionElem::Field(..)) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast projection must be followed by Field",
                    ));
                }
            }
            let actual = if shell.is_adt { shell.variant_idx } else { 0 };
            if actual != *expected_variant {
                return Err(RvalueEvalError::InactiveVariantProjection {
                    expected: *expected_variant,
                    actual,
                });
            }
            read_from_partial_shell(
                shell,
                rest,
                read_index,
                ptr_width,
                base_local,
                full_place,
                Some(*expected_variant),
            )
        }
        ProjectionElem::Field(idx, expected_ty) => {
            let expected_variant = active_downcast.unwrap_or(0);
            let actual = if shell.is_adt { shell.variant_idx } else { 0 };
            if actual != expected_variant {
                return Err(RvalueEvalError::InactiveVariantProjection {
                    expected: expected_variant,
                    actual,
                });
            }
            let Some(field_slot) = shell.fields.get(*idx) else {
                return Err(RvalueEvalError::FieldOutOfBounds {
                    field_idx: *idx,
                    field_count: shell.fields.len(),
                });
            };
            match field_slot {
                FieldSlot::Uninit => Err(RvalueEvalError::UninitializedLocal(base_local)),
                FieldSlot::Partial(child_shell) => read_from_partial_shell(
                    child_shell,
                    rest,
                    read_index,
                    ptr_width,
                    base_local,
                    full_place,
                    None,
                ),
                FieldSlot::Init(field_val) => {
                    if !mir_value_matches_ty(field_val, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected field runtime type does not match expected type",
                        ));
                    }
                    read_projected_mir_value(
                        field_val,
                        rest,
                        read_index,
                        ptr_width,
                        full_place,
                        None,
                    )
                }
            }
        }
        // Shells only model tuple/struct/enum-variant values, so an array projection directly on
        // a shell is a static type error, not an uninitialized read.
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => Err(RvalueEvalError::TypeMismatch(
            "array projection applied to a partially initialized tuple/ADT shell",
        )),
    }
}

/// Follows a pure `Field` / `Downcast`+`Field` chain through nested partially initialized
/// shells and returns the shell that `proj` designates, or `None` if `proj` reaches an
/// initialized or uninitialized field slot, selects an inactive variant, ends in `Downcast`,
/// or contains any other projection.
fn partial_shell_at<'a>(
    shell: &'a PartialAggregate,
    proj: &[ProjectionElem],
    active_downcast: Option<usize>,
) -> Option<&'a PartialAggregate> {
    let Some((first, rest)) = proj.split_first() else {
        return active_downcast.is_none().then_some(shell);
    };
    let actual = if shell.is_adt { shell.variant_idx } else { 0 };
    match first {
        ProjectionElem::Downcast(v) if active_downcast.is_none() && actual == *v => {
            partial_shell_at(shell, rest, Some(*v))
        }
        ProjectionElem::Field(idx, _) if actual == active_downcast.unwrap_or(0) => {
            match shell.fields.get(*idx)? {
                FieldSlot::Partial(child) => partial_shell_at(child, rest, None),
                FieldSlot::Uninit | FieldSlot::Init(_) => None,
            }
        }
        _ => None,
    }
}

/// Writes `new_val` along `proj` into `slot` of declared type `declared_ty`, materializing
/// `PartialAggregate` shells only for `Ty::Tuple` field writes (`D13b`) and rejecting array
/// element writes on uninitialized arrays (`c6d2ad74`).
#[allow(clippy::too_many_arguments)]
fn write_to_partial_slot(
    slot: &mut FieldSlot,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    new_val: MirValue,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    base_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    if proj.is_empty() {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection in write must be followed by Field",
            ));
        }
        if !mir_value_matches_ty(&new_val, declared_ty) {
            return Err(RvalueEvalError::TypeMismatch(
                "assigned value runtime type does not match declared field type",
            ));
        }
        *slot = FieldSlot::Init(new_val);
        return Ok(());
    }

    if let FieldSlot::Init(existing_val) = slot {
        return write_projected_mir_value(
            existing_val,
            proj,
            new_val,
            read_index,
            ptr_width,
            full_place,
            active_downcast,
        );
    }

    let (first, rest) = proj.split_first().unwrap();
    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Downcast(expected_variant) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "consecutive Downcast projections without Field",
                ));
            }
            if !matches!(rest.first(), Some(ProjectionElem::Field(..))) {
                if matches!(rest.first(), Some(ProjectionElem::Deref)) {
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(
                        full_place.clone(),
                    ));
                }
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let Ty::Tuple(field_tys) = declared_ty else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection requires a tuple-typed (ADT) place",
                ));
            };
            match slot {
                FieldSlot::Uninit => {
                    *slot = FieldSlot::Partial(PartialAggregate::new_uninit(
                        field_tys.len(),
                        *expected_variant,
                        true,
                    ));
                }
                FieldSlot::Partial(shell) => {
                    let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                    if actual != *expected_variant {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual,
                        });
                    }
                }
                FieldSlot::Init(_) => unreachable!(),
            }
            write_to_partial_slot(
                slot,
                declared_ty,
                rest,
                new_val,
                read_index,
                ptr_width,
                base_local,
                full_place,
                Some(*expected_variant),
            )
        }
        ProjectionElem::Field(idx, expected_ty) => {
            let Ty::Tuple(field_tys) = declared_ty else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Field projection requires a tuple-typed place",
                ));
            };
            if *idx >= field_tys.len() {
                return Err(RvalueEvalError::FieldOutOfBounds {
                    field_idx: *idx,
                    field_count: field_tys.len(),
                });
            }
            if field_tys[*idx] != *expected_ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "projected field type does not match declared tuple field type",
                ));
            }
            if matches!(slot, FieldSlot::Uninit) {
                *slot = FieldSlot::Partial(PartialAggregate::new_uninit(
                    field_tys.len(),
                    active_downcast.unwrap_or(0),
                    active_downcast.is_some(),
                ));
            }
            let FieldSlot::Partial(shell) = slot else {
                unreachable!()
            };
            let expected_variant = active_downcast.unwrap_or(0);
            let actual = if shell.is_adt { shell.variant_idx } else { 0 };
            if actual != expected_variant {
                return Err(RvalueEvalError::InactiveVariantProjection {
                    expected: expected_variant,
                    actual,
                });
            }
            if shell.fields.len() != field_tys.len() {
                return Err(RvalueEvalError::TypeMismatch(
                    "partial shell field count does not match declared tuple type",
                ));
            }
            write_to_partial_slot(
                &mut shell.fields[*idx],
                &field_tys[*idx],
                rest,
                new_val,
                read_index,
                ptr_width,
                base_local,
                full_place,
                None,
            )?;
            if let Some(full_val) = shell.try_into_mir_value() {
                *slot = FieldSlot::Init(full_val);
            }
            Ok(())
        }
        // `c6d2ad74`: an element or window write into an uninitialized array is undefined
        // behavior (no array shell is ever materialized). An array projection on a
        // tuple/ADT shell or a non-array declared type is a static type error.
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => match (slot, declared_ty) {
            (FieldSlot::Uninit, Ty::Array(_, _)) => {
                Err(RvalueEvalError::UninitializedLocal(base_local))
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "array projection applied to a non-array place",
            )),
        },
    }
}

/// Updates the discriminant of a target `FieldSlot` at `proj` for `Statement::SetDiscriminant`.
fn set_discriminant_in_slot(
    slot: &mut FieldSlot,
    proj: &[ProjectionElem],
    variant_index: usize,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    base_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    if proj.is_empty() {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "SetDiscriminant target cannot end with Downcast",
            ));
        }
        match slot {
            FieldSlot::Uninit => Err(RvalueEvalError::UninitializedLocal(base_local)),
            FieldSlot::Partial(shell) => {
                shell.variant_idx = variant_index;
                shell.is_adt = true;
                shell.discriminant_set = true;
                if let Some(full_val) = shell.try_into_mir_value() {
                    *slot = FieldSlot::Init(full_val);
                }
                Ok(())
            }
            FieldSlot::Init(MirValue::Adt {
                variant_idx,
                active_field: None,
                ..
            }) => {
                *variant_idx = variant_index;
                Ok(())
            }
            FieldSlot::Init(MirValue::Tuple(fields)) => {
                let moved = std::mem::take(fields);
                *slot = FieldSlot::Init(MirValue::Adt {
                    def_path: String::new(),
                    variant_idx: variant_index,
                    active_field: None,
                    fields: moved,
                });
                Ok(())
            }
            FieldSlot::Init(_) => Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone())),
        }
    } else if let FieldSlot::Init(existing_val) = slot {
        // Read the target sub-value, update its discriminant, and write it back.
        let sub_val = read_projected_mir_value(
            existing_val,
            proj,
            read_index,
            ptr_width,
            full_place,
            active_downcast,
        )?;
        let updated_sub = match sub_val {
            MirValue::Adt {
                def_path,
                active_field: None,
                fields,
                ..
            } => MirValue::Adt {
                def_path,
                variant_idx: variant_index,
                active_field: None,
                fields,
            },
            MirValue::Tuple(fields) => MirValue::Adt {
                def_path: String::new(),
                variant_idx: variant_index,
                active_field: None,
                fields,
            },
            _ => return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone())),
        };
        write_projected_mir_value(
            existing_val,
            proj,
            updated_sub,
            read_index,
            ptr_width,
            full_place,
            active_downcast,
        )
    } else {
        let (first, rest) = proj.split_first().unwrap();
        let res = match (&mut *slot, first) {
            (_, ProjectionElem::Deref) => Err(RvalueEvalError::UnsupportedPlaceProjection(
                full_place.clone(),
            )),
            (FieldSlot::Uninit, _) => Err(RvalueEvalError::UninitializedLocal(base_local)),
            (FieldSlot::Partial(shell), ProjectionElem::Downcast(expected_variant)) => {
                if active_downcast.is_some() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "consecutive Downcast projections",
                    ));
                }
                let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                if actual != *expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: *expected_variant,
                        actual,
                    });
                }
                let mut temp = FieldSlot::Partial(shell.clone());
                set_discriminant_in_slot(
                    &mut temp,
                    rest,
                    variant_index,
                    read_index,
                    ptr_width,
                    base_local,
                    full_place,
                    Some(*expected_variant),
                )?;
                if let FieldSlot::Partial(updated_shell) = temp {
                    *shell = updated_shell;
                }
                Ok(())
            }
            (FieldSlot::Partial(shell), ProjectionElem::Field(idx, _)) => {
                let expected_variant = active_downcast.unwrap_or(0);
                let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                if actual != expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: expected_variant,
                        actual,
                    });
                }
                let field_count = shell.fields.len();
                let Some(child_slot) = shell.fields.get_mut(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count,
                    });
                };
                set_discriminant_in_slot(
                    child_slot,
                    rest,
                    variant_index,
                    read_index,
                    ptr_width,
                    base_local,
                    full_place,
                    None,
                )
            }
            // A shell is a tuple/struct/enum-variant value: an array projection on it is a
            // static type error.
            (FieldSlot::Partial(_), _) => Err(RvalueEvalError::TypeMismatch(
                "array projection applied to a partially initialized tuple/ADT shell",
            )),
            (FieldSlot::Init(_), _) => unreachable!(),
        };
        res?;
        if let FieldSlot::Partial(shell) = slot {
            if let Some(full_val) = shell.try_into_mir_value() {
                *slot = FieldSlot::Init(full_val);
            }
        }
        Ok(())
    }
}

/// Evaluates a `LoweredRvalue` in a stateful [`StatementEvalState`], respecting
/// `LocalSlotState` (`Dead`, `Uninit`, `PartialShell`, `Init`).
///
/// Operands are evaluated left to right. `Operand::Move` of a bare local leaves that local
/// `Uninit` for every later operand; `Operand::Move` of a projected place leaves the root
/// local unchanged (see [`StatementEvalState::move_place`]).
pub fn eval_lowered_rvalue_in_state(
    rvalue: &LoweredRvalue,
    state: &mut StatementEvalState,
) -> Result<MirValue, RvalueEvalError> {
    let eval_op = |op: &Operand, st: &mut StatementEvalState| -> Result<MirValue, RvalueEvalError> {
        match op {
            Operand::Copy(place) => st.read_place(place),
            Operand::Move(place) => st.move_place(place),
            Operand::Constant(c) => eval_constant(c, st.ptr_width),
        }
    };

    match rvalue {
        LoweredRvalue::Use { operand, .. } => eval_op(operand, state),
        LoweredRvalue::Repeat {
            operand,
            count,
            elem_ty,
            ..
        } => {
            if *count > MAX_EVAL_ARRAY_LEN {
                return Err(RvalueEvalError::EvaluationLimit { len: *count });
            }
            let v = eval_op(operand, state)?;
            if !mir_value_matches_ty(&v, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Repeat operand runtime type does not match element type",
                ));
            }
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
                    match state.slots.get(place.local.0) {
                        None => {
                            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
                        }
                        Some(LocalSlotState::Dead) => {
                            return Err(RvalueEvalError::DeadLocal(place.local));
                        }
                        Some(
                            LocalSlotState::Uninit
                            | LocalSlotState::PartialShell(_)
                            | LocalSlotState::Init(_),
                        ) => {}
                    }
                    let addr = ((place.local.0 as u128 + 1) * 0x1000) & state.ptr_width.mask();
                    PointerValue::with_provenance(addr as u64, place.local.0 as u64 + 1, 1)
                }
                [ProjectionElem::Deref] => match state.read_place(&Place::from_local(place.local.0))? {
                    MirValue::Ptr { ptr, ty } => {
                        if !ty.is_any_ptr() || ty.pointee_ty() != ref_ty.pointee_ty() {
                            return Err(RvalueEvalError::TypeMismatch(
                                "Deref projection requires a pointer value with matching pointee type",
                            ));
                        }
                        let masked_addr = (u128::from(ptr.addr) & state.ptr_width.mask()) as u64;
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
        LoweredRvalue::Len {
            place,
            static_len,
            ty,
        } => {
            if *ty != Ty::Uint(UintTy::Usize) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len result type must be usize",
                ));
            }
            let val = state.read_place(place)?;
            let MirValue::Array { elements, .. } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len target runtime value must be MirValue::Array",
                ));
            };
            if elements.len() != *static_len {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len target array length does not match static_len",
                ));
            }
            Ok(MirValue::unsigned(
                *static_len as u128,
                UintTy::Usize,
                state.ptr_width,
            ))
        }
        LoweredRvalue::Cast { cast, .. } => {
            let op = match cast {
                LoweredCast::PtrToInt { operand, .. }
                | LoweredCast::IntToPtr { operand, .. }
                | LoweredCast::IntToInt { operand, .. }
                | LoweredCast::CharToInt { operand, .. }
                | LoweredCast::PtrToPtr { operand, .. }
                | LoweredCast::Transmute { operand, .. } => operand,
            };
            let v = eval_op(op, state)?;
            eval_lowered_cast(cast, &v, state.ptr_width, state.policy, &mut state.tracker)
        }
        LoweredRvalue::BinaryOp { op, lhs, rhs, .. } => {
            let lv = eval_op(lhs, state)?;
            let rv = eval_op(rhs, state)?;
            eval_binop(*op, &lv, &rv, state.ptr_width)
        }
        LoweredRvalue::CheckedBinaryOp {
            op,
            lhs,
            rhs,
            lhs_ty,
            rhs_ty,
            ..
        } => {
            let lv = eval_op(lhs, state)?;
            let rv = eval_op(rhs, state)?;
            if lv.ty() != *lhs_ty || rv.ty() != *rhs_ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "CheckedBinaryOp operand runtime types do not match lowered types",
                ));
            }
            let (wrapped, overflowed) = eval_checked_binop(*op, &lv, &rv, state.ptr_width)?;
            Ok(MirValue::Tuple(vec![
                MirValue::Int {
                    bits: wrapped,
                    ty: lhs_ty.clone(),
                },
                MirValue::Bool(overflowed),
            ]))
        }
        LoweredRvalue::NullaryOp { op, arg_ty, ty } => {
            let val = if matches!(op, NullOp::UbChecks) {
                if *arg_ty != Ty::Bool {
                    return Err(RvalueEvalError::TypeMismatch(
                        "NullOp::UbChecks requires Ty::Bool",
                    ));
                }
                MirValue::Bool(state.ub_checks)
            } else {
                eval_nullary_op(op, arg_ty, state.ptr_width)?
            };
            if val.ty() != *ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "NullaryOp result type does not match lowered ty",
                ));
            }
            Ok(val)
        }
        LoweredRvalue::UnaryOp { op, operand, .. } => {
            let v = eval_op(operand, state)?;
            eval_unop(*op, &v, state.ptr_width)
        }
        LoweredRvalue::Discriminant { place, .. } => {
            let discr = match state.read_place(place) {
                Ok(MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    ..
                }) => variant_idx as i128,
                Ok(_) => 0,
                Err(err @ RvalueEvalError::UninitializedLocal(_)) => {
                    // `Rvalue::Discriminant` reads only the variant tag: an enum shell (bare or
                    // nested) whose tag was written by `SetDiscriminant` has a defined
                    // discriminant even while some of its variant fields are uninitialized. A
                    // shell narrowed only by `Downcast` writes has an unwritten tag.
                    match state.tagged_shell_variant(place) {
                        Some(variant_idx) => variant_idx as i128,
                        None => return Err(err),
                    }
                }
                Err(e) => return Err(e),
            };
            Ok(MirValue::signed(discr, IntTy::Isize, state.ptr_width))
        }
        LoweredRvalue::Aggregate { kind, operands, .. } => {
            let mut vals = Vec::with_capacity(operands.len());
            for op in operands {
                vals.push(eval_op(op, state)?);
            }
            eval_aggregate(kind, vals, state.ptr_width)
        }
        LoweredRvalue::CopyForDeref { place, ty } => match state.read_place(place)? {
            MirValue::Ptr { ptr, ty: val_ty } if val_ty == *ty && ty.is_any_ptr() => {
                let masked_addr = (u128::from(ptr.addr) & state.ptr_width.mask()) as u64;
                if ty.is_ref() && masked_addr == 0 {
                    return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                        target_ty: ty.clone(),
                        bits: 0,
                    }));
                }
                Ok(MirValue::Ptr {
                    ptr: PointerValue {
                        addr: masked_addr,
                        provenance: ptr.provenance,
                    },
                    ty: ty.clone(),
                })
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "CopyForDeref requires a pointer value matching the place type",
            )),
        },
    }
}

/// Evaluates a single `LoweredStatement` in `state`.
///
/// Faithfully models:
/// - `Nop`: no-op.
/// - `StorageLive(loc)` / `StorageDead(loc)`: transitions `state.slots[loc.0]` to `Uninit` / `Dead`.
/// - `PlaceMention { place, .. }` (`D9`): requires `place.local` to not be `Dead`, validates that
///   every `ProjectionElem::Index(idx_loc)` local is an initialized `usize`, and when
///   `place.projection` contains `ProjectionElem::Deref` requires the pointer prefix before
///   `Deref` to evaluate to a valid initialized pointer without loading the target place.
/// - `Assume { operand }`: evaluates `operand` (including `Move`) and requires `MirValue::Bool(true)`,
///   returning `Err(RvalueEvalError::AssumeFalse)` on `false`.
/// - `SetDiscriminant { place, variant_index, .. }`: updates `variant_idx` on an initialized
///   `Adt`/`Tuple` or `PartialShell` at `place`, failing closed on `Dead`, `Uninit`, or
///   non-aggregate places (`Trusted.MirSemantics.Statements.evalStmt`). On a `PartialShell` it
///   also records that the variant tag is written ([`PartialAggregate::discriminant_set`]),
///   which is required before an enum shell can be read as a whole value.
/// - `Assign { place, place_ty, rvalue }`: evaluates `rvalue` first (including `Operand::Move`),
///   then writes `place` (reading any `Index` locals of `place` *after* the rvalue, as
///   `evalStmt` writes the destination in the post-rvalue locals), supporting `D13b` nested
///   tuple/ADT field initialization while rejecting array-element writes on uninitialized
///   arrays (`c6d2ad74`).
///
/// `Operand::Move` follows `Trusted.MirSemantics.evalOperand`: moving a bare local leaves it
/// `Uninit`, while moving a projected place leaves the root local unchanged.
pub fn eval_lowered_statement(
    stmt: &LoweredStatement,
    state: &mut StatementEvalState,
) -> Result<(), RvalueEvalError> {
    match stmt {
        LoweredStatement::Nop => Ok(()),
        LoweredStatement::StorageLive(loc) => {
            if loc.0 >= state.slots.len() || loc.0 >= state.local_decls.len() {
                return Err(RvalueEvalError::TypeMismatch(
                    "StorageLive local index out of bounds",
                ));
            }
            state.slots[loc.0] = LocalSlotState::Uninit;
            Ok(())
        }
        LoweredStatement::StorageDead(loc) => {
            if loc.0 >= state.slots.len() || loc.0 >= state.local_decls.len() {
                return Err(RvalueEvalError::TypeMismatch(
                    "StorageDead local index out of bounds",
                ));
            }
            state.slots[loc.0] = LocalSlotState::Dead;
            Ok(())
        }
        LoweredStatement::PlaceMention { place, .. } => {
            match state.slots.get(place.local.0) {
                None => return Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
                Some(LocalSlotState::Dead) => return Err(RvalueEvalError::DeadLocal(place.local)),
                Some(_) => {}
            }
            // Validate every `Index(idx_local)` operand read while computing `place`.
            for elem in &place.projection {
                if let ProjectionElem::Index(idx_local) = elem {
                    let _ = state.read_index_local(*idx_local)?;
                }
            }
            // If `place.projection` contains `Deref`, the pointer sub-place before the first
            // `Deref` is read to compute the dereferenced place's address (`D9`).
            if let Some(first_deref_pos) = place
                .projection
                .iter()
                .position(|p| matches!(p, ProjectionElem::Deref))
            {
                if place.projection[first_deref_pos + 1..]
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref))
                {
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
                }
                let ptr_place = Place {
                    local: place.local,
                    projection: place.projection[..first_deref_pos].to_vec(),
                };
                let ptr_val = state.read_place(&ptr_place)?;
                match ptr_val {
                    MirValue::Ptr { ptr, ty } if ty.is_any_ptr() => {
                        let masked_addr = (u128::from(ptr.addr) & state.ptr_width.mask()) as u64;
                        if ty.is_ref() && masked_addr == 0 {
                            return Err(RvalueEvalError::CastEval(
                                CastEvalError::InvalidBitPattern {
                                    target_ty: ty,
                                    bits: 0,
                                },
                            ));
                        }
                    }
                    _ => {
                        return Err(RvalueEvalError::TypeMismatch(
                            "PlaceMention Deref requires an initialized pointer value",
                        ));
                    }
                }
            }
            Ok(())
        }
        LoweredStatement::Assume { operand } => {
            let val = match operand {
                Operand::Copy(place) => state.read_place(place)?,
                Operand::Move(place) => state.move_place(place)?,
                Operand::Constant(c) => eval_constant(c, state.ptr_width)?,
            };
            match val {
                MirValue::Bool(true) => Ok(()),
                MirValue::Bool(false) => Err(RvalueEvalError::AssumeFalse),
                _ => Err(RvalueEvalError::TypeMismatch(
                    "Statement::Assume requires MirValue::Bool operand",
                )),
            }
        }
        LoweredStatement::SetDiscriminant {
            place,
            variant_index,
            ..
        } => {
            if place
                .projection
                .iter()
                .any(|p| matches!(p, ProjectionElem::Deref))
            {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
            }
            let mut index_cache: Vec<(Local, u128)> = Vec::new();
            for elem in &place.projection {
                if let ProjectionElem::Index(idx_local) = elem {
                    let bits = state.read_index_local(*idx_local)?;
                    index_cache.push((*idx_local, bits));
                }
            }
            let read_index = |idx_local: Local| -> Result<u128, RvalueEvalError> {
                index_cache
                    .iter()
                    .find_map(|(loc, bits)| (*loc == idx_local).then_some(*bits))
                    .ok_or(RvalueEvalError::TypeMismatch(
                        "index local not found in pre-validated cache",
                    ))
            };
            let mut root_slot = match state.slots.get(place.local.0) {
                None => return Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
                Some(LocalSlotState::Dead) => return Err(RvalueEvalError::DeadLocal(place.local)),
                Some(LocalSlotState::Uninit) => FieldSlot::Uninit,
                Some(LocalSlotState::PartialShell(shell)) => FieldSlot::Partial(shell.clone()),
                Some(LocalSlotState::Init(v)) => FieldSlot::Init(v.clone()),
            };
            set_discriminant_in_slot(
                &mut root_slot,
                &place.projection,
                *variant_index,
                &read_index,
                state.ptr_width,
                place.local,
                place,
                None,
            )?;
            state.slots[place.local.0] = match root_slot {
                FieldSlot::Uninit => LocalSlotState::Uninit,
                FieldSlot::Partial(shell) => {
                    if let Some(full_val) = shell.try_into_mir_value() {
                        LocalSlotState::Init(full_val)
                    } else {
                        LocalSlotState::PartialShell(shell)
                    }
                }
                FieldSlot::Init(v) => LocalSlotState::Init(v),
            };
            Ok(())
        }
        LoweredStatement::Assign {
            place,
            place_ty,
            rvalue,
        } => {
            let val = eval_lowered_rvalue_in_state(rvalue, state)?;
            state.write_place(place, place_ty, val)
        }
    }
}

/// Evaluates all statements of a `LoweredBasicBlock` sequentially in `state`.
pub fn eval_lowered_block(
    block: &LoweredBasicBlock,
    state: &mut StatementEvalState,
) -> Result<(), RvalueEvalError> {
    for stmt in &block.statements {
        eval_lowered_statement(stmt, state)?;
    }
    Ok(())
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
