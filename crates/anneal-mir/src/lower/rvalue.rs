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
use std::sync::Arc;

use crate::ir::{
    AdtDef, AdtKind, AggregateKind, BasicBlockData, BinOp, Body, Constant, IntTy, LayoutError,
    Local, Mutability, NullOp, Operand, Place, PointerValue, ProjectionElem, PtrWidth,
    RetagKind, Rvalue, Statement, Ty, UintTy, UnOp,
};
use crate::lower::cast::{
    AbstractByte, CastEvalError, CastLowerError, ExposedProvenanceTracker, LoweredCast,
    TransmutePolicy, TransmuteValue, canonical_untagged_fields, cast_eval_layout_error,
    decode_int_bytes, decode_ptr_bytes, encode_int_bytes, encode_ptr_bytes,
    eval_char_to_int, eval_int_to_int, eval_int_to_ptr_with_ptr_width,
    eval_ptr_to_int_with_ptr_width, eval_transmute, is_valid_pointer_coercion,
    lower_cast_rvalue_with_ptr_width,
};
use crate::lower::cfg::{LoweredTerminator, TerminatorLowerError, lower_terminator};

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
    /// A type contains an ill-formed [`AdtDef`] (see [`LayoutError::IllFormed`]).
    InvalidAdtDef {
        ty: Ty,
        reason: &'static str,
    },
    /// An operation needs the exact layout of a type whose layout is unspecified (see
    /// [`LayoutError::Unspecified`]).
    UnsupportedLayout(Ty),
    /// Variant index out of range for an ADT (`SetDiscriminant`, aggregates, `Downcast`).
    InvalidVariantIndex {
        ty: Ty,
        variant_index: usize,
    },
    /// `Statement::Retag(Raw(m), place)` on a place that is not a raw pointer of mutability `m`.
    InvalidRetagTarget {
        kind: RetagKind,
        ty: Ty,
    },
    /// `Statement::CopyNonOverlapping` operands are not `*const T` / `*mut T` / `usize`.
    InvalidCopyNonOverlapping {
        src_ty: Ty,
        dst_ty: Ty,
        count_ty: Ty,
    },
    /// `Rvalue::ShallowInitBox` with a non-raw-pointer operand.
    InvalidShallowInitBox {
        operand_ty: Ty,
        inner_ty: Ty,
    },
    /// `Rvalue::WrapUnsafeBinder` whose binder type does not wrap the operand type.
    InvalidWrapUnsafeBinder {
        operand_ty: Ty,
        binder_ty: Ty,
    },
    /// Ill-formed terminator of basic block `bb`.
    InvalidTerminator {
        bb: usize,
        error: TerminatorLowerError,
    },
}

/// Maps a [`LayoutError`] of `ty` to the corresponding [`RvalueLowerError`].
pub(crate) fn lower_layout_error(ty: &Ty, err: LayoutError) -> RvalueLowerError {
    match err {
        LayoutError::TooLarge => RvalueLowerError::LayoutTooLarge(ty.clone()),
        LayoutError::Unspecified => RvalueLowerError::UnsupportedLayout(ty.clone()),
        LayoutError::IllFormed(reason) => RvalueLowerError::InvalidAdtDef {
            ty: ty.clone(),
            reason,
        },
    }
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
            RvalueLowerError::InvalidAdtDef { ty, reason } => {
                write!(f, "ill-formed ADT in type {ty:?}: {reason}")
            }
            RvalueLowerError::UnsupportedLayout(ty) => {
                write!(f, "type {ty:?} has an unspecified layout")
            }
            RvalueLowerError::InvalidVariantIndex { ty, variant_index } => {
                write!(f, "variant index {variant_index} out of range for {ty:?}")
            }
            RvalueLowerError::InvalidRetagTarget { kind, ty } => {
                write!(f, "Retag({kind:?}) applied to place of type {ty:?}")
            }
            RvalueLowerError::InvalidCopyNonOverlapping {
                src_ty,
                dst_ty,
                count_ty,
            } => {
                write!(
                    f,
                    "copy_nonoverlapping requires (*const T, *mut T, usize), got ({src_ty:?}, {dst_ty:?}, {count_ty:?})"
                )
            }
            RvalueLowerError::InvalidShallowInitBox {
                operand_ty,
                inner_ty,
            } => {
                write!(
                    f,
                    "ShallowInitBox of {inner_ty:?} requires a raw pointer operand, got {operand_ty:?}"
                )
            }
            RvalueLowerError::InvalidWrapUnsafeBinder {
                operand_ty,
                binder_ty,
            } => {
                write!(f, "WrapUnsafeBinder type {binder_ty:?} does not wrap {operand_ty:?}")
            }
            RvalueLowerError::InvalidTerminator { bb, error } => {
                write!(f, "invalid terminator in bb{bb}: {error}")
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
    /// `ShallowInitBox(operand, inner)` typed `*mut inner`.
    ShallowInitBox {
        operand: Operand,
        operand_ty: Ty,
        ty: Ty,
    },
    /// `WrapUnsafeBinder(operand, ty)`.
    WrapUnsafeBinder {
        operand: Operand,
        operand_ty: Ty,
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
            | LoweredRvalue::CopyForDeref { ty, .. }
            | LoweredRvalue::ShallowInitBox { ty, .. }
            | LoweredRvalue::WrapUnsafeBinder { ty, .. } => ty,
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
    /// `Deinit(place)` of declared type `place_ty`.
    Deinit {
        place: Place,
        place_ty: Ty,
    },
    /// `Retag(kind, place)` of declared type `place_ty`.
    Retag {
        kind: RetagKind,
        place: Place,
        place_ty: Ty,
    },
    /// `copy_nonoverlapping::<elem_ty>(src, dst, count)` with `elem_ty`'s exact layout.
    CopyNonOverlapping {
        src: Operand,
        dst: Operand,
        count: Operand,
        elem_ty: Ty,
        elem_size: usize,
        elem_align: usize,
    },
}

/// Lowered representation of a MIR basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweredBasicBlock {
    pub statements: Vec<LoweredStatement>,
    /// Lowered terminator (`None` when the captured block has no terminator).
    pub terminator: Option<LoweredTerminator>,
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
///
/// On a `Ty::Adt`, `Field(i, ty)` selects field `i` of a struct or union, and of variant `v`
/// of an enum only directly after `Downcast(v)` (with `v` in range); `Downcast` is invalid on
/// structs and unions.
pub fn resolve_place_ty(place: &Place, local_decls: &[Ty]) -> Result<Ty, RvalueLowerError> {
    let Some(base_ty) = local_decls.get(place.local.0) else {
        return Err(RvalueLowerError::UnknownLocal(place.local));
    };
    let mut cur_ty = base_ty.clone();
    let mut downcast: Option<usize> = None;

    for (i, elem) in place.projection.iter().enumerate() {
        let invalid = |current_ty: Ty| RvalueLowerError::InvalidProjection {
            place: place.clone(),
            current_ty,
            elem: elem.clone(),
        };
        cur_ty = match (elem, cur_ty) {
            (ProjectionElem::Deref, Ty::RawPtr(inner, _) | Ty::Ref(inner, _)) => *inner,
            (ProjectionElem::Field(idx, field_ty), ty @ (Ty::Tuple(_) | Ty::Adt(_))) => {
                if projectable_field_tys(&ty, downcast).and_then(|fields| fields.get(*idx))
                    != Some(field_ty)
                {
                    return Err(invalid(ty));
                }
                downcast = None;
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
            (ProjectionElem::Downcast(v), ty @ (Ty::Tuple(_) | Ty::Adt(_))) => {
                if !matches!(place.projection.get(i + 1), Some(ProjectionElem::Field(..)))
                    || !downcast_allowed(&ty, *v)
                {
                    return Err(invalid(ty));
                }
                downcast = Some(*v);
                ty
            }
            (_, other) => return Err(invalid(other)),
        };
    }

    Ok(cur_ty)
}

/// Field types that a `Field` projection selects from a place of type `ty` after an optional
/// `Downcast(variant)`: a tuple's fields (the legacy ADT model, any downcast), a struct's or
/// union's fields (no downcast), or the fields of the downcast variant of an enum.
pub(crate) fn projectable_field_tys(ty: &Ty, downcast: Option<usize>) -> Option<&[Ty]> {
    match (ty, downcast) {
        (Ty::Tuple(fields), _) => Some(fields),
        (Ty::Adt(def), None) if !def.is_enum() => def.variant_fields(0),
        (Ty::Adt(def), Some(variant)) if def.is_enum() => def.variant_fields(variant),
        _ => None,
    }
}

/// Returns true if `Downcast(variant)` is statically valid on a place of type `ty`: any variant
/// of a legacy tuple-modeled ADT, or an in-range variant of an enum `Ty::Adt`.
pub(crate) fn downcast_allowed(ty: &Ty, variant: usize) -> bool {
    match ty {
        Ty::Tuple(_) => true,
        Ty::Adt(def) => def.is_enum() && variant < def.variant_count(),
        _ => false,
    }
}

/// Field types of a union-typed place: a legacy union modeled as the `Ty::Tuple` of its
/// fields, or a union `Ty::Adt`.
fn union_fields_of(ty: &Ty) -> Option<&[Ty]> {
    match ty {
        Ty::Tuple(fields) => Some(fields),
        Ty::Adt(def) if def.is_union() => def.variant_fields(0),
        _ => None,
    }
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
pub(crate) fn lower_operand_ty(
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
///
/// ADTs must be well-formed (`InvalidAdtDef` otherwise); unspecified ADT layouts are
/// representable (see [`Ty::check_representable`]).
fn check_layout(ty: Ty, ptr_width: PtrWidth) -> Result<Ty, RvalueLowerError> {
    if let Err(err) = ty.check_representable(ptr_width) {
        return Err(lower_layout_error(&ty, err));
    }
    Ok(ty)
}

/// Resolves the byte offset of `fields` (`(variant_idx, field_idx)` chain) inside `arg_ty`
/// under `ptr_width`.
///
/// Requires `arg_ty` to have a representable layout ([`Ty::layout_size_for`]) and every
/// projected container to be a `Ty::Tuple` with a canonical byte layout
/// ([`Ty::has_canonical_byte_layout`]), `variant_idx == 0`, and `field_idx < fields.len()`.
///
/// A projected `Ty::Adt` container follows [`AdtDef::field_offset`]: `variant_idx` must select
/// an existing variant (`0` for structs and unions) and `field_idx` one of its fields; an
/// unspecified offset fails with `UnsupportedOffsetOfLayout(container)`. Every `Ok(off)` step
/// satisfies `off + size_of(field) <= size_of(container)` and `off % align_of(field) == 0`.
pub fn resolve_offset_of(
    arg_ty: &Ty,
    fields: &[(usize, usize)],
    ptr_width: PtrWidth,
) -> Result<usize, RvalueLowerError> {
    check_layout(arg_ty.clone(), ptr_width)?;
    let mut cur_ty = arg_ty;
    let mut total_offset = 0usize;
    for &(variant_idx, field_idx) in fields {
        let invalid_step = |container_ty: &Ty| RvalueLowerError::InvalidOffsetOfField {
            container_ty: container_ty.clone(),
            variant_idx,
            field_idx,
        };
        if let Ty::Adt(def) = cur_ty {
            let Some(variant_fields) = def.variant_fields(variant_idx) else {
                return Err(invalid_step(cur_ty));
            };
            if field_idx >= variant_fields.len() {
                return Err(invalid_step(cur_ty));
            }
            let offset = def
                .field_offset(variant_idx, field_idx, ptr_width)
                .map_err(|err| match err {
                    LayoutError::TooLarge => RvalueLowerError::LayoutTooLarge(arg_ty.clone()),
                    LayoutError::Unspecified => {
                        RvalueLowerError::UnsupportedOffsetOfLayout(cur_ty.clone())
                    }
                    LayoutError::IllFormed(reason) => RvalueLowerError::InvalidAdtDef {
                        ty: cur_ty.clone(),
                        reason,
                    },
                })?;
            total_offset = total_offset
                .checked_add(offset)
                .ok_or_else(|| RvalueLowerError::LayoutTooLarge(arg_ty.clone()))?;
            cur_ty = &variant_fields[field_idx];
            continue;
        }
        let Ty::Tuple(tuple_fields) = cur_ty else {
            return Err(invalid_step(cur_ty));
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
    if arg_ty.layout_for(ptr_width).is_err() {
        return Err(RvalueLowerError::UnsupportedOffsetOfLayout(arg_ty.clone()));
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
                .layout_for(ptr_width)
                .map_err(|err| lower_layout_error(pointee, err))?
                .size;
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
                    // `size_of` / `align_of` need the exact layout (not merely a bound).
                    arg_ty
                        .layout_for(ptr_width)
                        .map_err(|err| lower_layout_error(arg_ty, err))?;
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
            if !place_ty.is_inhabited_for(ptr_width) {
                return Err(RvalueLowerError::UninhabitedType(place_ty));
            }
            let ty = discriminant_result_ty(&place_ty);
            Ok(LoweredRvalue::Discriminant {
                place: place.clone(),
                place_ty,
                ty,
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
                    def_path,
                    variant_idx,
                    active_field,
                    adt_def: Some(def),
                } => {
                    let adt_ty = check_layout(Ty::Adt(def.clone()), ptr_width)?;
                    if *def_path != def.def_path {
                        return Err(invalid("ADT aggregate def_path does not match its AdtDef"));
                    }
                    let Some(variant_fields) = def.variant_fields(*variant_idx) else {
                        return Err(RvalueLowerError::InvalidVariantIndex {
                            ty: adt_ty,
                            variant_index: *variant_idx,
                        });
                    };
                    match (def.is_union(), active_field) {
                        (true, Some(field_idx)) => {
                            if operands.len() != 1 {
                                return Err(invalid(
                                    "union aggregate initialization requires exactly 1 operand",
                                ));
                            }
                            let Some(field_ty) = variant_fields.get(*field_idx) else {
                                return Err(invalid("union aggregate active_field out of range"));
                            };
                            if operand_tys[0] != *field_ty {
                                return Err(RvalueLowerError::AggregateElementTypeMismatch {
                                    expected: field_ty.clone(),
                                    got: operand_tys[0].clone(),
                                });
                            }
                        }
                        (true, None) => {
                            return Err(invalid("union aggregate requires an active_field"));
                        }
                        (false, Some(_)) => {
                            return Err(invalid("only union aggregates have an active_field"));
                        }
                        (false, None) => {
                            if operand_tys.len() != variant_fields.len() {
                                return Err(invalid(
                                    "ADT aggregate operand count does not match the variant's fields",
                                ));
                            }
                            for (op_ty, field_ty) in operand_tys.iter().zip(variant_fields) {
                                if op_ty != field_ty {
                                    return Err(RvalueLowerError::AggregateElementTypeMismatch {
                                        expected: field_ty.clone(),
                                        got: op_ty.clone(),
                                    });
                                }
                            }
                        }
                    }
                    adt_ty
                }
                AggregateKind::Adt {
                    variant_idx,
                    active_field,
                    adt_def: None,
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
        Rvalue::ShallowInitBox(operand, inner_ty) => {
            let operand_ty = lower_operand_ty(operand, local_decls, ptr_width)?;
            if !operand_ty.is_raw_ptr() {
                return Err(RvalueLowerError::InvalidShallowInitBox {
                    operand_ty,
                    inner_ty: inner_ty.clone(),
                });
            }
            check_layout(inner_ty.clone(), ptr_width)?;
            Ok(LoweredRvalue::ShallowInitBox {
                operand: operand.clone(),
                operand_ty,
                ty: Ty::RawPtr(Box::new(inner_ty.clone()), Mutability::Mut),
            })
        }
        Rvalue::WrapUnsafeBinder(operand, binder_ty) => {
            let operand_ty = lower_operand_ty(operand, local_decls, ptr_width)?;
            let binder_ty = check_layout(binder_ty.clone(), ptr_width)?;
            if binder_ty != operand_ty && wrapped_field_ty(&binder_ty) != Some(&operand_ty) {
                return Err(RvalueLowerError::InvalidWrapUnsafeBinder {
                    operand_ty,
                    binder_ty,
                });
            }
            Ok(LoweredRvalue::WrapUnsafeBinder {
                operand: operand.clone(),
                operand_ty,
                ty: binder_ty,
            })
        }
    }
}

/// Field type of a single-field struct `Ty::Adt` without an explicit `repr(align)` override
/// (the type a `WrapUnsafeBinder` wraps).
fn wrapped_field_ty(ty: &Ty) -> Option<&Ty> {
    match ty {
        Ty::Adt(def) if def.is_struct() && def.repr.align.is_none() => {
            match def.variant_fields(0) {
                Some([field]) => Some(field),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Result type of `Rvalue::Discriminant` on a place of type `place_ty`: [`AdtDef::discr_ty`]
/// for a `Ty::Adt` (the enum's `tag_ty` or `isize`; `u8` for structs and unions, as `rustc`'s
/// `discriminant_ty`), and `isize` for every other type, matching the legacy model in which
/// enums are captured as the `Ty::Tuple` of their fields.
pub(crate) fn discriminant_result_ty(place_ty: &Ty) -> Ty {
    match place_ty {
        Ty::Adt(def) => def.discr_ty(),
        _ => Ty::Int(IntTy::Isize),
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
                        adt_def: None,
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
            match &place_ty {
                Ty::Tuple(_) => {}
                Ty::Adt(def) => {
                    // `rustc` allows `SetDiscriminant` on any ADT; on structs and unions only
                    // variant `0` exists. Writing the tag of an uninhabited variant is UB, but
                    // that is a dynamic property of the executed statement.
                    if *variant_index >= def.variant_count() {
                        return Err(RvalueLowerError::InvalidVariantIndex {
                            ty: place_ty,
                            variant_index: *variant_index,
                        });
                    }
                }
                _ => return Err(RvalueLowerError::InvalidSetDiscriminantTarget(place_ty)),
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
        Statement::Deinit(place) => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            Ok(LoweredStatement::Deinit {
                place: place.clone(),
                place_ty,
            })
        }
        Statement::Retag(kind, place) => {
            let place_ty = resolve_place_ty(place, local_decls)?;
            if let RetagKind::Raw(mutability) = kind
                && !matches!(&place_ty, Ty::RawPtr(_, m) if m == mutability)
            {
                return Err(RvalueLowerError::InvalidRetagTarget {
                    kind: *kind,
                    ty: place_ty,
                });
            }
            Ok(LoweredStatement::Retag {
                kind: *kind,
                place: place.clone(),
                place_ty,
            })
        }
        Statement::CopyNonOverlapping { src, dst, count } => {
            let src_ty = lower_operand_ty(src, local_decls, ptr_width)?;
            let dst_ty = lower_operand_ty(dst, local_decls, ptr_width)?;
            let count_ty = lower_operand_ty(count, local_decls, ptr_width)?;
            // `copy_nonoverlapping::<T>(src: *const T, dst: *mut T, count: usize)`: `rustc`'s
            // validator accepts any dereferenceable `src`, but `dst` must be writable.
            let elem_ty = match (&src_ty, &dst_ty) {
                (
                    Ty::RawPtr(src_pointee, _) | Ty::Ref(src_pointee, _),
                    Ty::RawPtr(dst_pointee, Mutability::Mut) | Ty::Ref(dst_pointee, Mutability::Mut),
                ) if src_pointee == dst_pointee && count_ty == Ty::Uint(UintTy::Usize) => {
                    (**src_pointee).clone()
                }
                _ => {
                    return Err(RvalueLowerError::InvalidCopyNonOverlapping {
                        src_ty,
                        dst_ty,
                        count_ty,
                    });
                }
            };
            let layout = elem_ty
                .layout_for(ptr_width)
                .map_err(|err| lower_layout_error(&elem_ty, err))?;
            Ok(LoweredStatement::CopyNonOverlapping {
                src: src.clone(),
                dst: dst.clone(),
                count: count.clone(),
                elem_ty,
                elem_size: layout.size,
                elem_align: layout.align,
            })
        }
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
/// Unspecified ADT layouts are representable; ill-formed ADTs are `InvalidAdtDef`. Every
/// terminator is lowered with [`lower_terminator`] against the whole body (block indices,
/// cleanup edges, and operand types).
pub fn lower_body_with_policy(
    body: &Body,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredBody, RvalueLowerError> {
    for local_ty in &body.local_decls {
        check_layout(local_ty.clone(), ptr_width)?;
    }
    let mut basic_blocks = Vec::with_capacity(body.basic_blocks.len());
    for (bb, block) in body.basic_blocks.iter().enumerate() {
        let BasicBlockData {
            statements,
            terminator,
            is_cleanup,
        } = block;
        let mut lowered_stmts = Vec::with_capacity(statements.len());
        for stmt in statements {
            lowered_stmts.push(lower_statement_with_policy(
                stmt,
                &body.local_decls,
                ptr_width,
                policy,
            )?);
        }
        let lowered_terminator = match terminator {
            Some(term) => Some(lower_terminator(term, bb, body, ptr_width)?),
            None => None,
        };
        basic_blocks.push(LoweredBasicBlock {
            statements: lowered_stmts,
            terminator: lowered_terminator,
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
    ///
    /// `adt_def: Some(def)` types the value as `Ty::Adt(def)` (`def_path == def.def_path`;
    /// a union holds exactly its active field's value in `fields`); legacy values with
    /// `adt_def: None` are typed as the `Ty::Tuple` of their fields.
    Adt {
        def_path: String,
        variant_idx: usize,
        active_field: Option<usize>,
        fields: Vec<MirValue>,
        adt_def: Option<Arc<AdtDef>>,
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

    /// Constructs a typed struct or enum-variant value of `def` (`variant_idx` `0` for
    /// structs), without validating `fields` against `def`.
    pub fn adt(def: &Arc<AdtDef>, variant_idx: usize, fields: Vec<MirValue>) -> Self {
        MirValue::Adt {
            def_path: def.def_path.clone(),
            variant_idx,
            active_field: None,
            fields,
            adt_def: Some(def.clone()),
        }
    }

    /// Constructs a typed union value of `def` whose active field `field_idx` holds `value`.
    pub fn union_value(def: &Arc<AdtDef>, field_idx: usize, value: MirValue) -> Self {
        MirValue::Adt {
            def_path: def.def_path.clone(),
            variant_idx: 0,
            active_field: Some(field_idx),
            fields: vec![value],
            adt_def: Some(def.clone()),
        }
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
    ///
    /// A typed ADT value reports `Ty::Adt(def)`; a legacy ADT value (`adt_def: None`) reports
    /// the `Ty::Tuple` of its fields' types.
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
            MirValue::Adt {
                adt_def: Some(def),
                ..
            } => Ty::Adt(def.clone()),
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
    /// Place that cannot be evaluated without a byte-level memory model: a `Deref` of a pointer
    /// that does not resolve to a unique, runtime-consistent synthetic sub-place of a local
    /// (no synthetic provenance, an offset outside the local's allocation or inside padding or
    /// a scalar, a pointee type matching no sub-place there, an ambiguous non-zero-sized
    /// sub-place, or bytes of an inactive union field / enum variant), the address of a
    /// projected place whose layout offset is unspecified, or a nested write into an inactive
    /// union field.
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
    /// A pointer used for a memory access (`copy_nonoverlapping`) is null.
    NullPointerAccess,
    /// A pointer used for a memory access, or a retagged reference, is not aligned to
    /// `required_align`.
    MisalignedPointer {
        addr: u64,
        required_align: usize,
    },
    /// A retagged reference points to an uninhabited type.
    UninhabitedPointee(Ty),
    /// `copy_nonoverlapping`'s byte length `count * elem_size` overflows or exceeds the
    /// target's `isize::MAX`.
    CopyLengthOverflow {
        count: u128,
        elem_size: usize,
    },
    /// A memory range `[addr, addr + byte_len)` wraps around the target address space.
    PointerRangeOverflow {
        addr: u64,
        byte_len: u128,
    },
    /// `copy_nonoverlapping` source and destination ranges overlap.
    CopyNonOverlappingOverlap {
        src_addr: u64,
        dst_addr: u64,
        byte_len: u128,
    },
    /// A memory access that the value-tree evaluator cannot perform (no byte-level memory):
    /// raised only after every undefined-behavior check of the access has passed.
    UnsupportedMemoryAccess(&'static str),
    /// `SetDiscriminant` to (or `Discriminant` of) an uninhabited enum variant.
    UninhabitedEnumVariant {
        variant_index: usize,
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
            RvalueEvalError::NullPointerAccess => write!(f, "memory access through a null pointer (UB)"),
            RvalueEvalError::MisalignedPointer {
                addr,
                required_align,
            } => {
                write!(f, "pointer {addr:#x} is not aligned to {required_align} bytes (UB)")
            }
            RvalueEvalError::UninhabitedPointee(ty) => {
                write!(f, "reference to uninhabited type {ty:?} (UB)")
            }
            RvalueEvalError::CopyLengthOverflow { count, elem_size } => {
                write!(
                    f,
                    "copy length {count} * {elem_size} bytes overflows isize::MAX (UB)"
                )
            }
            RvalueEvalError::PointerRangeOverflow { addr, byte_len } => {
                write!(
                    f,
                    "memory range of {byte_len} bytes at {addr:#x} wraps the address space (UB)"
                )
            }
            RvalueEvalError::CopyNonOverlappingOverlap {
                src_addr,
                dst_addr,
                byte_len,
            } => {
                write!(
                    f,
                    "copy_nonoverlapping ranges of {byte_len} bytes at {src_addr:#x} and {dst_addr:#x} overlap (UB)"
                )
            }
            RvalueEvalError::UnsupportedMemoryAccess(reason) => {
                write!(f, "memory access requires a memory model: {reason}")
            }
            RvalueEvalError::UninhabitedEnumVariant { variant_index } => {
                write!(f, "discriminant of uninhabited enum variant {variant_index} (UB)")
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
                let addr = checked_ptr_addr(ptr, ty, ptr_width)?;
                if ty.is_ref() && addr == 0 {
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
                if !mir_value_matches_ty(op, elem_ty) {
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
            adt_def: Some(def),
        } => {
            if *def_path != def.def_path {
                return Err(RvalueEvalError::TypeMismatch(
                    "ADT aggregate def_path does not match its AdtDef",
                ));
            }
            def.validate(ptr_width).map_err(|err| {
                RvalueEvalError::CastEval(cast_eval_layout_error(&Ty::Adt(def.clone()), err))
            })?;
            let Some(variant_fields) = def.variant_fields(*variant_idx) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "ADT aggregate variant index out of range",
                ));
            };
            let shape_ok = match (def.is_union(), active_field) {
                (true, Some(field_idx)) => {
                    operands.len() == 1
                        && variant_fields
                            .get(*field_idx)
                            .is_some_and(|ty| mir_value_matches_ty(&operands[0], ty))
                }
                (false, None) => {
                    operands.len() == variant_fields.len()
                        && operands
                            .iter()
                            .zip(variant_fields)
                            .all(|(v, ty)| mir_value_matches_ty(v, ty))
                }
                _ => false,
            };
            if !shape_ok {
                return Err(RvalueEvalError::TypeMismatch(
                    "ADT aggregate operands do not match the AdtDef's field types",
                ));
            }
            let value = MirValue::Adt {
                def_path: def_path.clone(),
                variant_idx: *variant_idx,
                active_field: *active_field,
                fields: operands,
                adt_def: Some(def.clone()),
            };
            check_scalar_ranges(&value, ptr_width)?;
            Ok(value)
        }
        AggregateKind::Adt {
            def_path,
            variant_idx,
            active_field,
            adt_def: None,
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
                adt_def: None,
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
        (Ty::Adt(def), MirValue::Adt { .. }) => {
            if !mir_value_head_matches_ty(val, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "transmute operand value does not match its source ADT type",
                ));
            }
            if !def.has_canonical_byte_layout(ptr_width) {
                return Err(RvalueEvalError::CastEval(CastEvalError::UnsupportedLayout {
                    ty: ty.clone(),
                }));
            }
            check_scalar_ranges(val, ptr_width)?;
            let MirValue::Adt {
                variant_idx,
                fields: values,
                ..
            } = val
            else {
                unreachable!()
            };
            let field_tys = match &def.kind {
                AdtKind::Enum {
                    tag_ty: Some(tag),
                    variants,
                } => {
                    let bits = def
                        .discriminant_bits(*variant_idx, ptr_width)
                        .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(ty, err)))?;
                    out.extend(encode_int_bytes(bits, tag.size_bytes(ptr_width)));
                    variants[*variant_idx].fields.as_slice()
                }
                _ => {
                    if def.is_enum() && def.univariant_index() != Some(*variant_idx) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "transmute operand enum value is not of its only present variant",
                        ));
                    }
                    canonical_untagged_fields(def).ok_or_else(|| {
                        RvalueEvalError::CastEval(CastEvalError::UnsupportedLayout {
                            ty: ty.clone(),
                        })
                    })?
                }
            };
            if values.len() != field_tys.len() {
                return Err(RvalueEvalError::TypeMismatch(
                    "transmute operand ADT value does not match its field count",
                ));
            }
            for (value, field) in values.iter().zip(field_tys) {
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

/// Returns true if `ty` may contain a value restricted by a `scalar_valid_range` (a typed
/// ADT with a range, directly or nested in arrays, tuples, or ADT fields).
fn ty_has_scalar_range(ty: &Ty) -> bool {
    match ty {
        Ty::Array(elem, count) => *count > 0 && ty_has_scalar_range(elem),
        Ty::Tuple(fields) => fields.iter().any(ty_has_scalar_range),
        Ty::Adt(def) => def.scalar_valid_range.is_some() || def.all_fields().any(ty_has_scalar_range),
        _ => false,
    }
}

/// Scalar bit pattern of a scalar `MirValue` (integer bits, `bool`, `char`, or a pointer's
/// address).
fn scalar_value_bits(val: &MirValue) -> Option<u128> {
    match val {
        MirValue::Ptr { ptr, .. } => Some(u128::from(ptr.addr)),
        _ => val.as_bits(),
    }
}

/// Enforces the `scalar_valid_range` of every typed ADT value inside `val` (e.g. a
/// `NonZeroU32` holding `0`), which the structural check [`mir_value_matches_ty`] does not
/// cover, failing with `CastEvalError::InvalidBitPattern { target_ty: Ty::Adt(def), bits }`.
pub(crate) fn check_scalar_ranges(val: &MirValue, ptr_width: PtrWidth) -> Result<(), RvalueEvalError> {
    match val {
        MirValue::Array { elements, elem_ty } => {
            if ty_has_scalar_range(elem_ty) {
                for element in elements {
                    check_scalar_ranges(element, ptr_width)?;
                }
            }
            Ok(())
        }
        MirValue::Tuple(fields) => {
            for field in fields {
                check_scalar_ranges(field, ptr_width)?;
            }
            Ok(())
        }
        MirValue::Adt {
            active_field,
            fields,
            adt_def,
            ..
        } => {
            if let Some(def) = adt_def
                && def.scalar_valid_range.is_some()
                && let Some((idx, _)) = def.scalar_field(ptr_width)
                && let Some(bits) = fields.get(idx).and_then(scalar_value_bits)
                && !def.scalar_range_contains(bits, ptr_width)
            {
                return Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                    target_ty: Ty::Adt(def.clone()),
                    bits,
                }));
            }
            if let Some(active) = active_field {
                let active_val = if fields.len() == 1 {
                    fields.first()
                } else {
                    fields.get(*active)
                };
                if let Some(field) = active_val {
                    check_scalar_ranges(field, ptr_width)?;
                }
            } else {
                for field in fields {
                    check_scalar_ranges(field, ptr_width)?;
                }
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Checks that a value entering the evaluator from outside (a body argument or a call
/// handler's return value) is well formed: every integer leaf is a valid bit pattern of its
/// type under `ptr_width`, every pointer address fits `ptr_width` (and `&T` is non-null), and
/// every typed ADT respects its `scalar_valid_range` ([`check_scalar_ranges`]). Fails with
/// `CastEvalError::InvalidBitPattern` naming the offending leaf type and bits.
pub(crate) fn check_value_well_formed(
    val: &MirValue,
    ptr_width: PtrWidth,
) -> Result<(), RvalueEvalError> {
    fn check_leaves(val: &MirValue, ptr_width: PtrWidth) -> Result<(), RvalueEvalError> {
        let invalid = |target_ty: &Ty, bits: u128| {
            Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: target_ty.clone(),
                bits,
            }))
        };
        match val {
            MirValue::Int { bits, ty }
                if !ty.is_integral() || !ty.is_valid_scalar_bits(*bits, ptr_width) =>
            {
                invalid(ty, *bits)
            }
            MirValue::Ptr { ptr, ty }
                if !ty.is_any_ptr()
                    || !ty.is_valid_scalar_bits(u128::from(ptr.addr), ptr_width) =>
            {
                invalid(ty, u128::from(ptr.addr))
            }
            MirValue::Array { elements, .. } => elements
                .iter()
                .try_for_each(|element| check_leaves(element, ptr_width)),
            MirValue::Tuple(fields)
            | MirValue::Adt {
                active_field: None,
                fields,
                ..
            } => fields
                .iter()
                .try_for_each(|field| check_leaves(field, ptr_width)),
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
                if let Some(field) = active_val {
                    check_leaves(field, ptr_width)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    check_leaves(val, ptr_width)?;
    check_scalar_ranges(val, ptr_width)
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
                adt_def: None,
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
                adt_def: None,
            })
        }
        (
            Ty::Tuple(fields),
            MirValue::Adt {
                def_path,
                variant_idx: 0,
                active_field: Some(field_idx),
                fields: values,
                adt_def: None,
            },
        ) if values.len() == 1 || values.len() == fields.len() => {
            let Some(field_ty) = fields.get(*field_idx) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "union Adt active_field index out of bounds for union type",
                ));
            };
            let active_val = if values.len() == 1 {
                &values[0]
            } else {
                &values[*field_idx]
            };
            let norm = eval_identity_transmute_value(active_val, field_ty, ptr_width)?;
            Ok(MirValue::Adt {
                def_path: def_path.clone(),
                variant_idx: 0,
                active_field: Some(*field_idx),
                fields: vec![norm],
                adt_def: None,
            })
        }
        (
            Ty::Adt(def),
            MirValue::Adt {
                def_path,
                variant_idx,
                active_field,
                fields: values,
                adt_def: Some(_),
            },
        ) if mir_value_head_matches_ty(val, ty) => {
            let field_tys: &[Ty] = match (active_field, def.variant_fields(*variant_idx)) {
                (Some(field_idx), Some(union_fields)) => {
                    std::slice::from_ref(&union_fields[*field_idx])
                }
                (None, Some(variant_fields)) => variant_fields,
                (_, None) => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "transmute operand ADT variant out of range",
                    ));
                }
            };
            let norm = values
                .iter()
                .zip(field_tys)
                .map(|(value, field)| eval_identity_transmute_value(value, field, ptr_width))
                .collect::<Result<Vec<_>, _>>()?;
            let out = MirValue::Adt {
                def_path: def_path.clone(),
                variant_idx: *variant_idx,
                active_field: *active_field,
                fields: norm,
                adt_def: Some(def.clone()),
            };
            check_scalar_ranges(&out, ptr_width)?;
            Ok(out)
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
        Ty::Adt(def) => {
            if !def.is_inhabited_for(ptr_width) {
                return Err(RvalueEvalError::CastEval(CastEvalError::UninhabitedTarget {
                    target_ty: ty.clone(),
                }));
            }
            let (start, variant_idx, field_tys) = match &def.kind {
                AdtKind::Enum {
                    tag_ty: Some(tag),
                    variants,
                } => {
                    let tag_size = tag.size_bytes(ptr_width);
                    let tag_bits = decode_int_bytes(&bytes[..tag_size]);
                    let Some(variant_idx) = def.variant_index_of_discriminant(tag_bits, ptr_width)
                    else {
                        return Err(invalid(tag_bits));
                    };
                    if !variants[variant_idx]
                        .fields
                        .iter()
                        .all(|f| f.is_inhabited_for(ptr_width))
                    {
                        return Err(invalid(tag_bits));
                    }
                    (tag_size, variant_idx, variants[variant_idx].fields.as_slice())
                }
                _ => {
                    let fields = canonical_untagged_fields(def).ok_or_else(|| {
                        RvalueEvalError::CastEval(CastEvalError::UnsupportedLayout {
                            ty: ty.clone(),
                        })
                    })?;
                    // An enum laid out without a tag always holds its only present variant.
                    (0, def.univariant_index().unwrap_or(0), fields)
                }
            };
            let mut offset = start;
            let mut values = Vec::with_capacity(field_tys.len());
            for field in field_tys {
                let size = field.byte_size_for(ptr_width);
                values.push(decode_mir_value(&bytes[offset..offset + size], field, ptr_width)?);
                offset += size;
            }
            let value = if def.is_union() {
                let Some(field) = values.pop() else {
                    return Err(RvalueEvalError::CastEval(CastEvalError::UnsupportedLayout {
                        ty: ty.clone(),
                    }));
                };
                MirValue::union_value(def, 0, field)
            } else {
                MirValue::adt(def, variant_idx, values)
            };
            check_scalar_ranges(&value, ptr_width)?;
            Ok(value)
        }
    }
}

/// Predicts an exposed provenance for `PointerWithExposedProvenance` at `addr_bits` (with
/// target pointer type `target_ty`) in a frame with `local_decls` and optional `slots`.
///
/// When multiple provenances have been exposed, prefers one whose synthetic local allocation
/// `[base_addr, base_addr + alloc_size]` contains `addr_bits` (preferring live locals and
/// interior addresses `[base_addr, base_addr + alloc_size)` over one-past-the-end, and
/// matching [`decode_subplace_tag`] when multiple tags of that local were exposed), falling
/// back to `tracker.exposed.first().copied()`.
fn predict_exposed_provenance_for_decls(
    addr_bits: u128,
    target_ty: &Ty,
    local_decls: &[Ty],
    slots: Option<&[LocalSlotState]>,
    ptr_width: PtrWidth,
    tracker: &ExposedProvenanceTracker,
) -> Option<crate::ir::Provenance> {
    if !local_decls.is_empty() && tracker.exposed.len() > 1 {
        let pointee_ty = target_ty.pointee_ty();
        let mut best: Option<(u8, crate::ir::Provenance)> = None;
        for &prov in &tracker.exposed {
            let Some(loc) = prov
                .alloc_id
                .checked_sub(1)
                .and_then(|id| usize::try_from(id).ok())
                .filter(|&loc| loc < local_decls.len())
            else {
                continue;
            };
            let Ok(base_addr) = local_base_addr_for_decls(loc, local_decls, ptr_width) else {
                continue;
            };
            let Ok((alloc_size, _)) = local_decls[loc].alloc_size_and_align(ptr_width) else {
                continue;
            };
            let end_addr = base_addr.saturating_add(alloc_size as u128);
            if addr_bits < base_addr || addr_bits > end_addr {
                continue;
            }
            let is_live = !slots.is_some_and(|s| matches!(s.get(loc), Some(LocalSlotState::Dead)));
            let is_interior = addr_bits < end_addr || (alloc_size == 0 && addr_bits == base_addr);
            let tag_matches = pointee_ty
                .and_then(|pty| decode_subplace_tag(prov.tag, pty))
                .is_some();
            let rank = (u8::from(is_live) << 2)
                | (u8::from(is_interior) << 1)
                | u8::from(tag_matches);
            if best.is_none_or(|(best_rank, _)| rank > best_rank) {
                best = Some((rank, prov));
            }
        }
        if let Some((_, prov)) = best {
            return Some(prov);
        }
    }
    tracker.exposed.first().copied()
}

/// Evaluates a `LoweredCast` on an evaluated `MirValue` operand under `ptr_width` and `policy`.
pub fn eval_lowered_cast(
    cast: &LoweredCast,
    val: &MirValue,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<MirValue, RvalueEvalError> {
    eval_lowered_cast_with_decls(cast, val, &[], None, ptr_width, policy, tracker)
}

fn eval_lowered_cast_with_decls(
    cast: &LoweredCast,
    val: &MirValue,
    local_decls: &[Ty],
    slots: Option<&[LocalSlotState]>,
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
                predict_exposed_provenance_for_decls(
                    addr_bits,
                    target_ty,
                    local_decls,
                    slots,
                    ptr_width,
                    tracker,
                )
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
                if !src_ty.is_inhabited_for(ptr_width) {
                    return Err(RvalueEvalError::CastEval(CastEvalError::UninhabitedTarget {
                        target_ty: target_ty.clone(),
                    }));
                }
                if let Err(err) = src_ty.layout_for(ptr_width) {
                    return Err(RvalueEvalError::CastEval(cast_eval_layout_error(src_ty, err)));
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
        LoweredCast::Subtype { src_ty, target_ty, .. } => {
            src_ty
                .check_representable(ptr_width)
                .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(src_ty, err)))?;
            if !crate::lower::cast::is_subtype_compatible(src_ty, target_ty)
                || !mir_value_matches_ty(val, src_ty)
            {
                return Err(RvalueEvalError::TypeMismatch(
                    "Subtype operand must match the (equal) source and target types",
                ));
            }
            check_value_well_formed(val, ptr_width)?;
            Ok(val.clone())
        }
        LoweredCast::PointerCoercion {
            coercion,
            src_ty,
            target_ty,
            ..
        } => {
            let MirValue::Ptr { ptr, ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "PointerCoercion requires pointer value",
                ));
            };
            if ty != src_ty || !is_valid_pointer_coercion(*coercion, src_ty, target_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "PointerCoercion requires valid raw pointer source and target types matching operand",
                ));
            }
            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: (u128::from(ptr.addr) & ptr_width.mask()) as u64,
                    provenance: ptr.provenance,
                },
                ty: target_ty.clone(),
            })
        }
    }
}

/// The address of the pointer `ptr` of type `ty` for a memory-access or validity check, which
/// must fit `ptr_width`: an address beyond the target's pointer width is an ill-formed value
/// (`InvalidBitPattern` naming `ty`) that a check must not truncate into a valid one.
fn checked_ptr_addr(
    ptr: &PointerValue,
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<u128, RvalueEvalError> {
    let addr = u128::from(ptr.addr);
    if addr > ptr_width.mask() {
        return Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: ty.clone(),
                bits: addr,
            },
        ));
    }
    Ok(addr)
}

/// Checks whether a runtime `MirValue` is structurally compatible with `expected_ty`,
/// accounting for union `MirValue::Adt { active_field: Some(field_idx), .. }` values whose
/// single operand corresponds to `field_tys[field_idx]` of the union's declared tuple type.
pub(crate) fn mir_value_matches_ty(val: &MirValue, expected_ty: &Ty) -> bool {
    match (val, expected_ty) {
        (MirValue::Int { ty, .. }, expected) => ty.is_integral() && ty == expected,
        (MirValue::Bool(_), Ty::Bool) => true,
        (MirValue::Char(_), Ty::Char) => true,
        (MirValue::Ptr { ty, .. }, expected) => ty.is_any_ptr() && ty == expected,
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
                adt_def: None,
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
                adt_def: None,
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
        (MirValue::Adt { fields: vals, .. }, Ty::Adt(_)) => {
            typed_adt_field_tys(val, expected_ty).is_some_and(|field_tys| {
                vals.iter()
                    .zip(field_tys)
                    .all(|(v, t)| mir_value_matches_ty(v, t))
            })
        }
        _ => false,
    }
}

/// For a typed ADT value `val` whose outermost constructor matches the `Ty::Adt` `ty` (same
/// definition and `def_path`; a struct's variant `0`, an in-range enum variant, or a union's
/// in-range active field with exactly one value; field counts matching), returns the types of
/// `val`'s fields in order. Returns `None` on any mismatch.
fn typed_adt_field_tys<'t>(val: &MirValue, ty: &'t Ty) -> Option<&'t [Ty]> {
    let (
        MirValue::Adt {
            def_path,
            variant_idx,
            active_field,
            fields,
            adt_def: Some(val_def),
        },
        Ty::Adt(def),
    ) = (val, ty)
    else {
        return None;
    };
    if val_def != def || *def_path != def.def_path {
        return None;
    }
    let variant_fields = def.variant_fields(*variant_idx)?;
    match (def.is_union(), active_field) {
        (true, Some(field_idx)) => {
            let field_ty = variant_fields.get(*field_idx)?;
            (fields.len() == 1).then_some(std::slice::from_ref(field_ty))
        }
        (false, None) => (fields.len() == variant_fields.len()).then_some(variant_fields),
        _ => None,
    }
}

/// Checks only the outermost constructor of `val` against `expected_ty`: scalars in full, an
/// array's element type and length, a tuple's or non-union ADT's field count, and a union's
/// active-field index and active-field head constructor, without traversing nested elements or
/// fields.
fn mir_value_head_matches_ty(val: &MirValue, expected_ty: &Ty) -> bool {
    match (val, expected_ty) {
        (MirValue::Array { elements, elem_ty }, Ty::Array(expected_elem, expected_len)) => {
            elem_ty == &**expected_elem && elements.len() == *expected_len
        }
        (MirValue::Tuple(vals), Ty::Tuple(field_tys)) => vals.len() == field_tys.len(),
        (
            MirValue::Adt {
                active_field: None,
                fields: vals,
                adt_def: None,
                ..
            },
            Ty::Tuple(field_tys),
        ) => vals.len() == field_tys.len(),
        (
            MirValue::Adt {
                variant_idx: 0,
                active_field: Some(field_idx),
                fields: vals,
                adt_def: None,
                ..
            },
            Ty::Tuple(field_tys),
        ) => {
            if vals.len() == 1 {
                field_tys
                    .get(*field_idx)
                    .is_some_and(|ft| mir_value_head_matches_ty(&vals[0], ft))
            } else {
                vals.len() == field_tys.len()
                    && field_tys
                        .get(*field_idx)
                        .zip(vals.get(*field_idx))
                        .is_some_and(|(ft, v)| mir_value_head_matches_ty(v, ft))
            }
        }
        (
            MirValue::Adt {
                active_field: Some(_),
                fields: vals,
                ..
            },
            Ty::Adt(_),
        ) => typed_adt_field_tys(val, expected_ty)
            .is_some_and(|field_tys| mir_value_head_matches_ty(&vals[0], &field_tys[0])),
        (MirValue::Adt { .. }, Ty::Adt(_)) => typed_adt_field_tys(val, expected_ty).is_some(),
        _ => mir_value_matches_ty(val, expected_ty),
    }
}

/// Checks a value selected by a projection step against the step's type: in full when no
/// later step selects a part of it (`rest` is empty, so it is the leaf value a read returns
/// or a write replaces), otherwise only its outermost constructor ([`mir_value_head_matches_ty`]),
/// since the later steps check the parts they select.
fn projected_value_matches_ty(val: &MirValue, ty: &Ty, rest: &[ProjectionElem]) -> bool {
    if rest.is_empty() {
        mir_value_matches_ty(val, ty)
    } else {
        mir_value_head_matches_ty(val, ty)
    }
}

/// Resolves a `ProjectionElem::ConstantIndex` against an array or window of length `arr_len`.
fn resolve_constant_index(
    arr_len: usize,
    offset: u64,
    min_length: u64,
    from_end: bool,
) -> Result<usize, RvalueEvalError> {
    let len = arr_len as u64;
    if len < min_length {
        return Err(RvalueEvalError::IndexOutOfBounds {
            index: u128::from(offset),
            len: arr_len,
        });
    }
    if from_end {
        if offset == 0 || offset > len {
            return Err(RvalueEvalError::IndexOutOfBounds {
                index: u128::from(offset),
                len: arr_len,
            });
        }
        Ok(arr_len - (offset as usize))
    } else {
        if offset >= len {
            return Err(RvalueEvalError::IndexOutOfBounds {
                index: u128::from(offset),
                len: arr_len,
            });
        }
        Ok(offset as usize)
    }
}

/// Resolves a `ProjectionElem::Subslice` range `(start, end)` against an array or window of
/// length `arr_len`.
fn resolve_subslice_range(
    arr_len: usize,
    from: u64,
    to: u64,
    from_end: bool,
) -> Result<(usize, usize), RvalueEvalError> {
    let len = arr_len as u64;
    if from_end {
        let Some(sum) = from.checked_add(to) else {
            return Err(RvalueEvalError::IndexOutOfBounds {
                index: u128::from(from) + u128::from(to),
                len: arr_len,
            });
        };
        if sum > len {
            return Err(RvalueEvalError::IndexOutOfBounds {
                index: u128::from(sum),
                len: arr_len,
            });
        }
        Ok((from as usize, (len - to) as usize))
    } else {
        if from > to || to > len {
            return Err(RvalueEvalError::IndexOutOfBounds {
                index: u128::from(from.max(to)),
                len: arr_len,
            });
        }
        Ok((from as usize, to as usize))
    }
}

/// Validates that a remaining projection path `proj` is structurally compatible with `cur_ty`,
/// returning `leaf_ty`. Every `Downcast` must be immediately followed by `Field`. When
/// `local_decls` is `Some`, also checks that every `Index(idx_local)` local has declared type
/// `usize`; when `read_index` is `Some`, also checks dynamic `Index(idx_local)` bounds against
/// `Ty::Array` length.
fn validate_projection_tail<F>(
    cur_ty: &Ty,
    proj: &[ProjectionElem],
    local_decls: Option<&[Ty]>,
    read_index: Option<&F>,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<Ty, RvalueEvalError>
where
    F: Fn(Local) -> Result<u128, RvalueEvalError>,
{
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        return Ok(cur_ty.clone());
    };
    match first {
        ProjectionElem::Deref => {
            if local_decls.is_some() && read_index.is_none() {
                if active_downcast.is_some() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast projection must be followed by Field",
                    ));
                }
                let Some(pointee_ty) = cur_ty.pointee_ty() else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Deref projection requires a pointer-typed place",
                    ));
                };
                return validate_projection_tail(
                    pointee_ty,
                    rest,
                    local_decls,
                    read_index,
                    full_place,
                    None,
                );
            }
            Err(RvalueEvalError::UnsupportedPlaceProjection(
                full_place.clone(),
            ))
        }
        ProjectionElem::Downcast(v) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "consecutive Downcast projections without Field",
                ));
            }
            if !(local_decls.is_some() && read_index.is_none())
                && matches!(rest.first(), Some(ProjectionElem::Deref))
            {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            if !matches!(rest.first(), Some(ProjectionElem::Field(..))) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            if !downcast_allowed(cur_ty, *v) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection requires a tuple-typed (ADT) place or an in-range enum variant",
                ));
            }
            validate_projection_tail(cur_ty, rest, local_decls, read_index, full_place, Some(*v))
        }
        ProjectionElem::Field(idx, expected_ty) => {
            let Some(field_tys) = projectable_field_tys(cur_ty, active_downcast) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Field projection requires a tuple-typed place (or a struct/union, or a downcast enum)",
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
            validate_projection_tail(
                &field_tys[*idx],
                rest,
                local_decls,
                read_index,
                full_place,
                None,
            )
        }
        ProjectionElem::Index(idx_local) => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let Ty::Array(elem_ty, len) = cur_ty else {
                return Err(RvalueEvalError::TypeMismatch(
                    "array projection applied to a non-array place",
                ));
            };
            if let Some(decls) = local_decls
                && decls.get(idx_local.0) != Some(&Ty::Uint(UintTy::Usize))
            {
                return Err(RvalueEvalError::TypeMismatch(
                    "array index local must have declared type usize",
                ));
            }
            if let Some(read_idx) = read_index {
                let idx_bits = read_idx(*idx_local)?;
                let Ok(i) = usize::try_from(idx_bits) else {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: idx_bits,
                        len: *len,
                    });
                };
                if i >= *len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: idx_bits,
                        len: *len,
                    });
                }
            }
            validate_projection_tail(elem_ty, rest, local_decls, read_index, full_place, None)
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
            let Ty::Array(elem_ty, len) = cur_ty else {
                return Err(RvalueEvalError::TypeMismatch(
                    "array projection applied to a non-array place",
                ));
            };
            let _ = resolve_constant_index(*len, *offset, *min_length, *from_end)?;
            validate_projection_tail(elem_ty, rest, local_decls, read_index, full_place, None)
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
            let Ty::Array(elem_ty, len) = cur_ty else {
                return Err(RvalueEvalError::TypeMismatch(
                    "array projection applied to a non-array place",
                ));
            };
            let (start, end) = resolve_subslice_range(*len, *from, *to, *from_end)?;
            let sub_ty = Ty::Array(elem_ty.clone(), end - start);
            validate_projection_tail(&sub_ty, rest, local_decls, read_index, full_place, None)
        }
    }
}

/// Borrowed target designated by an immutable projection walk over a [`MirValue`]: either a
/// single [`MirValue`] node or a `Subslice` window `&[MirValue]` with its element type.
enum ProjectedRef<'a> {
    Value(&'a MirValue),
    ArrayWindow {
        window: &'a [MirValue],
        elem_ty: &'a Ty,
    },
}

/// Converts a [`ProjectedRef`] into an owned [`MirValue`], checking the returned value or
/// window elements in full against `leaf_ty` / `elem_ty`.
fn projected_ref_into_mir_value(
    target: ProjectedRef<'_>,
    leaf_ty: Option<&Ty>,
) -> Result<MirValue, RvalueEvalError> {
    match target {
        ProjectedRef::Value(v) => {
            if let Some(ty) = leaf_ty
                && !mir_value_matches_ty(v, ty)
            {
                return Err(RvalueEvalError::TypeMismatch(
                    "projected leaf runtime value does not match expected type",
                ));
            }
            Ok(v.clone())
        }
        ProjectedRef::ArrayWindow { window, elem_ty } => {
            for elem_val in window {
                if !mir_value_matches_ty(elem_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
            }
            Ok(MirValue::Array {
                elements: window.to_vec(),
                elem_ty: elem_ty.clone(),
            })
        }
    }
}

/// Converts a [`ProjectedRef`] into an array length for `Rvalue::Len` in `O(1)` time without
/// cloning or scanning array elements.
fn projected_ref_into_array_len(
    target: ProjectedRef<'_>,
    leaf_ty: Option<&Ty>,
) -> Result<usize, RvalueEvalError> {
    match target {
        ProjectedRef::Value(v) => {
            let MirValue::Array { elements, .. } = v else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len target runtime value must be MirValue::Array",
                ));
            };
            if let Some(ty) = leaf_ty
                && !mir_value_head_matches_ty(v, ty)
            {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len target runtime value does not match declared array type",
                ));
            }
            Ok(elements.len())
        }
        ProjectedRef::ArrayWindow { window, .. } => Ok(window.len()),
    }
}

/// Walks `proj` over an immutable array window `window` of element type `elem_ty`, narrowing
/// `Subslice` windows in `O(1)` without cloning or scanning unselected elements.
fn project_array_window<'a>(
    window: &'a [MirValue],
    elem_ty: &'a Ty,
    proj: &'a [ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
) -> Result<(ProjectedRef<'a>, Option<&'a Ty>), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        return Ok((ProjectedRef::ArrayWindow { window, elem_ty }, None));
    };

    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Index(idx_local) => {
            let idx_bits = read_index(*idx_local)?;
            let Ok(i) = usize::try_from(idx_bits) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: window.len(),
                });
            };
            let Some(elem_val) = window.get(i) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: window.len(),
                });
            };
            if !mir_value_head_matches_ty(elem_val, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array element runtime type does not match elem_ty",
                ));
            }
            project_mir_value(elem_val, Some(elem_ty), rest, read_index, full_place, None)
        }
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => {
            let idx = resolve_constant_index(window.len(), *offset, *min_length, *from_end)?;
            let elem_val = &window[idx];
            if !mir_value_head_matches_ty(elem_val, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array element runtime type does not match elem_ty",
                ));
            }
            project_mir_value(elem_val, Some(elem_ty), rest, read_index, full_place, None)
        }
        ProjectionElem::Subslice {
            from,
            to,
            from_end,
        } => {
            let (start, end) = resolve_subslice_range(window.len(), *from, *to, *from_end)?;
            project_array_window(&window[start..end], elem_ty, rest, read_index, full_place)
        }
        ProjectionElem::Downcast(_) => {
            if matches!(rest.first(), Some(ProjectionElem::Deref)) {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            Err(RvalueEvalError::TypeMismatch(
                "Downcast requires a non-union Adt or Tuple value",
            ))
        }
        ProjectionElem::Field(..) => Err(RvalueEvalError::TypeMismatch(
            "Field projection requires Tuple or Adt value",
        )),
    }
}

/// Walks `proj` over `val`, checking each step's outermost constructor with
/// [`mir_value_head_matches_ty`] and returning the borrowed leaf [`ProjectedRef`] and its
/// expected [`Ty`] in `O(proj.len())` time.
fn project_mir_value<'a>(
    val: &'a MirValue,
    declared_ty: Option<&'a Ty>,
    proj: &'a [ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(ProjectedRef<'a>, Option<&'a Ty>), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        return Ok((ProjectedRef::Value(val), declared_ty));
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
            if matches!(rest.first(), Some(ProjectionElem::Deref)) {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            if !matches!(rest.first(), Some(ProjectionElem::Field(..))) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            match val {
                MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    adt_def,
                    ..
                } => {
                    if let Some(def) = adt_def
                        && (!def.is_enum() || *expected_variant >= def.variant_count())
                    {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Downcast requires an enum ADT with an in-range variant",
                        ));
                    }
                    if *variant_idx != *expected_variant {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual: *variant_idx,
                        });
                    }
                    project_mir_value(
                        val,
                        declared_ty,
                        rest,
                        read_index,
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
                    project_mir_value(val, declared_ty, rest, read_index, full_place, Some(0))
                }
                _ => Err(RvalueEvalError::TypeMismatch(
                    "Downcast requires a non-union Adt or Tuple value",
                )),
            }
        }
        ProjectionElem::Field(idx, expected_ty) => match val {
            MirValue::Tuple(fields) => {
                if let Some(v) = active_downcast
                    && v != 0
                {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: v,
                        actual: 0,
                    });
                }
                let Some(field_val) = fields.get(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count: fields.len(),
                    });
                };
                if !mir_value_head_matches_ty(field_val, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected tuple field runtime type does not match expected type",
                    ));
                }
                project_mir_value(field_val, Some(expected_ty), rest, read_index, full_place, None)
            }
            MirValue::Unit => {
                if let Some(v) = active_downcast
                    && v != 0
                {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: v,
                        actual: 0,
                    });
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
                adt_def,
                ..
            } => {
                if let Some(def) = adt_def
                    && (def.is_union() || (def.is_enum() && active_downcast.is_none()))
                {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Field projection on an enum ADT requires a preceding Downcast",
                    ));
                }
                let expected_variant = active_downcast.unwrap_or(0);
                if *variant_idx != expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: expected_variant,
                        actual: *variant_idx,
                    });
                }
                if let Some(def) = adt_def {
                    let Some(decl_fields) = def.variant_fields(expected_variant) else {
                        return Err(RvalueEvalError::TypeMismatch(
                            "ADT runtime variant index out of range",
                        ));
                    };
                    if fields.len() != decl_fields.len() {
                        return Err(RvalueEvalError::TypeMismatch(
                            "ADT runtime field count does not match its AdtDef",
                        ));
                    }
                    let Some(decl_field_ty) = decl_fields.get(*idx) else {
                        return Err(RvalueEvalError::FieldOutOfBounds {
                            field_idx: *idx,
                            field_count: decl_fields.len(),
                        });
                    };
                    if decl_field_ty != expected_ty {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected ADT field type does not match declared field type",
                        ));
                    }
                }
                let Some(field_val) = fields.get(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count: fields.len(),
                    });
                };
                if !mir_value_head_matches_ty(field_val, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected ADT field runtime type does not match expected type",
                    ));
                }
                project_mir_value(field_val, Some(expected_ty), rest, read_index, full_place, None)
            }
            MirValue::Adt {
                variant_idx,
                active_field: Some(active),
                fields,
                adt_def,
                ..
            } => {
                if active_downcast.is_some() || *variant_idx != 0 || fields.is_empty() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT must have variant 0, at least one field, and cannot be downcast",
                    ));
                }
                let active_val = if fields.len() == 1 {
                    &fields[0]
                } else {
                    fields.get(*active).ok_or(RvalueEvalError::TypeMismatch(
                        "union ADT active_field index out of bounds of fields",
                    ))?
                };
                let union_field_tys = match (declared_ty, adt_def) {
                    (Some(decl_ty), _) => Some(union_fields_of(decl_ty).ok_or(
                        RvalueEvalError::TypeMismatch(
                            "union ADT declared type must be a Ty::Tuple or a union Ty::Adt",
                        ),
                    )?),
                    (None, Some(def)) => {
                        if !def.is_union() {
                            return Err(RvalueEvalError::TypeMismatch(
                                "only union ADTs may have an active_field",
                            ));
                        }
                        def.variant_fields(0)
                    }
                    (None, None) => None,
                };
                if let Some(union_field_tys) = union_field_tys {
                    let Some(active_ty) = union_field_tys.get(*active) else {
                        return Err(RvalueEvalError::TypeMismatch(
                            "union ADT active_field index out of bounds of declared fields",
                        ));
                    };
                    if *idx >= union_field_tys.len() {
                        return Err(RvalueEvalError::FieldOutOfBounds {
                            field_idx: *idx,
                            field_count: union_field_tys.len(),
                        });
                    }
                    if union_field_tys[*idx] != *expected_ty {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected union field type does not match declared union field type",
                        ));
                    }
                    if *active != *idx && !mir_value_matches_ty(active_val, active_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "union ADT active field runtime value does not match declared type",
                        ));
                    }
                }
                if *active != *idx {
                    validate_projection_tail(
                        expected_ty,
                        rest,
                        None,
                        Some(read_index),
                        full_place,
                        None,
                    )?;
                    return Err(RvalueEvalError::InactiveUnionField {
                        active_field: *active,
                        requested_field: *idx,
                    });
                }
                if !mir_value_head_matches_ty(active_val, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected union field runtime type does not match expected type",
                    ));
                }
                project_mir_value(active_val, Some(expected_ty), rest, read_index, full_place, None)
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "Field projection requires Tuple or Adt value",
            )),
        },
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "array projection requires Array value",
                ));
            };
            project_array_window(elements.as_slice(), elem_ty, proj, read_index, full_place)
        }
    }
}

/// Traverses `proj` on `val` for a value-tree read.
///
/// Each step checks the value it selects against the step's expected type. A value that is
/// only passed through to later steps is checked with [`mir_value_head_matches_ty`] (its
/// outermost constructor), because the later steps check the parts of it they select; the
/// value the read returns is checked in full with [`mir_value_matches_ty`]. A read therefore
/// costs time proportional to the projection length plus the size of the returned value,
/// not the size of the containing local.
///
/// The returned value must also satisfy the `scalar_valid_range` of every typed ADT inside it
/// (a typed copy of an invalid `NonZeroU32` is undefined behavior), while reading a field of
/// such an ADT only validates that field.
fn read_projected_mir_value(
    val: &MirValue,
    declared_ty: Option<&Ty>,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<MirValue, RvalueEvalError> {
    let (target, leaf_ty) = project_mir_value(
        val,
        declared_ty,
        proj,
        read_index,
        full_place,
        active_downcast,
    )?;
    // When `proj` is empty and `declared_ty` is `None` (pure `eval_place_read` on a bare local),
    // `leaf_ty` is `None`; when `proj` is non-empty, `project_mir_value` supplies the last
    // step's type as `leaf_ty`.
    let value = projected_ref_into_mir_value(target, if proj.is_empty() { None } else { leaf_ty })?;
    check_scalar_ranges(&value, ptr_width)?;
    Ok(value)
}

/// Traverses `proj` over a mutable array window `window` of element type `elem_ty` for an
/// in-place value-tree write, narrowing `Subslice` windows in `O(1)` without cloning or
/// scanning unselected elements when `rest` continues with further projections.
fn write_projected_array_window(
    window: &mut [MirValue],
    elem_ty: &Ty,
    proj: &[ProjectionElem],
    new_val: MirValue,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    full_place: &Place,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        for elem_val in window.iter() {
            if !mir_value_matches_ty(elem_val, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array element runtime type does not match elem_ty",
                ));
            }
        }
        let MirValue::Array {
            elements: new_sub_elems,
            elem_ty: new_elem_ty,
        } = new_val
        else {
            return Err(RvalueEvalError::TypeMismatch(
                "written value runtime type does not match declared place type",
            ));
        };
        if new_elem_ty != *elem_ty || new_sub_elems.len() != window.len() {
            return Err(RvalueEvalError::TypeMismatch(
                "written value runtime type does not match declared place type",
            ));
        }
        for elem_val in &new_sub_elems {
            if !mir_value_matches_ty(elem_val, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "written value runtime type does not match declared place type",
                ));
            }
        }
        for (dst, src) in window.iter_mut().zip(new_sub_elems) {
            *dst = src;
        }
        return Ok(());
    };

    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Index(idx_local) => {
            let idx_bits = read_index(*idx_local)?;
            let arr_len = window.len();
            let Ok(i) = usize::try_from(idx_bits) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: arr_len,
                });
            };
            let Some(elem_slot) = window.get_mut(i) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: arr_len,
                });
            };
            if rest.is_empty() {
                if !mir_value_matches_ty(elem_slot, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
                if !mir_value_matches_ty(&new_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "written Array element runtime type does not match elem_ty",
                    ));
                }
                *elem_slot = new_val;
                Ok(())
            } else {
                if !projected_value_matches_ty(elem_slot, elem_ty, rest) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
                write_projected_mir_value(
                    elem_slot,
                    Some(elem_ty),
                    rest,
                    new_val,
                    read_index,
                    ptr_width,
                    full_place,
                    None,
                )
            }
        }
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => {
            let idx = resolve_constant_index(window.len(), *offset, *min_length, *from_end)?;
            let elem_slot = &mut window[idx];
            if rest.is_empty() {
                if !mir_value_matches_ty(elem_slot, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
                if !mir_value_matches_ty(&new_val, elem_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "written Array element runtime type does not match elem_ty",
                    ));
                }
                *elem_slot = new_val;
                Ok(())
            } else {
                if !projected_value_matches_ty(elem_slot, elem_ty, rest) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Array element runtime type does not match elem_ty",
                    ));
                }
                write_projected_mir_value(
                    elem_slot,
                    Some(elem_ty),
                    rest,
                    new_val,
                    read_index,
                    ptr_width,
                    full_place,
                    None,
                )
            }
        }
        ProjectionElem::Subslice {
            from,
            to,
            from_end,
        } => {
            let (start, end) = resolve_subslice_range(window.len(), *from, *to, *from_end)?;
            write_projected_array_window(
                &mut window[start..end],
                elem_ty,
                rest,
                new_val,
                read_index,
                ptr_width,
                full_place,
            )
        }
        ProjectionElem::Downcast(_) => {
            if matches!(rest.first(), Some(ProjectionElem::Deref)) {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            Err(RvalueEvalError::TypeMismatch(
                "Downcast requires a non-union Adt or Tuple value",
            ))
        }
        ProjectionElem::Field(..) => Err(RvalueEvalError::TypeMismatch(
            "Field projection requires Tuple or Adt value",
        )),
    }
}

/// Traverses `proj` on `val` for an in-place value-tree write.
///
/// Intermediate containers along `proj` are checked with [`projected_value_matches_ty`], while
/// both the replaced leaf value and `new_val` are checked in full with [`mir_value_matches_ty`].
/// Every error path returns before mutating `val`, so a failed write leaves `val` unchanged.
#[allow(clippy::too_many_arguments)]
fn write_projected_mir_value(
    val: &mut MirValue,
    declared_ty: Option<&Ty>,
    proj: &[ProjectionElem],
    new_val: MirValue,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        if let Some(decl_ty) = declared_ty
            && !mir_value_matches_ty(&new_val, decl_ty)
        {
            return Err(RvalueEvalError::TypeMismatch(
                "written value runtime type does not match declared place type",
            ));
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
            if matches!(rest.first(), Some(ProjectionElem::Deref)) {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            if !matches!(rest.first(), Some(ProjectionElem::Field(..))) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            match val {
                MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    adt_def,
                    ..
                } => {
                    if let Some(def) = adt_def
                        && (!def.is_enum() || *expected_variant >= def.variant_count())
                    {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Downcast requires an enum ADT with an in-range variant",
                        ));
                    }
                    if *variant_idx != *expected_variant {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual: *variant_idx,
                        });
                    }
                    write_projected_mir_value(
                        val,
                        declared_ty,
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
                        declared_ty,
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
                if let Some(v) = active_downcast
                    && v != 0
                {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: v,
                        actual: 0,
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
                    if !projected_value_matches_ty(field_slot, expected_ty, rest) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected tuple field runtime type does not match expected type",
                        ));
                    }
                    write_projected_mir_value(
                        field_slot,
                        Some(expected_ty),
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        None,
                    )
                }
            }
            MirValue::Unit => {
                if let Some(v) = active_downcast
                    && v != 0
                {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: v,
                        actual: 0,
                    });
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
                adt_def,
                ..
            } => {
                if let Some(def) = adt_def
                    && (def.is_union() || (def.is_enum() && active_downcast.is_none()))
                {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Field projection on an enum ADT requires a preceding Downcast",
                    ));
                }
                let expected_variant = active_downcast.unwrap_or(0);
                if *variant_idx != expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: expected_variant,
                        actual: *variant_idx,
                    });
                }
                if let Some(def) = adt_def {
                    let Some(decl_fields) = def.variant_fields(expected_variant) else {
                        return Err(RvalueEvalError::TypeMismatch(
                            "ADT runtime variant index out of range",
                        ));
                    };
                    if fields.len() != decl_fields.len() {
                        return Err(RvalueEvalError::TypeMismatch(
                            "ADT runtime field count does not match its AdtDef",
                        ));
                    }
                    let Some(decl_field_ty) = decl_fields.get(*idx) else {
                        return Err(RvalueEvalError::FieldOutOfBounds {
                            field_idx: *idx,
                            field_count: decl_fields.len(),
                        });
                    };
                    if decl_field_ty != expected_ty {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected ADT field type does not match declared field type",
                        ));
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
                    if !projected_value_matches_ty(field_slot, expected_ty, rest) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected ADT field runtime type does not match expected type",
                        ));
                    }
                    write_projected_mir_value(
                        field_slot,
                        Some(expected_ty),
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        None,
                    )
                }
            }
            MirValue::Adt {
                variant_idx,
                active_field: Some(active),
                fields,
                adt_def,
                ..
            } => {
                if active_downcast.is_some() || *variant_idx != 0 || fields.is_empty() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT must have variant 0, at least one field, and cannot be downcast",
                    ));
                }
                let active_val = if fields.len() == 1 {
                    &fields[0]
                } else {
                    fields.get(*active).ok_or(RvalueEvalError::TypeMismatch(
                        "union ADT active_field index out of bounds of fields",
                    ))?
                };
                let union_field_tys = match (declared_ty, adt_def.as_ref()) {
                    (Some(decl_ty), _) => Some(union_fields_of(decl_ty).ok_or(
                        RvalueEvalError::TypeMismatch(
                            "union ADT declared type must be a Ty::Tuple or a union Ty::Adt",
                        ),
                    )?),
                    (None, Some(def)) => {
                        if !def.is_union() {
                            return Err(RvalueEvalError::TypeMismatch(
                                "only union ADTs may have an active_field",
                            ));
                        }
                        def.variant_fields(0)
                    }
                    (None, None) => None,
                };
                if let Some(union_field_tys) = union_field_tys {
                    let Some(active_ty) = union_field_tys.get(*active) else {
                        return Err(RvalueEvalError::TypeMismatch(
                            "union ADT active_field index out of bounds of declared fields",
                        ));
                    };
                    if *idx >= union_field_tys.len() {
                        return Err(RvalueEvalError::FieldOutOfBounds {
                            field_idx: *idx,
                            field_count: union_field_tys.len(),
                        });
                    }
                    if union_field_tys[*idx] != *expected_ty {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected union field type does not match declared union field type",
                        ));
                    }
                    if (rest.is_empty() || *active != *idx)
                        && !mir_value_matches_ty(active_val, active_ty)
                    {
                        return Err(RvalueEvalError::TypeMismatch(
                            "union ADT active field runtime value does not match declared type",
                        ));
                    }
                } else if rest.is_empty()
                    && *active == *idx
                    && !mir_value_matches_ty(active_val, expected_ty)
                {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected union field runtime type does not match expected type",
                    ));
                }
                if rest.is_empty() {
                    if !mir_value_matches_ty(&new_val, expected_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "written union field runtime type does not match expected type",
                        ));
                    }
                    if fields.len() == 1 {
                        *active = *idx;
                        fields[0] = new_val;
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
                        let leaf_ty = validate_projection_tail(
                            expected_ty,
                            rest,
                            None,
                            Some(read_index),
                            full_place,
                            None,
                        )?;
                        if !mir_value_matches_ty(&new_val, &leaf_ty) {
                            return Err(RvalueEvalError::TypeMismatch(
                                "written value runtime type does not match projected leaf type",
                            ));
                        }
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
                    if !projected_value_matches_ty(field_slot, expected_ty, rest) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected union field runtime type does not match expected type",
                        ));
                    }
                    write_projected_mir_value(
                        field_slot,
                        Some(expected_ty),
                        rest,
                        new_val,
                        read_index,
                        ptr_width,
                        full_place,
                        None,
                    )
                }
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "Field projection requires Tuple or Adt value",
            )),
        },
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "array projection requires Array value",
                ));
            };
            write_projected_array_window(
                elements.as_mut_slice(),
                elem_ty,
                proj,
                new_val,
                read_index,
                ptr_width,
                full_place,
            )
        }
    }
}

/// Traverses `proj` on `val` to resolve the length of the target `MirValue::Array` for
/// `Rvalue::Len` in `O(proj.len())` time without cloning or scanning array elements.
fn read_projected_array_len(
    val: &MirValue,
    declared_ty: Option<&Ty>,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    _ptr_width: PtrWidth,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<usize, RvalueEvalError> {
    let (target, leaf_ty) = project_mir_value(
        val,
        declared_ty,
        proj,
        read_index,
        full_place,
        active_downcast,
    )?;
    projected_ref_into_array_len(target, leaf_ty)
}

/// Evaluates the runtime array length at `place` over `locals` under `ptr_width` in
/// `O(place.projection.len())` time without cloning or scanning array elements.
fn eval_place_array_len(
    place: &Place,
    locals: &[MirValue],
    ptr_width: PtrWidth,
) -> Result<usize, RvalueEvalError> {
    if place
        .projection
        .iter()
        .any(|p| matches!(p, ProjectionElem::Deref))
    {
        let local_decls: Vec<Ty> = locals.iter().map(MirValue::ty).collect();
        let (target_local, target_proj, index_cache) =
            resolve_deref_place_in(
                &ValuesFrame {
                    locals,
                    decls: local_decls,
                    ptr_width,
                },
                place,
                false,
            )?;
        let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
        return read_projected_array_len(
            &locals[target_local.0],
            None,
            &target_proj,
            &read_index,
            ptr_width,
            place,
            None,
        );
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
    read_projected_array_len(
        root_val,
        None,
        &place.projection,
        &read_index,
        ptr_width,
        place,
        None,
    )
}

/// Evaluates a value-tree `Place` read over an initialized `locals` slice under `ptr_width`.
///
/// Supports arbitrary chains of `Deref` (into synthetic local allocations), `Field`, `Index`,
/// `ConstantIndex`, `Subslice`, and `Downcast` projections over `MirValue::{Tuple, Array, Adt}`.
///
/// `locals` carries no declared types, so a `Field(i, ty)` annotation on an intermediate step
/// is checked against the selected value's outermost constructor only, and the returned value
/// is checked in full against the last step's type. Callers must type-check `place` against
/// the local declarations first ([`resolve_place_ty`], as `lower_rvalue` does);
/// [`StatementEvalState::read_place`] performs that check itself.
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
        let local_decls: Vec<Ty> = locals.iter().map(MirValue::ty).collect();
        let (target_local, target_proj, index_cache) =
            resolve_deref_place_in(
                &ValuesFrame {
                    locals,
                    decls: local_decls,
                    ptr_width,
                },
                place,
                false,
            )?;
        let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
        return read_projected_mir_value(
            &locals[target_local.0],
            None,
            &target_proj,
            &read_index,
            ptr_width,
            place,
            None,
        );
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
    read_projected_mir_value(
        root_val,
        None,
        &place.projection,
        &read_index,
        ptr_width,
        place,
        None,
    )
}

/// Evaluates a value-tree `Place` write of `new_val` into an initialized `locals` slice under
/// `ptr_width`.
///
/// Supports arbitrary chains of `Deref` (into synthetic local allocations), `Field`, `Index`,
/// `ConstantIndex`, `Subslice`, and `Downcast` projections over `MirValue::{Tuple, Array, Adt}`.
///
/// A projected write never changes the type of a container along `place`: the replaced value
/// and `new_val` must both have the projected field or element type (a union write may switch
/// the active field), and a `Subslice` write must supply an array of the window's exact length
/// and element type. On any error `locals` is left unchanged. As with [`eval_place_read`],
/// intermediate `Field` annotations are checked by outermost constructor only, and a bare-local
/// write (empty projection) replaces the local without a type check, because `locals` carries
/// no declared types; [`StatementEvalState::write_place`] checks both against `local_decls`.
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
        let local_decls: Vec<Ty> = locals.iter().map(MirValue::ty).collect();
        let Some(base_decl_ty) = local_decls.get(place.local.0) else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        let leaf_ty = validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
            base_decl_ty,
            &place.projection,
            Some(&local_decls),
            None,
            place,
            None,
        )?;
        if !mir_value_matches_ty(&new_val, &leaf_ty) {
            return Err(RvalueEvalError::TypeMismatch(
                "written value runtime type does not match destination place type",
            ));
        }
        // A whole-place write through a final `Deref` resolves like `write_place` (it may
        // overwrite an inactive leaf union field) without cloning `locals`.
        let (target_local, target_proj, index_cache) =
            resolve_deref_place_in(
                &ValuesFrame {
                    locals,
                    decls: local_decls,
                    ptr_width,
                },
                place,
                true,
            )?;
        let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
        return write_projected_mir_value(
            &mut locals[target_local.0],
            None,
            &target_proj,
            new_val,
            &read_index,
            ptr_width,
            place,
            None,
        );
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
    write_projected_mir_value(
        &mut locals[place.local.0],
        None,
        &place.projection,
        new_val,
        &read_index,
        ptr_width,
        place,
        None,
    )
}

/// Evaluates a `NullOp` against `arg_ty` under `ptr_width`.
pub fn eval_nullary_op(
    op: &NullOp,
    arg_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    match op {
        NullOp::SizeOf => {
            let layout = arg_ty
                .layout_for(ptr_width)
                .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(arg_ty, err)))?;
            Ok(MirValue::unsigned(layout.size as u128, UintTy::Usize, ptr_width))
        }
        NullOp::AlignOf => {
            let layout = arg_ty
                .layout_for(ptr_width)
                .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(arg_ty, err)))?;
            Ok(MirValue::unsigned(layout.align as u128, UintTy::Usize, ptr_width))
        }
        NullOp::OffsetOf(fields) => {
            let offset = resolve_offset_of(arg_ty, fields, ptr_width).map_err(|err| match err {
                RvalueLowerError::LayoutTooLarge(ty) => {
                    RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge { ty })
                }
                RvalueLowerError::UnsupportedOffsetOfLayout(ty)
                | RvalueLowerError::UnsupportedLayout(ty) => {
                    RvalueEvalError::CastEval(CastEvalError::UnsupportedLayout { ty })
                }
                RvalueLowerError::InvalidAdtDef { ty, reason } => {
                    RvalueEvalError::CastEval(CastEvalError::IllFormedType { ty, reason })
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
        LoweredRvalue::Use { operand, ty } => {
            let v = eval_op(operand)?;
            if !mir_value_matches_ty(&v, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Use operand runtime type does not match lowered type",
                ));
            }
            Ok(v)
        }
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
            place,
            mutability,
            ty: ref_ty,
        }
        | LoweredRvalue::RawPtr {
            place,
            mutability,
            ty: ref_ty,
        } => {
            let expected_ref = matches!(rvalue, LoweredRvalue::Ref { .. });
            let ty_ok = match ref_ty {
                Ty::Ref(_, m) => expected_ref && m == mutability,
                Ty::RawPtr(_, m) => !expected_ref && m == mutability,
                _ => false,
            };
            if !ty_ok {
                return Err(RvalueEvalError::TypeMismatch(
                    "Ref/RawPtr lowered ty does not match rvalue kind and mutability",
                ));
            }
            let ptr = match place.projection.as_slice() {
                [] => {
                    // Synthetic, page-aligned per-local allocation with a fresh provenance.
                    let addr = if locals.is_empty() {
                        ((place.local.0 as u128 + 1) * 0x1000) & ptr_width.mask()
                    } else {
                        local_base_addr_for_values(place.local.0, locals, ptr_width)?
                    };
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
                        let masked_addr = checked_ptr_addr(&ptr, &ty, ptr_width)? as u64;
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
                _ => {
                    let Some(pointee_ty) = ref_ty.pointee_ty() else {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Ref/RawPtr lowered ty must have a pointee type",
                        ));
                    };
                    eval_projected_ref_in(
                        &ValuesFrame::new(locals, ptr_width),
                        place,
                        pointee_ty,
                        expected_ref,
                    )?
                }
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
            if *ty != Ty::Uint(UintTy::Usize) || (*static_len as u128) > ptr_width.max_usize() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len result type must be a representable usize",
                ));
            }
            if !place.projection.is_empty() || !locals.is_empty() {
                let len = eval_place_array_len(place, locals, ptr_width)?;
                if len != *static_len {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Len target array length does not match static_len",
                    ));
                }
            }
            Ok(MirValue::unsigned(*static_len as u128, UintTy::Usize, ptr_width))
        }
        LoweredRvalue::Cast { cast, ty } => {
            let op = cast.operand();
            let v = eval_op(op)?;
            // Only `PointerWithExposedProvenance` consults the frame's (value-typed) layout.
            let decls: Vec<Ty> = if matches!(cast, LoweredCast::IntToPtr { .. }) {
                locals.iter().map(MirValue::ty).collect()
            } else {
                Vec::new()
            };
            let out =
                eval_lowered_cast_with_decls(cast, &v, &decls, None, ptr_width, policy, tracker)?;
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Cast result runtime type does not match lowered ty",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::BinaryOp {
            op,
            lhs,
            rhs,
            lhs_ty,
            rhs_ty,
            ty,
            ..
        } => {
            let lv = eval_op(lhs)?;
            let rv = eval_op(rhs)?;
            if !mir_value_matches_ty(&lv, lhs_ty) || !mir_value_matches_ty(&rv, rhs_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "BinaryOp operand runtime types do not match lowered types",
                ));
            }
            let out = eval_binop(*op, &lv, &rv, ptr_width)?;
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "BinaryOp result runtime type does not match lowered type",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::CheckedBinaryOp {
            op,
            lhs,
            rhs,
            lhs_ty,
            rhs_ty,
            ty,
        } => {
            let lv = eval_op(lhs)?;
            let rv = eval_op(rhs)?;
            if !mir_value_matches_ty(&lv, lhs_ty) || !mir_value_matches_ty(&rv, rhs_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "CheckedBinaryOp operand runtime types do not match lowered types",
                ));
            }
            let (wrapped, overflowed) = eval_checked_binop(*op, &lv, &rv, ptr_width)?;
            let out = MirValue::Tuple(vec![
                MirValue::Int {
                    bits: wrapped,
                    ty: lhs_ty.clone(),
                },
                MirValue::Bool(overflowed),
            ]);
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "CheckedBinaryOp result runtime type does not match lowered type",
                ));
            }
            Ok(out)
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
        LoweredRvalue::UnaryOp {
            op,
            operand,
            operand_ty,
            ty,
        } => {
            let v = eval_op(operand)?;
            if !mir_value_matches_ty(&v, operand_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "UnaryOp operand runtime type does not match lowered type",
                ));
            }
            let out = eval_unop(*op, &v, ptr_width)?;
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "UnaryOp result runtime type does not match lowered type",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::Discriminant {
            place,
            place_ty,
            ty,
        } => {
            if *ty != discriminant_result_ty(place_ty) || !place_ty.is_inhabited_for(ptr_width) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Discriminant requires an inhabited place_ty and its discriminant result ty",
                ));
            }
            if let Ty::Adt(def) = place_ty {
                // `Rvalue::Discriminant` on a typed ADT reads only the tag (not the variant
                // payload fields), after validating the place projection over `locals` without
                // cloning `locals`.
                let target_proj: Vec<ProjectionElem>;
                let (target_local, index_cache);
                let proj_slice: &[ProjectionElem];
                if place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref))
                {
                    let local_decls: Vec<Ty> = locals.iter().map(MirValue::ty).collect();
                    let Some(base_decl_ty) = local_decls.get(place.local.0) else {
                        return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
                    };
                    let decl_place_ty = validate_projection_tail::<
                        fn(Local) -> Result<u128, RvalueEvalError>,
                    >(
                        base_decl_ty,
                        &place.projection,
                        Some(&local_decls),
                        None,
                        place,
                        None,
                    )?;
                    if decl_place_ty != *place_ty {
                        return Err(RvalueEvalError::TypeMismatch(
                            "statement place_ty does not match declared place type",
                        ));
                    }
                    (target_local, target_proj, index_cache) = resolve_deref_place_in(
                        &ValuesFrame {
                            locals,
                            decls: local_decls,
                            ptr_width,
                        },
                        place,
                        false,
                    )?;
                    proj_slice = &target_proj;
                } else {
                    target_local = place.local;
                    index_cache = Vec::new();
                    proj_slice = &place.projection;
                }
                let root_val = locals
                    .get(target_local.0)
                    .ok_or(RvalueEvalError::TypeMismatch("local index out of bounds"))?;
                let read_index = |idx_local: Local| -> Result<u128, RvalueEvalError> {
                    if !index_cache.is_empty() {
                        return cached_index(&index_cache, idx_local);
                    }
                    match locals.get(idx_local.0) {
                        Some(MirValue::Int {
                            bits,
                            ty: Ty::Uint(UintTy::Usize),
                        }) if *bits <= ptr_width.max_usize() => Ok(*bits),
                        None => Err(RvalueEvalError::TypeMismatch(
                            "local index out of bounds",
                        )),
                        _ => Err(RvalueEvalError::TypeMismatch(
                            "array index local must hold a valid usize value",
                        )),
                    }
                };
                let (target, _) = project_mir_value(
                    root_val,
                    None,
                    proj_slice,
                    &read_index,
                    place,
                    None,
                )?;
                return match target {
                    ProjectedRef::Value(val @ MirValue::Adt { variant_idx, .. })
                        if mir_value_head_matches_ty(val, place_ty) =>
                    {
                        if !def.tag_survives_field_deinit() {
                            if !mir_value_matches_ty(val, place_ty) {
                                return Err(RvalueEvalError::TypeMismatch(
                                    "Discriminant place runtime value does not match lowered place_ty",
                                ));
                            }
                            check_value_well_formed(val, ptr_width)?;
                        }
                        discriminant_value(def, *variant_idx, ptr_width)
                    }
                    _ => Err(RvalueEvalError::TypeMismatch(
                        "Discriminant place runtime value does not match lowered place_ty",
                    )),
                };
            }
            let val = read_place(place)?;
            if !mir_value_matches_ty(&val, place_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Discriminant place runtime value does not match lowered place_ty",
                ));
            }
            match (&val, place_ty) {
                (MirValue::Adt { variant_idx, .. }, Ty::Adt(def)) => {
                    discriminant_value(def, *variant_idx, ptr_width)
                }
                (
                    MirValue::Adt {
                        variant_idx,
                        active_field: None,
                        ..
                    },
                    _,
                ) => Ok(MirValue::signed(*variant_idx as i128, IntTy::Isize, ptr_width)),
                _ => Ok(MirValue::signed(0, IntTy::Isize, ptr_width)),
            }
        }
        LoweredRvalue::Aggregate {
            kind,
            operands,
            operand_tys,
            ty,
        } => {
            if operands.len() != operand_tys.len() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Aggregate operands length does not match lowered operand_tys",
                ));
            }
            let mut vals = Vec::with_capacity(operands.len());
            for (op, op_ty) in operands.iter().zip(operand_tys) {
                let v = eval_op(op)?;
                if !mir_value_matches_ty(&v, op_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Aggregate operand runtime type does not match lowered operand_ty",
                    ));
                }
                vals.push(v);
            }
            let out = eval_aggregate(kind, vals, ptr_width)?;
            let ty_ok = match kind {
                AggregateKind::Adt {
                    active_field: Some(_),
                    ..
                } => *ty == Ty::Tuple(operand_tys.clone()) || mir_value_matches_ty(&out, ty),
                _ => mir_value_matches_ty(&out, ty),
            };
            if !ty_ok {
                return Err(RvalueEvalError::TypeMismatch(
                    "Aggregate result runtime type does not match lowered ty",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::CopyForDeref { place, ty } => match read_place(place)? {
            MirValue::Ptr { ptr, ty: val_ty } if val_ty == *ty && ty.is_any_ptr() => {
                let masked_addr = checked_ptr_addr(&ptr, ty, ptr_width)? as u64;
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
        LoweredRvalue::ShallowInitBox {
            operand,
            operand_ty,
            ty,
        } => eval_shallow_init_box(&eval_op(operand)?, operand_ty, ty, ptr_width),
        LoweredRvalue::WrapUnsafeBinder {
            operand,
            operand_ty,
            ty,
        } => eval_wrap_unsafe_binder(eval_op(operand)?, operand_ty, ty, ptr_width),
    }
}

/// `Rvalue::Discriminant` result for variant `variant_idx` of `def`: its discriminant bits
/// typed [`AdtDef::discr_ty`].
fn discriminant_value(
    def: &Arc<AdtDef>,
    variant_idx: usize,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    if def.is_enum()
        && let Some(fields) = def.variant_fields(variant_idx)
        && !fields.iter().all(|f| f.is_inhabited_for(ptr_width))
    {
        return Err(RvalueEvalError::UninhabitedEnumVariant {
            variant_index: variant_idx,
        });
    }
    let bits = def.discriminant_bits(variant_idx, ptr_width).map_err(|err| {
        RvalueEvalError::CastEval(cast_eval_layout_error(&Ty::Adt(def.clone()), err))
    })?;
    Ok(MirValue::Int {
        bits,
        ty: def.discr_ty(),
    })
}

/// Evaluates `ShallowInitBox` on the evaluated raw pointer `val`: the same address (masked to
/// `ptr_width`) and provenance, typed `ty` (`*mut T`).
fn eval_shallow_init_box(
    val: &MirValue,
    operand_ty: &Ty,
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    let Ty::RawPtr(inner_ty, Mutability::Mut) = ty else {
        return Err(RvalueEvalError::TypeMismatch(
            "ShallowInitBox result type must be a mutable raw pointer *mut T",
        ));
    };
    inner_ty.check_representable(ptr_width).map_err(|err| {
        RvalueEvalError::CastEval(cast_eval_layout_error(inner_ty, err))
    })?;
    match val {
        MirValue::Ptr { ptr, ty: val_ty } if val_ty == operand_ty && val_ty.is_raw_ptr() => {
            Ok(MirValue::Ptr {
                ptr: PointerValue {
                    addr: (u128::from(ptr.addr) & ptr_width.mask()) as u64,
                    provenance: ptr.provenance,
                },
                ty: ty.clone(),
            })
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "ShallowInitBox requires a raw pointer operand matching its lowered type",
        )),
    }
}

/// Evaluates `WrapUnsafeBinder` on `val`: unchanged when `ty` is the operand type, otherwise
/// wrapped as the single field of the struct `ty` (enforcing its `scalar_valid_range`).
fn eval_wrap_unsafe_binder(
    val: MirValue,
    operand_ty: &Ty,
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<MirValue, RvalueEvalError> {
    ty.check_representable(ptr_width).map_err(|err| {
        RvalueEvalError::CastEval(cast_eval_layout_error(ty, err))
    })?;
    if !mir_value_matches_ty(&val, operand_ty) {
        return Err(RvalueEvalError::TypeMismatch(
            "WrapUnsafeBinder operand runtime type does not match lowered type",
        ));
    }
    check_value_well_formed(&val, ptr_width)?;
    if ty == operand_ty {
        return Ok(val);
    }
    match ty {
        Ty::Adt(def) if wrapped_field_ty(ty) == Some(operand_ty) => {
            let out = MirValue::adt(def, 0, vec![val]);
            check_scalar_ranges(&out, ptr_width)?;
            Ok(out)
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "WrapUnsafeBinder type does not wrap the operand type",
        )),
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
    /// Definition of a typed ADT shell (`Ty::Adt` place): promotes to a typed
    /// `MirValue::Adt`, and requires `discriminant_set` only when
    /// [`AdtDef::requires_tag_write`]. `None` for tuples and legacy tuple-modeled ADTs.
    pub adt_def: Option<Arc<AdtDef>>,
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
            adt_def: None,
        }
    }

    /// Creates an all-uninitialized shell for variant `variant_idx` of the typed ADT `def`,
    /// with an unwritten tag. Returns `None` if the variant does not exist or `def` is a union
    /// (union fields overlap, so unions never get per-field shells).
    pub fn new_uninit_adt(def: &Arc<AdtDef>, variant_idx: usize) -> Option<Self> {
        if def.is_union() {
            return None;
        }
        let field_count = def.variant_fields(variant_idx)?.len();
        Some(PartialAggregate {
            def_path: Some(def.def_path.clone()),
            variant_idx,
            is_adt: true,
            discriminant_set: false,
            fields: vec![FieldSlot::Uninit; field_count],
            adt_def: Some(def.clone()),
        })
    }

    /// Returns true if a whole-value read of this shell needs its tag written first: enum
    /// shells of a legacy tuple-modeled ADT (`is_adt` without `adt_def`) and typed shells
    /// whose ADT stores a tag ([`AdtDef::requires_tag_write`]).
    pub fn requires_tag_write(&self) -> bool {
        match &self.adt_def {
            Some(def) => def.requires_tag_write(),
            None => self.is_adt,
        }
    }

    /// Returns true if the variant of this (incomplete) shell can be read from its tag
    /// without reading its possibly uninitialized fields, as `Rvalue::Discriminant` and
    /// `Statement::Retag` do: always for a shell whose ADT stores no tag, and otherwise once
    /// `SetDiscriminant` has written a tag that is stored apart from the variant fields
    /// ([`AdtDef::tag_survives_field_deinit`]; legacy tuple-modeled shells keep the rule that a
    /// written tag is readable).
    ///
    /// A typed enum whose tag may be niche-encoded in a variant field (a tagless `repr(Rust)`
    /// enum with several present variants) has no readable tag until the value is complete:
    /// `SetDiscriminant` of the variant `rustc` leaves untagged writes no bytes at all, so its
    /// discriminant is decoded from the (still uninitialized) niche field, which is undefined
    /// behavior in MiniRust (and `InvalidNichedEnumVariantWritten` in Miri). This mirrors the
    /// rule that deinitializing a variant field of such an enum loses its tag.
    pub fn tag_is_readable(&self) -> bool {
        match &self.adt_def {
            Some(def) => {
                !def.requires_tag_write()
                    || (self.discriminant_set && def.tag_survives_field_deinit())
            }
            None => !self.is_adt || self.discriminant_set,
        }
    }

    /// Returns true if the shell has no initialized field and no written tag that matters
    /// (only shells needing a tag write remember their tag), i.e. it is indistinguishable from
    /// an uninitialized place.
    pub fn is_empty(&self) -> bool {
        (!self.discriminant_set || !self.requires_tag_write())
            && self.fields.iter().all(|f| matches!(f, FieldSlot::Uninit))
    }

    /// Returns `Some(MirValue)` if every field in `self.fields` is `FieldSlot::Init` and, for
    /// an enum/ADT shell (`is_adt`), the variant tag has been written by `SetDiscriminant`.
    ///
    /// A typed shell (`adt_def: Some(def)`) promotes to a typed `MirValue::Adt` and only needs
    /// its tag written when `def` stores one ([`PartialAggregate::requires_tag_write`]).
    pub fn try_into_mir_value(&self) -> Option<MirValue> {
        if self.requires_tag_write() && !self.discriminant_set {
            return None;
        }
        if !self.fields.iter().all(|f| matches!(f, FieldSlot::Init(_))) {
            return None;
        }
        let mut init_fields = Vec::with_capacity(self.fields.len());
        for f in &self.fields {
            match f {
                FieldSlot::Init(v) => init_fields.push(v.clone()),
                FieldSlot::Uninit | FieldSlot::Partial(_) => return None,
            }
        }
        if let Some(def) = &self.adt_def {
            Some(MirValue::adt(def, self.variant_idx, init_fields))
        } else if self.is_adt {
            Some(MirValue::Adt {
                def_path: self.def_path.clone().unwrap_or_default(),
                variant_idx: self.variant_idx,
                active_field: None,
                fields: init_fields,
                adt_def: None,
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
    /// remaining temporaries start `Dead` (awaiting `StorageLive`). Every argument must match
    /// its parameter type and be well formed (valid scalar bits, non-null references, ADT
    /// scalar valid ranges).
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
            check_value_well_formed(arg, body.ptr_width)?;
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

    /// Reads an index local as a `usize` bit pattern, returning `TypeMismatch` if the local is
    /// out of bounds or not declared as `usize`, and `DeadLocal` or `UninitializedLocal` if its
    /// slot is not initialized.
    fn read_index_local(&self, idx_local: Local) -> Result<u128, RvalueEvalError> {
        match self.local_decls.get(idx_local.0) {
            None => {
                return Err(RvalueEvalError::TypeMismatch(
                    "index local index out of bounds",
                ));
            }
            Some(Ty::Uint(UintTy::Usize)) => {}
            Some(_) => {
                return Err(RvalueEvalError::TypeMismatch(
                    "array index local must have declared type usize",
                ));
            }
        }
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

    /// Checks every projection step of `place` against `self.local_decls`: field indices and
    /// `Field` type annotations, array projections on array types, `Index(idx_local)` local
    /// bounds and `usize` declaration, `Downcast` followed immediately by `Field`, and static
    /// `ConstantIndex` / `Subslice` bounds. Returns the declared type of `place`.
    ///
    /// This is a type-level check whose cost depends on the projection and the declared types
    /// only, not on the size of the local's value. Projection traversals check intermediate
    /// values by their outermost constructor, so this check is what rejects a `Field`
    /// annotation that differs from the declared field type below the outermost constructor.
    fn check_place_against_decls(&self, place: &Place) -> Result<Ty, RvalueEvalError> {
        let Some(base_decl_ty) = self.local_decls.get(place.local.0) else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
            base_decl_ty,
            &place.projection,
            Some(&self.local_decls),
            None,
            place,
            None,
        )
    }

    /// Synthetic allocation base address of `local` in this frame (see
    /// [`local_base_addr_for_decls`]: `UnsupportedMemoryAccess` when the local's synthetic
    /// allocation does not fit the target address space).
    pub(crate) fn local_base_addr(&self, local: usize) -> Result<u128, RvalueEvalError> {
        local_base_addr_for_decls(local, &self.local_decls, self.ptr_width)
    }

    /// Maps a synthetic local or sub-place pointer `ptr` (of type `ptr_ty` with pointee
    /// `pointee_ty`) back to `(Local(target_local), prefix_proj)` in `self.local_decls`.
    pub(crate) fn resolve_synthetic_subplace(
        &self,
        ptr: &PointerValue,
        ptr_ty: &Ty,
        pointee_ty: &Ty,
        full_place: &Place,
    ) -> Result<(Local, Vec<ProjectionElem>), RvalueEvalError> {
        self.resolve_synthetic_subplace_with_mode(ptr, ptr_ty, pointee_ty, full_place, false)
    }

    /// [`Self::resolve_synthetic_subplace`] for a final `Deref` of a whole-place write when
    /// `allow_union_overwrite` (see [`resolve_synthetic_subplace_in`]).
    pub(crate) fn resolve_synthetic_subplace_with_mode(
        &self,
        ptr: &PointerValue,
        ptr_ty: &Ty,
        pointee_ty: &Ty,
        full_place: &Place,
        allow_union_overwrite: bool,
    ) -> Result<(Local, Vec<ProjectionElem>), RvalueEvalError> {
        resolve_synthetic_subplace_in(
            self,
            ptr,
            ptr_ty,
            pointee_ty,
            full_place,
            allow_union_overwrite,
        )
    }

    /// Reads the value at the `Deref`-free `(target_local, target_proj)` from `self.slots`.
    fn read_resolved_place(
        &self,
        target_local: Local,
        target_proj: &[ProjectionElem],
        index_cache: &[(Local, u128)],
        full_place: &Place,
    ) -> Result<MirValue, RvalueEvalError> {
        read_frame_place(self, target_local, target_proj, index_cache, full_place)
    }

    /// Resolves all `ProjectionElem::Deref` steps in `place` from left to right and pre-reads any
    /// trailing `ProjectionElem::Index(idx_local)` operands into `index_cache`, returning the
    /// resolved `(target_local, target_proj, index_cache)`.
    #[allow(clippy::type_complexity)]
    fn resolve_deref_place(
        &self,
        place: &Place,
    ) -> Result<(Local, Vec<ProjectionElem>, Vec<(Local, u128)>), RvalueEvalError> {
        self.resolve_deref_place_with_mode(place, false)
    }

    #[allow(clippy::type_complexity)]
    fn resolve_deref_place_with_mode(
        &self,
        place: &Place,
        allow_final_union_overwrite: bool,
    ) -> Result<(Local, Vec<ProjectionElem>, Vec<(Local, u128)>), RvalueEvalError> {
        resolve_deref_place_in(self, place, allow_final_union_overwrite)
    }

    /// Reads the value at `place` from `self.slots` without moving it.
    pub fn read_place(&self, place: &Place) -> Result<MirValue, RvalueEvalError> {
        let (target_local, target_proj, index_cache) = self.resolve_deref_place(place)?;
        self.read_resolved_place(target_local, &target_proj, &index_cache, place)
    }

    /// Resolves the runtime array length at `place` from `self.slots` in `O(place.projection.len())`
    /// time without cloning or scanning array elements, verifying that the declared array length
    /// matches `expected_static_len`.
    fn read_place_array_len(
        &self,
        place: &Place,
        expected_static_len: usize,
    ) -> Result<usize, RvalueEvalError> {
        let Ty::Array(_, decl_len) = self.check_place_against_decls(place)? else {
            return Err(RvalueEvalError::TypeMismatch(
                "Len target place must have array type",
            ));
        };
        if decl_len != expected_static_len {
            return Err(RvalueEvalError::TypeMismatch(
                "Len target declared array length does not match static_len",
            ));
        }
        let (target_local, target_proj, index_cache) = self.resolve_deref_place(place)?;
        let Some(base_decl_ty) = self.local_decls.get(target_local.0) else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        let read_index = |loc: Local| cached_index(&index_cache, loc);
        match self.slots.get(target_local.0) {
            None => Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
            Some(LocalSlotState::Dead) => Err(RvalueEvalError::DeadLocal(target_local)),
            Some(LocalSlotState::Uninit) => Err(RvalueEvalError::UninitializedLocal(target_local)),
            Some(LocalSlotState::Init(root_val)) => {
                if !mir_value_head_matches_ty(root_val, base_decl_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "initialized local runtime value does not match local declaration type",
                    ));
                }
                read_projected_array_len(
                    root_val,
                    Some(base_decl_ty),
                    &target_proj,
                    &read_index,
                    self.ptr_width,
                    place,
                    None,
                )
            }
            Some(LocalSlotState::PartialShell(shell)) => read_array_len_from_partial_shell(
                shell,
                base_decl_ty,
                &target_proj,
                &read_index,
                self.ptr_width,
                target_local,
                place,
                None,
            ),
        }
    }

    /// Reads the value at `place` for `Operand::Move`, matching
    /// `Trusted.MirSemantics.evalOperand` on `.move`:
    /// - a bare local (`place.projection` empty) is read and then becomes
    ///   `LocalSlotState::Uninit`;
    /// - a projected place (`_1.0`, `(_1 as V).0`, `_1[_2]`, `*_p`, ...) is read and the root
    ///   local's slot is left unchanged, so the parent aggregate stays initialized.
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
    /// through `Deref` and `Field` / `Downcast`+`Field` steps over partially initialized shells,
    /// to a [`PartialAggregate`] whose variant tag has been written by `SetDiscriminant`.
    ///
    /// `Rvalue::Discriminant` reads only the tag, so it is defined on such a shell even while
    /// some variant fields are still uninitialized.
    fn tagged_shell_variant(&self, place: &Place) -> Option<usize> {
        let (target_local, target_proj, index_cache) = self.resolve_deref_place(place).ok()?;
        let base_decl_ty = self.local_decls.get(target_local.0)?;
        let Some(LocalSlotState::PartialShell(root)) = self.slots.get(target_local.0) else {
            return None;
        };
        let read_index = |loc: Local| cached_index(&index_cache, loc);
        match project_from_partial_shell(
            root,
            base_decl_ty,
            &target_proj,
            &read_index,
            self.ptr_width,
            target_local,
            place,
            None,
        )
        .ok()?
        {
            ProjectedShellRef::Shell(shell, _) if shell.is_adt && shell.discriminant_set => {
                Some(shell.variant_idx)
            }
            _ => None,
        }
    }

    /// Checks the projection of `place` against the local declarations (must have declared type
    /// `place_ty`), that the root local and any dereferenced target local are live (`DeadLocal`
    /// otherwise), and reads every `Index(idx_local)` operand in order (faulting on dead or
    /// uninitialized index locals), without reading or changing the target place itself.
    pub fn check_place_access(&self, place: &Place, place_ty: &Ty) -> Result<(), RvalueEvalError> {
        self.prepare_place_access(place, place_ty).map(|_| ())
    }

    /// [`Self::check_place_access`] for a place about to be written as a whole (a `Call`
    /// destination): the place is evaluated exactly as [`Self::write_place`] evaluates it, so a
    /// final `Deref` may designate an inactive leaf union field that the write overwrites
    /// (switching the union's active field, as a direct `u.b = v` does).
    pub fn check_place_write_access(
        &self,
        place: &Place,
        place_ty: &Ty,
    ) -> Result<(), RvalueEvalError> {
        self.prepare_place_access_with_mode(place, place_ty, true)
            .map(|_| ())
    }

    /// Evaluates an operand in this state: `Copy` reads the place, `Move` reads it and (for a
    /// bare local) deinitializes it (see [`StatementEvalState::move_place`]), and `Constant`
    /// is validated and evaluated.
    pub fn eval_operand(&mut self, operand: &Operand) -> Result<MirValue, RvalueEvalError> {
        match operand {
            Operand::Copy(place) => self.read_place(place),
            Operand::Move(place) => self.move_place(place),
            Operand::Constant(c) => eval_constant(c, self.ptr_width),
        }
    }

    /// Checks the projection of `place` against the local declarations (must have declared type
    /// `place_ty`), resolves any `ProjectionElem::Deref` steps, verifies that the root and target
    /// locals are live (`DeadLocal` otherwise), and reads every `Index(idx_local)` operand in
    /// order, returning `(target_local, target_proj, index_cache)`.
    #[allow(clippy::type_complexity)]
    fn prepare_place_access(
        &self,
        place: &Place,
        place_ty: &Ty,
    ) -> Result<(Local, Vec<ProjectionElem>, Vec<(Local, u128)>), RvalueEvalError> {
        self.prepare_place_access_with_mode(place, place_ty, false)
    }

    /// [`Self::prepare_place_access`], resolving a final `Deref` for a whole-place write when
    /// `allow_final_union_overwrite` (see [`Self::resolve_synthetic_subplace_with_mode`]).
    #[allow(clippy::type_complexity)]
    fn prepare_place_access_with_mode(
        &self,
        place: &Place,
        place_ty: &Ty,
        allow_final_union_overwrite: bool,
    ) -> Result<(Local, Vec<ProjectionElem>, Vec<(Local, u128)>), RvalueEvalError> {
        if self.local_decls.get(place.local.0).is_none() {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        }
        let decl_place_ty = self.check_place_against_decls(place)?;
        if decl_place_ty != *place_ty {
            return Err(RvalueEvalError::TypeMismatch(
                "statement place_ty does not match declared place type",
            ));
        }
        let (target_local, target_proj, index_cache) =
            self.resolve_deref_place_with_mode(place, allow_final_union_overwrite)?;
        let Some(base_decl_ty) = self.local_decls.get(target_local.0) else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        let Some(slot) = self.slots.get(target_local.0) else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        if matches!(slot, LocalSlotState::Dead) {
            return Err(RvalueEvalError::DeadLocal(target_local));
        }
        let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
        validate_projection_tail(
            base_decl_ty,
            &target_proj,
            Some(&self.local_decls),
            Some(&read_index),
            place,
            None,
        )?;
        check_slot_projection(slot, base_decl_ty, &target_proj, &read_index, place)?;
        Ok((target_local, target_proj, index_cache))
    }

    /// Variant index read from the tag of the typed enum at `(target_local, target_proj)` for
    /// `Rvalue::Discriminant`, without reading (or requiring initialized) variant fields: an
    /// initialized value's variant, or a shell's variant once its tag is readable
    /// ([`PartialAggregate::tag_is_readable`]).
    fn typed_enum_variant(
        &self,
        target_local: Local,
        target_proj: &[ProjectionElem],
        full_place: &Place,
        place_ty: &Ty,
        index_cache: &[(Local, u128)],
    ) -> Result<usize, RvalueEvalError> {
        let base_decl_ty = &self.local_decls[target_local.0];
        let read_index = |idx_local: Local| cached_index(index_cache, idx_local);
        let variant_of = |val: &MirValue| match val {
            MirValue::Adt {
                variant_idx,
                adt_def,
                ..
            } if mir_value_head_matches_ty(val, place_ty) => {
                if adt_def
                    .as_ref()
                    .is_some_and(|def| !def.tag_survives_field_deinit())
                {
                    if !mir_value_matches_ty(val, place_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Discriminant place runtime value does not match lowered place_ty",
                        ));
                    }
                    check_value_well_formed(val, self.ptr_width)?;
                }
                Ok(*variant_idx)
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "Discriminant place runtime value does not match lowered place_ty",
            )),
        };
        match &self.slots[target_local.0] {
            LocalSlotState::Dead => Err(RvalueEvalError::DeadLocal(target_local)),
            LocalSlotState::Uninit => Err(RvalueEvalError::UninitializedLocal(target_local)),
            LocalSlotState::Init(root) => {
                match project_mir_value(
                    root,
                    Some(base_decl_ty),
                    target_proj,
                    &read_index,
                    full_place,
                    None,
                )? {
                    (ProjectedRef::Value(val), _) => variant_of(val),
                    (ProjectedRef::ArrayWindow { .. }, _) => Err(RvalueEvalError::TypeMismatch(
                        "Discriminant place must not be an array window",
                    )),
                }
            }
            LocalSlotState::PartialShell(root) => match project_from_partial_shell(
                root,
                base_decl_ty,
                target_proj,
                &read_index,
                self.ptr_width,
                target_local,
                full_place,
                None,
            )? {
                ProjectedShellRef::Shell(shell, _) => {
                    if shell.tag_is_readable() {
                        Ok(shell.variant_idx)
                    } else {
                        Err(RvalueEvalError::UninitializedLocal(target_local))
                    }
                }
                ProjectedShellRef::Init(ProjectedRef::Value(val), _) => variant_of(val),
                ProjectedShellRef::Init(ProjectedRef::ArrayWindow { .. }, _) => {
                    Err(RvalueEvalError::TypeMismatch(
                        "Discriminant place must not be an array window",
                    ))
                }
            },
        }
    }

    /// Evaluates `Statement::Deinit(place)` (of declared type `place_ty`).
    ///
    /// Requires a live root local (`DeadLocal`), resolves every `Deref` step to its synthetic
    /// target sub-place (which must be live as well, see [`Self::resolve_synthetic_subplace`])
    /// while reading the `Index` operands in place-evaluation order, then, on the resolved
    /// `(target_local, target_proj)`:
    /// - a bare (or wholly dereferenced) local becomes `LocalSlotState::Uninit`; `Deinit(*p)`
    ///   never deinitializes the pointer local `p` itself;
    /// - a projected place through tuple/struct fields and `Downcast` variant fields demotes the
    ///   containing values to `PartialShell`s whose target slot is `FieldSlot::Uninit`, keeping
    ///   every disjoint sibling (and the enum tag when it is stored apart from the fields, see
    ///   [`AdtDef::tag_survives_field_deinit`]) initialized; writing the place again re-promotes
    ///   the shells to `Init`;
    /// - a place inside an already uninitialized part is a no-op (after the static and dynamic
    ///   bounds checks);
    /// - a `Downcast` to an inactive variant of an initialized enum is
    ///   `InactiveVariantProjection` (as for assignments); a place inside an initialized array
    ///   element or union field is `UnsupportedPlaceProjection` (arrays and unions have no
    ///   per-element shells).
    ///
    /// Deinitializing a zero-sized part still marks it uninitialized (Anneal tracks
    /// initialization per field, like `rustc`'s move paths, rather than per byte).
    pub fn deinit_place(&mut self, place: &Place, place_ty: &Ty) -> Result<(), RvalueEvalError> {
        let (target_local, target_proj, index_cache) = self.prepare_place_access(place, place_ty)?;
        if target_proj.is_empty() {
            self.slots[target_local.0] = LocalSlotState::Uninit;
            return Ok(());
        }
        let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
        let mut root_slot = take_root_slot(&mut self.slots[target_local.0]);
        let res = deinit_in_slot(
            &mut root_slot,
            &self.local_decls[target_local.0],
            &target_proj,
            &read_index,
            place,
            None,
        );
        normalize_slot(&mut root_slot);
        self.slots[target_local.0] = root_slot_state(root_slot);
        res
    }

    /// Evaluates `Statement::Retag(kind, place)` (of declared type `place_ty`).
    ///
    /// Requires a live root local, resolves every `Deref` step to its (live) synthetic target
    /// sub-place, and reads the `Index` operands. `RetagKind::Raw(m)` reads the raw pointer at
    /// `place` (it must be initialized and its address must fit the target's pointer width; it
    /// may be null, unaligned, or dangling).
    /// The other kinds validate every reference reachable in `place`'s value without
    /// indirection (see [`Ty::contains_ref`]): each must be initialized, non-null, within the
    /// target's pointer width, aligned to its pointee's alignment, point to an inhabited type,
    /// and must not point into the synthetic allocation of a storage-dead local (at its base
    /// address or at any sub-place offset, e.g. `&_s.1`) unless its pointee is zero-sized
    /// (`DeadLocal`: the reference dangles). A place whose type holds no references only needs
    /// to be live. Anneal does not model aliasing tags, so the value is unchanged.
    pub fn retag_place(
        &self,
        kind: RetagKind,
        place: &Place,
        place_ty: &Ty,
    ) -> Result<(), RvalueEvalError> {
        let (target_local, target_proj, index_cache) = self.prepare_place_access(place, place_ty)?;
        if let RetagKind::Raw(mutability) = kind {
            if !matches!(place_ty, Ty::RawPtr(_, m) if *m == mutability) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Retag(Raw) requires a raw pointer place of matching mutability",
                ));
            }
            return match self.read_resolved_place(target_local, &target_proj, &index_cache, place)? {
                // A raw pointer may be null, unaligned, or dangling, but its address must still
                // be a valid bit pattern of the target's pointer width.
                val @ MirValue::Ptr { .. } => check_value_well_formed(&val, self.ptr_width),
                _ => Err(RvalueEvalError::TypeMismatch(
                    "Retag(Raw) place must hold a pointer value",
                )),
            };
        }
        if !place_ty.contains_ref() {
            return Ok(());
        }
        let base_decl_ty = &self.local_decls[target_local.0];
        let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
        let ctx = RetagCtx {
            ptr_width: self.ptr_width,
            slots: &self.slots,
        };
        match &self.slots[target_local.0] {
            LocalSlotState::Dead => Err(RvalueEvalError::DeadLocal(target_local)),
            LocalSlotState::Uninit => Err(RvalueEvalError::UninitializedLocal(target_local)),
            LocalSlotState::Init(root) => {
                let (target, _) = project_mir_value(
                    root,
                    Some(base_decl_ty),
                    &target_proj,
                    &read_index,
                    place,
                    None,
                )?;
                retag_projected(target, place_ty, ctx)
            }
            LocalSlotState::PartialShell(root) => match project_from_partial_shell(
                root,
                base_decl_ty,
                &target_proj,
                &read_index,
                self.ptr_width,
                target_local,
                place,
                None,
            )? {
                ProjectedShellRef::Shell(shell, _) => {
                    retag_shell(shell, place_ty, ctx, target_local)
                }
                ProjectedShellRef::Init(target, _) => retag_projected(target, place_ty, ctx),
            },
        }
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
        let decl_place_ty = self.check_place_against_decls(place)?;
        if decl_place_ty != *place_ty {
            return Err(RvalueEvalError::TypeMismatch(
                "destination place_ty does not match declared place type",
            ));
        }
        if self.local_decls.get(place.local.0).is_none() {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        }
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
        let (target_local, target_proj, index_cache) =
            self.resolve_deref_place_with_mode(place, true)?;
        let Some(base_decl_ty) = self.local_decls.get(target_local.0) else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        if target_proj.is_empty() {
            if !mir_value_matches_ty(&val, base_decl_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "assigned value runtime type does not match local declaration type",
                ));
            }
            self.slots[target_local.0] = LocalSlotState::Init(val);
            return Ok(());
        }

        let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);

        let mut root_slot = match std::mem::replace(
            &mut self.slots[target_local.0],
            LocalSlotState::Uninit,
        ) {
            LocalSlotState::Dead => {
                self.slots[target_local.0] = LocalSlotState::Dead;
                return Err(RvalueEvalError::DeadLocal(target_local));
            }
            LocalSlotState::Uninit => FieldSlot::Uninit,
            LocalSlotState::PartialShell(shell) => FieldSlot::Partial(shell),
            LocalSlotState::Init(v) => FieldSlot::Init(v),
        };

        let write_res = write_to_partial_slot(
            &mut root_slot,
            &self.local_decls[target_local.0],
            &target_proj,
            val,
            &read_index,
            self.ptr_width,
            target_local,
            place,
            None,
        );

        self.slots[target_local.0] = match root_slot {
            FieldSlot::Uninit => LocalSlotState::Uninit,
            FieldSlot::Partial(shell) => {
                if write_res.is_ok() {
                    if let Some(full_val) = shell.try_into_mir_value() {
                        LocalSlotState::Init(full_val)
                    } else {
                        LocalSlotState::PartialShell(shell)
                    }
                } else {
                    LocalSlotState::PartialShell(shell)
                }
            }
            FieldSlot::Init(v) => LocalSlotState::Init(v),
        };
        write_res
    }

    /// Reads the [`FieldSlot`] (`Uninit`, `Partial`, or `Init`) at `(target_local, target_proj)`,
    /// cloning only the selected sub-slot.
    fn read_subplace_slot(
        &self,
        target_local: Local,
        target_proj: &[ProjectionElem],
        full_place: &Place,
    ) -> Result<FieldSlot, RvalueEvalError> {
        let Some(base_decl_ty) = self.local_decls.get(target_local.0) else {
            return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
        };
        let root_slot = match self.slots.get(target_local.0) {
            None => return Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
            Some(LocalSlotState::Dead) => return Err(RvalueEvalError::DeadLocal(target_local)),
            Some(LocalSlotState::Uninit) => SlotRef::Uninit,
            Some(LocalSlotState::PartialShell(s)) => SlotRef::Partial(s),
            Some(LocalSlotState::Init(v)) => SlotRef::Init(v),
        };
        read_slot_at_proj(root_slot, base_decl_ty, target_proj, full_place, None)
    }

    /// Writes `new_slot` (`Uninit`, `Partial`, or `Init`) into `(dst_local, dst_proj)` of type
    /// `expected_ty`.
    ///
    /// An `Init` slot is an ordinary write ([`Self::write_place`]). A non-`Init` slot that the
    /// value tree cannot hold at the destination is never stored as a guess:
    /// - inside a union field (a union value is one initialized field), it is
    ///   `UnsupportedMemoryAccess`, unless an uninitialized slot lands on an already
    ///   uninitialized destination (no change);
    /// - in an array element (arrays have no per-element `Uninit` / `PartialShell` slots,
    ///   `c6d2ad74`), an uninitialized slot leaves an uninitialized array unchanged and
    ///   deinitializes a 1-element array `[T; 1]` whose element 0 it covers, while any other
    ///   element write fails closed with `UninitializedLocal` (as an element write into an
    ///   uninitialized array does).
    fn write_subplace_slot(
        &mut self,
        dst_local: Local,
        dst_proj: &[ProjectionElem],
        expected_ty: &Ty,
        new_slot: FieldSlot,
        src_local: Local,
        full_place: &Place,
    ) -> Result<(), RvalueEvalError> {
        // Element `0` of a 1-element array `[T; 1]` (canonically `ConstantIndex { offset: 0,
        // min_length: 1 }`, whose `min_length` is the array length) covers the entire array, so
        // writing `Init(val)` or `Uninit` to it initializes or deinitializes the 1-element array
        // itself. (A canonical `Subslice { from: 0, to: 1 }` is a proper window of a longer
        // array, never the whole array, so it is not stripped.)
        let mut dst_proj = dst_proj;
        if let FieldSlot::Init(mut val) = new_slot {
            let mut cur_ty = expected_ty.clone();
            while let Some((
                ProjectionElem::ConstantIndex {
                    offset: 0,
                    min_length: 1,
                    from_end: false,
                },
                prefix,
            )) = dst_proj.split_last()
            {
                val = MirValue::Array {
                    elements: vec![val],
                    elem_ty: cur_ty.clone(),
                };
                cur_ty = Ty::Array(Box::new(cur_ty), 1);
                dst_proj = prefix;
            }
            let dst_place = Place {
                local: dst_local,
                projection: dst_proj.to_vec(),
            };
            return self.write_place(&dst_place, &cur_ty, val);
        }
        if matches!(new_slot, FieldSlot::Uninit) {
            while let Some((
                ProjectionElem::ConstantIndex {
                    offset: 0,
                    min_length: 1,
                    from_end: false,
                },
                prefix,
            )) = dst_proj.split_last()
            {
                dst_proj = prefix;
            }
        }
        if proj_traverses_union(&self.local_decls[dst_local.0], dst_proj) {
            if matches!(new_slot, FieldSlot::Uninit)
                && matches!(
                    self.read_subplace_slot(dst_local, dst_proj, full_place),
                    Ok(FieldSlot::Uninit)
                )
            {
                return Ok(());
            }
            return Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY));
        }
        // Array elements do not have per-element `Uninit` / `PartialShell` slots (`c6d2ad74`).
        if dst_proj.iter().any(|p| {
            matches!(
                p,
                ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            )
        }) {
            // Uninitialized bytes copied over uninitialized bytes: nothing changes.
            if matches!(new_slot, FieldSlot::Uninit)
                && matches!(
                    self.read_subplace_slot(dst_local, dst_proj, full_place),
                    Ok(FieldSlot::Uninit)
                )
            {
                return Ok(());
            }
            if matches!(self.slots.get(dst_local.0), Some(LocalSlotState::Uninit)) {
                return Err(RvalueEvalError::UninitializedLocal(dst_local));
            }
            return Err(RvalueEvalError::UninitializedLocal(src_local));
        }
        if dst_proj.is_empty() {
            let mut slot = new_slot;
            normalize_slot(&mut slot);
            self.slots[dst_local.0] = root_slot_state(slot);
            return Ok(());
        }
        let no_index = |_: Local| -> Result<u128, RvalueEvalError> {
            Err(RvalueEvalError::TypeMismatch("unexpected dynamic index"))
        };
        let mut root_slot = take_root_slot(&mut self.slots[dst_local.0]);
        let res = match new_slot {
            FieldSlot::Uninit => deinit_in_slot(
                &mut root_slot,
                &self.local_decls[dst_local.0],
                dst_proj,
                &no_index,
                full_place,
                None,
            )
            .map_err(|err| match err {
                // Array element destinations were handled above, so this is (a place inside) a
                // union field: copying uninitialized bytes into it is defined, but the value tree
                // cannot hold a union with uninitialized bytes (unsupported, not undefined).
                RvalueEvalError::UnsupportedPlaceProjection(_) => {
                    RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY)
                }
                other => other,
            }),
            FieldSlot::Partial(shell) => write_partial_shell_in_slot(
                &mut root_slot,
                &self.local_decls[dst_local.0],
                dst_proj,
                shell,
                src_local,
                full_place,
                None,
            ),
            FieldSlot::Init(_) => unreachable!(),
        };
        normalize_slot(&mut root_slot);
        self.slots[dst_local.0] = root_slot_state(root_slot);
        res
    }
}

/// Borrowed target of projecting into a [`PartialAggregate`] shell.
enum ProjectedShellRef<'a> {
    /// A nested (or root) `PartialAggregate` shell at the end of `proj`, paired with its
    /// declared type.
    Shell(&'a PartialAggregate, &'a Ty),
    /// A projected reference into an initialized `FieldSlot::Init` child value.
    Init(ProjectedRef<'a>, Option<&'a Ty>),
}

/// Returns whether `shell`'s container kind, ADT definition, and variant field count match
/// `declared_ty`.
fn shell_matches_declared_ty(shell: &PartialAggregate, declared_ty: &Ty) -> bool {
    match declared_ty {
        Ty::Tuple(fields) => shell.adt_def.is_none() && shell.fields.len() == fields.len(),
        Ty::Adt(def) => {
            !def.is_union()
                && shell.is_adt
                && shell.adt_def.as_ref() == Some(def)
                && shell.def_path.as_deref() == Some(def.def_path.as_str())
                && def.variant_fields(shell.variant_idx).map(<[Ty]>::len)
                    == Some(shell.fields.len())
        }
        _ => false,
    }
}

/// Verifies that `slot` (when initialized or partially initialized) is compatible with
/// `declared_ty` and with every runtime-dependent step of `proj` (`Downcast` active variant,
/// dynamic `Index` against runtime array window lengths, and runtime container constructors).
/// Uninitialized slots (`LocalSlotState::Uninit` / `FieldSlot::Uninit`) have no active variant
/// or runtime value to conflict with `proj`.
fn check_slot_projection(
    slot: &LocalSlotState,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
) -> Result<(), RvalueEvalError> {
    match slot {
        LocalSlotState::Dead => Err(RvalueEvalError::DeadLocal(full_place.local)),
        LocalSlotState::Uninit => Ok(()),
        LocalSlotState::Init(val) => {
            check_value_projection(val, declared_ty, proj, read_index, full_place, None)
        }
        LocalSlotState::PartialShell(shell) => {
            check_shell_projection(shell, declared_ty, proj, read_index, full_place, None)
        }
    }
}

fn check_value_projection(
    val: &MirValue,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    if active_downcast.is_none() && !mir_value_head_matches_ty(val, declared_ty) {
        return Err(RvalueEvalError::TypeMismatch(
            "place runtime value does not match declared type",
        ));
    }
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        return Ok(());
    };
    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Downcast(expected_variant) => {
            let actual = match val {
                MirValue::Adt {
                    variant_idx,
                    active_field: None,
                    ..
                } => *variant_idx,
                MirValue::Tuple(_) | MirValue::Unit => 0,
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast requires a non-union Adt or Tuple value",
                    ));
                }
            };
            if actual != *expected_variant {
                return Err(RvalueEvalError::InactiveVariantProjection {
                    expected: *expected_variant,
                    actual,
                });
            }
            check_value_projection(
                val,
                declared_ty,
                rest,
                read_index,
                full_place,
                Some(*expected_variant),
            )
        }
        ProjectionElem::Field(idx, expected_ty) => match val {
            MirValue::Tuple(fields) => {
                let expected_variant = active_downcast.unwrap_or(0);
                if expected_variant != 0 {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: expected_variant,
                        actual: 0,
                    });
                }
                let Some(field_val) = fields.get(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count: fields.len(),
                    });
                };
                check_value_projection(field_val, expected_ty, rest, read_index, full_place, None)
            }
            MirValue::Unit => {
                let expected_variant = active_downcast.unwrap_or(0);
                if expected_variant != 0 {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: expected_variant,
                        actual: 0,
                    });
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
                check_value_projection(field_val, expected_ty, rest, read_index, full_place, None)
            }
            MirValue::Adt {
                variant_idx,
                active_field: Some(active),
                fields,
                ..
            } => {
                if active_downcast.is_some() || *variant_idx != 0 || fields.is_empty() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT must have variant 0, at least one field, and cannot be downcast",
                    ));
                }
                let active_val = if fields.len() == 1 {
                    &fields[0]
                } else {
                    fields.get(*active).ok_or(RvalueEvalError::TypeMismatch(
                        "union ADT active_field index out of bounds of fields",
                    ))?
                };
                let Some(union_field_tys) = union_fields_of(declared_ty) else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT declared type must be a Ty::Tuple or a union Ty::Adt",
                    ));
                };
                let Some(active_ty) = union_field_tys.get(*active) else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT active_field index out of bounds of declared fields",
                    ));
                };
                if !mir_value_matches_ty(active_val, active_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT active field runtime value does not match declared type",
                    ));
                }
                if *active == *idx {
                    check_value_projection(
                        active_val,
                        expected_ty,
                        rest,
                        read_index,
                        full_place,
                        None,
                    )
                } else {
                    Ok(())
                }
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "Field projection requires Tuple or Adt value",
            )),
        },
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "array projection requires Array value",
                ));
            };
            check_array_window_projection(
                elements.as_slice(),
                elem_ty,
                proj,
                read_index,
                full_place,
            )
        }
    }
}

fn check_array_window_projection(
    window: &[MirValue],
    elem_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        return Ok(());
    };
    match first {
        ProjectionElem::Index(idx_local) => {
            let idx_bits = read_index(*idx_local)?;
            let Ok(i) = usize::try_from(idx_bits) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: window.len(),
                });
            };
            let Some(elem_val) = window.get(i) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: window.len(),
                });
            };
            check_value_projection(elem_val, elem_ty, rest, read_index, full_place, None)
        }
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => {
            let idx = resolve_constant_index(window.len(), *offset, *min_length, *from_end)?;
            check_value_projection(&window[idx], elem_ty, rest, read_index, full_place, None)
        }
        ProjectionElem::Subslice {
            from,
            to,
            from_end,
        } => {
            let (start, end) = resolve_subslice_range(window.len(), *from, *to, *from_end)?;
            check_array_window_projection(&window[start..end], elem_ty, rest, read_index, full_place)
        }
        _ => Err(RvalueEvalError::TypeMismatch(
            "non-array projection on array window",
        )),
    }
}

fn check_shell_projection(
    shell: &PartialAggregate,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    if !shell_matches_declared_ty(shell, declared_ty) {
        return Err(RvalueEvalError::TypeMismatch(
            "partial shell does not match declared type",
        ));
    }
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        return Ok(());
    };
    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Downcast(expected_variant) => {
            let actual = if shell.is_adt { shell.variant_idx } else { 0 };
            if actual != *expected_variant {
                return Err(RvalueEvalError::InactiveVariantProjection {
                    expected: *expected_variant,
                    actual,
                });
            }
            check_shell_projection(
                shell,
                declared_ty,
                rest,
                read_index,
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
                FieldSlot::Uninit => Ok(()),
                FieldSlot::Partial(child) => check_shell_projection(
                    child,
                    expected_ty,
                    rest,
                    read_index,
                    full_place,
                    None,
                ),
                FieldSlot::Init(val) => {
                    check_value_projection(val, expected_ty, rest, read_index, full_place, None)
                }
            }
        }
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => Err(RvalueEvalError::TypeMismatch(
            "array projection applied to a partially initialized tuple/ADT shell",
        )),
    }
}

/// Projects `proj` through a `PartialAggregate` shell in `O(proj.len())` time without cloning
/// or scanning sibling fields, returning either the reached `PartialAggregate` shell or a
/// [`ProjectedRef`] inside an initialized field slot.
#[allow(clippy::too_many_arguments, clippy::only_used_in_recursion)]
fn project_from_partial_shell<'a>(
    shell: &'a PartialAggregate,
    declared_ty: &'a Ty,
    proj: &'a [ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    base_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<ProjectedShellRef<'a>, RvalueEvalError> {
    if !shell_matches_declared_ty(shell, declared_ty) {
        return Err(RvalueEvalError::TypeMismatch(
            "partial shell does not match declared type",
        ));
    }
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        return Ok(ProjectedShellRef::Shell(shell, declared_ty));
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
            match rest.first() {
                Some(ProjectionElem::Deref) => {
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(
                        full_place.clone(),
                    ));
                }
                Some(ProjectionElem::Field(..)) => {}
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast projection must be followed by Field",
                    ));
                }
            }
            if !downcast_allowed(declared_ty, *expected_variant) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection requires a tuple-typed (ADT) place or an in-range enum variant",
                ));
            }
            let actual = if shell.is_adt { shell.variant_idx } else { 0 };
            if actual != *expected_variant {
                return Err(RvalueEvalError::InactiveVariantProjection {
                    expected: *expected_variant,
                    actual,
                });
            }
            project_from_partial_shell(
                shell,
                declared_ty,
                rest,
                read_index,
                ptr_width,
                base_local,
                full_place,
                Some(*expected_variant),
            )
        }
        ProjectionElem::Field(idx, expected_ty) => {
            let Some(field_tys) = projectable_field_tys(declared_ty, active_downcast) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Field projection requires a tuple-typed place (or a struct/union, or a downcast enum)",
                ));
            };
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
            match field_slot {
                FieldSlot::Uninit => {
                    validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
                        &field_tys[*idx],
                        rest,
                        None,
                        None,
                        full_place,
                        None,
                    )?;
                    Err(RvalueEvalError::UninitializedLocal(base_local))
                }
                FieldSlot::Partial(child_shell) => project_from_partial_shell(
                    child_shell,
                    &field_tys[*idx],
                    rest,
                    read_index,
                    ptr_width,
                    base_local,
                    full_place,
                    None,
                ),
                FieldSlot::Init(field_val) => {
                    if !projected_value_matches_ty(field_val, expected_ty, rest) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "projected field runtime type does not match expected type",
                        ));
                    }
                    project_mir_value(
                        field_val,
                        Some(expected_ty),
                        rest,
                        read_index,
                        full_place,
                        None,
                    )
                    .map(|(projected, leaf_ty)| ProjectedShellRef::Init(projected, leaf_ty))
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

/// Resolves the runtime array length at `proj` out of a `PartialAggregate` shell for
/// `Rvalue::Len` without cloning or scanning array elements.
#[allow(clippy::too_many_arguments)]
fn read_array_len_from_partial_shell(
    shell: &PartialAggregate,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    base_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<usize, RvalueEvalError> {
    match project_from_partial_shell(
        shell,
        declared_ty,
        proj,
        read_index,
        ptr_width,
        base_local,
        full_place,
        active_downcast,
    )? {
        ProjectedShellRef::Shell(_, _) => Err(RvalueEvalError::TypeMismatch(
            "Len target runtime value must be MirValue::Array",
        )),
        ProjectedShellRef::Init(projected, leaf_ty) => {
            projected_ref_into_array_len(projected, leaf_ty)
        }
    }
}

/// Reads a projected value out of a `PartialAggregate` shell.
#[allow(clippy::too_many_arguments)]
fn read_from_partial_shell(
    shell: &PartialAggregate,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    base_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<MirValue, RvalueEvalError> {
    match project_from_partial_shell(
        shell,
        declared_ty,
        proj,
        read_index,
        ptr_width,
        base_local,
        full_place,
        active_downcast,
    )? {
        ProjectedShellRef::Shell(reached, reached_ty) => {
            let value = reached
                .try_into_mir_value()
                .ok_or(RvalueEvalError::UninitializedLocal(base_local))?;
            if !mir_value_matches_ty(&value, reached_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "completed partial shell runtime value does not match declared type",
                ));
            }
            check_scalar_ranges(&value, ptr_width)?;
            Ok(value)
        }
        ProjectedShellRef::Init(projected, leaf_ty) => {
            let value = projected_ref_into_mir_value(projected, leaf_ty)?;
            check_scalar_ranges(&value, ptr_width)?;
            Ok(value)
        }
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
        if !projected_value_matches_ty(existing_val, declared_ty, proj) {
            return Err(RvalueEvalError::TypeMismatch(
                "initialized slot runtime value does not match declared type",
            ));
        }
        return write_projected_mir_value(
            existing_val,
            Some(declared_ty),
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
            if !downcast_allowed(declared_ty, *expected_variant) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection requires a tuple-typed (ADT) place or an in-range enum variant",
                ));
            }
            if let FieldSlot::Partial(shell) = &*slot {
                if !shell_matches_declared_ty(shell, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "partial shell does not match declared type",
                    ));
                }
                let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                if actual != *expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: *expected_variant,
                        actual,
                    });
                }
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
            let Some(field_tys) = projectable_field_tys(declared_ty, active_downcast) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Field projection requires a tuple-typed place (or a struct/union, or a downcast enum)",
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
            if let (FieldSlot::Uninit, Ty::Adt(def)) = (&*slot, declared_ty)
                && def.is_union()
            {
                // Writing a whole union field initializes the union with that field active; a
                // nested write into an uninitialized union field would need a per-byte model of
                // the overlapping fields.
                let leaf_ty = validate_projection_tail(
                    expected_ty,
                    rest,
                    None,
                    Some(read_index),
                    full_place,
                    None,
                )?;
                if !mir_value_matches_ty(&new_val, &leaf_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "assigned value runtime type does not match declared field type",
                    ));
                }
                if !rest.is_empty() {
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()));
                }
                *slot = FieldSlot::Init(MirValue::union_value(def, *idx, new_val));
                return Ok(());
            }
            if matches!(slot, FieldSlot::Uninit) {
                let mut child_slot = FieldSlot::Uninit;
                write_to_partial_slot(
                    &mut child_slot,
                    &field_tys[*idx],
                    rest,
                    new_val,
                    read_index,
                    ptr_width,
                    base_local,
                    full_place,
                    None,
                )?;
                let mut shell = match declared_ty {
                    Ty::Adt(def) => PartialAggregate::new_uninit_adt(def, active_downcast.unwrap_or(0))
                        .ok_or(RvalueEvalError::TypeMismatch(
                            "ADT shell variant out of range",
                        ))?,
                    _ => PartialAggregate::new_uninit(
                        field_tys.len(),
                        active_downcast.unwrap_or(0),
                        active_downcast.is_some(),
                    ),
                };
                shell.fields[*idx] = child_slot;
                *slot = if let Some(full_val) = shell.try_into_mir_value() {
                    FieldSlot::Init(full_val)
                } else {
                    FieldSlot::Partial(shell)
                };
                return Ok(());
            }
            let FieldSlot::Partial(shell) = slot else {
                unreachable!()
            };
            if !shell_matches_declared_ty(shell, declared_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "partial shell does not match declared type",
                ));
            }
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
                if !mir_value_matches_ty(&full_val, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "completed partial shell runtime value does not match declared type",
                    ));
                }
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
                let leaf_ty =
                    validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
                        declared_ty,
                        proj,
                        None,
                        None,
                        full_place,
                        active_downcast,
                    )?;
                if !mir_value_matches_ty(&new_val, &leaf_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "assigned value runtime type does not match projected array leaf type",
                    ));
                }
                Err(RvalueEvalError::UninitializedLocal(base_local))
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "array projection applied to a non-array place",
            )),
        },
    }
}

/// Updates the discriminant of a target `MirValue` inside an array window in place for
/// `Statement::SetDiscriminant` in `O(proj.len())` time without cloning or scanning unselected
/// elements.
fn set_discriminant_array_window(
    window: &mut [MirValue],
    elem_ty: &Ty,
    proj: &[ProjectionElem],
    variant_index: usize,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()));
    };
    match first {
        ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
        ProjectionElem::Index(idx_local) => {
            let idx_bits = read_index(*idx_local)?;
            let Ok(i) = usize::try_from(idx_bits) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len: window.len(),
                });
            };
            let len = window.len();
            let Some(elem_slot) = window.get_mut(i) else {
                return Err(RvalueEvalError::IndexOutOfBounds {
                    index: idx_bits,
                    len,
                });
            };
            if !mir_value_head_matches_ty(elem_slot, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array element runtime type does not match elem_ty",
                ));
            }
            set_discriminant_projected_mir_value(
                elem_slot,
                elem_ty,
                rest,
                variant_index,
                read_index,
                full_place,
                None,
            )
        }
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => {
            let idx = resolve_constant_index(window.len(), *offset, *min_length, *from_end)?;
            let elem_slot = &mut window[idx];
            if !mir_value_head_matches_ty(elem_slot, elem_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array element runtime type does not match elem_ty",
                ));
            }
            set_discriminant_projected_mir_value(
                elem_slot,
                elem_ty,
                rest,
                variant_index,
                read_index,
                full_place,
                None,
            )
        }
        ProjectionElem::Subslice {
            from,
            to,
            from_end,
        } => {
            let (start, end) = resolve_subslice_range(window.len(), *from, *to, *from_end)?;
            set_discriminant_array_window(
                &mut window[start..end],
                elem_ty,
                rest,
                variant_index,
                read_index,
                full_place,
            )
        }
        ProjectionElem::Downcast(_) => {
            if matches!(rest.first(), Some(ProjectionElem::Deref)) {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            Err(RvalueEvalError::TypeMismatch(
                "Downcast requires a non-union Adt or Tuple value",
            ))
        }
        ProjectionElem::Field(..) => Err(RvalueEvalError::TypeMismatch(
            "Field projection requires Tuple or Adt value",
        )),
    }
}

/// Updates the discriminant of the sub-value at `proj` inside `val` in place for
/// `Statement::SetDiscriminant` in `O(proj.len())` time without cloning or scanning the target
/// aggregate's fields.
#[allow(clippy::too_many_arguments)]
fn set_discriminant_projected_mir_value(
    val: &mut MirValue,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    variant_index: usize,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "SetDiscriminant target cannot end with Downcast",
            ));
        }
        if let Ty::Adt(def) = declared_ty {
            // Typed ADT values: same-variant `SetDiscriminant` is a no-op, and switching to a
            // fieldless enum variant replaces the value in place. A switch to a variant with
            // fields must demote the value to a shell first, which `set_discriminant_in_slot`
            // does whenever the container chain has shells (so reaching here means an array
            // element or union field tried to switch to a multi-field variant).
            if !mir_value_head_matches_ty(val, declared_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "SetDiscriminant target runtime value does not match declared type",
                ));
            }
            if !def.is_enum() {
                return if variant_index == 0 {
                    Ok(())
                } else {
                    Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()))
                };
            }
            let Some(fields) = def.variant_fields(variant_index) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "SetDiscriminant variant index out of range",
                ));
            };
            let MirValue::Adt { variant_idx, .. } = val else {
                unreachable!()
            };
            if *variant_idx == variant_index {
                return Ok(());
            }
            if fields.is_empty() {
                *val = MirValue::adt(def, variant_index, Vec::new());
                return Ok(());
            }
            return Err(RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()));
        }
        if !matches!(declared_ty, Ty::Tuple(_)) {
            return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()));
        }
        return match val {
            MirValue::Adt {
                active_field: None, ..
            } => {
                if !mir_value_head_matches_ty(val, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "SetDiscriminant target runtime value does not match declared type",
                    ));
                }
                let MirValue::Adt { variant_idx, .. } = val else {
                    unreachable!()
                };
                *variant_idx = variant_index;
                Ok(())
            }
            MirValue::Tuple(_) => {
                if !mir_value_head_matches_ty(val, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "SetDiscriminant target runtime value does not match declared type",
                    ));
                }
                let MirValue::Tuple(fields) = val else {
                    unreachable!()
                };
                let moved = std::mem::take(fields);
                *val = MirValue::Adt {
                    def_path: String::new(),
                    variant_idx: variant_index,
                    active_field: None,
                    fields: moved,
                    adt_def: None,
                };
                Ok(())
            }
            MirValue::Unit => {
                if !mir_value_head_matches_ty(val, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "SetDiscriminant target runtime value does not match declared type",
                    ));
                }
                *val = MirValue::Adt {
                    def_path: String::new(),
                    variant_idx: variant_index,
                    active_field: None,
                    fields: Vec::new(),
                    adt_def: None,
                };
                Ok(())
            }
            _ => Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone())),
        };
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
            if matches!(rest.first(), Some(ProjectionElem::Deref)) {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            if !matches!(rest.first(), Some(ProjectionElem::Field(..))) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
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
                    set_discriminant_projected_mir_value(
                        val,
                        declared_ty,
                        rest,
                        variant_index,
                        read_index,
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
                    set_discriminant_projected_mir_value(
                        val,
                        declared_ty,
                        rest,
                        variant_index,
                        read_index,
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
                if let Some(v) = active_downcast
                    && v != 0
                {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: v,
                        actual: 0,
                    });
                }
                let field_count = fields.len();
                let Some(field_slot) = fields.get_mut(*idx) else {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count,
                    });
                };
                if !mir_value_head_matches_ty(field_slot, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected tuple field runtime type does not match expected type",
                    ));
                }
                set_discriminant_projected_mir_value(
                    field_slot,
                    expected_ty,
                    rest,
                    variant_index,
                    read_index,
                    full_place,
                    None,
                )
            }
            MirValue::Unit => {
                if let Some(v) = active_downcast
                    && v != 0
                {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: v,
                        actual: 0,
                    });
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
                if !mir_value_head_matches_ty(field_slot, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected ADT field runtime type does not match expected type",
                    ));
                }
                set_discriminant_projected_mir_value(
                    field_slot,
                    expected_ty,
                    rest,
                    variant_index,
                    read_index,
                    full_place,
                    None,
                )
            }
            MirValue::Adt {
                variant_idx,
                active_field: Some(active),
                fields,
                ..
            } => {
                if active_downcast.is_some() || *variant_idx != 0 || fields.is_empty() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT must have variant 0, at least one field, and cannot be downcast",
                    ));
                }
                let active_val = if fields.len() == 1 {
                    &fields[0]
                } else {
                    fields.get(*active).ok_or(RvalueEvalError::TypeMismatch(
                        "union ADT active_field index out of bounds of fields",
                    ))?
                };
                let Some(union_field_tys) = union_fields_of(declared_ty) else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT declared type must be a Ty::Tuple or a union Ty::Adt",
                    ));
                };
                let Some(active_ty) = union_field_tys.get(*active) else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "union ADT active_field index out of bounds of declared fields",
                    ));
                };
                if *idx >= union_field_tys.len() {
                    return Err(RvalueEvalError::FieldOutOfBounds {
                        field_idx: *idx,
                        field_count: union_field_tys.len(),
                    });
                }
                if union_field_tys[*idx] != *expected_ty {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected union field type does not match declared union field type",
                    ));
                }
                if *active != *idx {
                    if !mir_value_matches_ty(active_val, active_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "union ADT active field runtime value does not match declared type",
                        ));
                    }
                    let leaf_ty = validate_projection_tail(
                        expected_ty,
                        rest,
                        None,
                        Some(read_index),
                        full_place,
                        None,
                    )?;
                    if !matches!(leaf_ty, Ty::Tuple(_) | Ty::Adt(_)) {
                        return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()));
                    }
                    return Err(RvalueEvalError::UnsupportedPlaceProjection(
                        full_place.clone(),
                    ));
                }
                let active_slot = if fields.len() == 1 {
                    &mut fields[0]
                } else {
                    &mut fields[*idx]
                };
                if !mir_value_head_matches_ty(active_slot, expected_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "projected union field runtime type does not match expected type",
                    ));
                }
                set_discriminant_projected_mir_value(
                    active_slot,
                    expected_ty,
                    rest,
                    variant_index,
                    read_index,
                    full_place,
                    None,
                )
            }
            _ => Err(RvalueEvalError::TypeMismatch(
                "Field projection requires Tuple or Adt value",
            )),
        },
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => {
            if active_downcast.is_some() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            let MirValue::Array { elements, elem_ty } = val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Array projection requires MirValue::Array",
                ));
            };
            set_discriminant_array_window(
                elements,
                elem_ty,
                proj,
                variant_index,
                read_index,
                full_place,
            )
        }
    }
}

/// Promotes a complete `Partial` shell to `Init` and collapses an empty shell (no initialized
/// field, no written tag) to `Uninit`, so that equivalent slots have one representation.
fn normalize_slot(slot: &mut FieldSlot) {
    if let FieldSlot::Partial(shell) = slot {
        if let Some(full_val) = shell.try_into_mir_value() {
            *slot = FieldSlot::Init(full_val);
        } else if shell.is_empty() {
            *slot = FieldSlot::Uninit;
        }
    }
}

/// Converts an initialized tuple or (non-union) ADT value in `slot` into the equivalent
/// complete `Partial` shell (every field `Init`; an ADT's tag counts as written), so that a
/// statement can deinitialize or re-tag one of its parts. [`normalize_slot`] restores the
/// value if nothing below changed. Other values (arrays, unions, scalars, `()`) have no
/// per-field shells: `UnsupportedPlaceProjection(full_place)`.
fn explode_init_slot(slot: &mut FieldSlot, full_place: &Place) -> Result<(), RvalueEvalError> {
    let FieldSlot::Init(val) = std::mem::replace(slot, FieldSlot::Uninit) else {
        unreachable!("explode_init_slot requires an initialized slot")
    };
    let shell = match val {
        MirValue::Tuple(fields) => PartialAggregate {
            def_path: None,
            variant_idx: 0,
            is_adt: false,
            discriminant_set: false,
            fields: fields.into_iter().map(FieldSlot::Init).collect(),
            adt_def: None,
        },
        MirValue::Adt {
            def_path,
            variant_idx,
            active_field: None,
            fields,
            adt_def,
        } => PartialAggregate {
            def_path: Some(def_path),
            variant_idx,
            is_adt: true,
            discriminant_set: true,
            fields: fields.into_iter().map(FieldSlot::Init).collect(),
            adt_def,
        },
        other => {
            *slot = FieldSlot::Init(other);
            return Err(RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()));
        }
    };
    *slot = FieldSlot::Partial(shell);
    Ok(())
}

/// The slot of a typed enum whose tag was just written to `variant_index` while every field is
/// uninitialized (initialized right away if the variant has no fields).
fn tagged_variant_slot(def: &Arc<AdtDef>, variant_index: usize) -> Result<FieldSlot, RvalueEvalError> {
    let mut shell = PartialAggregate::new_uninit_adt(def, variant_index).ok_or(
        RvalueEvalError::TypeMismatch("SetDiscriminant variant index out of range"),
    )?;
    shell.discriminant_set = true;
    Ok(match shell.try_into_mir_value() {
        Some(full_val) => FieldSlot::Init(full_val),
        None => FieldSlot::Partial(shell),
    })
}

/// Returns true if `SetDiscriminant` at `proj` inside the initialized `val` targets a typed
/// enum value of a different variant with fields (which must be demoted to a shell of the new
/// variant; a fieldless target variant is already complete and is updated in place by
/// [`set_discriminant_projected_mir_value`]).
fn typed_variant_switch_target(
    val: &MirValue,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    variant_index: usize,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> bool {
    matches!(
        project_mir_value(val, Some(declared_ty), proj, read_index, full_place, active_downcast),
        Ok((
            ProjectedRef::Value(MirValue::Adt {
                adt_def: Some(def),
                variant_idx,
                ..
            }),
            _,
        )) if def.is_enum()
            && *variant_idx != variant_index
            && def
                .variant_fields(variant_index)
                .is_some_and(|fields| !fields.is_empty())
    )
}

/// Looks up the pre-read value of `idx_local` in a statement's index cache.
fn cached_index(index_cache: &[(Local, u128)], idx_local: Local) -> Result<u128, RvalueEvalError> {
    index_cache
        .iter()
        .find_map(|(loc, bits)| (*loc == idx_local).then_some(*bits))
        .ok_or(RvalueEvalError::TypeMismatch(
            "index local not found in pre-validated cache",
        ))
}

/// Moves a live local's state out as a [`FieldSlot`] (leaving `Uninit` behind until
/// [`root_slot_state`] writes it back).
fn take_root_slot(slot: &mut LocalSlotState) -> FieldSlot {
    match std::mem::replace(slot, LocalSlotState::Uninit) {
        LocalSlotState::Dead | LocalSlotState::Uninit => FieldSlot::Uninit,
        LocalSlotState::PartialShell(shell) => FieldSlot::Partial(shell),
        LocalSlotState::Init(v) => FieldSlot::Init(v),
    }
}

/// Converts a (normalized) root [`FieldSlot`] back into a live local's state.
fn root_slot_state(slot: FieldSlot) -> LocalSlotState {
    match slot {
        FieldSlot::Uninit => LocalSlotState::Uninit,
        FieldSlot::Partial(shell) => LocalSlotState::PartialShell(shell),
        FieldSlot::Init(v) => LocalSlotState::Init(v),
    }
}

/// Writes "uninitialized" over the sub-place `proj` of `slot` (of declared type `declared_ty`)
/// for `Statement::Deinit` (see [`StatementEvalState::deinit_place`]). The caller normalizes
/// `slot` afterwards; every error leaves the represented state unchanged.
fn deinit_in_slot(
    slot: &mut FieldSlot,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        *slot = FieldSlot::Uninit;
        return Ok(());
    };
    if matches!(slot, FieldSlot::Uninit) {
        // Writing uninitialized bytes into an uninitialized part changes nothing, but the
        // place must still be well-typed and in bounds.
        validate_projection_tail(declared_ty, proj, None, Some(read_index), full_place, active_downcast)?;
        return Ok(());
    }
    if let FieldSlot::Init(val) = &*slot {
        if !mir_value_head_matches_ty(val, declared_ty) {
            return Err(RvalueEvalError::TypeMismatch(
                "initialized slot runtime value does not match declared type",
            ));
        }
        match (first, val) {
            (ProjectionElem::Deref, _) => {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()));
            }
            (
                ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. },
                _,
            )
            | (
                _,
                MirValue::Adt {
                    active_field: Some(_),
                    ..
                },
            ) => {
                // Array elements and union fields have no per-part shells.
                validate_projection_tail(
                    declared_ty,
                    proj,
                    None,
                    Some(read_index),
                    full_place,
                    active_downcast,
                )?;
                return Err(RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()));
            }
            (ProjectionElem::Field(idx, _), MirValue::Unit) => {
                return Err(RvalueEvalError::FieldOutOfBounds {
                    field_idx: *idx,
                    field_count: 0,
                });
            }
            _ => explode_init_slot(slot, full_place)?,
        }
    }
    let res = (|| match first {
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
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            if !downcast_allowed(declared_ty, *expected_variant) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection requires a tuple-typed (ADT) place or an in-range enum variant",
                ));
            }
            let FieldSlot::Partial(shell) = &*slot else {
                unreachable!()
            };
            if !shell_matches_declared_ty(shell, declared_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "partial shell does not match declared type",
                ));
            }
            let actual = if shell.is_adt { shell.variant_idx } else { 0 };
            if actual != *expected_variant {
                return Err(RvalueEvalError::InactiveVariantProjection {
                    expected: *expected_variant,
                    actual,
                });
            }
            deinit_in_slot(slot, declared_ty, rest, read_index, full_place, Some(*expected_variant))
        }
        ProjectionElem::Field(idx, expected_ty) => {
            let Some(field_tys) = projectable_field_tys(declared_ty, active_downcast) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Field projection requires a tuple-typed place (or a struct/union, or a downcast enum)",
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
            let FieldSlot::Partial(shell) = &mut *slot else {
                unreachable!()
            };
            if !shell_matches_declared_ty(shell, declared_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "partial shell does not match declared type",
                ));
            }
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
            deinit_in_slot(child_slot, &field_tys[*idx], rest, read_index, full_place, None)?;
            normalize_slot(child_slot);
            // Uninitialized bytes in a variant field may cover a niche-encoded tag; only a tag
            // stored apart from the fields (or no tag at all) is known to survive.
            if active_downcast.is_some()
                && !shell
                    .adt_def
                    .as_ref()
                    .is_some_and(|def| def.tag_survives_field_deinit())
            {
                shell.discriminant_set = false;
            }
            Ok(())
        }
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => Err(RvalueEvalError::TypeMismatch(
            "array projection applied to a partially initialized tuple/ADT shell",
        )),
    })();
    normalize_slot(slot);
    res
}

/// Context of a `Statement::Retag`: the target pointer width and the storage state of every
/// local (whose synthetic allocations references may point into, see
/// [`local_base_addr_for_decls`]).
#[derive(Clone, Copy)]
struct RetagCtx<'a> {
    ptr_width: PtrWidth,
    slots: &'a [LocalSlotState],
}

/// Validates the reference `ptr` of type `ref_ty` (`&pointee`) for `Statement::Retag`: its
/// address must be a valid `&T` bit pattern (non-null and within the target's pointer width:
/// `InvalidBitPattern`), aligned to the pointee's alignment (`MisalignedPointer`; an alignment
/// the layout model leaves unspecified is `UnsupportedLayout`), point to an inhabited type
/// (`UninhabitedPointee`), and its pointee range `[addr, addr + size)` must not wrap the
/// address space (`PointerRangeOverflow` under an exact layout; when only an upper bound of an
/// unspecified layout wraps, the verdict depends on `rustc`'s layout and the retag is
/// `UnsupportedMemoryAccess`). A reference into the synthetic allocation of a local whose
/// storage is dead (at its base or any sub-place offset) dangles (`DeadLocal`), unless its
/// pointee is zero-sized (a zero-sized retag accesses no memory).
fn check_retagged_reference(
    ptr: &PointerValue,
    ref_ty: &Ty,
    pointee: &Ty,
    ctx: RetagCtx<'_>,
) -> Result<(), RvalueEvalError> {
    let ptr_width = ctx.ptr_width;
    let addr = u128::from(ptr.addr);
    if !ref_ty.is_valid_scalar_bits(addr, ptr_width) {
        return Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: ref_ty.clone(),
                bits: addr,
            },
        ));
    }
    let (min_align, max_align) = pointee
        .align_bounds(ptr_width)
        .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(pointee, err)))?;
    if !addr.is_multiple_of(min_align as u128) {
        return Err(RvalueEvalError::MisalignedPointer {
            addr: addr as u64,
            required_align: min_align,
        });
    }
    if !addr.is_multiple_of(max_align as u128) {
        return Err(RvalueEvalError::CastEval(CastEvalError::UnsupportedLayout {
            ty: pointee.clone(),
        }));
    }
    if !pointee.is_inhabited_for(ptr_width) {
        return Err(RvalueEvalError::UninhabitedPointee(pointee.clone()));
    }
    if let Ok((pointee_size, _)) = pointee.alloc_size_and_align(ptr_width) {
        let byte_len = pointee_size as u128;
        if addr
            .checked_add(byte_len)
            .is_none_or(|end| end > ptr_width.max_usize())
        {
            // Only an exact size proves the wrap: an upper bound of an unspecified layout
            // (e.g. a 2-byte tagged bound of a 1-byte niche enum) leaves it to `rustc`.
            if pointee.layout_for(ptr_width).is_err() {
                return Err(RvalueEvalError::UnsupportedMemoryAccess(
                    "retagged reference range may wrap the address space under an unspecified pointee layout",
                ));
            }
            return Err(RvalueEvalError::PointerRangeOverflow {
                addr: addr as u64,
                byte_len,
            });
        }
    }
    // Unspecified layouts are never zero-sized (they store a tag), so only an exact size `0`
    // exempts a reference into a dead local.
    if let Some(local) = resolve_synthetic_alloc_local(ptr, ctx.slots.len())
        && matches!(ctx.slots[local], LocalSlotState::Dead)
        && !pointee
            .layout_for(ptr_width)
            .is_ok_and(|layout| layout.size == 0)
    {
        return Err(RvalueEvalError::DeadLocal(Local(local)));
    }
    Ok(())
}

/// Validates every reference reachable in the initialized value `val` of type `ty` for
/// `Statement::Retag` (skipping union contents and subtrees without references).
fn retag_value(val: &MirValue, ty: &Ty, ctx: RetagCtx<'_>) -> Result<(), RvalueEvalError> {
    if !ty.contains_ref() {
        return Ok(());
    }
    let mismatch = || {
        RvalueEvalError::TypeMismatch("retagged runtime value does not match its declared type")
    };
    match (ty, val) {
        (Ty::Ref(pointee, _), MirValue::Ptr { ptr, ty: val_ty }) if val_ty == ty => {
            check_retagged_reference(ptr, ty, pointee, ctx)
        }
        (Ty::Array(elem, _), MirValue::Array { elements, .. }) => {
            for element in elements {
                retag_value(element, elem, ctx)?;
            }
            Ok(())
        }
        (Ty::Tuple(field_tys), MirValue::Tuple(vals))
        | (
            Ty::Tuple(field_tys),
            MirValue::Adt {
                active_field: None,
                fields: vals,
                adt_def: None,
                ..
            },
        ) => {
            if vals.len() != field_tys.len() {
                return Err(mismatch());
            }
            for (value, field_ty) in vals.iter().zip(field_tys) {
                retag_value(value, field_ty, ctx)?;
            }
            Ok(())
        }
        (
            Ty::Tuple(_),
            MirValue::Adt {
                active_field: Some(_),
                adt_def: None,
                ..
            },
        ) => Ok(()),
        (
            Ty::Adt(def),
            MirValue::Adt {
                variant_idx,
                fields: vals,
                ..
            },
        ) => {
            let Some(field_tys) = typed_adt_field_tys(val, ty) else {
                return Err(mismatch());
            };
            if def.is_enum() && !field_tys.iter().all(|f| f.is_inhabited_for(ctx.ptr_width)) {
                return Err(RvalueEvalError::UninhabitedEnumVariant {
                    variant_index: *variant_idx,
                });
            }
            if def.is_enum() && !def.tag_survives_field_deinit() {
                if !mir_value_matches_ty(val, ty) {
                    return Err(mismatch());
                }
                check_value_well_formed(val, ctx.ptr_width)?;
            }
            for (value, field_ty) in vals.iter().zip(field_tys) {
                retag_value(value, field_ty, ctx)?;
            }
            Ok(())
        }
        _ => Err(mismatch()),
    }
}

/// [`retag_value`] for the target of a projection (a value or an array window).
fn retag_projected(
    target: ProjectedRef<'_>,
    ty: &Ty,
    ctx: RetagCtx<'_>,
) -> Result<(), RvalueEvalError> {
    match target {
        ProjectedRef::Value(val) => retag_value(val, ty, ctx),
        ProjectedRef::ArrayWindow { window, elem_ty } => {
            for element in window {
                retag_value(element, elem_ty, ctx)?;
            }
            Ok(())
        }
    }
}

/// Validates every reference reachable in the partially initialized `shell` of type `ty` for
/// `Statement::Retag`: an uninitialized field holding references is `UninitializedLocal`, as
/// is an enum shell whose variant cannot be read from its tag
/// ([`PartialAggregate::tag_is_readable`]: the tag is unwritten, or may be niche-encoded in a
/// still uninitialized field).
fn retag_shell(
    shell: &PartialAggregate,
    ty: &Ty,
    ctx: RetagCtx<'_>,
    base_local: Local,
) -> Result<(), RvalueEvalError> {
    if !shell_matches_declared_ty(shell, ty) {
        return Err(RvalueEvalError::TypeMismatch(
            "retagged shell does not match its declared type",
        ));
    }
    if !ty.contains_ref() {
        return Ok(());
    }
    // Retagging an enum visits the fields of the variant its tag selects (Miri's retag
    // visitor reads the discriminant), so the tag must be readable without the fields.
    if !shell.tag_is_readable() {
        return Err(RvalueEvalError::UninitializedLocal(base_local));
    }
    let field_tys = match ty {
        Ty::Tuple(fields) => Some(fields.as_slice()),
        Ty::Adt(def) => def.variant_fields(shell.variant_idx),
        _ => None,
    };
    let Some(field_tys) = field_tys.filter(|tys| tys.len() == shell.fields.len()) else {
        return Err(RvalueEvalError::TypeMismatch(
            "retagged shell does not match its declared type",
        ));
    };
    if matches!(ty, Ty::Adt(def) if def.is_enum())
        && !field_tys.iter().all(|f| f.is_inhabited_for(ctx.ptr_width))
    {
        return Err(if shell.discriminant_set {
            RvalueEvalError::UninhabitedEnumVariant {
                variant_index: shell.variant_idx,
            }
        } else {
            RvalueEvalError::UninitializedLocal(base_local)
        });
    }
    for (slot, field_ty) in shell.fields.iter().zip(field_tys) {
        match slot {
            FieldSlot::Uninit if field_ty.contains_ref() => {
                return Err(RvalueEvalError::UninitializedLocal(base_local));
            }
            FieldSlot::Uninit => {}
            FieldSlot::Init(val) => retag_value(val, field_ty, ctx)?,
            FieldSlot::Partial(child) => retag_shell(child, field_ty, ctx, base_local)?,
        }
    }
    Ok(())
}

/// Synthetic allocation base address of `local` given `local_decls` under `ptr_width`.
///
/// Preserves `(local + 1) * 0x1000` whenever every preceding local has allocation size
/// `<= 0x1000` and alignment `<= 0x1000`, and advances past larger locals by rounding each
/// local's allocation size up to a multiple of `0x1000` (and aligning to `align.max(0x1000)`),
/// so the synthetic allocations of distinct locals never overlap.
///
/// The allocation `[base, base + size)` of `local` (`size` the upper-bound layout size of its
/// declared type) must fit the target address space (`base + size <= usize::MAX`, as for
/// [`RvalueEvalError::PointerRangeOverflow`]); otherwise the frame's locals cannot all be
/// allocated without wrapping around (and aliasing other locals' addresses), and the result is
/// `UnsupportedMemoryAccess` rather than a masked, colliding address.
pub(crate) fn local_base_addr_for_decls(
    local: usize,
    local_decls: &[Ty],
    ptr_width: PtrWidth,
) -> Result<u128, RvalueEvalError> {
    const PAGE: u128 = 0x1000;
    let too_large = RvalueEvalError::UnsupportedMemoryAccess(
        "synthetic stack allocation does not fit the target address space",
    );
    let limit = ptr_width.max_usize();
    let mut cur = PAGE;
    let preceding = local.min(local_decls.len());
    for decl_ty in &local_decls[..preceding] {
        let stride = match decl_ty.alloc_size_and_align(ptr_width) {
            Ok((size, align)) => {
                let a = (align as u128).max(PAGE);
                cur = cur.div_ceil(a) * a;
                (size as u128).max(1).div_ceil(PAGE) * PAGE
            }
            Err(_) => PAGE,
        };
        cur += stride;
        if cur > limit {
            return Err(too_large);
        }
    }
    let own_layout = local_decls
        .get(local)
        .and_then(|decl_ty| decl_ty.alloc_size_and_align(ptr_width).ok());
    if let Some((_, align)) = own_layout
        && align as u128 > PAGE
    {
        let a = align as u128;
        cur = cur.div_ceil(a) * a;
    }
    if local > preceding {
        cur += (local - preceding) as u128 * PAGE;
    }
    let own_size = own_layout.map_or(0, |(size, _)| size as u128);
    if cur.checked_add(own_size).is_none_or(|end| end > limit) {
        return Err(too_large);
    }
    Ok(cur)
}

/// [`local_base_addr_for_decls`] for a frame whose locals are typed by their runtime values.
fn local_base_addr_for_values(
    local: usize,
    locals: &[MirValue],
    ptr_width: PtrWidth,
) -> Result<u128, RvalueEvalError> {
    let decls: Vec<Ty> = locals.iter().map(MirValue::ty).collect();
    local_base_addr_for_decls(local, &decls, ptr_width)
}

// -------------------------------------------------------------------------------------------
// Synthetic sub-place resolution over a frame view, shared by `StatementEvalState` and the
// stateless `eval_place_*` / `eval_lowered_rvalue` evaluators (one implementation, so the two
// evaluators can never diverge on `Deref` semantics).
// -------------------------------------------------------------------------------------------

/// State of a frame slot as seen by synthetic sub-place resolution.
#[derive(Clone, Copy)]
enum FrameSlot<'a> {
    Dead,
    Live(SlotRef<'a>),
}

/// Read-only view of a frame's locals for synthetic sub-place resolution: the slots of a
/// [`StatementEvalState`] (dead, uninitialized, partially initialized, or initialized) or the
/// initialized values of a stateless frame ([`ValuesFrame`], borrowed and never cloned, so a
/// stateless `Deref` stays `O(path)`).
trait FrameView {
    /// Declared types of the locals (runtime value types for a stateless frame).
    fn frame_decls(&self) -> &[Ty];
    /// Target pointer width.
    fn frame_ptr_width(&self) -> PtrWidth;
    /// Number of locals that have both a type and a slot.
    fn frame_local_count(&self) -> usize;
    /// The slot of `local`, or `None` when out of bounds.
    fn frame_slot(&self, local: usize) -> Option<FrameSlot<'_>>;
    /// Reads the `usize` operand of a `ProjectionElem::Index(idx_local)` step.
    fn frame_index_operand(&self, idx_local: Local) -> Result<u128, RvalueEvalError>;
}

impl FrameView for StatementEvalState {
    fn frame_decls(&self) -> &[Ty] {
        &self.local_decls
    }

    fn frame_ptr_width(&self) -> PtrWidth {
        self.ptr_width
    }

    fn frame_local_count(&self) -> usize {
        self.slots.len().min(self.local_decls.len())
    }

    fn frame_slot(&self, local: usize) -> Option<FrameSlot<'_>> {
        Some(match self.slots.get(local)? {
            LocalSlotState::Dead => FrameSlot::Dead,
            LocalSlotState::Uninit => FrameSlot::Live(SlotRef::Uninit),
            LocalSlotState::PartialShell(shell) => FrameSlot::Live(SlotRef::Partial(shell)),
            LocalSlotState::Init(val) => FrameSlot::Live(SlotRef::Init(val)),
        })
    }

    fn frame_index_operand(&self, idx_local: Local) -> Result<u128, RvalueEvalError> {
        self.read_index_local(idx_local)
    }
}

/// A stateless frame: initialized `locals` typed by their runtime values (`decls`).
struct ValuesFrame<'a> {
    locals: &'a [MirValue],
    decls: Vec<Ty>,
    ptr_width: PtrWidth,
}

impl<'a> ValuesFrame<'a> {
    fn new(locals: &'a [MirValue], ptr_width: PtrWidth) -> Self {
        ValuesFrame {
            locals,
            decls: locals.iter().map(MirValue::ty).collect(),
            ptr_width,
        }
    }
}

impl FrameView for ValuesFrame<'_> {
    fn frame_decls(&self) -> &[Ty] {
        &self.decls
    }

    fn frame_ptr_width(&self) -> PtrWidth {
        self.ptr_width
    }

    fn frame_local_count(&self) -> usize {
        self.locals.len().min(self.decls.len())
    }

    fn frame_slot(&self, local: usize) -> Option<FrameSlot<'_>> {
        self.locals
            .get(local)
            .map(|val| FrameSlot::Live(SlotRef::Init(val)))
    }

    fn frame_index_operand(&self, idx_local: Local) -> Result<u128, RvalueEvalError> {
        read_index_in_values(idx_local, self.locals, &self.decls, self.ptr_width)
    }
}

/// Reads an index local of a stateless frame as a `usize` bit pattern.
fn read_index_in_values(
    idx_local: Local,
    locals: &[MirValue],
    local_decls: &[Ty],
    ptr_width: PtrWidth,
) -> Result<u128, RvalueEvalError> {
    match local_decls.get(idx_local.0) {
        None => return Err(RvalueEvalError::TypeMismatch("index local index out of bounds")),
        Some(Ty::Uint(UintTy::Usize)) => {}
        Some(_) => {
            return Err(RvalueEvalError::TypeMismatch(
                "array index local must have declared type usize",
            ));
        }
    }
    match locals.get(idx_local.0) {
        None => Err(RvalueEvalError::TypeMismatch("index local index out of bounds")),
        Some(MirValue::Int {
            bits,
            ty: Ty::Uint(UintTy::Usize),
        }) if *bits <= ptr_width.max_usize() => Ok(*bits),
        Some(_) => Err(RvalueEvalError::TypeMismatch(
            "array index local must hold a valid usize value",
        )),
    }
}

/// [`check_slot_projection`] on the frame slot of `local`.
fn check_frame_slot_projection(
    slot: FrameSlot<'_>,
    local: Local,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    full_place: &Place,
) -> Result<(), RvalueEvalError> {
    match slot {
        FrameSlot::Dead => Err(RvalueEvalError::DeadLocal(local)),
        FrameSlot::Live(SlotRef::Uninit) => Ok(()),
        FrameSlot::Live(SlotRef::Init(val)) => {
            check_value_projection(val, declared_ty, proj, read_index, full_place, None)
        }
        FrameSlot::Live(SlotRef::Partial(shell)) => {
            check_shell_projection(shell, declared_ty, proj, read_index, full_place, None)
        }
    }
}

/// [`slot_union_path_active`] on a frame slot.
fn frame_slot_union_path_active(
    slot: FrameSlot<'_>,
    proj: &[ProjectionElem],
    allow_leaf_union_overwrite: bool,
) -> bool {
    match slot {
        FrameSlot::Live(SlotRef::Init(val)) => {
            value_union_path_active(val, proj, allow_leaf_union_overwrite)
        }
        FrameSlot::Live(SlotRef::Partial(shell)) => {
            shell_union_path_active(shell, proj, allow_leaf_union_overwrite)
        }
        FrameSlot::Live(SlotRef::Uninit) | FrameSlot::Dead => true,
    }
}

/// Reads the value at the `Deref`-free `(local, proj)` of `frame`, whose `Index` operands were
/// pre-read into `index_cache`.
fn read_frame_place<F: FrameView + ?Sized>(
    frame: &F,
    local: Local,
    proj: &[ProjectionElem],
    index_cache: &[(Local, u128)],
    full_place: &Place,
) -> Result<MirValue, RvalueEvalError> {
    let Some(base_decl_ty) = frame.frame_decls().get(local.0) else {
        return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
    };
    let read_index = |loc: Local| cached_index(index_cache, loc);
    match frame.frame_slot(local.0) {
        None => Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
        Some(FrameSlot::Dead) => Err(RvalueEvalError::DeadLocal(local)),
        Some(FrameSlot::Live(SlotRef::Uninit)) => Err(RvalueEvalError::UninitializedLocal(local)),
        Some(FrameSlot::Live(SlotRef::Init(root_val))) => {
            if !projected_value_matches_ty(root_val, base_decl_ty, proj) {
                return Err(RvalueEvalError::TypeMismatch(
                    "initialized local runtime value does not match local declaration type",
                ));
            }
            read_projected_mir_value(
                root_val,
                Some(base_decl_ty),
                proj,
                &read_index,
                frame.frame_ptr_width(),
                full_place,
                None,
            )
        }
        Some(FrameSlot::Live(SlotRef::Partial(shell))) => read_from_partial_shell(
            shell,
            base_decl_ty,
            proj,
            &read_index,
            frame.frame_ptr_width(),
            local,
            full_place,
            None,
        ),
    }
}

/// Maps a synthetic local or sub-place pointer `ptr` (of type `ptr_ty` with pointee
/// `pointee_ty`) back to `(Local(target_local), prefix_proj)` in `frame`.
///
/// Checks, in order: the address bit pattern (`InvalidBitPattern`), non-null
/// (`InvalidBitPattern` for `&T`, `NullPointerAccess` otherwise), alignment
/// (`MisalignedPointer`, or `UnsupportedLayout` for an unspecified alignment), an inhabited
/// `&T` pointee (`UninhabitedPointee`), a pointee range that does not wrap the address space
/// (`PointerRangeOverflow` under an exact layout), synthetic provenance of a live local
/// (`DeadLocal`), a synthetic allocation that fits the address space, and an in-bounds
/// `[rel_off, rel_off + size)`; then selects the designated sub-place among the same-offset,
/// same-type candidates ([`select_subplace_candidate_in`]). Every unresolvable pointer is
/// `UnsupportedPlaceProjection` (never a guessed sub-place). With `allow_union_overwrite` (a
/// final `Deref` of a whole-place write), the designated sub-place may be an inactive leaf
/// union field that the write overwrites.
fn resolve_synthetic_subplace_in<F: FrameView + ?Sized>(
    frame: &F,
    ptr: &PointerValue,
    ptr_ty: &Ty,
    pointee_ty: &Ty,
    full_place: &Place,
    allow_union_overwrite: bool,
) -> Result<(Local, Vec<ProjectionElem>), RvalueEvalError> {
    let ptr_width = frame.frame_ptr_width();
    let addr = checked_ptr_addr(ptr, ptr_ty, ptr_width)?;
    if addr == 0 {
        if ptr_ty.is_ref() {
            return Err(RvalueEvalError::CastEval(
                CastEvalError::InvalidBitPattern {
                    target_ty: ptr_ty.clone(),
                    bits: 0,
                },
            ));
        }
        return Err(RvalueEvalError::NullPointerAccess);
    }
    let (min_align, max_align) = pointee_ty
        .align_bounds(ptr_width)
        .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(pointee_ty, err)))?;
    if !addr.is_multiple_of(min_align as u128) {
        return Err(RvalueEvalError::MisalignedPointer {
            addr: addr as u64,
            required_align: min_align,
        });
    }
    if !addr.is_multiple_of(max_align as u128) {
        return Err(RvalueEvalError::CastEval(
            CastEvalError::UnsupportedLayout {
                ty: pointee_ty.clone(),
            },
        ));
    }
    if ptr_ty.is_ref() && !pointee_ty.is_inhabited_for(ptr_width) {
        return Err(RvalueEvalError::UninhabitedPointee(pointee_ty.clone()));
    }
    let (pointee_size, _) = pointee_ty
        .alloc_size_and_align(ptr_width)
        .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(pointee_ty, err)))?;
    let byte_len = pointee_size as u128;
    if addr
        .checked_add(byte_len)
        .is_none_or(|end| end > ptr_width.max_usize())
    {
        // Only an exact size proves the wrap; an upper bound of an unspecified layout leaves
        // it to the layout `rustc` picks (unsupported, never undefined).
        if pointee_ty.layout_for(ptr_width).is_err() {
            return Err(RvalueEvalError::UnsupportedPlaceProjection(
                full_place.clone(),
            ));
        }
        return Err(RvalueEvalError::PointerRangeOverflow {
            addr: addr as u64,
            byte_len,
        });
    }
    let Some(prov) = ptr.provenance else {
        return Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        ));
    };
    let Some(target_local) = prov
        .alloc_id
        .checked_sub(1)
        .and_then(|id| usize::try_from(id).ok())
        .filter(|&loc| loc < frame.frame_local_count())
    else {
        return Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        ));
    };
    if matches!(frame.frame_slot(target_local), Some(FrameSlot::Dead)) {
        return Err(RvalueEvalError::DeadLocal(Local(target_local)));
    }
    let base_addr = local_base_addr_for_decls(target_local, frame.frame_decls(), ptr_width)?;
    let target_decl_ty = &frame.frame_decls()[target_local];
    let (target_alloc_size, _) = target_decl_ty
        .alloc_size_and_align(ptr_width)
        .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(target_decl_ty, err)))?;
    let Some(rel_off_u128) = addr.checked_sub(base_addr) else {
        return Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        ));
    };
    let Ok(rel_off) = usize::try_from(rel_off_u128) else {
        return Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        ));
    };
    if rel_off
        .checked_add(pointee_size)
        .is_none_or(|end| end > target_alloc_size)
    {
        return Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        ));
    }
    // A finite `Ty` never contains a strict sub-place of the same type, so offset 0 with
    // `target_decl_ty == pointee_ty` is uniquely the root local (even for unspecified layouts).
    if rel_off == 0 && target_decl_ty == pointee_ty {
        return Ok((Local(target_local), Vec::new()));
    }
    let candidates = collect_subplace_paths(target_decl_ty, rel_off, pointee_ty, ptr_width);
    match select_subplace_candidate_in(
        frame,
        target_local,
        pointee_ty,
        candidates,
        prov.tag,
        full_place,
        allow_union_overwrite,
    ) {
        Some(path) => Ok((Local(target_local), path)),
        None => Err(RvalueEvalError::UnsupportedPlaceProjection(
            full_place.clone(),
        )),
    }
}

/// Selects, without guessing, the sub-place of `target_local` that a pointer with provenance
/// tag `tag` and pointee type `pointee_ty` designates among the same-offset, same-type
/// `candidates` produced by [`collect_subplace_paths`]:
/// 1. candidates inconsistent with the runtime state of the local (an inactive enum variant
///    or union field along the path) are discarded: a byte memory holds the active ones, so
///    reaching an inactive one would pun the bytes of another variant or union field
///    (unsupported without a byte-level memory model, never a guessed sub-place). On a
///    whole-target write (`allow_union_overwrite`), overwriting a leaf union field switches
///    that union's active field when designated by an uncast field-borrow tag or when no
///    active candidate of `pointee_ty` exists;
/// 2. a unique remaining candidate is the designated sub-place;
/// 3. among several, the one whose ordinal the borrow encoded in `tag` for the same pointee
///    type is selected ([`decode_subplace_tag`]; a tag that survived a pointer cast to
///    another pointee type carries no usable ordinal);
/// 4. otherwise a zero-sized `pointee_ty` (all of whose values are equal) selects the first
///    initialized remaining candidate (or the first one), and any other ambiguity (e.g.
///    same-typed fields of two variants of an uninitialized enum) is `None`.
///
/// `None` is reported as unsupported by the caller.
fn select_subplace_candidate_in<F: FrameView + ?Sized>(
    frame: &F,
    target_local: usize,
    pointee_ty: &Ty,
    mut candidates: Vec<Vec<ProjectionElem>>,
    tag: u64,
    full_place: &Place,
    allow_union_overwrite: bool,
) -> Option<Vec<ProjectionElem>> {
    let slot = frame.frame_slot(target_local)?;
    let decl_ty = frame.frame_decls().get(target_local)?;
    let no_index = |_: Local| -> Result<u128, RvalueEvalError> {
        Err(RvalueEvalError::TypeMismatch("unexpected dynamic index"))
    };
    let consistent_with = |allow_overwrite: bool| -> Vec<usize> {
        (0..candidates.len())
            .filter(|&i| {
                check_frame_slot_projection(
                    slot,
                    Local(target_local),
                    decl_ty,
                    &candidates[i],
                    &no_index,
                    full_place,
                )
                .is_ok()
                    && frame_slot_union_path_active(slot, &candidates[i], allow_overwrite)
            })
            .collect()
    };
    let active_consistent = consistent_with(false);
    let overwrite_consistent = if allow_union_overwrite {
        consistent_with(true)
    } else {
        Vec::new()
    };
    if allow_union_overwrite
        && let Some(ordinal) = decode_subplace_tag(tag, pointee_ty)
        && overwrite_consistent.contains(&ordinal)
    {
        return Some(candidates.swap_remove(ordinal));
    }
    let consistent = if !active_consistent.is_empty() || !allow_union_overwrite {
        &active_consistent
    } else {
        &overwrite_consistent
    };
    let chosen = match consistent.as_slice() {
        [] => return None,
        [only] => *only,
        [first, ..] => {
            if let Some(ordinal) = decode_subplace_tag(tag, pointee_ty)
                && consistent.contains(&ordinal)
            {
                ordinal
            } else if pointee_ty
                .layout_for(frame.frame_ptr_width())
                .is_ok_and(|layout| layout.size == 0)
            {
                consistent
                    .iter()
                    .copied()
                    .find(|&i| {
                        read_frame_place(frame, Local(target_local), &candidates[i], &[], full_place)
                            .is_ok()
                    })
                    .unwrap_or(*first)
            } else {
                return None;
            }
        }
    };
    Some(candidates.swap_remove(chosen))
}

/// Resolves all `ProjectionElem::Deref` steps in `place` from left to right (reading each
/// dereferenced pointer from the place resolved so far) and reads the `Index` operands in
/// place-evaluation order, returning `(target_local, target_proj, index_cache)` where
/// `index_cache` holds the operands of the `Index` steps after the last `Deref`. With
/// `allow_final_union_overwrite`, a final `Deref` (nothing projected after it) resolves for a
/// whole-place write (see [`resolve_synthetic_subplace_in`]).
#[allow(clippy::type_complexity)]
fn resolve_deref_place_in<F: FrameView + ?Sized>(
    frame: &F,
    place: &Place,
    allow_final_union_overwrite: bool,
) -> Result<(Local, Vec<ProjectionElem>, Vec<(Local, u128)>), RvalueEvalError> {
    let decls = frame.frame_decls();
    let Some(base_decl_ty) = decls.get(place.local.0) else {
        return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
    };
    validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
        base_decl_ty,
        &place.projection,
        Some(decls),
        None,
        place,
        None,
    )?;
    match frame.frame_slot(place.local.0) {
        None => return Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
        Some(FrameSlot::Dead) => return Err(RvalueEvalError::DeadLocal(place.local)),
        Some(FrameSlot::Live(_)) => {}
    }
    let mut cur_local = place.local;
    let mut cur_proj: Vec<ProjectionElem> = Vec::new();
    let mut cur_index_cache: Vec<(Local, u128)> = Vec::new();
    let proj_len = place.projection.len();
    for (idx, elem) in place.projection.iter().enumerate() {
        if matches!(elem, ProjectionElem::Deref) {
            let ptr_val = read_frame_place(frame, cur_local, &cur_proj, &cur_index_cache, place)?;
            let MirValue::Ptr { ptr, ty: ptr_ty } = ptr_val else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Deref projection requires a pointer value",
                ));
            };
            let Some(pointee_ty) = ptr_ty.pointee_ty() else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Deref projection requires a pointer-typed place",
                ));
            };
            let allow_union_overwrite = allow_final_union_overwrite && idx + 1 == proj_len;
            let (next_local, next_proj) = resolve_synthetic_subplace_in(
                frame,
                &ptr,
                &ptr_ty,
                pointee_ty,
                place,
                allow_union_overwrite,
            )?;
            cur_local = next_local;
            cur_proj = next_proj;
            cur_index_cache.clear();
        } else {
            if let ProjectionElem::Index(idx_local) = elem {
                cur_index_cache.push((*idx_local, frame.frame_index_operand(*idx_local)?));
            }
            cur_proj.push(elem.clone());
        }
    }
    Ok((cur_local, cur_proj, cur_index_cache))
}

/// Evaluates `Rvalue::Ref` / `Rvalue::RawPtr` (`expected_ref` for `Ref`) of the projected
/// `place` (non-empty projection) with pointee type `pointee_ty` in `frame`, returning the
/// synthetic pointer value (the caller rejects a null `&T`):
/// - `&(*p)` / `&raw (*p)` (nothing after the last `Deref`) keeps `p`'s address and
///   provenance;
/// - `&((*p).tail)` / `&raw ((*p).tail)` addresses `tail` inside `*p`'s synthetic
///   allocation ([`resolve_reborrow_with_tail_in`]);
/// - `&_l.proj` / `&raw _l.proj` (no `Deref`) adds the layout offset of `proj` to `_l`'s
///   synthetic base address, after reading the `Index` operands and checking the runtime
///   state along `proj` (active variants and union fields, array bounds), without reading the
///   place itself (an uninitialized `_l` can be borrowed).
fn eval_projected_ref_in<F: FrameView + ?Sized>(
    frame: &F,
    place: &Place,
    pointee_ty: &Ty,
    expected_ref: bool,
) -> Result<PointerValue, RvalueEvalError> {
    let decls = frame.frame_decls();
    let ptr_width = frame.frame_ptr_width();
    let Some(base_decl_ty) = decls.get(place.local.0) else {
        return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
    };
    let leaf_ty = validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
        base_decl_ty,
        &place.projection,
        Some(decls),
        None,
        place,
        None,
    )?;
    if leaf_ty != *pointee_ty {
        return Err(RvalueEvalError::TypeMismatch(
            "Ref/RawPtr projected place type does not match pointee type",
        ));
    }
    let root_slot = match frame.frame_slot(place.local.0) {
        None => return Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
        Some(FrameSlot::Dead) => return Err(RvalueEvalError::DeadLocal(place.local)),
        Some(slot) => slot,
    };
    if let Some(last_deref_pos) = place
        .projection
        .iter()
        .rposition(|p| matches!(p, ProjectionElem::Deref))
    {
        let ptr_place = Place {
            local: place.local,
            projection: place.projection[..last_deref_pos].to_vec(),
        };
        let tail = &place.projection[last_deref_pos + 1..];
        let (ptr_local, ptr_proj, ptr_index_cache) = resolve_deref_place_in(frame, &ptr_place, false)?;
        let ptr_val = read_frame_place(frame, ptr_local, &ptr_proj, &ptr_index_cache, &ptr_place)?;
        let MirValue::Ptr {
            ptr: base_ptr,
            ty: base_ptr_ty,
        } = ptr_val
        else {
            return Err(RvalueEvalError::TypeMismatch(
                "Deref projection requires a pointer value",
            ));
        };
        let Some(deref_ty) = base_ptr_ty.pointee_ty() else {
            return Err(RvalueEvalError::TypeMismatch(
                "Deref projection requires a pointer-typed place",
            ));
        };
        if tail.is_empty() {
            if deref_ty != pointee_ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "Deref projection requires a pointer value with matching pointee type",
                ));
            }
            let addr = checked_ptr_addr(&base_ptr, &base_ptr_ty, ptr_width)? as u64;
            if base_ptr_ty.is_ref() && addr == 0 {
                return Err(RvalueEvalError::CastEval(
                    CastEvalError::InvalidBitPattern {
                        target_ty: base_ptr_ty,
                        bits: 0,
                    },
                ));
            }
            return Ok(PointerValue {
                addr,
                provenance: base_ptr.provenance,
            });
        }
        return resolve_reborrow_with_tail_in(
            frame,
            place,
            &base_ptr,
            &base_ptr_ty,
            deref_ty,
            tail,
            pointee_ty,
            expected_ref,
        );
    }
    let mut index_cache = Vec::new();
    for elem in &place.projection {
        if let ProjectionElem::Index(idx_local) = elem {
            index_cache.push((*idx_local, frame.frame_index_operand(*idx_local)?));
        }
    }
    let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
    validate_projection_tail(
        base_decl_ty,
        &place.projection,
        Some(decls),
        Some(&read_index),
        place,
        None,
    )?;
    check_frame_slot_projection(
        root_slot,
        place.local,
        base_decl_ty,
        &place.projection,
        &read_index,
        place,
    )?;
    let (off, tag) = compute_subplace_offset_and_tag(
        base_decl_ty,
        &place.projection,
        &read_index,
        ptr_width,
        place,
    )?;
    // In bounds of an allocation that fits the address space: no wrap.
    let addr = local_base_addr_for_decls(place.local.0, decls, ptr_width)? + off as u128;
    Ok(PointerValue::with_provenance(
        addr as u64,
        place.local.0 as u64 + 1,
        tag,
    ))
}

/// Evaluates the non-empty `tail` of `&((*base_ptr).tail)` / `&raw ((*base_ptr).tail)` in
/// `frame`, after `base_ptr` (of type `base_ptr_ty`, pointee `deref_ty`) has been read from
/// the prefix of `place` before its last `ProjectionElem::Deref`.
///
/// A reference result (`expected_ref`) or a reference base requires `base_ptr` to be aligned
/// to `deref_ty` (and, for a reference base, an inhabited `deref_ty`). The target local must
/// be live (`DeadLocal`) before the tail's `Index` operands are read. `*base_ptr` normally
/// resolves to a synthetic sub-place ([`resolve_synthetic_subplace_in`]) that `tail` is
/// appended to. When it does not, an address-only raw reborrow without `Downcast` steps (an
/// `&raw` result through a raw `base_ptr`) only needs MiniRust's `offset_inbounds`:
/// `rel_off <= alloc_size` and `rel_off + tail_off <= alloc_size` inside the target local
/// (e.g. a misaligned `*const (u32, u32)` into a byte array).
#[allow(clippy::too_many_arguments)]
fn resolve_reborrow_with_tail_in<F: FrameView + ?Sized>(
    frame: &F,
    place: &Place,
    base_ptr: &PointerValue,
    base_ptr_ty: &Ty,
    deref_ty: &Ty,
    tail: &[ProjectionElem],
    pointee_ty: &Ty,
    expected_ref: bool,
) -> Result<PointerValue, RvalueEvalError> {
    let ptr_width = frame.frame_ptr_width();
    let decls = frame.frame_decls();
    let base_addr = checked_ptr_addr(base_ptr, base_ptr_ty, ptr_width)?;
    if expected_ref || base_ptr_ty.is_ref() {
        if base_addr == 0 {
            if base_ptr_ty.is_ref() {
                return Err(RvalueEvalError::CastEval(
                    CastEvalError::InvalidBitPattern {
                        target_ty: base_ptr_ty.clone(),
                        bits: 0,
                    },
                ));
            }
            return Err(RvalueEvalError::NullPointerAccess);
        }
        let (min_align, max_align) = deref_ty
            .align_bounds(ptr_width)
            .map_err(|err| RvalueEvalError::CastEval(cast_eval_layout_error(deref_ty, err)))?;
        if !base_addr.is_multiple_of(min_align as u128) {
            return Err(RvalueEvalError::MisalignedPointer {
                addr: base_addr as u64,
                required_align: min_align,
            });
        }
        if !base_addr.is_multiple_of(max_align as u128) {
            return Err(RvalueEvalError::CastEval(
                CastEvalError::UnsupportedLayout {
                    ty: deref_ty.clone(),
                },
            ));
        }
        if base_ptr_ty.is_ref() && !deref_ty.is_inhabited_for(ptr_width) {
            return Err(RvalueEvalError::UninhabitedPointee(deref_ty.clone()));
        }
    }
    let target_local_opt = base_ptr.provenance.and_then(|prov| {
        prov.alloc_id
            .checked_sub(1)
            .and_then(|id| usize::try_from(id).ok())
            .filter(|&loc| loc < frame.frame_local_count())
    });
    let target_is_dead =
        target_local_opt.is_some_and(|loc| matches!(frame.frame_slot(loc), Some(FrameSlot::Dead)));
    let has_downcast = tail.iter().any(|p| matches!(p, ProjectionElem::Downcast(_)));
    let is_address_only_raw =
        !expected_ref && matches!(base_ptr_ty, Ty::RawPtr(..)) && !has_downcast;
    if !is_address_only_raw {
        if base_addr == 0 {
            return Err(RvalueEvalError::NullPointerAccess);
        }
        let Some(target_local) = target_local_opt else {
            return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
        };
        if target_is_dead {
            return Err(RvalueEvalError::DeadLocal(Local(target_local)));
        }
    }
    // As for loads and stores (`resolve_deref_place_in` resolves a `Deref` before reading the
    // `Index` operands after it), the pointer's own faults come first: when a tail `Index`
    // operand cannot be read, a null or storage-dead `base_ptr` is reported before it.
    let mut tail_index_cache = Vec::new();
    for elem in tail {
        if let ProjectionElem::Index(idx_local) = elem {
            match frame.frame_index_operand(*idx_local) {
                Ok(bits) => tail_index_cache.push((*idx_local, bits)),
                Err(err) => {
                    if base_addr == 0 {
                        return Err(RvalueEvalError::NullPointerAccess);
                    }
                    if let Some(dead_loc) = target_local_opt.filter(|_| target_is_dead) {
                        return Err(RvalueEvalError::DeadLocal(Local(dead_loc)));
                    }
                    return Err(err);
                }
            }
        }
    }
    let read_index = |idx_local: Local| cached_index(&tail_index_cache, idx_local);
    if is_address_only_raw && (base_addr == 0 || target_local_opt.is_none() || target_is_dead) {
        validate_projection_tail(
            deref_ty,
            tail,
            Some(decls),
            Some(&read_index),
            place,
            None,
        )?;
        let (tail_off, _) =
            compute_subplace_offset_and_tag(deref_ty, tail, &read_index, ptr_width, place)?;
        if tail_off == 0 {
            return Ok(PointerValue {
                addr: base_addr as u64,
                provenance: base_ptr.provenance,
            });
        }
        if base_addr == 0 {
            return Err(RvalueEvalError::NullPointerAccess);
        }
        if let Some(dead_loc) = target_local_opt.filter(|_| target_is_dead) {
            return Err(RvalueEvalError::DeadLocal(Local(dead_loc)));
        }
        return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
    }
    let target_local = target_local_opt.unwrap();
    let prov = base_ptr.provenance.unwrap();
    match resolve_synthetic_subplace_in(frame, base_ptr, base_ptr_ty, deref_ty, place, false) {
        Ok((resolved_local, mut combined_proj)) => {
            combined_proj.extend_from_slice(tail);
            let base_decl_ty = &decls[resolved_local.0];
            validate_projection_tail(
                base_decl_ty,
                &combined_proj,
                Some(decls),
                Some(&read_index),
                place,
                None,
            )?;
            let Some(slot) = frame.frame_slot(resolved_local.0) else {
                return Err(RvalueEvalError::TypeMismatch("local index out of bounds"));
            };
            check_frame_slot_projection(
                slot,
                resolved_local,
                base_decl_ty,
                &combined_proj,
                &read_index,
                place,
            )?;
            let (off, tag) = compute_subplace_offset_and_tag(
                base_decl_ty,
                &combined_proj,
                &read_index,
                ptr_width,
                place,
            )?;
            let addr = local_base_addr_for_decls(resolved_local.0, decls, ptr_width)? + off as u128;
            Ok(PointerValue::with_provenance(
                addr as u64,
                resolved_local.0 as u64 + 1,
                tag,
            ))
        }
        Err(err) => {
            if !is_address_only_raw {
                return Err(err);
            }
            validate_projection_tail(
                deref_ty,
                tail,
                Some(decls),
                Some(&read_index),
                place,
                None,
            )?;
            let (tail_off, _) =
                compute_subplace_offset_and_tag(deref_ty, tail, &read_index, ptr_width, place)?;
            let local_base = local_base_addr_for_decls(target_local, decls, ptr_width)?;
            let target_decl_ty = &decls[target_local];
            let (target_alloc_size, _) = target_decl_ty
                .alloc_size_and_align(ptr_width)
                .map_err(|e| RvalueEvalError::CastEval(cast_eval_layout_error(target_decl_ty, e)))?;
            let Some(rel_off) = base_addr
                .checked_sub(local_base)
                .and_then(|off| usize::try_from(off).ok())
                .filter(|&off| off <= target_alloc_size)
            else {
                if tail_off == 0 {
                    return Ok(PointerValue {
                        addr: base_addr as u64,
                        provenance: base_ptr.provenance,
                    });
                }
                return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
            };
            let Some(total_off) = rel_off
                .checked_add(tail_off)
                .filter(|&end| end <= target_alloc_size)
            else {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(place.clone()));
            };
            let matches = collect_subplace_paths(target_decl_ty, total_off, pointee_ty, ptr_width);
            let tag = if matches.len() <= 1 {
                1
            } else if let Some(ord) =
                decode_subplace_tag(prov.tag, pointee_ty).filter(|&o| o < matches.len())
            {
                encode_subplace_tag(pointee_ty, ord)
            } else {
                1
            };
            Ok(PointerValue::with_provenance(
                (local_base + total_off as u128) as u64,
                target_local as u64 + 1,
                tag,
            ))
        }
    }
}

/// The local whose synthetic allocation id `ptr` carries, if in `0..local_count`.
fn resolve_synthetic_alloc_local(ptr: &PointerValue, local_count: usize) -> Option<usize> {
    let alloc_id = ptr.provenance?.alloc_id;
    let local = usize::try_from(alloc_id.checked_sub(1)?).ok()?;
    (local < local_count).then_some(local)
}

/// Byte offset of field `idx` of variant `variant` of the tuple or ADT `container_ty` for
/// synthetic sub-place addressing, or `None` when the layout model does not determine it.
///
/// ADT fields use [`AdtDef::field_offset`], and tuple fields the `#[repr(Rust)]` rule shared
/// with repr(Rust) structs (declaration-order offsets only for canonical field tuples, see
/// [`Ty::has_canonical_byte_layout`]): e.g. `rustc` lays out `(u32, (u32, u32))` pair-first, so
/// its declaration-order offsets must not be committed to. In addition, a zero-sized field at a
/// non-zero declaration offset of a field list `rustc` may reorder (tuples, `#[repr(Rust)]` and
/// `#[repr(transparent)]` structs, and enums laid out without a tag) is unspecified: `rustc`
/// sorts 1-ZST fields first (offset `0`), so e.g. the `()` of `(u32, ())` is not at offset `4`.
fn subplace_field_offset(
    container_ty: &Ty,
    variant: usize,
    idx: usize,
    ptr_width: PtrWidth,
) -> Option<usize> {
    let (off, field_ty, reorderable) = match container_ty {
        Ty::Tuple(fields) => (
            crate::ir::rust_field_offset(fields, idx, ptr_width).ok()?,
            fields.get(idx)?,
            true,
        ),
        Ty::Adt(def) => {
            let off = def.field_offset(variant, idx, ptr_width).ok()?;
            let field_ty = def.variant_fields(variant)?.get(idx)?;
            let reorderable = def.repr.kind != crate::ir::AdtReprKind::C
                && matches!(
                    def.kind,
                    crate::ir::AdtKind::Struct { .. } | crate::ir::AdtKind::Enum { tag_ty: None, .. }
                );
            (off, field_ty, reorderable)
        }
        _ => return None,
    };
    if reorderable && off != 0 && field_ty.layout_for(ptr_width).ok()?.size == 0 {
        return None;
    }
    Some(off)
}

/// Deterministic (per-process) 32-bit fingerprint of `ty`, binding a sub-place provenance tag
/// ordinal to the pointee type it was computed for (see [`encode_subplace_tag`]).
fn subplace_type_fingerprint(ty: &Ty) -> u32 {
    use std::hash::{DefaultHasher, Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    ty.hash(&mut hasher);
    let h = hasher.finish();
    (h ^ (h >> 32)) as u32
}

/// Provenance tag of a sub-place that is the `ordinal`-th of several same-offset candidates of
/// type `ty` ([`collect_subplace_paths`]): `(fingerprint(ty) << 32) | (ordinal + 2)`. Tag `1`
/// (or any tag whose low half is `< 2`) carries no ordinal.
fn encode_subplace_tag(ty: &Ty, ordinal: usize) -> u64 {
    match u32::try_from(ordinal).ok().and_then(|o| o.checked_add(2)) {
        Some(low) => (u64::from(subplace_type_fingerprint(ty)) << 32) | u64::from(low),
        None => 1,
    }
}

/// The candidate ordinal carried by provenance tag `tag` for pointee type `ty`, if `tag` was
/// computed by [`encode_subplace_tag`] for the same type (a tag that survived a pointer cast to
/// another pointee type, or a type-punning transmute, carries no usable ordinal).
fn decode_subplace_tag(tag: u64, ty: &Ty) -> Option<usize> {
    let low = (tag & 0xFFFF_FFFF) as u32;
    let ordinal = low.checked_sub(2)?;
    ((tag >> 32) as u32 == subplace_type_fingerprint(ty)).then_some(ordinal as usize)
}

/// Collects all canonical projection paths inside `root_ty` whose sub-place has byte offset
/// `target_off` and declared type `target_ty` under `ptr_width`.
fn collect_subplace_paths(
    root_ty: &Ty,
    target_off: usize,
    target_ty: &Ty,
    ptr_width: PtrWidth,
) -> Vec<Vec<ProjectionElem>> {
    let mut cur_path = Vec::new();
    let mut out = Vec::new();
    collect_subplace_paths_rec(
        root_ty,
        0,
        target_off,
        target_ty,
        ptr_width,
        &mut cur_path,
        &mut out,
    );
    out
}

fn collect_subplace_paths_rec(
    cur_ty: &Ty,
    cur_off: usize,
    target_off: usize,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    cur_path: &mut Vec<ProjectionElem>,
    out: &mut Vec<Vec<ProjectionElem>>,
) {
    if cur_off == target_off && cur_ty == target_ty {
        out.push(cur_path.clone());
    }
    if target_off < cur_off {
        return;
    }
    if let Ok((cur_size, _)) = cur_ty.alloc_size_and_align(ptr_width)
        && target_off > cur_off.saturating_add(cur_size)
    {
        return;
    }
    match cur_ty {
        Ty::Tuple(fields) => {
            for (idx, field_ty) in fields.iter().enumerate() {
                let Some(field_off) = subplace_field_offset(cur_ty, 0, idx, ptr_width)
                    .and_then(|off| cur_off.checked_add(off))
                else {
                    continue;
                };
                cur_path.push(ProjectionElem::Field(idx, field_ty.clone()));
                collect_subplace_paths_rec(
                    field_ty,
                    field_off,
                    target_off,
                    target_ty,
                    ptr_width,
                    cur_path,
                    out,
                );
                cur_path.pop();
            }
        }
        Ty::Array(elem_ty, len) => {
            let Ok(elem_layout) = elem_ty.layout_for(ptr_width) else {
                return;
            };
            let elem_size = elem_layout.size;
            let rel = target_off - cur_off;
            if let Ty::Array(sub_elem, sub_len) = target_ty
                && **sub_elem == **elem_ty
                && *sub_len < *len
            {
                if elem_size > 0 {
                    if rel.is_multiple_of(elem_size) {
                        let start = rel / elem_size;
                        if let Some(end) = start.checked_add(*sub_len)
                            && end <= *len
                        {
                            cur_path.push(ProjectionElem::Subslice {
                                from: start as u64,
                                to: end as u64,
                                from_end: false,
                            });
                            out.push(cur_path.clone());
                            cur_path.pop();
                        }
                    }
                } else if rel == 0 {
                    // Zero-sized elements: every window `[start..start + sub_len]` holds equal
                    // values in the same (per-array) state, so only `start == 0` is a candidate
                    // (see the element case below).
                    cur_path.push(ProjectionElem::Subslice {
                        from: 0,
                        to: *sub_len as u64,
                        from_end: false,
                    });
                    out.push(cur_path.clone());
                    cur_path.pop();
                }
            }
            if *len == 0 {
                return;
            }
            if let Some(q) = rel.checked_div(elem_size) {
                let mut candidates = Vec::with_capacity(2);
                if q > 0 && rel.is_multiple_of(elem_size) && q - 1 < *len {
                    candidates.push(q - 1);
                }
                if q < *len {
                    candidates.push(q);
                }
                for idx in candidates {
                    let Some(elem_off) = cur_off.checked_add(idx.saturating_mul(elem_size)) else {
                        continue;
                    };
                    cur_path.push(ProjectionElem::ConstantIndex {
                        offset: idx as u64,
                        min_length: *len as u64,
                        from_end: false,
                    });
                    collect_subplace_paths_rec(
                        elem_ty,
                        elem_off,
                        target_off,
                        target_ty,
                        ptr_width,
                        cur_path,
                        out,
                    );
                    cur_path.pop();
                }
            } else if rel == 0 {
                // Zero-sized elements all sit at offset 0. Arrays have no per-element
                // initialization state and all values of a zero-sized type are equal, so every
                // element designates an equivalent sub-place: only element 0 is enumerated
                // (canonical, see `compute_subplace_offset_and_tag`), which also keeps the
                // enumeration bounded for huge or nested zero-sized arrays
                // (`[[(); 1 << 20]; 1 << 20]`).
                cur_path.push(ProjectionElem::ConstantIndex {
                    offset: 0,
                    min_length: *len as u64,
                    from_end: false,
                });
                collect_subplace_paths_rec(
                    elem_ty,
                    cur_off,
                    target_off,
                    target_ty,
                    ptr_width,
                    cur_path,
                    out,
                );
                cur_path.pop();
            }
        }
        Ty::Adt(def) => {
            if def.is_enum() {
                for v in 0..def.variant_count() {
                    let Some(fields) = def.variant_fields(v) else {
                        continue;
                    };
                    for (idx, field_ty) in fields.iter().enumerate() {
                        let Some(field_off) = subplace_field_offset(cur_ty, v, idx, ptr_width)
                            .and_then(|off| cur_off.checked_add(off))
                        else {
                            continue;
                        };
                        cur_path.push(ProjectionElem::Downcast(v));
                        cur_path.push(ProjectionElem::Field(idx, field_ty.clone()));
                        collect_subplace_paths_rec(
                            field_ty,
                            field_off,
                            target_off,
                            target_ty,
                            ptr_width,
                            cur_path,
                            out,
                        );
                        cur_path.pop();
                        cur_path.pop();
                    }
                }
            } else if let Some(fields) = def.variant_fields(0) {
                for (idx, field_ty) in fields.iter().enumerate() {
                    let Some(field_off) = subplace_field_offset(cur_ty, 0, idx, ptr_width)
                        .and_then(|off| cur_off.checked_add(off))
                    else {
                        continue;
                    };
                    cur_path.push(ProjectionElem::Field(idx, field_ty.clone()));
                    collect_subplace_paths_rec(
                        field_ty,
                        field_off,
                        target_off,
                        target_ty,
                        ptr_width,
                        cur_path,
                        out,
                    );
                    cur_path.pop();
                }
            }
        }
        _ => {}
    }
}

/// Computes the byte offset and disambiguation provenance tag of the `Deref`-free projection
/// `proj` from `root_ty` under `ptr_width`.
fn compute_subplace_offset_and_tag(
    root_ty: &Ty,
    proj: &[ProjectionElem],
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    full_place: &Place,
) -> Result<(usize, u64), RvalueEvalError> {
    let mut cur_ty = root_ty.clone();
    let mut total_off = 0usize;
    let mut active_downcast: Option<usize> = None;
    let mut canonical_proj: Vec<ProjectionElem> = Vec::with_capacity(proj.len());
    // Track original array length before a `Subslice` step so consecutive `Subslice`/`Index`
    // steps coalesce into the canonical single-step form produced by `collect_subplace_paths`.
    let mut subslice_base_len: Option<usize> = None;

    for elem in proj {
        match elem {
            ProjectionElem::Deref => {
                return Err(RvalueEvalError::UnsupportedPlaceProjection(
                    full_place.clone(),
                ));
            }
            ProjectionElem::Downcast(v) => {
                if active_downcast.is_some() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "consecutive Downcast projections without Field",
                    ));
                }
                active_downcast = Some(*v);
                canonical_proj.push(ProjectionElem::Downcast(*v));
                subslice_base_len = None;
            }
            ProjectionElem::Field(idx, _) => {
                subslice_base_len = None;
                match &cur_ty {
                    Ty::Adt(def) => {
                        let v = active_downcast.take().unwrap_or(0);
                        let Some(variant_fields) = def.variant_fields(v) else {
                            return Err(RvalueEvalError::TypeMismatch(
                                "Field variant index out of range",
                            ));
                        };
                        let Some(field_ty) = variant_fields.get(*idx).cloned() else {
                            return Err(RvalueEvalError::FieldOutOfBounds {
                                field_idx: *idx,
                                field_count: variant_fields.len(),
                            });
                        };
                        let off = subplace_field_offset(&cur_ty, v, *idx, ptr_width).ok_or_else(
                            || RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()),
                        )?;
                        total_off = total_off.checked_add(off).ok_or_else(|| {
                            RvalueEvalError::UnsupportedPlaceProjection(full_place.clone())
                        })?;
                        canonical_proj.push(ProjectionElem::Field(*idx, field_ty.clone()));
                        cur_ty = field_ty;
                    }
                    Ty::Tuple(fields) => {
                        if active_downcast.take().is_some() {
                            return Err(RvalueEvalError::UnsupportedPlaceProjection(
                                full_place.clone(),
                            ));
                        }
                        let Some(field_ty) = fields.get(*idx).cloned() else {
                            return Err(RvalueEvalError::FieldOutOfBounds {
                                field_idx: *idx,
                                field_count: fields.len(),
                            });
                        };
                        let off = subplace_field_offset(&cur_ty, 0, *idx, ptr_width).ok_or_else(
                            || RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()),
                        )?;
                        total_off = total_off.checked_add(off).ok_or_else(|| {
                            RvalueEvalError::UnsupportedPlaceProjection(full_place.clone())
                        })?;
                        canonical_proj.push(ProjectionElem::Field(*idx, field_ty.clone()));
                        cur_ty = field_ty;
                    }
                    _ => {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Field projection requires Tuple or Adt type",
                        ));
                    }
                }
            }
            ProjectionElem::Index(idx_local) => {
                if active_downcast.is_some() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast projection must be followed by Field",
                    ));
                }
                let Ty::Array(elem_ty, len) = &cur_ty else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Index projection requires Array type",
                    ));
                };
                let idx_bits = read_index(*idx_local)?;
                let Ok(i) = usize::try_from(idx_bits) else {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: idx_bits,
                        len: *len,
                    });
                };
                if i >= *len {
                    return Err(RvalueEvalError::IndexOutOfBounds {
                        index: idx_bits,
                        len: *len,
                    });
                }
                let elem_size = elem_ty
                    .layout_for(ptr_width)
                    .map_err(|_| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?
                    .size;
                let step_off = i
                    .checked_mul(elem_size)
                    .ok_or_else(|| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?;
                total_off = total_off
                    .checked_add(step_off)
                    .ok_or_else(|| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?;
                // Zero-sized elements are canonically element 0 (see `collect_subplace_paths`).
                let i_canon = if elem_size == 0 { 0 } else { i };
                if let (
                    Some(orig_len),
                    Some(ProjectionElem::Subslice {
                        from: s_from,
                        from_end: false,
                        ..
                    }),
                ) = (subslice_base_len.take(), canonical_proj.last().cloned())
                {
                    canonical_proj.pop();
                    canonical_proj.push(ProjectionElem::ConstantIndex {
                        offset: s_from + i_canon as u64,
                        min_length: orig_len as u64,
                        from_end: false,
                    });
                } else {
                    canonical_proj.push(ProjectionElem::ConstantIndex {
                        offset: i_canon as u64,
                        min_length: *len as u64,
                        from_end: false,
                    });
                }
                cur_ty = (**elem_ty).clone();
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
                let Ty::Array(elem_ty, len) = &cur_ty else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "ConstantIndex projection requires Array type",
                    ));
                };
                let i = resolve_constant_index(*len, *offset, *min_length, *from_end)?;
                let elem_size = elem_ty
                    .layout_for(ptr_width)
                    .map_err(|_| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?
                    .size;
                let step_off = i
                    .checked_mul(elem_size)
                    .ok_or_else(|| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?;
                total_off = total_off
                    .checked_add(step_off)
                    .ok_or_else(|| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?;
                // Zero-sized elements are canonically element 0 (see `collect_subplace_paths`).
                let i_canon = if elem_size == 0 { 0 } else { i };
                if let (
                    Some(orig_len),
                    Some(ProjectionElem::Subslice {
                        from: s_from,
                        from_end: false,
                        ..
                    }),
                ) = (subslice_base_len.take(), canonical_proj.last().cloned())
                {
                    canonical_proj.pop();
                    canonical_proj.push(ProjectionElem::ConstantIndex {
                        offset: s_from + i_canon as u64,
                        min_length: orig_len as u64,
                        from_end: false,
                    });
                } else {
                    canonical_proj.push(ProjectionElem::ConstantIndex {
                        offset: i_canon as u64,
                        min_length: *len as u64,
                        from_end: false,
                    });
                }
                cur_ty = (**elem_ty).clone();
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
                let Ty::Array(elem_ty, len) = &cur_ty else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Subslice projection requires Array type",
                    ));
                };
                let (start, end) = resolve_subslice_range(*len, *from, *to, *from_end)?;
                let elem_size = elem_ty
                    .layout_for(ptr_width)
                    .map_err(|_| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?
                    .size;
                let step_off = start
                    .checked_mul(elem_size)
                    .ok_or_else(|| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?;
                total_off = total_off
                    .checked_add(step_off)
                    .ok_or_else(|| RvalueEvalError::UnsupportedPlaceProjection(full_place.clone()))?;
                let sub_len = end - start;
                // Zero-sized windows canonically start at element 0 (see `collect_subplace_paths`).
                let (start, end) = if elem_size == 0 { (0, sub_len) } else { (start, end) };
                if let (
                    Some(orig_len),
                    Some(ProjectionElem::Subslice {
                        from: s_from,
                        from_end: false,
                        ..
                    }),
                ) = (subslice_base_len, canonical_proj.last().cloned())
                {
                    canonical_proj.pop();
                    if sub_len < orig_len {
                        canonical_proj.push(ProjectionElem::Subslice {
                            from: s_from + start as u64,
                            to: s_from + end as u64,
                            from_end: false,
                        });
                        subslice_base_len = Some(orig_len);
                    } else {
                        subslice_base_len = None;
                    }
                } else if sub_len < *len {
                    subslice_base_len = Some(*len);
                    canonical_proj.push(ProjectionElem::Subslice {
                        from: start as u64,
                        to: end as u64,
                        from_end: false,
                    });
                }
                cur_ty = Ty::Array(elem_ty.clone(), sub_len);
            }
        }
    }
    if active_downcast.is_some() {
        return Err(RvalueEvalError::TypeMismatch(
            "Downcast projection must be followed by Field",
        ));
    }
    let matches = collect_subplace_paths(root_ty, total_off, &cur_ty, ptr_width);
    let tag = if matches.len() <= 1 {
        1
    } else if let Some(ordinal) = matches.iter().position(|p| *p == canonical_proj) {
        encode_subplace_tag(&cur_ty, ordinal)
    } else {
        1
    };
    Ok((total_off, tag))
}

/// Returns whether every union `Field` step in `proj` selects the active union field of the
/// initialized values reached in `slot` (also through partially initialized shells); steps
/// into uninitialized parts are unconstrained. When `allow_leaf_union_overwrite` is true, a
/// final leaf `Field` step on an initialized union may select an inactive union field (so a
/// whole-field write overwrites the union's active field).
fn slot_union_path_active(
    slot: &LocalSlotState,
    proj: &[ProjectionElem],
    allow_leaf_union_overwrite: bool,
) -> bool {
    match slot {
        LocalSlotState::Init(val) => {
            value_union_path_active(val, proj, allow_leaf_union_overwrite)
        }
        LocalSlotState::PartialShell(shell) => {
            shell_union_path_active(shell, proj, allow_leaf_union_overwrite)
        }
        LocalSlotState::Uninit | LocalSlotState::Dead => true,
    }
}

fn shell_union_path_active(
    shell: &PartialAggregate,
    proj: &[ProjectionElem],
    allow_leaf_union_overwrite: bool,
) -> bool {
    let Some((first, rest)) = proj.split_first() else {
        return true;
    };
    match first {
        ProjectionElem::Downcast(_) => {
            shell_union_path_active(shell, rest, allow_leaf_union_overwrite)
        }
        ProjectionElem::Field(idx, _) => match shell.fields.get(*idx) {
            Some(FieldSlot::Init(val)) => {
                value_union_path_active(val, rest, allow_leaf_union_overwrite)
            }
            Some(FieldSlot::Partial(child)) => {
                shell_union_path_active(child, rest, allow_leaf_union_overwrite)
            }
            Some(FieldSlot::Uninit) | None => true,
        },
        _ => true,
    }
}

fn value_union_path_active(
    val: &MirValue,
    proj: &[ProjectionElem],
    allow_leaf_union_overwrite: bool,
) -> bool {
    let Some((first, rest)) = proj.split_first() else {
        return true;
    };
    match first {
        ProjectionElem::Downcast(_) => {
            value_union_path_active(val, rest, allow_leaf_union_overwrite)
        }
        ProjectionElem::Field(idx, _) => match val {
            MirValue::Tuple(fields) => fields
                .get(*idx)
                .is_some_and(|child| value_union_path_active(child, rest, allow_leaf_union_overwrite)),
            MirValue::Adt {
                active_field: None,
                fields,
                ..
            } => fields
                .get(*idx)
                .is_some_and(|child| value_union_path_active(child, rest, allow_leaf_union_overwrite)),
            MirValue::Adt {
                active_field: Some(active),
                fields,
                ..
            } => {
                let is_leaf_or_array_start = rest.is_empty()
                    || matches!(
                        rest,
                        [ProjectionElem::ConstantIndex {
                            offset: 0,
                            from_end: false,
                            ..
                        }]
                    );
                if is_leaf_or_array_start && allow_leaf_union_overwrite {
                    return true;
                }
                if *active != *idx {
                    return false;
                }
                let child = if fields.len() == 1 {
                    fields.first()
                } else {
                    fields.get(*active)
                };
                child.is_some_and(|c| value_union_path_active(c, rest, allow_leaf_union_overwrite))
            }
            _ => true,
        },
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => {
            let MirValue::Array { elements, .. } = val else {
                return true;
            };
            let Ok(i) = resolve_constant_index(elements.len(), *offset, *min_length, *from_end)
            else {
                return false;
            };
            value_union_path_active(&elements[i], rest, allow_leaf_union_overwrite)
        }
        _ => true,
    }
}

/// Borrowed view of a slot (a local's root `LocalSlotState` or a nested [`FieldSlot`]) for
/// [`read_slot_at_proj`], so reading a sub-slot clones only the selected part of the local.
#[derive(Clone, Copy)]
enum SlotRef<'a> {
    Uninit,
    Partial(&'a PartialAggregate),
    Init(&'a MirValue),
}

impl<'a> SlotRef<'a> {
    fn of_field(slot: &'a FieldSlot) -> Self {
        match slot {
            FieldSlot::Uninit => SlotRef::Uninit,
            FieldSlot::Partial(shell) => SlotRef::Partial(shell),
            FieldSlot::Init(val) => SlotRef::Init(val),
        }
    }

    fn to_field_slot(self) -> FieldSlot {
        match self {
            SlotRef::Uninit => FieldSlot::Uninit,
            SlotRef::Partial(shell) => FieldSlot::Partial(shell.clone()),
            SlotRef::Init(val) => FieldSlot::Init(val.clone()),
        }
    }
}

/// Reads the [`FieldSlot`] (`Uninit`, `Partial`, or `Init`) at `proj` inside `slot`, cloning
/// only the selected sub-slot (`O(proj.len())` traversal).
fn read_slot_at_proj(
    slot: SlotRef<'_>,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<FieldSlot, RvalueEvalError> {
    let no_index = |_: Local| -> Result<u128, RvalueEvalError> {
        Err(RvalueEvalError::TypeMismatch("unexpected dynamic index"))
    };
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        return Ok(slot.to_field_slot());
    };
    match slot {
        SlotRef::Uninit => {
            validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
                declared_ty,
                proj,
                None,
                None,
                full_place,
                active_downcast,
            )?;
            Ok(FieldSlot::Uninit)
        }
        SlotRef::Init(val) => {
            let (projected, _) = project_mir_value(
                val,
                Some(declared_ty),
                proj,
                &no_index,
                full_place,
                active_downcast,
            )?;
            let sub_val = match projected {
                ProjectedRef::Value(v) => v.clone(),
                ProjectedRef::ArrayWindow { window, elem_ty } => MirValue::Array {
                    elements: window.to_vec(),
                    elem_ty: elem_ty.clone(),
                },
            };
            Ok(FieldSlot::Init(sub_val))
        }
        SlotRef::Partial(shell) => {
            if !shell_matches_declared_ty(shell, declared_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "partial shell does not match declared type",
                ));
            }
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
                        return Err(RvalueEvalError::TypeMismatch(
                            "Downcast projection must be followed by Field",
                        ));
                    }
                    let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                    if actual != *expected_variant {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: *expected_variant,
                            actual,
                        });
                    }
                    read_slot_at_proj(
                        slot,
                        declared_ty,
                        rest,
                        full_place,
                        Some(*expected_variant),
                    )
                }
                ProjectionElem::Field(idx, expected_ty) => {
                    let Some(field_tys) = projectable_field_tys(declared_ty, active_downcast)
                    else {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Field projection requires a tuple-typed place (or a struct/union, or a downcast enum)",
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
                    let expected_variant = active_downcast.unwrap_or(0);
                    let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                    if actual != expected_variant {
                        return Err(RvalueEvalError::InactiveVariantProjection {
                            expected: expected_variant,
                            actual,
                        });
                    }
                    let Some(child_slot) = shell.fields.get(*idx) else {
                        return Err(RvalueEvalError::FieldOutOfBounds {
                            field_idx: *idx,
                            field_count: shell.fields.len(),
                        });
                    };
                    read_slot_at_proj(
                        SlotRef::of_field(child_slot),
                        &field_tys[*idx],
                        rest,
                        full_place,
                        None,
                    )
                }
                ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => Err(RvalueEvalError::TypeMismatch(
                    "array projection applied to a partially initialized tuple/ADT shell",
                )),
            }
        }
    }
}

/// `UnsupportedMemoryAccess` reason for copying (partially) uninitialized bytes into a union
/// field: defined in Rust, but a union value in the value tree is one initialized field.
const UNINIT_UNION_COPY: &str =
    "copy of uninitialized bytes into a union field needs a byte-level memory model";

/// Returns whether any `ProjectionElem::Field` step in `proj` projects out of a union ADT
/// starting from `cur_ty`.
fn proj_traverses_union<'a>(mut cur_ty: &'a Ty, proj: &'a [ProjectionElem]) -> bool {
    let mut active_downcast: Option<usize> = None;
    for elem in proj {
        match elem {
            ProjectionElem::Downcast(v) => {
                active_downcast = Some(*v);
            }
            ProjectionElem::Field(idx, field_ty) => {
                let v = active_downcast.take().unwrap_or(0);
                if matches!(cur_ty, Ty::Adt(def) if def.is_union()) {
                    return true;
                }
                cur_ty = match cur_ty {
                    Ty::Tuple(fields) => fields.get(*idx).unwrap_or(field_ty),
                    Ty::Adt(def) => def
                        .variant_fields(v)
                        .and_then(|fs| fs.get(*idx))
                        .unwrap_or(field_ty),
                    _ => field_ty,
                };
            }
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                active_downcast = None;
                let Ty::Array(elem_ty, _) = cur_ty else {
                    return false;
                };
                cur_ty = elem_ty;
            }
            ProjectionElem::Subslice { .. } => {
                active_downcast = None;
            }
            ProjectionElem::Deref => return false,
        }
    }
    false
}

/// Writes `FieldSlot::Partial(new_shell)` into `proj` inside `slot` (materializing parent
/// shells on `FieldSlot::Uninit` or exploding `FieldSlot::Init` aggregates as needed).
///
/// A partially initialized value written into an array element fails closed with
/// `UninitializedLocal` (arrays have no per-element shells, `c6d2ad74`); written into a union
/// field it is `UnsupportedMemoryAccess` (unions hold one initialized field).
fn write_partial_shell_in_slot(
    slot: &mut FieldSlot,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    new_shell: PartialAggregate,
    src_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    let Some((first, rest)) = proj.split_first() else {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "Downcast projection must be followed by Field",
            ));
        }
        *slot = FieldSlot::Partial(new_shell);
        normalize_slot(slot);
        return Ok(());
    };
    let is_union = matches!(declared_ty, Ty::Adt(def) if def.is_union());
    if matches!(slot, FieldSlot::Init(_)) {
        explode_init_slot(slot, full_place).map_err(|err| match err {
            RvalueEvalError::UnsupportedPlaceProjection(_) if is_union => {
                RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY)
            }
            RvalueEvalError::UnsupportedPlaceProjection(_) => {
                RvalueEvalError::UninitializedLocal(src_local)
            }
            other => other,
        })?;
    }
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
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection must be followed by Field",
                ));
            }
            if !downcast_allowed(declared_ty, *expected_variant) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Downcast projection requires a tuple-typed (ADT) place or an in-range enum variant",
                ));
            }
            if let FieldSlot::Partial(shell) = &*slot {
                if !shell_matches_declared_ty(shell, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "partial shell does not match declared type",
                    ));
                }
                let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                if actual != *expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: *expected_variant,
                        actual,
                    });
                }
            }
            write_partial_shell_in_slot(
                slot,
                declared_ty,
                rest,
                new_shell,
                src_local,
                full_place,
                Some(*expected_variant),
            )
        }
        ProjectionElem::Field(idx, expected_ty) => {
            let Some(field_tys) = projectable_field_tys(declared_ty, active_downcast) else {
                return Err(RvalueEvalError::TypeMismatch(
                    "Field projection requires a tuple-typed place (or a struct/union, or a downcast enum)",
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
            if is_union {
                return Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY));
            }
            if matches!(slot, FieldSlot::Uninit) {
                let shell = match declared_ty {
                    Ty::Adt(def) => {
                        PartialAggregate::new_uninit_adt(def, active_downcast.unwrap_or(0))
                            .ok_or(RvalueEvalError::TypeMismatch(
                                "ADT shell variant out of range",
                            ))?
                    }
                    _ => PartialAggregate::new_uninit(
                        field_tys.len(),
                        active_downcast.unwrap_or(0),
                        active_downcast.is_some(),
                    ),
                };
                *slot = FieldSlot::Partial(shell);
            }
            let FieldSlot::Partial(shell) = &mut *slot else {
                unreachable!()
            };
            if !shell_matches_declared_ty(shell, declared_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "partial shell does not match declared type",
                ));
            }
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
            write_partial_shell_in_slot(
                child_slot,
                &field_tys[*idx],
                rest,
                new_shell,
                src_local,
                full_place,
                None,
            )?;
            normalize_slot(child_slot);
            if active_downcast.is_some()
                && !matches!(child_slot, FieldSlot::Init(_))
                && !shell
                    .adt_def
                    .as_ref()
                    .is_some_and(|def| def.tag_survives_field_deinit())
            {
                shell.discriminant_set = false;
            }
            normalize_slot(slot);
            Ok(())
        }
        ProjectionElem::Index(_)
        | ProjectionElem::ConstantIndex { .. }
        | ProjectionElem::Subslice { .. } => Err(RvalueEvalError::UninitializedLocal(src_local)),
    }
}

/// Evaluates `copy_nonoverlapping::<elem_ty>(src, dst, count)` in `state`.
///
/// Operands are evaluated left to right; both addresses and the count must fit the target's
/// pointer width (an out-of-width value is `InvalidBitPattern`, never truncated). Then, even
/// when the byte length is zero, both pointers must be non-null (`NullPointerAccess`) and
/// aligned to `elem_align` (`MisalignedPointer`), `count * elem_size` must not exceed
/// `isize::MAX` (`CopyLengthOverflow`), and neither range may wrap the address space
/// (`PointerRangeOverflow`). A zero-length copy is then a no-op. A non-empty copy between
/// pointers of the same allocation (same provenance `alloc_id`, or both without provenance)
/// must not overlap (`CopyNonOverlappingOverlap`), and a non-empty or `count == 1` copy must
/// not touch a storage-dead local (`DeadLocal`). After all of these checks:
/// - `count == 1` between resolved synthetic sub-places copies the source sub-place's state
///   (`Uninit`, `PartialShell`, or `Init`) into the destination sub-place (a whole inactive
///   union field destination is overwritten, switching the union's active field);
/// - `count >= 1` between resolved contiguous array element windows copies the `count`
///   elements from the source slice into the destination slice; an uninitialized source
///   window leaves an uninitialized destination array unchanged and deinitializes a wholly
///   overwritten one;
/// - a non-`Init` state that the value tree cannot hold in the destination fails closed in an
///   array element (`UninitializedLocal`, `c6d2ad74`) and is `UnsupportedMemoryAccess` in a
///   union field;
/// - a zero-byte copy with `count > 1` copies the state between resolved sub-places and is
///   otherwise a no-op (it accesses no memory, not even of storage-dead locals);
/// - any other memory access is `UnsupportedMemoryAccess`.
#[allow(clippy::too_many_arguments)]
fn eval_copy_nonoverlapping(
    state: &mut StatementEvalState,
    src: &Operand,
    dst: &Operand,
    count: &Operand,
    elem_ty: &Ty,
    elem_size: usize,
    elem_align: usize,
) -> Result<(), RvalueEvalError> {
    let mut eval_op = |op: &Operand| -> Result<MirValue, RvalueEvalError> {
        match op {
            Operand::Copy(place) => state.read_place(place),
            Operand::Move(place) => state.move_place(place),
            Operand::Constant(c) => eval_constant(c, state.ptr_width),
        }
    };
    let src_val = eval_op(src)?;
    let dst_val = eval_op(dst)?;
    let count_val = eval_op(count)?;
    let ptr_width = state.ptr_width;
    let Ok(layout) = elem_ty.layout_for(ptr_width) else {
        return Err(RvalueEvalError::TypeMismatch(
            "copy_nonoverlapping element type must have an exact layout",
        ));
    };
    if layout.size != elem_size || layout.align != elem_align {
        return Err(RvalueEvalError::TypeMismatch(
            "copy_nonoverlapping lowered layout does not match element type layout",
        ));
    }
    let pointer =
        |val: &MirValue, need_mut: bool| -> Result<(PointerValue, u128), RvalueEvalError> {
            match val {
                MirValue::Ptr {
                    ptr,
                    ty: ptr_ty @ (Ty::RawPtr(pointee, m) | Ty::Ref(pointee, m)),
                } if **pointee == *elem_ty && (!need_mut || *m == Mutability::Mut) => {
                    Ok((*ptr, checked_ptr_addr(ptr, ptr_ty, ptr_width)?))
                }
                _ => Err(RvalueEvalError::TypeMismatch(
                    "copy_nonoverlapping pointers must point to the copied element type",
                )),
            }
        };
    let (src_ptr, src_addr) = pointer(&src_val, false)?;
    let (dst_ptr, dst_addr) = pointer(&dst_val, true)?;
    let MirValue::Int {
        bits: count,
        ty: Ty::Uint(UintTy::Usize),
    } = count_val
    else {
        return Err(RvalueEvalError::TypeMismatch(
            "copy_nonoverlapping count must be a usize",
        ));
    };
    // An out-of-width count is an ill-formed value, never truncated to a valid one.
    if count > ptr_width.max_usize() {
        return Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: Ty::Uint(UintTy::Usize),
                bits: count,
            },
        ));
    }
    if src_addr == 0 || dst_addr == 0 {
        return Err(RvalueEvalError::NullPointerAccess);
    }
    for addr in [src_addr, dst_addr] {
        if !addr.is_multiple_of(elem_align as u128) {
            return Err(RvalueEvalError::MisalignedPointer {
                addr: addr as u64,
                required_align: elem_align,
            });
        }
    }
    let byte_len = count
        .checked_mul(elem_size as u128)
        .filter(|len| *len <= ptr_width.max_object_size())
        .ok_or(RvalueEvalError::CopyLengthOverflow { count, elem_size })?;
    for addr in [src_addr, dst_addr] {
        if addr + byte_len > ptr_width.max_usize() {
            return Err(RvalueEvalError::PointerRangeOverflow {
                addr: addr as u64,
                byte_len,
            });
        }
    }
    if count == 0 {
        return Ok(());
    }
    let same_allocation =
        src_ptr.provenance.map(|p| p.alloc_id) == dst_ptr.provenance.map(|p| p.alloc_id);
    if byte_len > 0 && same_allocation && src_addr < dst_addr + byte_len && dst_addr < src_addr + byte_len {
        return Err(RvalueEvalError::CopyNonOverlappingOverlap {
            src_addr: src_addr as u64,
            dst_addr: dst_addr as u64,
            byte_len,
        });
    }
    let local_count = state.slots.len().min(state.local_decls.len());
    for ptr in [&src_ptr, &dst_ptr] {
        if let Some(prov) = ptr.provenance
            && let Some(idx) = prov.alloc_id.checked_sub(1).and_then(|i| usize::try_from(i).ok())
            && idx < local_count
            && (byte_len > 0 || count == 1)
            && matches!(state.slots[idx], LocalSlotState::Dead)
        {
            return Err(RvalueEvalError::DeadLocal(Local(idx)));
        }
    }
    let dummy_place = Place::from_local(0);
    let src_ptr_ty = src_val.ty();
    let dst_ptr_ty = dst_val.ty();
    let src_resolved =
        state.resolve_synthetic_subplace(&src_ptr, &src_ptr_ty, elem_ty, &dummy_place);
    let dst_resolved = state.resolve_synthetic_subplace_with_mode(
        &dst_ptr,
        &dst_ptr_ty,
        elem_ty,
        &dummy_place,
        true,
    );

    if count == 1 {
        match (src_resolved, dst_resolved) {
            (Ok((src_local, src_proj)), Ok((dst_local, dst_proj))) => {
                if byte_len == 0 && src_local == dst_local && src_proj == dst_proj {
                    let _ = state.read_subplace_slot(src_local, &src_proj, &dummy_place)?;
                    return Ok(());
                }
                let src_slot = state.read_subplace_slot(src_local, &src_proj, &dummy_place)?;
                // Strip any trailing 1-element array indices (`[T; 1]` is covered as a whole by
                // `count == 1`); if a multi-element array step remains inside an inactive union
                // field, a 1-element write is a partial union-field write (unsupported).
                let mut whole_dst_proj = dst_proj.as_slice();
                while let Some((
                    ProjectionElem::ConstantIndex {
                        offset: 0,
                        min_length: 1,
                        from_end: false,
                    },
                    prefix,
                )) = whole_dst_proj.split_last()
                {
                    whole_dst_proj = prefix;
                }
                if !slot_union_path_active(&state.slots[dst_local.0], whole_dst_proj, false)
                    && matches!(
                        whole_dst_proj.last(),
                        Some(ProjectionElem::ConstantIndex { .. })
                    )
                {
                    return Err(RvalueEvalError::UnsupportedMemoryAccess(
                        "copy_nonoverlapping outside of whole-local copies",
                    ));
                }
                return state.write_subplace_slot(
                    dst_local,
                    &dst_proj,
                    elem_ty,
                    src_slot,
                    src_local,
                    &dummy_place,
                );
            }
            _ if byte_len == 0
                && resolve_synthetic_alloc_local(&src_ptr, local_count).is_none()
                && resolve_synthetic_alloc_local(&dst_ptr, local_count).is_none() =>
            {
                return Ok(());
            }
            (Err(err), _)
                if !matches!(err, RvalueEvalError::UnsupportedPlaceProjection(_)) =>
            {
                return Err(err);
            }
            (_, Err(err))
                if !matches!(err, RvalueEvalError::UnsupportedPlaceProjection(_)) =>
            {
                return Err(err);
            }
            _ => {
                return Err(RvalueEvalError::UnsupportedMemoryAccess(
                    "copy_nonoverlapping outside of whole-local copies",
                ));
            }
        }
    }

    // `count > 1`: contiguous array-element window copy. As for `count == 1`, a resolution
    // fault other than an unresolvable place is reported as is, except for zero-sized elements:
    // a zero-byte copy accesses no memory (no storage-dead check above), so it never faults.
    for resolved in [&src_resolved, &dst_resolved] {
        if byte_len > 0
            && let Err(err) = resolved
            && !matches!(err, RvalueEvalError::UnsupportedPlaceProjection(_))
        {
            return Err(err.clone());
        }
    }
    if let (
        Ok((src_local, src_elem_proj)),
        Ok((dst_local, dst_elem_proj)),
        Ok(count_u64),
        Ok(count_usize),
    ) = (
        src_resolved.as_ref(),
        dst_resolved.as_ref(),
        u64::try_from(count),
        usize::try_from(count),
    )
        && let Some((
            ProjectionElem::ConstantIndex {
                offset: src_start,
                min_length: src_len,
                from_end: false,
            },
            src_arr_proj,
        )) = src_elem_proj.split_last()
        && let Some((
            ProjectionElem::ConstantIndex {
                offset: dst_start,
                min_length: dst_len,
                from_end: false,
            },
            dst_arr_proj,
        )) = dst_elem_proj.split_last()
        && let Some(src_end) = src_start.checked_add(count_u64)
        && src_end <= *src_len
        && let Some(dst_end) = dst_start.checked_add(count_u64)
        && dst_end <= *dst_len
        && let Ok(dst_len_usize) = usize::try_from(*dst_len)
    {
        let src_local = *src_local;
        let dst_local = *dst_local;
        // Overwriting only part of an inactive union array field is unsupported without a byte
        // memory model; overwriting the entire union array field (`0..dst_len_usize`) switches
        // the union's active field.
        if (*dst_start != 0 || count_usize != dst_len_usize)
            && !slot_union_path_active(&state.slots[dst_local.0], dst_arr_proj, false)
        {
            return Err(RvalueEvalError::UnsupportedMemoryAccess(
                "copy_nonoverlapping outside of whole-local copies",
            ));
        }
        let mut src_slice_proj = src_arr_proj.to_vec();
        src_slice_proj.push(ProjectionElem::Subslice {
            from: *src_start,
            to: src_end,
            from_end: false,
        });
        let src_slice_place = Place {
            local: src_local,
            projection: src_slice_proj,
        };
        let slice_val = match state.read_place(&src_slice_place) {
            Ok(val) => val,
            // Arrays have no per-element state, so an uninitialized source window means the
            // whole source array is uninitialized. Copying uninitialized bytes over an
            // uninitialized destination array changes nothing, and over a whole destination
            // array deinitializes it; a partially overwritten initialized array would hold
            // uninitialized elements, which fails closed (`c6d2ad74`).
            Err(RvalueEvalError::UninitializedLocal(_))
                if matches!(
                    state.read_subplace_slot(src_local, src_arr_proj, &dummy_place),
                    Ok(FieldSlot::Uninit)
                ) =>
            {
                if matches!(
                    state.read_subplace_slot(dst_local, dst_arr_proj, &dummy_place),
                    Ok(FieldSlot::Uninit)
                ) {
                    return Ok(());
                }
                if proj_traverses_union(&state.local_decls[dst_local.0], dst_arr_proj) {
                    return Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY));
                }
                if *dst_start == 0 && count_usize == dst_len_usize {
                    let arr_ty = Ty::Array(Box::new(elem_ty.clone()), dst_len_usize);
                    return state.write_subplace_slot(
                        dst_local,
                        dst_arr_proj,
                        &arr_ty,
                        FieldSlot::Uninit,
                        src_local,
                        &dummy_place,
                    );
                }
                return Err(RvalueEvalError::UninitializedLocal(src_local));
            }
            Err(err) => return Err(err),
        };
        if *dst_start == 0 && count_usize == dst_len_usize {
            let arr_ty = Ty::Array(Box::new(elem_ty.clone()), dst_len_usize);
            return state.write_subplace_slot(
                dst_local,
                dst_arr_proj,
                &arr_ty,
                FieldSlot::Init(slice_val),
                src_local,
                &dummy_place,
            );
        }
        let mut dst_slice_proj = dst_arr_proj.to_vec();
        dst_slice_proj.push(ProjectionElem::Subslice {
            from: *dst_start,
            to: dst_end,
            from_end: false,
        });
        let dst_slice_place = Place {
            local: dst_local,
            projection: dst_slice_proj,
        };
        let slice_ty = Ty::Array(Box::new(elem_ty.clone()), count_usize);
        return state.write_place(&dst_slice_place, &slice_ty, slice_val);
    }

    if byte_len == 0 {
        // Zero-sized elements, `count > 1` (no bytes accessed): resolved sub-places copy the
        // source's initialization state as for `count == 1`; any other pair of (non-null,
        // aligned) pointers, even into storage-dead locals, is a no-op.
        if let (Ok((src_local, src_proj)), Ok((dst_local, dst_proj))) = (src_resolved, dst_resolved)
        {
            if src_local == dst_local && src_proj == dst_proj {
                let _ = state.read_subplace_slot(src_local, &src_proj, &dummy_place)?;
                return Ok(());
            }
            let src_slot = state.read_subplace_slot(src_local, &src_proj, &dummy_place)?;
            return state.write_subplace_slot(
                dst_local,
                &dst_proj,
                elem_ty,
                src_slot,
                src_local,
                &dummy_place,
            );
        }
        return Ok(());
    }
    Err(RvalueEvalError::UnsupportedMemoryAccess(
        "copy_nonoverlapping outside of whole-local copies",
    ))
}

/// Updates the discriminant of a target `FieldSlot` at `proj` for `Statement::SetDiscriminant`.
///
/// On a typed enum (`Ty::Adt`), `SetDiscriminant(v)` writes the tag: an uninitialized enum
/// becomes a shell of variant `v` with its tag written (MiniRust writes the tag bytes only),
/// a same-variant value is unchanged, and a value of another variant becomes a shell of `v`
/// whose fields are uninitialized (the old variant's fields do not initialize `v`'s). Typed
/// struct/union containers along `proj` materialize shells as needed. Legacy tuple-modeled
/// places keep the conservative rule that an uninitialized place cannot be re-tagged.
#[allow(clippy::too_many_arguments, clippy::only_used_in_recursion)]
fn set_discriminant_in_slot(
    slot: &mut FieldSlot,
    declared_ty: &Ty,
    proj: &[ProjectionElem],
    variant_index: usize,
    read_index: &impl Fn(Local) -> Result<u128, RvalueEvalError>,
    ptr_width: PtrWidth,
    base_local: Local,
    full_place: &Place,
    active_downcast: Option<usize>,
) -> Result<(), RvalueEvalError> {
    if let FieldSlot::Init(existing_val) = slot {
        if !mir_value_head_matches_ty(existing_val, declared_ty) {
            return Err(RvalueEvalError::TypeMismatch(
                "initialized slot runtime value does not match declared type",
            ));
        }
        let demote = if proj.is_empty() {
            if let (Ty::Adt(def), None) = (declared_ty, active_downcast) {
                let MirValue::Adt { variant_idx, .. } = &*existing_val else {
                    unreachable!("head match guarantees an ADT value")
                };
                if *variant_idx == variant_index {
                    return Ok(());
                }
                if !def.is_enum() {
                    return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()));
                }
                *slot = tagged_variant_slot(def, variant_index)?;
                return Ok(());
            }
            false
        } else {
            typed_variant_switch_target(
                existing_val,
                declared_ty,
                proj,
                variant_index,
                read_index,
                full_place,
                active_downcast,
            )
        };
        if !demote {
            return set_discriminant_projected_mir_value(
                existing_val,
                declared_ty,
                proj,
                variant_index,
                read_index,
                full_place,
                active_downcast,
            );
        }
        explode_init_slot(slot, full_place)?;
    }
    if proj.is_empty() {
        if active_downcast.is_some() {
            return Err(RvalueEvalError::TypeMismatch(
                "SetDiscriminant target cannot end with Downcast",
            ));
        }
        if !matches!(declared_ty, Ty::Tuple(_) | Ty::Adt(_)) {
            return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()));
        }
        if matches!(slot, FieldSlot::Uninit) {
            let Ty::Adt(def) = declared_ty else {
                return Err(RvalueEvalError::UninitializedLocal(base_local));
            };
            if def.is_enum() {
                *slot = tagged_variant_slot(def, variant_index)?;
            } else if variant_index != 0 {
                return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()));
            }
            return Ok(());
        }
        let FieldSlot::Partial(shell) = &mut *slot else {
            unreachable!()
        };
        if !shell_matches_declared_ty(shell, declared_ty) {
            return Err(RvalueEvalError::TypeMismatch(
                "partial shell does not match declared type",
            ));
        }
        if shell.adt_def.as_ref().is_some_and(|def| !def.is_enum()) {
            // Structs (and their shells) have only variant 0 and no tag.
            return if variant_index == 0 {
                Ok(())
            } else {
                Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()))
            };
        }
        if let Some(def) = &shell.adt_def
            && def.variant_fields(variant_index).is_none()
        {
            return Err(RvalueEvalError::TypeMismatch(
                "SetDiscriminant variant index out of range",
            ));
        }
        // If `SetDiscriminant` switches the shell to a different variant than the one
        // whose fields were partially written via `Downcast(v)` (or tuple `Field` writes
        // on variant 0), those written fields belong to the old variant and do not
        // initialize the new variant's fields.
        if shell.variant_idx != variant_index {
            if let Some(def) = &shell.adt_def {
                let field_count = def.variant_fields(variant_index).map_or(0, <[Ty]>::len);
                shell.fields = vec![FieldSlot::Uninit; field_count];
            } else {
                shell.fields.fill(FieldSlot::Uninit);
            }
        }
        shell.variant_idx = variant_index;
        shell.is_adt = true;
        shell.discriminant_set = true;
        normalize_slot(slot);
        Ok(())
    } else {
        let (first, rest) = proj.split_first().unwrap();
        if matches!(slot, FieldSlot::Uninit) {
            // A typed struct or enum container materializes an (empty) shell for the step,
            // which `normalize_slot` collapses again if nothing below gets initialized.
            let fresh_shell = match (declared_ty, first) {
                (Ty::Adt(def), ProjectionElem::Downcast(v))
                    if active_downcast.is_none() && downcast_allowed(declared_ty, *v) =>
                {
                    PartialAggregate::new_uninit_adt(def, *v)
                }
                (Ty::Adt(def), ProjectionElem::Field(..)) if !def.is_union() => {
                    PartialAggregate::new_uninit_adt(def, active_downcast.unwrap_or(0))
                }
                _ => None,
            };
            match fresh_shell {
                Some(shell) => *slot = FieldSlot::Partial(shell),
                None => {
                    let leaf_ty =
                        validate_projection_tail::<fn(Local) -> Result<u128, RvalueEvalError>>(
                            declared_ty,
                            proj,
                            None,
                            None,
                            full_place,
                            active_downcast,
                        )?;
                    if !matches!(leaf_ty, Ty::Tuple(_) | Ty::Adt(_)) {
                        return Err(RvalueEvalError::InvalidSetDiscriminant(full_place.clone()));
                    }
                    if matches!(declared_ty, Ty::Adt(def) if def.is_union()) {
                        // A re-tag inside an uninitialized union field writes part of the
                        // union's overlapping storage.
                        return Err(RvalueEvalError::UnsupportedPlaceProjection(
                            full_place.clone(),
                        ));
                    }
                    return Err(RvalueEvalError::UninitializedLocal(base_local));
                }
            }
        }
        let res = (|| match first {
            ProjectionElem::Deref => Err(RvalueEvalError::UnsupportedPlaceProjection(
                full_place.clone(),
            )),
            ProjectionElem::Downcast(expected_variant) => {
                if active_downcast.is_some() {
                    return Err(RvalueEvalError::TypeMismatch(
                        "consecutive Downcast projections",
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
                if !downcast_allowed(declared_ty, *expected_variant) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Downcast projection requires a tuple-typed (ADT) place or an in-range enum variant",
                    ));
                }
                let FieldSlot::Partial(shell) = &*slot else {
                    unreachable!()
                };
                if !shell_matches_declared_ty(shell, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "partial shell does not match declared type",
                    ));
                }
                let actual = if shell.is_adt { shell.variant_idx } else { 0 };
                if actual != *expected_variant {
                    return Err(RvalueEvalError::InactiveVariantProjection {
                        expected: *expected_variant,
                        actual,
                    });
                }
                set_discriminant_in_slot(
                    slot,
                    declared_ty,
                    rest,
                    variant_index,
                    read_index,
                    ptr_width,
                    base_local,
                    full_place,
                    Some(*expected_variant),
                )
            }
            ProjectionElem::Field(idx, expected_ty) => {
                let Some(field_tys) = projectable_field_tys(declared_ty, active_downcast) else {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Field projection requires a tuple-typed place (or a struct/union, or a downcast enum)",
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
                let FieldSlot::Partial(shell) = &mut *slot else {
                    unreachable!()
                };
                if !shell_matches_declared_ty(shell, declared_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "partial shell does not match declared type",
                    ));
                }
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
                    &field_tys[*idx],
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
            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. } => Err(RvalueEvalError::TypeMismatch(
                "array projection applied to a partially initialized tuple/ADT shell",
            )),
        })();
        normalize_slot(slot);
        res
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
        LoweredRvalue::Use { operand, ty } => {
            let v = eval_op(operand, state)?;
            if !mir_value_matches_ty(&v, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Use operand runtime type does not match lowered type",
                ));
            }
            Ok(v)
        }
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
            place,
            mutability,
            ty: ref_ty,
        }
        | LoweredRvalue::RawPtr {
            place,
            mutability,
            ty: ref_ty,
        } => {
            let expected_ref = matches!(rvalue, LoweredRvalue::Ref { .. });
            let pointee_ty = match ref_ty {
                Ty::Ref(pointee, m) if expected_ref && m == mutability => pointee.as_ref(),
                Ty::RawPtr(pointee, m) if !expected_ref && m == mutability => pointee.as_ref(),
                _ => {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Ref/RawPtr lowered ty does not match rvalue kind and mutability",
                    ));
                }
            };
            let ptr = match place.projection.as_slice() {
                [] => {
                    if state.local_decls.get(place.local.0) != Some(pointee_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Ref/RawPtr local declaration type does not match pointee type",
                        ));
                    }
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
                    let addr = state.local_base_addr(place.local.0)?;
                    PointerValue::with_provenance(addr as u64, place.local.0 as u64 + 1, 1)
                }
                [ProjectionElem::Deref] => match state.read_place(&Place::from_local(place.local.0))? {
                    MirValue::Ptr { ptr, ty } => {
                        if !ty.is_any_ptr() || ty.pointee_ty() != Some(pointee_ty) {
                            return Err(RvalueEvalError::TypeMismatch(
                                "Deref projection requires a pointer value with matching pointee type",
                            ));
                        }
                        let masked_addr =
                            checked_ptr_addr(&ptr, &ty, state.ptr_width)? as u64;
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
                _ => eval_projected_ref_in(state, place, pointee_ty, expected_ref)?,
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
            if *ty != Ty::Uint(UintTy::Usize)
                || (*static_len as u128) > state.ptr_width.max_usize()
            {
                return Err(RvalueEvalError::TypeMismatch(
                    "Len result type must be a representable usize",
                ));
            }
            let len = state.read_place_array_len(place, *static_len)?;
            if len != *static_len {
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
        LoweredRvalue::Cast { cast, ty } => {
            let op = cast.operand();
            let v = eval_op(op, state)?;
            let out = eval_lowered_cast_with_decls(
                cast,
                &v,
                &state.local_decls,
                Some(&state.slots),
                state.ptr_width,
                state.policy,
                &mut state.tracker,
            )?;
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "Cast result runtime type does not match lowered ty",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::BinaryOp {
            op,
            lhs,
            rhs,
            lhs_ty,
            rhs_ty,
            ty,
            ..
        } => {
            let lv = eval_op(lhs, state)?;
            let rv = eval_op(rhs, state)?;
            if !mir_value_matches_ty(&lv, lhs_ty) || !mir_value_matches_ty(&rv, rhs_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "BinaryOp operand runtime types do not match lowered types",
                ));
            }
            let out = eval_binop(*op, &lv, &rv, state.ptr_width)?;
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "BinaryOp result runtime type does not match lowered type",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::CheckedBinaryOp {
            op,
            lhs,
            rhs,
            lhs_ty,
            rhs_ty,
            ty,
        } => {
            let lv = eval_op(lhs, state)?;
            let rv = eval_op(rhs, state)?;
            if !mir_value_matches_ty(&lv, lhs_ty) || !mir_value_matches_ty(&rv, rhs_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "CheckedBinaryOp operand runtime types do not match lowered types",
                ));
            }
            let (wrapped, overflowed) = eval_checked_binop(*op, &lv, &rv, state.ptr_width)?;
            let out = MirValue::Tuple(vec![
                MirValue::Int {
                    bits: wrapped,
                    ty: lhs_ty.clone(),
                },
                MirValue::Bool(overflowed),
            ]);
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "CheckedBinaryOp result runtime type does not match lowered type",
                ));
            }
            Ok(out)
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
        LoweredRvalue::UnaryOp {
            op,
            operand,
            operand_ty,
            ty,
        } => {
            let v = eval_op(operand, state)?;
            if !mir_value_matches_ty(&v, operand_ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "UnaryOp operand runtime type does not match lowered type",
                ));
            }
            let out = eval_unop(*op, &v, state.ptr_width)?;
            if !mir_value_matches_ty(&out, ty) {
                return Err(RvalueEvalError::TypeMismatch(
                    "UnaryOp result runtime type does not match lowered type",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::Discriminant {
            place,
            place_ty,
            ty,
        } => {
            if *ty != discriminant_result_ty(place_ty)
                || !place_ty.is_inhabited_for(state.ptr_width)
            {
                return Err(RvalueEvalError::TypeMismatch(
                    "Discriminant requires an inhabited place_ty and its discriminant result ty",
                ));
            }
            if let Ty::Adt(def) = place_ty {
                // `Rvalue::Discriminant` on a typed ADT reads only the tag (Miri's
                // `read_discriminant`): layouts without a tag (structs, unions, and
                // `AdtDef::univariant_index` enums) need no initialized tag when the place is
                // uninitialized, while an initialized or partially initialized ADT still validates
                // its runtime variant index.
                let (target_local, target_proj, index_cache) =
                    state.prepare_place_access(place, place_ty)?;
                let variant_idx = match state.typed_enum_variant(
                    target_local,
                    &target_proj,
                    place,
                    place_ty,
                    &index_cache,
                ) {
                    Ok(v) => v,
                    Err(RvalueEvalError::UninitializedLocal(_)) if !def.requires_tag_write() => {
                        def.univariant_index().unwrap_or(0)
                    }
                    Err(err) => return Err(err),
                };
                return discriminant_value(def, variant_idx, state.ptr_width);
            }
            let decl_place_ty = state.check_place_against_decls(place)?;
            if decl_place_ty != *place_ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "Discriminant lowered place_ty does not match declared place type",
                ));
            }
            let discr = match state.read_place(place) {
                Ok(val) => {
                    if !mir_value_matches_ty(&val, place_ty) {
                        return Err(RvalueEvalError::TypeMismatch(
                            "Discriminant place runtime value does not match lowered place_ty",
                        ));
                    }
                    match val {
                        MirValue::Adt {
                            variant_idx,
                            active_field: None,
                            ..
                        } => variant_idx as i128,
                        _ => 0,
                    }
                }
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
        LoweredRvalue::Aggregate {
            kind,
            operands,
            operand_tys,
            ty,
        } => {
            if operands.len() != operand_tys.len() {
                return Err(RvalueEvalError::TypeMismatch(
                    "Aggregate operands length does not match lowered operand_tys",
                ));
            }
            let mut vals = Vec::with_capacity(operands.len());
            for (op, op_ty) in operands.iter().zip(operand_tys) {
                let v = eval_op(op, state)?;
                if !mir_value_matches_ty(&v, op_ty) {
                    return Err(RvalueEvalError::TypeMismatch(
                        "Aggregate operand runtime type does not match lowered operand_ty",
                    ));
                }
                vals.push(v);
            }
            let out = eval_aggregate(kind, vals, state.ptr_width)?;
            let ty_ok = match kind {
                AggregateKind::Adt {
                    active_field: Some(_),
                    ..
                } => *ty == Ty::Tuple(operand_tys.clone()) || mir_value_matches_ty(&out, ty),
                _ => mir_value_matches_ty(&out, ty),
            };
            if !ty_ok {
                return Err(RvalueEvalError::TypeMismatch(
                    "Aggregate result runtime type does not match lowered ty",
                ));
            }
            Ok(out)
        }
        LoweredRvalue::CopyForDeref { place, ty } => match state.read_place(place)? {
            MirValue::Ptr { ptr, ty: val_ty } if val_ty == *ty && ty.is_any_ptr() => {
                let masked_addr = checked_ptr_addr(&ptr, ty, state.ptr_width)? as u64;
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
        LoweredRvalue::ShallowInitBox {
            operand,
            operand_ty,
            ty,
        } => {
            let v = eval_op(operand, state)?;
            eval_shallow_init_box(&v, operand_ty, ty, state.ptr_width)
        }
        LoweredRvalue::WrapUnsafeBinder {
            operand,
            operand_ty,
            ty,
        } => {
            let v = eval_op(operand, state)?;
            eval_wrap_unsafe_binder(v, operand_ty, ty, state.ptr_width)
        }
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
        LoweredStatement::PlaceMention { place, place_ty } => {
            match state.slots.get(place.local.0) {
                None => return Err(RvalueEvalError::TypeMismatch("local index out of bounds")),
                Some(LocalSlotState::Dead) => return Err(RvalueEvalError::DeadLocal(place.local)),
                Some(_) => {}
            }
            let resolved_ty = state.check_place_against_decls(place)?;
            if resolved_ty != *place_ty {
                return Err(RvalueEvalError::TypeMismatch(
                    "PlaceMention place_ty does not match declared place type",
                ));
            }
            // Validate every `Index(idx_local)` operand read while computing `place`.
            for elem in &place.projection {
                if let ProjectionElem::Index(idx_local) = elem {
                    let _ = state.read_index_local(*idx_local)?;
                }
            }
            // If `place.projection` contains `Deref`, the pointer sub-place before the last
            // `Deref` is read (recursively resolving any earlier `Deref`s) to compute the
            // dereferenced place's address without loading the mentioned target place (`D9`).
            if let Some(last_deref_pos) = place
                .projection
                .iter()
                .rposition(|p| matches!(p, ProjectionElem::Deref))
            {
                let ptr_place = Place {
                    local: place.local,
                    projection: place.projection[..last_deref_pos].to_vec(),
                };
                let ptr_val = state.read_place(&ptr_place)?;
                match ptr_val {
                    MirValue::Ptr { ptr, ty } if ty.is_any_ptr() => {
                        let masked_addr = checked_ptr_addr(&ptr, &ty, state.ptr_width)? as u64;
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
            place_ty,
            variant_index,
        } => {
            let (target_local, target_proj, index_cache) =
                state.prepare_place_access(place, place_ty)?;
            if !matches!(place_ty, Ty::Tuple(_) | Ty::Adt(_)) {
                return Err(RvalueEvalError::InvalidSetDiscriminant(place.clone()));
            }
            if let Ty::Adt(def) = place_ty {
                if !def.is_enum() {
                    if *variant_index != 0 {
                        return Err(RvalueEvalError::InvalidSetDiscriminant(place.clone()));
                    }
                } else {
                    let Some(fields) = def.variant_fields(*variant_index) else {
                        return Err(RvalueEvalError::TypeMismatch(
                            "SetDiscriminant variant index out of range",
                        ));
                    };
                    // Miri's `write_discriminant`: writing the tag of an uninhabited variant is UB.
                    if !fields.iter().all(|f| f.is_inhabited_for(state.ptr_width)) {
                        return Err(RvalueEvalError::UninhabitedEnumVariant {
                            variant_index: *variant_index,
                        });
                    }
                }
            }
            let base_decl_ty = state.local_decls[target_local.0].clone();
            let read_index = |idx_local: Local| cached_index(&index_cache, idx_local);
            let mut root_slot = take_root_slot(&mut state.slots[target_local.0]);
            let set_res = set_discriminant_in_slot(
                &mut root_slot,
                &base_decl_ty,
                &target_proj,
                *variant_index,
                &read_index,
                state.ptr_width,
                target_local,
                place,
                None,
            );
            normalize_slot(&mut root_slot);
            state.slots[target_local.0] = root_slot_state(root_slot);
            set_res
        }
        LoweredStatement::Assign {
            place,
            place_ty,
            rvalue,
        } => {
            let val = eval_lowered_rvalue_in_state(rvalue, state)?;
            state.write_place(place, place_ty, val)
        }
        LoweredStatement::Deinit { place, place_ty } => state.deinit_place(place, place_ty),
        LoweredStatement::Retag {
            kind,
            place,
            place_ty,
        } => state.retag_place(*kind, place, place_ty),
        LoweredStatement::CopyNonOverlapping {
            src,
            dst,
            count,
            elem_ty,
            elem_size,
            elem_align,
        } => eval_copy_nonoverlapping(state, src, dst, count, elem_ty, *elem_size, *elem_align),
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
            adt_def: None,
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
