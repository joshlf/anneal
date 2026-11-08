//! Lowering and evaluation for MIR casts, including:
//! 1. `rustc` MIR pointer-to-integer (`CastKind::PointerExposeProvenance`) and
//!    integer-to-pointer (`CastKind::PointerWithExposedProvenance`) casts;
//! 2. MiniRust `IntPtrCast` provenance-exposure semantics (`spec/mem/intptrcast.md`); and
//! 3. UCG `#286` / MiniRust same-size `CastKind::Transmute` semantics across 32-bit and
//!    64-bit target pointer widths (`PtrWidth::Bits32` and `PtrWidth::Bits64`), preserving
//!    provenance on `Ptr -> Ptr`, rejecting or stripping provenance on `Ptr -> Int` without
//!    exposing it, and enforcing bit-validity on niche-constrained types (`bool`, `char`, `&T`).

use std::collections::BTreeSet;

use crate::ir::{CastKind, Operand, PointerValue, Provenance, PtrWidth, ScalarTy, Ty};

/// Policy governing pointer-to-integer reinterpretation in `CastKind::Transmute`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum TransmutePolicy {
    /// Rejects `Ptr -> Int` transmutes (`RawPtr`/`Ref` to non-pointer scalars or aggregates),
    /// requiring callers to use `CastKind::PointerExposeProvenance` or explicitly opt into
    /// provenance stripping.
    #[default]
    RejectPtrToInt,
    /// Permits same-size `Ptr -> Int` transmutes while stripping pointer provenance
    /// (`exposes_provenance: false`) without adding it to `ExposedProvenanceTracker`.
    AllowPtrToIntStripProvenance,
}

/// Lowered transmute descriptor distinguishing scalar-to-scalar transmutes from
/// composite/aggregate byte transmutes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastOp {
    /// Scalar-to-scalar bit reinterpretation (`ScalarTy -> ScalarTy`).
    Transmute { src: ScalarTy, dst: ScalarTy },
    /// Same-size aggregate/composite byte reinterpretation (e.g. `[u8; 4] <-> u32`).
    AggregateTransmute { size_bytes: usize },
}

/// Errors encountered during MIR cast lowering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CastLowerError {
    /// Source type is invalid for the requested cast kind.
    InvalidSourceType {
        expected: &'static str,
        got: Ty,
    },
    /// Target type is invalid for the requested cast kind.
    InvalidTargetType {
        expected: &'static str,
        got: Ty,
    },
    /// Incompatible sizes or unsupported conversion.
    UnsupportedCast {
        kind: CastKind,
        src_ty: Ty,
        target_ty: Ty,
    },
    /// Source and target types have different byte sizes under the target pointer width.
    SizeMismatchTransmute {
        src_ty: Ty,
        target_ty: Ty,
        src_bytes: usize,
        target_bytes: usize,
    },
    /// Target type of a transmute is uninhabited (e.g. `!`, `(!, u32)`, `[!; 1]`).
    UninhabitedTarget {
        target_ty: Ty,
    },
    /// `Ptr -> Int` transmute rejected by `TransmutePolicy::RejectPtrToInt`.
    PtrToIntTransmuteDisallowed {
        src_ty: Ty,
        target_ty: Ty,
    },
}

impl std::fmt::Display for CastLowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CastLowerError::InvalidSourceType { expected, got } => {
                write!(f, "invalid cast source type: expected {expected}, got {got:?}")
            }
            CastLowerError::InvalidTargetType { expected, got } => {
                write!(f, "invalid cast target type: expected {expected}, got {got:?}")
            }
            CastLowerError::UnsupportedCast { kind, src_ty, target_ty } => {
                write!(f, "unsupported cast {kind:?} from {src_ty:?} to {target_ty:?}")
            }
            CastLowerError::SizeMismatchTransmute {
                src_ty,
                target_ty,
                src_bytes,
                target_bytes,
            } => {
                write!(
                    f,
                    "transmute size mismatch from {src_ty:?} ({src_bytes} bytes) to {target_ty:?} ({target_bytes} bytes)"
                )
            }
            CastLowerError::UninhabitedTarget { target_ty } => {
                write!(f, "cannot transmute to uninhabited target type {target_ty:?}")
            }
            CastLowerError::PtrToIntTransmuteDisallowed { src_ty, target_ty } => {
                write!(
                    f,
                    "pointer-to-integer transmute from {src_ty:?} to {target_ty:?} disallowed by policy"
                )
            }
        }
    }
}

impl std::error::Error for CastLowerError {}

/// Lowered representation of a MIR type cast.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweredCast {
    /// Pointer-to-integer cast (`CastKind::PointerExposeProvenance`).
    ///
    /// Evaluates the address of the pointer operand as an integer and exposes
    /// its provenance tag in the global exposed-provenance set.
    PtrToInt {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
        expose_provenance: bool,
    },
    /// Integer-to-pointer cast (`CastKind::PointerWithExposedProvenance`).
    ///
    /// Interprets an integer address as a pointer, non-deterministically
    /// reconstructing provenance from previously exposed tags (or wildcard/none).
    IntToPtr {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
        pick_exposed_provenance: bool,
    },
    /// Standard integer-to-integer conversion (`CastKind::IntToInt`).
    IntToInt {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
    },
    /// Raw pointer to raw pointer reinterpretation (`CastKind::PtrToPtr`).
    PtrToPtr {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
    },
    /// Same-size bitwise reinterpretation (`CastKind::Transmute`).
    ///
    /// Never exposes pointer provenance (`exposes_provenance == false`).
    Transmute {
        src_ty: Ty,
        target_ty: Ty,
        operand: Operand,
        op: CastOp,
        size_bytes: usize,
        exposes_provenance: bool,
    },
}

/// Lowers a pointer-to-integer cast (`Rvalue::Cast(PointerExposeProvenance)`).
///
/// Preconditions:
/// - `src_ty` must be a raw pointer (`*const T`, `*mut T`) or reference (`&T`, `&mut T`).
/// - `target_ty` must be an integer type (`usize`, `u64`, `isize`, `i64`, `u32`, etc.).
pub fn lower_ptr_to_int(
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
) -> Result<LoweredCast, CastLowerError> {
    if !src_ty.is_any_ptr() {
        return Err(CastLowerError::InvalidSourceType {
            expected: "raw pointer or reference",
            got: src_ty.clone(),
        });
    }
    if !target_ty.is_integral() {
        return Err(CastLowerError::InvalidTargetType {
            expected: "integral type",
            got: target_ty.clone(),
        });
    }

    Ok(LoweredCast::PtrToInt {
        src_ty: src_ty.clone(),
        target_ty: target_ty.clone(),
        operand: operand.clone(),
        expose_provenance: true,
    })
}

/// Lowers an integer-to-pointer cast (`Rvalue::Cast(PointerWithExposedProvenance)`).
///
/// Preconditions:
/// - `src_ty` must be an integer type (`usize`, `u64`, `isize`, etc.).
/// - `target_ty` must be a raw pointer (`*const T` or `*mut T`).
pub fn lower_int_to_ptr(
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
) -> Result<LoweredCast, CastLowerError> {
    if !src_ty.is_integral() {
        return Err(CastLowerError::InvalidSourceType {
            expected: "integral type",
            got: src_ty.clone(),
        });
    }
    if !target_ty.is_raw_ptr() {
        return Err(CastLowerError::InvalidTargetType {
            expected: "raw pointer",
            got: target_ty.clone(),
        });
    }

    Ok(LoweredCast::IntToPtr {
        src_ty: src_ty.clone(),
        target_ty: target_ty.clone(),
        operand: operand.clone(),
        pick_exposed_provenance: true,
    })
}

/// Lowers a `CastKind::Transmute` under an explicit `PtrWidth` and `TransmutePolicy`.
pub fn lower_transmute(
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredCast, CastLowerError> {
    if !target_ty.is_inhabited() {
        return Err(CastLowerError::UninhabitedTarget {
            target_ty: target_ty.clone(),
        });
    }
    if !src_ty.is_inhabited() {
        return Err(CastLowerError::InvalidSourceType {
            expected: "inhabited type",
            got: src_ty.clone(),
        });
    }

    let src_bytes = src_ty.byte_size_for(ptr_width);
    let target_bytes = target_ty.byte_size_for(ptr_width);
    if src_bytes != target_bytes {
        return Err(CastLowerError::SizeMismatchTransmute {
            src_ty: src_ty.clone(),
            target_ty: target_ty.clone(),
            src_bytes,
            target_bytes,
        });
    }

    // Check Ptr -> Int policy: if source contains a pointer and target does not preserve it as a pointer,
    // RejectPtrToInt forbids the transmute.
    if src_ty.contains_ptr() && !target_ty.is_any_ptr() && policy == TransmutePolicy::RejectPtrToInt
    {
        return Err(CastLowerError::PtrToIntTransmuteDisallowed {
            src_ty: src_ty.clone(),
            target_ty: target_ty.clone(),
        });
    }

    let op = match (src_ty.to_scalar_ty(), target_ty.to_scalar_ty()) {
        (Some(src), Some(dst)) => CastOp::Transmute { src, dst },
        _ => CastOp::AggregateTransmute {
            size_bytes: src_bytes,
        },
    };

    Ok(LoweredCast::Transmute {
        src_ty: src_ty.clone(),
        target_ty: target_ty.clone(),
        operand: operand.clone(),
        op,
        size_bytes: src_bytes,
        exposes_provenance: false,
    })
}

/// Lowers any supported MIR cast rvalue under an explicit `PtrWidth` and `TransmutePolicy`.
pub fn lower_cast_rvalue_with_ptr_width(
    kind: CastKind,
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
) -> Result<LoweredCast, CastLowerError> {
    match kind {
        CastKind::PointerExposeProvenance => lower_ptr_to_int(operand, src_ty, target_ty),
        CastKind::PointerWithExposedProvenance => lower_int_to_ptr(operand, src_ty, target_ty),
        CastKind::IntToInt => {
            let valid_src = src_ty.is_integral() || matches!(src_ty, Ty::Bool | Ty::Char);
            let valid_dst = target_ty.is_integral() || matches!(target_ty, Ty::Char);
            if !valid_src {
                return Err(CastLowerError::InvalidSourceType {
                    expected: "integral, bool, or char type",
                    got: src_ty.clone(),
                });
            }
            if !valid_dst {
                return Err(CastLowerError::InvalidTargetType {
                    expected: "integral or char type",
                    got: target_ty.clone(),
                });
            }
            // Note: rustc only permits `u8 as char` for char target in IntToInt.
            if *target_ty == Ty::Char && *src_ty != Ty::Uint(crate::ir::UintTy::U8) {
                return Err(CastLowerError::UnsupportedCast {
                    kind,
                    src_ty: src_ty.clone(),
                    target_ty: target_ty.clone(),
                });
            }
            Ok(LoweredCast::IntToInt {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: operand.clone(),
            })
        }
        CastKind::PtrToPtr => {
            if !src_ty.is_raw_ptr() {
                return Err(CastLowerError::InvalidSourceType {
                    expected: "raw pointer",
                    got: src_ty.clone(),
                });
            }
            if !target_ty.is_raw_ptr() {
                return Err(CastLowerError::InvalidTargetType {
                    expected: "raw pointer",
                    got: target_ty.clone(),
                });
            }
            Ok(LoweredCast::PtrToPtr {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: operand.clone(),
            })
        }
        CastKind::Transmute => lower_transmute(operand, src_ty, target_ty, ptr_width, policy),
    }
}

/// Lowers any supported MIR cast rvalue using the default 64-bit target pointer width
/// (`PtrWidth::Bits64`) and strict `TransmutePolicy::RejectPtrToInt`.
pub fn lower_cast_rvalue(
    kind: CastKind,
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
) -> Result<LoweredCast, CastLowerError> {
    lower_cast_rvalue_with_ptr_width(
        kind,
        operand,
        src_ty,
        target_ty,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
    )
}

/// Dynamic tracker for exposed pointer provenances, modeling MiniRust's `IntPtrCast`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExposedProvenanceTracker {
    pub exposed: BTreeSet<Provenance>,
}

impl ExposedProvenanceTracker {
    /// Creates a new empty provenance tracker.
    pub fn new() -> Self {
        Self { exposed: BTreeSet::new() }
    }

    /// Exposes a provenance tag, recording it as available for address-to-pointer casts.
    pub fn expose(&mut self, prov: Provenance) {
        self.exposed.insert(prov);
    }

    /// Returns true if the given provenance tag has been exposed.
    pub fn is_exposed(&self, prov: &Provenance) -> bool {
        self.exposed.contains(prov)
    }

    /// Count of exposed provenances.
    pub fn len(&self) -> usize {
        self.exposed.len()
    }

    /// Returns true if no provenance has been exposed.
    pub fn is_empty(&self) -> bool {
        self.exposed.is_empty()
    }
}

/// Errors during dynamic cast evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CastEvalError {
    /// Target integer type width cannot fit address bits without truncation.
    IntegerOverflow {
        addr: u64,
        target_bytes: usize,
    },
    /// Requested provenance is not in the set of exposed provenances.
    UnexposedProvenance(Provenance),
    /// Invalid types passed to evaluator.
    TypeMismatch(&'static str),
    /// Bit pattern violates the validity invariant (niche) of `target_ty`
    /// (e.g. `bool` not in `0..=1`, `char` surrogate or `> 0x10FFFF`, or null `&T`).
    InvalidBitPattern {
        target_ty: Ty,
        bits: u128,
    },
    /// Source and target byte sizes do not match under the target pointer width.
    SizeMismatch {
        src_bytes: usize,
        target_bytes: usize,
    },
    /// Target type is uninhabited (`!`, `(!, u32)`, `[!; 1]`).
    UninhabitedTarget {
        target_ty: Ty,
    },
    /// Pointer-to-integer transmute rejected by `TransmutePolicy::RejectPtrToInt`.
    PtrToIntDisallowed {
        src_ty: Ty,
        target_ty: Ty,
    },
}

impl std::fmt::Display for CastEvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CastEvalError::IntegerOverflow { addr, target_bytes } => {
                write!(f, "pointer address {addr:#x} overflows target width ({target_bytes} bytes)")
            }
            CastEvalError::UnexposedProvenance(p) => {
                write!(f, "provenance tag (alloc_id={}, tag={}) is not exposed", p.alloc_id, p.tag)
            }
            CastEvalError::TypeMismatch(msg) => write!(f, "type mismatch: {msg}"),
            CastEvalError::InvalidBitPattern { target_ty, bits } => {
                write!(f, "invalid bit pattern {bits:#x} for target type {target_ty:?}")
            }
            CastEvalError::SizeMismatch {
                src_bytes,
                target_bytes,
            } => {
                write!(f, "transmute size mismatch: {src_bytes} bytes vs {target_bytes} bytes")
            }
            CastEvalError::UninhabitedTarget { target_ty } => {
                write!(f, "cannot evaluate transmute to uninhabited target type {target_ty:?}")
            }
            CastEvalError::PtrToIntDisallowed { src_ty, target_ty } => {
                write!(
                    f,
                    "pointer-to-integer transmute from {src_ty:?} to {target_ty:?} disallowed by policy"
                )
            }
        }
    }
}

impl std::error::Error for CastEvalError {}

/// Runtime value representation for `CastKind::Transmute` evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransmuteValue {
    /// Scalar bit pattern (`bool`, `char`, `Int`, `Uint`).
    Scalar(u128),
    /// Machine pointer with address and optional provenance (`RawPtr` or `Ref`).
    Ptr(PointerValue),
    /// Little-endian byte representation for aggregate values (`Array`, `Tuple`).
    Bytes(Vec<u8>),
}

/// Evaluates a lowered `PtrToInt` cast on a concrete pointer value under `ptr_width`.
pub fn eval_ptr_to_int_with_ptr_width(
    ptr: PointerValue,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<u128, CastEvalError> {
    if !target_ty.is_integral() {
        return Err(CastEvalError::TypeMismatch("target type must be integral"));
    }

    // Expose provenance if present.
    if let Some(prov) = ptr.provenance {
        tracker.expose(prov);
    }

    let target_bytes = target_ty.byte_size_for(ptr_width);
    let addr = (ptr.addr as u128) & ptr_width.mask();

    if target_bytes < 16 {
        let modulus = 1u128 << (target_bytes * 8);
        Ok(addr % modulus)
    } else {
        Ok(addr)
    }
}

/// Evaluates a lowered `PtrToInt` cast on a concrete pointer value (64-bit default).
///
/// Corresponds to MiniRust:
/// `IntPtrCast::expose` followed by converting the thin pointer address to integer.
pub fn eval_ptr_to_int(
    ptr: PointerValue,
    target_ty: &Ty,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<u128, CastEvalError> {
    eval_ptr_to_int_with_ptr_width(ptr, target_ty, PtrWidth::Bits64, tracker)
}

/// Evaluates a lowered `IntToPtr` cast from an address value to a pointer under `ptr_width`.
pub fn eval_int_to_ptr_with_ptr_width(
    addr: u128,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    tracker: &ExposedProvenanceTracker,
    predicted_prov: Option<Provenance>,
) -> Result<PointerValue, CastEvalError> {
    if !target_ty.is_raw_ptr() {
        return Err(CastEvalError::TypeMismatch("target type must be raw pointer"));
    }

    if let Some(prov) = predicted_prov {
        if !tracker.is_exposed(&prov) {
            return Err(CastEvalError::UnexposedProvenance(prov));
        }
    }

    let masked_addr = (addr & ptr_width.mask()) as u64;
    Ok(PointerValue {
        addr: masked_addr,
        provenance: predicted_prov,
    })
}

/// Evaluates a lowered `IntToPtr` cast from an address value to a pointer (64-bit default).
///
/// Corresponds to MiniRust:
/// `IntPtrCast::int2ptr` predicting either `None` (untagged/wildcard) or an already-exposed provenance.
pub fn eval_int_to_ptr(
    addr: u128,
    target_ty: &Ty,
    tracker: &ExposedProvenanceTracker,
    predicted_prov: Option<Provenance>,
) -> Result<PointerValue, CastEvalError> {
    eval_int_to_ptr_with_ptr_width(addr, target_ty, PtrWidth::Bits64, tracker, predicted_prov)
}

/// Evaluates a numeric `CastKind::IntToInt` conversion (including `bool`/`char` as integer).
pub fn eval_int_to_int(
    src_bits: u128,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<u128, CastEvalError> {
    let dst_mask = match target_ty {
        Ty::Int(it) => it.mask(ptr_width),
        Ty::Uint(ut) => ut.mask(ptr_width),
        Ty::Char => 0xFFFF_FFFF,
        _ => return Err(CastEvalError::TypeMismatch("IntToInt target must be Int, Uint, or Char")),
    };

    match src_ty {
        Ty::Int(src_it) => {
            let signed = src_it.sign_extend(src_bits, ptr_width);
            Ok((signed as u128) & dst_mask)
        }
        Ty::Uint(src_ut) => {
            let unsigned = src_bits & src_ut.mask(ptr_width);
            Ok(unsigned & dst_mask)
        }
        Ty::Bool => {
            if src_bits > 1 {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: Ty::Bool,
                    bits: src_bits,
                });
            }
            Ok(src_bits & dst_mask)
        }
        Ty::Char => {
            if !ScalarTy::Char.is_valid_bits(src_bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: Ty::Char,
                    bits: src_bits,
                });
            }
            Ok(src_bits & dst_mask)
        }
        _ => Err(CastEvalError::TypeMismatch(
            "IntToInt source must be Int, Uint, Bool, or Char",
        )),
    }
}

/// Validates that `bytes` (of length `ty.byte_size_for(ptr_width)`) form a bit-valid value for `ty`.
fn validate_aggregate_bytes(
    bytes: &[u8],
    ty: &Ty,
    ptr_width: PtrWidth,
) -> Result<(), CastEvalError> {
    if !ty.is_inhabited() {
        return Err(CastEvalError::UninhabitedTarget {
            target_ty: ty.clone(),
        });
    }
    let expected_len = ty.byte_size_for(ptr_width);
    if bytes.len() != expected_len {
        return Err(CastEvalError::SizeMismatch {
            src_bytes: bytes.len(),
            target_bytes: expected_len,
        });
    }
    match ty {
        Ty::Bool | Ty::Char | Ty::Int(_) | Ty::Uint(_) | Ty::RawPtr(_, _) | Ty::Ref(_, _) => {
            let mut bits = 0u128;
            for (i, &b) in bytes.iter().enumerate().take(16) {
                bits |= (b as u128) << (i * 8);
            }
            if !ty.is_valid_scalar_bits(bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: ty.clone(),
                    bits,
                });
            }
            Ok(())
        }
        Ty::Array(elem, count) => {
            let elem_sz = elem.byte_size_for(ptr_width);
            for i in 0..*count {
                let start = i * elem_sz;
                let end = start + elem_sz;
                validate_aggregate_bytes(&bytes[start..end], elem, ptr_width)?;
            }
            Ok(())
        }
        Ty::Tuple(fields) => {
            let mut offset = 0usize;
            for field in fields {
                let f_sz = field.byte_size_for(ptr_width);
                validate_aggregate_bytes(&bytes[offset..offset + f_sz], field, ptr_width)?;
                offset += f_sz;
            }
            Ok(())
        }
        Ty::Never => Err(CastEvalError::UninhabitedTarget {
            target_ty: Ty::Never,
        }),
    }
}

/// Evaluates a same-size `CastKind::Transmute` on `val` under `ptr_width` and `policy`.
///
/// Key invariants (UCG `#286` / MiniRust):
/// 1. **Never** exposes provenance in `tracker` (`tracker` is borrowed only to prove/assert
///    that `eval_transmute` leaves the exposed provenance set untouched).
/// 2. `Ptr -> Ptr`: preserves `PointerValue { addr, provenance }` (masked to `ptr_width`),
///    and rejects `addr == 0` when `target_ty` is `Ty::Ref`.
/// 3. `Ptr -> Int` (under `TransmutePolicy::AllowPtrToIntStripProvenance`): strips `provenance`
///    without exposing it and validates `addr` against `target_ty`'s bit-validity niche
///    (e.g. `Ptr -> Char` on 32-bit checks Unicode scalar validity!).
/// 4. `Int -> Ptr`: produces `PointerValue { addr, provenance: None }`, rejecting `addr == 0`
///    when `target_ty` is `Ty::Ref`.
/// 5. `Scalar -> Scalar`: validates `target_ty` niche (`bool` `0..=1`, `char` scalar value),
///    returning `CastEvalError::InvalidBitPattern` on invalid bit patterns.
pub fn eval_transmute(
    val: TransmuteValue,
    src_ty: &Ty,
    target_ty: &Ty,
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    _tracker: &ExposedProvenanceTracker,
) -> Result<TransmuteValue, CastEvalError> {
    if !target_ty.is_inhabited() {
        return Err(CastEvalError::UninhabitedTarget {
            target_ty: target_ty.clone(),
        });
    }
    if !src_ty.is_inhabited() {
        return Err(CastEvalError::TypeMismatch("source type is uninhabited"));
    }

    let src_bytes = src_ty.byte_size_for(ptr_width);
    let target_bytes = target_ty.byte_size_for(ptr_width);
    if src_bytes != target_bytes {
        return Err(CastEvalError::SizeMismatch {
            src_bytes,
            target_bytes,
        });
    }

    if src_ty.contains_ptr() && !target_ty.is_any_ptr() && policy == TransmutePolicy::RejectPtrToInt
    {
        return Err(CastEvalError::PtrToIntDisallowed {
            src_ty: src_ty.clone(),
            target_ty: target_ty.clone(),
        });
    }

    match val {
        TransmuteValue::Ptr(ptr) => {
            if !src_ty.is_any_ptr() {
                return Err(CastEvalError::TypeMismatch(
                    "TransmuteValue::Ptr requires pointer or reference source type",
                ));
            }
            let addr_bits = (ptr.addr as u128) & ptr_width.mask();
            let addr = addr_bits as u64;
            if src_ty.is_ref() && addr == 0 {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: src_ty.clone(),
                    bits: 0,
                });
            }

            if target_ty.is_any_ptr() {
                if target_ty.is_ref() && addr == 0 {
                    return Err(CastEvalError::InvalidBitPattern {
                        target_ty: target_ty.clone(),
                        bits: 0,
                    });
                }
                Ok(TransmuteValue::Ptr(PointerValue {
                    addr,
                    provenance: ptr.provenance,
                }))
            } else if target_ty.is_scalar() {
                // Ptr -> Scalar (under AllowPtrToIntStripProvenance): strip provenance without exposing it,
                // and validate target scalar bit-validity (e.g., Ptr -> Char on 32-bit!).
                if !target_ty.is_valid_scalar_bits(addr_bits, ptr_width) {
                    return Err(CastEvalError::InvalidBitPattern {
                        target_ty: target_ty.clone(),
                        bits: addr_bits,
                    });
                }
                Ok(TransmuteValue::Scalar(addr_bits))
            } else {
                // Ptr -> Aggregate (under AllowPtrToIntStripProvenance): serialize address bytes
                // and validate aggregate niches.
                let bytes: Vec<u8> = (0..target_bytes)
                    .map(|i| ((addr_bits >> (i * 8)) & 0xFF) as u8)
                    .collect();
                validate_aggregate_bytes(&bytes, target_ty, ptr_width)?;
                Ok(TransmuteValue::Bytes(bytes))
            }
        }
        TransmuteValue::Scalar(src_bits) => {
            if src_ty.is_any_ptr() || !src_ty.is_scalar() {
                return Err(CastEvalError::TypeMismatch(
                    "TransmuteValue::Scalar requires non-pointer scalar source type",
                ));
            }
            if !src_ty.is_valid_scalar_bits(src_bits, ptr_width) {
                return Err(CastEvalError::InvalidBitPattern {
                    target_ty: src_ty.clone(),
                    bits: src_bits,
                });
            }

            if target_ty.is_any_ptr() {
                // Scalar -> Ptr: never fabricates or picks exposed provenance (`provenance: None`).
                if !target_ty.is_valid_scalar_bits(src_bits, ptr_width) {
                    return Err(CastEvalError::InvalidBitPattern {
                        target_ty: target_ty.clone(),
                        bits: src_bits,
                    });
                }
                let addr = (src_bits & ptr_width.mask()) as u64;
                Ok(TransmuteValue::Ptr(PointerValue {
                    addr,
                    provenance: None,
                }))
            } else if target_ty.is_scalar() {
                if !target_ty.is_valid_scalar_bits(src_bits, ptr_width) {
                    return Err(CastEvalError::InvalidBitPattern {
                        target_ty: target_ty.clone(),
                        bits: src_bits,
                    });
                }
                let masked = src_bits & target_ty.scalar_mask(ptr_width);
                Ok(TransmuteValue::Scalar(masked))
            } else {
                // Scalar -> Aggregate (e.g. u32 -> [u8; 4] or u32 -> (u16, u16)):
                let bytes: Vec<u8> = (0..target_bytes)
                    .map(|i| ((src_bits >> (i * 8)) & 0xFF) as u8)
                    .collect();
                validate_aggregate_bytes(&bytes, target_ty, ptr_width)?;
                Ok(TransmuteValue::Bytes(bytes))
            }
        }
        TransmuteValue::Bytes(bytes) => {
            if bytes.len() != src_bytes {
                return Err(CastEvalError::SizeMismatch {
                    src_bytes: bytes.len(),
                    target_bytes,
                });
            }
            validate_aggregate_bytes(&bytes, src_ty, ptr_width)?;
            validate_aggregate_bytes(&bytes, target_ty, ptr_width)?;

            if target_ty.is_any_ptr() {
                let mut bits = 0u128;
                for (i, &b) in bytes.iter().enumerate().take(16) {
                    bits |= (b as u128) << (i * 8);
                }
                Ok(TransmuteValue::Ptr(PointerValue {
                    addr: (bits & ptr_width.mask()) as u64,
                    provenance: None,
                }))
            } else if target_ty.is_scalar() {
                let mut bits = 0u128;
                for (i, &b) in bytes.iter().enumerate().take(16) {
                    bits |= (b as u128) << (i * 8);
                }
                Ok(TransmuteValue::Scalar(bits))
            } else {
                Ok(TransmuteValue::Bytes(bytes))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntTy, Mutability, UintTy};

    #[test]
    fn test_lower_ptr_to_int_valid() {
        let op = Operand::Constant(crate::ir::Constant::Int(0, Ty::Uint(UintTy::Usize)));
        let src_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let target_ty = Ty::Uint(UintTy::Usize);

        let lowered = lower_ptr_to_int(&op, &src_ty, &target_ty).expect("lowering must succeed");
        assert_eq!(
            lowered,
            LoweredCast::PtrToInt {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: op,
                expose_provenance: true,
            }
        );
    }

    #[test]
    fn test_lower_ptr_to_int_rejects_non_ptr_source() {
        let op = Operand::Constant(crate::ir::Constant::Int(42, Ty::Uint(UintTy::U32)));
        let src_ty = Ty::Uint(UintTy::U32);
        let target_ty = Ty::Uint(UintTy::Usize);

        let err = lower_ptr_to_int(&op, &src_ty, &target_ty).expect_err("must reject non-ptr source");
        assert!(matches!(err, CastLowerError::InvalidSourceType { .. }));
    }

    #[test]
    fn test_lower_ptr_to_int_rejects_non_int_target() {
        let op = Operand::Constant(crate::ir::Constant::Int(0, Ty::Uint(UintTy::Usize)));
        let src_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let target_ty = Ty::Bool;

        let err = lower_ptr_to_int(&op, &src_ty, &target_ty).expect_err("must reject non-int target");
        assert!(matches!(err, CastLowerError::InvalidTargetType { .. }));
    }

    #[test]
    fn test_lower_int_to_ptr_valid() {
        let op = Operand::Constant(crate::ir::Constant::Int(0x1000, Ty::Uint(UintTy::Usize)));
        let src_ty = Ty::Uint(UintTy::Usize);
        let target_ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Mut);

        let lowered = lower_int_to_ptr(&op, &src_ty, &target_ty).expect("lowering must succeed");
        assert_eq!(
            lowered,
            LoweredCast::IntToPtr {
                src_ty: src_ty.clone(),
                target_ty: target_ty.clone(),
                operand: op,
                pick_exposed_provenance: true,
            }
        );
    }

    #[test]
    fn test_lower_int_to_ptr_rejects_non_int_source() {
        let op = Operand::Constant(crate::ir::Constant::Bool(true));
        let src_ty = Ty::Bool;
        let target_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);

        let err = lower_int_to_ptr(&op, &src_ty, &target_ty).expect_err("must reject non-int source");
        assert!(matches!(err, CastLowerError::InvalidSourceType { .. }));
    }

    #[test]
    fn test_eval_ptr_to_int_exposes_provenance() {
        let mut tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 1, tag: 42 };
        let ptr = PointerValue {
            addr: 0x7fff_0000,
            provenance: Some(prov),
        };
        let target_ty = Ty::Uint(UintTy::Usize);

        let int_val = eval_ptr_to_int(ptr, &target_ty, &mut tracker).expect("evaluation succeeds");
        assert_eq!(int_val, 0x7fff_0000);
        assert!(tracker.is_exposed(&prov));
    }

    #[test]
    fn test_eval_ptr_to_int_truncation() {
        let mut tracker = ExposedProvenanceTracker::new();
        let ptr = PointerValue::without_provenance(0x1_0000_0005);
        let target_ty = Ty::Uint(UintTy::U32);

        let int_val = eval_ptr_to_int(ptr, &target_ty, &mut tracker).expect("evaluation succeeds");
        assert_eq!(int_val, 5);
    }

    #[test]
    fn test_eval_int_to_ptr_with_exposed_provenance() {
        let mut tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 2, tag: 99 };
        tracker.expose(prov);

        let target_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Mut);
        let ptr = eval_int_to_ptr(0x8000_1234, &target_ty, &tracker, Some(prov))
            .expect("must succeed with exposed provenance");

        assert_eq!(ptr.addr, 0x8000_1234);
        assert_eq!(ptr.provenance, Some(prov));
    }

    #[test]
    fn test_eval_int_to_ptr_rejects_unexposed_provenance() {
        let tracker = ExposedProvenanceTracker::new();
        let unexposed_prov = Provenance { alloc_id: 99, tag: 1 };

        let target_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Mut);
        let err = eval_int_to_ptr(0x8000_1234, &target_ty, &tracker, Some(unexposed_prov))
            .expect_err("must reject unexposed provenance");

        assert_eq!(err, CastEvalError::UnexposedProvenance(unexposed_prov));
    }

    #[test]
    fn test_roundtrip_pointer_int_pointer() {
        let mut tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 5, tag: 123 };
        let original_ptr = PointerValue {
            addr: 0x4000_8000,
            provenance: Some(prov),
        };

        let int_ty = Ty::Uint(UintTy::Usize);
        let ptr_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);

        // Step 1: Ptr to Int (exposes provenance)
        let int_val = eval_ptr_to_int(original_ptr, &int_ty, &mut tracker).unwrap();
        assert_eq!(int_val, 0x4000_8000);

        // Step 2: Int to Ptr (reconstructs pointer with exposed provenance)
        let roundtrip_ptr = eval_int_to_ptr(int_val, &ptr_ty, &tracker, Some(prov)).unwrap();
        assert_eq!(roundtrip_ptr, original_ptr);
    }

    #[test]
    fn test_transmute_ptr_width_32_vs_64() {
        let op = Operand::Constant(crate::ir::Constant::Int(42, Ty::Uint(UintTy::Usize)));
        let usize_ty = Ty::Uint(UintTy::Usize);
        let u32_ty = Ty::Uint(UintTy::U32);
        let u64_ty = Ty::Uint(UintTy::U64);

        // On 64-bit: usize <-> u64 succeeds, usize <-> u32 fails with SizeMismatchTransmute
        assert!(
            lower_transmute(
                &op,
                &usize_ty,
                &u64_ty,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt
            )
            .is_ok()
        );
        let err_64 = lower_transmute(
            &op,
            &usize_ty,
            &u32_ty,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect_err("64-bit usize -> u32 must fail");
        assert_eq!(
            err_64,
            CastLowerError::SizeMismatchTransmute {
                src_ty: usize_ty.clone(),
                target_ty: u32_ty.clone(),
                src_bytes: 8,
                target_bytes: 4,
            }
        );

        // On 32-bit: usize <-> u32 succeeds, usize <-> u64 fails with SizeMismatchTransmute
        assert!(
            lower_transmute(
                &op,
                &usize_ty,
                &u32_ty,
                PtrWidth::Bits32,
                TransmutePolicy::RejectPtrToInt
            )
            .is_ok()
        );
        let err_32 = lower_transmute(
            &op,
            &usize_ty,
            &u64_ty,
            PtrWidth::Bits32,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect_err("32-bit usize -> u64 must fail");
        assert_eq!(
            err_32,
            CastLowerError::SizeMismatchTransmute {
                src_ty: usize_ty,
                target_ty: u64_ty,
                src_bytes: 4,
                target_bytes: 8,
            }
        );
    }

    #[test]
    fn test_transmute_inhabitation_empty_array_of_never_vs_nonempty() {
        let op = Operand::Constant(crate::ir::Constant::Unit);
        let unit_ty = Ty::unit();
        let empty_never_arr = Ty::Array(Box::new(Ty::Never), 0);
        let nonempty_never_arr = Ty::Array(Box::new(Ty::Never), 1);
        let tuple_with_never = Ty::Tuple(vec![Ty::Never, Ty::Uint(UintTy::U32)]);

        // [!; 0] is inhabited and has size 0, so () <-> [!; 0] succeeds!
        assert!(empty_never_arr.is_inhabited());
        assert_eq!(empty_never_arr.checked_byte_size(PtrWidth::Bits64), Some(0));
        assert!(
            lower_transmute(
                &op,
                &unit_ty,
                &empty_never_arr,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt
            )
            .is_ok()
        );

        // !, [!; 1], and (!, u32) are uninhabited and rejected with UninhabitedTarget!
        for bad_target in [Ty::Never, nonempty_never_arr, tuple_with_never] {
            assert!(!bad_target.is_inhabited());
            assert_eq!(bad_target.checked_byte_size(PtrWidth::Bits64), None);
            let err = lower_transmute(
                &op,
                &unit_ty,
                &bad_target,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt,
            )
            .expect_err("uninhabited target must be rejected");
            assert_eq!(
                err,
                CastLowerError::UninhabitedTarget {
                    target_ty: bad_target
                }
            );
        }
    }

    #[test]
    fn test_transmute_provenance_never_exposed_and_null_ref_rejected() {
        let tracker = ExposedProvenanceTracker::new();
        let prov = Provenance { alloc_id: 7, tag: 77 };
        let ptr = PointerValue {
            addr: 0x1000,
            provenance: Some(prov),
        };
        let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let ref_u8 = Ty::Ref(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
        let usize_ty = Ty::Uint(UintTy::Usize);

        // Ptr -> Ptr preserves provenance without exposing it
        let res = eval_transmute(
            TransmuteValue::Ptr(ptr),
            &raw_u8,
            &ref_u8,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .expect("non-null Ptr -> Ref transmute succeeds");
        assert_eq!(res, TransmuteValue::Ptr(ptr));
        assert!(!tracker.is_exposed(&prov));

        // Null 0usize -> &u8 must fail with InvalidBitPattern
        let null_err = eval_transmute(
            TransmuteValue::Scalar(0),
            &usize_ty,
            &ref_u8,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .expect_err("null reference transmute must fail");
        assert_eq!(
            null_err,
            CastEvalError::InvalidBitPattern {
                target_ty: ref_u8,
                bits: 0,
            }
        );

        // Ptr ->Char on 32-bit under AllowPtrToIntStripProvenance must check Unicode scalar validity!
        let surrogate_ptr = PointerValue {
            addr: 0xD800,
            provenance: Some(prov),
        };
        let char_err = eval_transmute(
            TransmuteValue::Ptr(surrogate_ptr),
            &raw_u8,
            &Ty::Char,
            PtrWidth::Bits32,
            TransmutePolicy::AllowPtrToIntStripProvenance,
            &tracker,
        )
        .expect_err("surrogate address transmuted to char on 32-bit must fail");
        assert_eq!(
            char_err,
            CastEvalError::InvalidBitPattern {
                target_ty: Ty::Char,
                bits: 0xD800,
            }
        );
    }
}
