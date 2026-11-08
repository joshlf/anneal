//! Lowering and evaluation for MIR pointer-to-integer (`PtrToInt`) and
//! integer-to-pointer (`IntToPtr`) casts.
//!
//! Models both:
//! 1. `rustc` MIR semantics (`CastKind::PointerExposeProvenance` and
//!    `CastKind::PointerWithExposedProvenance`); and
//! 2. MiniRust `IntPtrCast` provenance-exposure semantics (`spec/mem/intptrcast.md`).

use std::collections::BTreeSet;

use crate::ir::{CastKind, Operand, PointerValue, Provenance, Ty};

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

/// Lowers any supported MIR cast rvalue.
pub fn lower_cast_rvalue(
    kind: CastKind,
    operand: &Operand,
    src_ty: &Ty,
    target_ty: &Ty,
) -> Result<LoweredCast, CastLowerError> {
    match kind {
        CastKind::PointerExposeProvenance => lower_ptr_to_int(operand, src_ty, target_ty),
        CastKind::PointerWithExposedProvenance => lower_int_to_ptr(operand, src_ty, target_ty),
        CastKind::IntToInt => {
            if !src_ty.is_integral() {
                return Err(CastLowerError::InvalidSourceType {
                    expected: "integral type",
                    got: src_ty.clone(),
                });
            }
            if !target_ty.is_integral() {
                return Err(CastLowerError::InvalidTargetType {
                    expected: "integral type",
                    got: target_ty.clone(),
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
        CastKind::Transmute => Err(CastLowerError::UnsupportedCast {
            kind,
            src_ty: src_ty.clone(),
            target_ty: target_ty.clone(),
        }),
    }
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
        }
    }
}

impl std::error::Error for CastEvalError {}

/// Evaluates a lowered `PtrToInt` cast on a concrete pointer value.
///
/// Corresponds to MiniRust:
/// `IntPtrCast::expose` followed by converting the thin pointer address to integer.
pub fn eval_ptr_to_int(
    ptr: PointerValue,
    target_ty: &Ty,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<u128, CastEvalError> {
    if !target_ty.is_integral() {
        return Err(CastEvalError::TypeMismatch("target type must be integral"));
    }

    // Expose provenance if present.
    if let Some(prov) = ptr.provenance {
        tracker.expose(prov);
    }

    let target_bytes = target_ty.byte_size();
    let addr = ptr.addr;

    if target_bytes < 8 {
        // Truncate according to target width modulus.
        let modulus = 1u128 << (target_bytes * 8);
        Ok((addr as u128) % modulus)
    } else {
        Ok(addr as u128)
    }
}

/// Evaluates a lowered `IntToPtr` cast from an address value to a pointer.
///
/// Corresponds to MiniRust:
/// `IntPtrCast::int2ptr` predicting either `None` (untagged/wildcard) or an already-exposed provenance.
pub fn eval_int_to_ptr(
    addr: u128,
    target_ty: &Ty,
    tracker: &ExposedProvenanceTracker,
    predicted_prov: Option<Provenance>,
) -> Result<PointerValue, CastEvalError> {
    if !target_ty.is_raw_ptr() {
        return Err(CastEvalError::TypeMismatch("target type must be raw pointer"));
    }

    // Validate that predicted provenance is either None or already exposed.
    if let Some(prov) = predicted_prov {
        if !tracker.is_exposed(&prov) {
            return Err(CastEvalError::UnexposedProvenance(prov));
        }
    }

    Ok(PointerValue {
        addr: addr as u64,
        provenance: predicted_prov,
    })
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
}
