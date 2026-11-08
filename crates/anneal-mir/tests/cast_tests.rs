//! Integration tests for MIR cast lowering, MiniRust provenance correspondence,
//! and same-size `CastKind::Transmute` lowering and evaluation across 32-bit and 64-bit targets.

use anneal_mir::ir::{
    CastKind, Constant, IntTy, Mutability, Operand, PointerValue, Provenance, PtrWidth, ScalarTy,
    Ty, UintTy,
};
use anneal_mir::lower::{
    CastEvalError, CastLowerError, CastOp, ExposedProvenanceTracker, LoweredCast, TransmutePolicy,
    TransmuteValue, eval_int_to_ptr, eval_ptr_to_int, eval_transmute, lower_cast_rvalue,
    lower_cast_rvalue_with_ptr_width, lower_transmute,
};

#[test]
fn test_end_to_end_ptr_to_int_to_ptr() {
    let mut tracker = ExposedProvenanceTracker::new();
    let prov = Provenance { alloc_id: 10, tag: 456 };
    let ptr = PointerValue::with_provenance(0xbeef_0000, prov.alloc_id, prov.tag);

    let ptr_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Mut);
    let usize_ty = Ty::Uint(UintTy::Usize);

    // Lowering checks
    let op = Operand::Constant(anneal_mir::ir::Constant::Ptr(ptr, ptr_ty.clone()));
    let lowered_p2i = lower_cast_rvalue(CastKind::PointerExposeProvenance, &op, &ptr_ty, &usize_ty)
        .expect("lower ptr to int");
    assert!(matches!(lowered_p2i, LoweredCast::PtrToInt { .. }));

    // Dynamic evaluation
    let addr = eval_ptr_to_int(ptr, &usize_ty, &mut tracker).expect("eval ptr to int");
    assert_eq!(addr, 0xbeef_0000);
    assert!(tracker.is_exposed(&prov));

    // Lowering int to ptr
    let int_op = Operand::Constant(anneal_mir::ir::Constant::Int(addr, usize_ty.clone()));
    let lowered_i2p = lower_cast_rvalue(CastKind::PointerWithExposedProvenance, &int_op, &usize_ty, &ptr_ty)
        .expect("lower int to ptr");
    assert!(matches!(lowered_i2p, LoweredCast::IntToPtr { .. }));

    // Dynamic reconstruction
    let reconstituted = eval_int_to_ptr(addr, &ptr_ty, &tracker, Some(prov))
        .expect("eval int to ptr with exposed provenance");
    assert_eq!(reconstituted.addr, ptr.addr);
    assert_eq!(reconstituted.provenance, ptr.provenance);
}

#[test]
fn test_unexposed_provenance_rejected() {
    let tracker = ExposedProvenanceTracker::new();
    let unexposed = Provenance { alloc_id: 999, tag: 888 };
    let ptr_ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Not);

    let err = eval_int_to_ptr(0x1234_5678, &ptr_ty, &tracker, Some(unexposed))
        .expect_err("unexposed provenance must be rejected");
    assert_eq!(err, CastEvalError::UnexposedProvenance(unexposed));
}

#[test]
fn test_wildcard_provenance_allowed() {
    let tracker = ExposedProvenanceTracker::new();
    let ptr_ty = Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Not);

    let ptr = eval_int_to_ptr(0x1234_5678, &ptr_ty, &tracker, None)
        .expect("wildcard / None provenance is always valid");
    assert_eq!(ptr.addr, 0x1234_5678);
    assert_eq!(ptr.provenance, None);
}

#[test]
fn test_transmute_32bit_vs_64bit_pointer_width_sizes() {
    let usize_ty = Ty::Uint(UintTy::Usize);
    let isize_ty = Ty::Int(IntTy::Isize);
    let raw_ptr_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let u32_ty = Ty::Uint(UintTy::U32);
    let u64_ty = Ty::Uint(UintTy::U64);
    let op = Operand::Constant(Constant::Int(0x1234, u32_ty.clone()));

    // Under Bits32: usize, isize, RawPtr are 4 bytes (match u32, mismatch u64)
    for ptr_sized in [&usize_ty, &isize_ty, &raw_ptr_ty] {
        assert_eq!(ptr_sized.byte_size_for(PtrWidth::Bits32), 4);
        assert_eq!(ptr_sized.byte_size_for(PtrWidth::Bits64), 8);

        let lowered_32 = lower_cast_rvalue_with_ptr_width(
            CastKind::Transmute,
            &op,
            &u32_ty,
            ptr_sized,
            PtrWidth::Bits32,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect("u32 -> ptr-sized on 32-bit must succeed");
        assert!(matches!(
            lowered_32,
            LoweredCast::Transmute {
                size_bytes: 4,
                exposes_provenance: false,
                ..
            }
        ));

        let mismatch_32 = lower_cast_rvalue_with_ptr_width(
            CastKind::Transmute,
            &op,
            &u64_ty,
            ptr_sized,
            PtrWidth::Bits32,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect_err("u64 -> ptr-sized on 32-bit must fail");
        assert_eq!(
            mismatch_32,
            CastLowerError::SizeMismatchTransmute {
                src_ty: u64_ty.clone(),
                target_ty: (*ptr_sized).clone(),
                src_bytes: 8,
                target_bytes: 4,
            }
        );

        // Under Bits64: u64 -> ptr-sized succeeds, u32 -> ptr-sized fails
        let lowered_64 = lower_cast_rvalue_with_ptr_width(
            CastKind::Transmute,
            &op,
            &u64_ty,
            ptr_sized,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect("u64 -> ptr-sized on 64-bit must succeed");
        assert!(matches!(
            lowered_64,
            LoweredCast::Transmute {
                size_bytes: 8,
                exposes_provenance: false,
                ..
            }
        ));

        let mismatch_64 = lower_cast_rvalue_with_ptr_width(
            CastKind::Transmute,
            &op,
            &u32_ty,
            ptr_sized,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect_err("u32 -> ptr-sized on 64-bit must fail");
        assert_eq!(
            mismatch_64,
            CastLowerError::SizeMismatchTransmute {
                src_ty: u32_ty.clone(),
                target_ty: (*ptr_sized).clone(),
                src_bytes: 4,
                target_bytes: 8,
            }
        );
    }
}

#[test]
fn test_transmute_inhabitation_subtlety_empty_vs_nonempty_never_array() {
    let op = Operand::Constant(Constant::Unit);
    let unit_ty = Ty::unit();
    let arr_never_0 = Ty::Array(Box::new(Ty::Never), 0);
    let arr_never_1 = Ty::Array(Box::new(Ty::Never), 1);
    let tuple_never = Ty::Tuple(vec![Ty::Never, Ty::Uint(UintTy::U32)]);

    // [!; 0] is inhabited of size 0
    assert!(arr_never_0.is_inhabited());
    assert_eq!(arr_never_0.checked_byte_size(PtrWidth::Bits64), Some(0));
    let ok_lower = lower_transmute(
        &op,
        &unit_ty,
        &arr_never_0,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
    )
    .expect("() -> [!; 0] must lower cleanly");
    assert_eq!(
        ok_lower,
        LoweredCast::Transmute {
            src_ty: unit_ty.clone(),
            target_ty: arr_never_0,
            operand: op.clone(),
            op: CastOp::AggregateTransmute { size_bytes: 0 },
            size_bytes: 0,
            exposes_provenance: false,
        }
    );

    // !, [!; 1], and (!, u32) are uninhabited
    for uninhabited in [Ty::Never, arr_never_1, tuple_never] {
        assert!(!uninhabited.is_inhabited());
        assert_eq!(uninhabited.checked_byte_size(PtrWidth::Bits64), None);
        let err = lower_transmute(
            &op,
            &unit_ty,
            &uninhabited,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
        )
        .expect_err("uninhabited target must be rejected");
        assert_eq!(
            err,
            CastLowerError::UninhabitedTarget {
                target_ty: uninhabited
            }
        );
    }
}

#[test]
fn test_transmute_provenance_discipline_vs_expose_provenance() {
    let tracker = ExposedProvenanceTracker::new();
    let prov = Provenance {
        alloc_id: 77,
        tag: 9001,
    };
    let ptr = PointerValue::with_provenance(0x0041, prov.alloc_id, prov.tag);
    let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let raw_u32 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U32)), Mutability::Mut);
    let usize_ty = Ty::Uint(UintTy::Usize);
    let op = Operand::Constant(Constant::Ptr(ptr, raw_u8.clone()));

    // 1. Default RejectPtrToInt rejects Ptr -> Int transmute
    let err = lower_cast_rvalue(CastKind::Transmute, &op, &raw_u8, &usize_ty)
        .expect_err("default policy must reject Ptr -> Int transmute");
    assert_eq!(
        err,
        CastLowerError::PtrToIntTransmuteDisallowed {
            src_ty: raw_u8.clone(),
            target_ty: usize_ty.clone(),
        }
    );

    // 2. AllowPtrToIntStripProvenance permits Ptr -> Int transmute with exposes_provenance: false,
    //    and evaluation strips provenance WITHOUT exposing it in tracker!
    let lowered_strip = lower_transmute(
        &op,
        &raw_u8,
        &usize_ty,
        PtrWidth::Bits64,
        TransmutePolicy::AllowPtrToIntStripProvenance,
    )
    .expect("AllowPtrToIntStripProvenance must allow Ptr -> usize");
    assert!(matches!(
        lowered_strip,
        LoweredCast::Transmute {
            exposes_provenance: false,
            ..
        }
    ));

    let eval_stripped = eval_transmute(
        TransmuteValue::Ptr(ptr),
        &raw_u8,
        &usize_ty,
        PtrWidth::Bits64,
        TransmutePolicy::AllowPtrToIntStripProvenance,
        &tracker,
    )
    .expect("eval Ptr -> usize under strip policy");
    assert_eq!(eval_stripped, TransmuteValue::Scalar(0x0041));
    assert!(!tracker.is_exposed(&prov));

    // Because provenance was NOT exposed by transmute, IntToPtr cannot claim `prov`!
    let reconstruct_err = eval_int_to_ptr(0x0041, &raw_u8, &tracker, Some(prov))
        .expect_err("provenance stripped by transmute is not exposed");
    assert_eq!(reconstruct_err, CastEvalError::UnexposedProvenance(prov));

    // 3. Ptr -> Ptr transmute preserves provenance without exposing it in tracker
    let eval_p2p = eval_transmute(
        TransmuteValue::Ptr(ptr),
        &raw_u8,
        &raw_u32,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .expect("Ptr -> Ptr transmute must succeed");
    assert_eq!(eval_p2p, TransmuteValue::Ptr(ptr));
    assert!(!tracker.is_exposed(&prov));

    // 4. Int -> Ptr transmute produces provenance: None
    let eval_i2p = eval_transmute(
        TransmuteValue::Scalar(0x0041),
        &usize_ty,
        &raw_u8,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .expect("usize -> RawPtr transmute must succeed");
    assert_eq!(
        eval_i2p,
        TransmuteValue::Ptr(PointerValue::without_provenance(0x0041))
    );
}

#[test]
fn test_transmute_niche_validation_bool_char_and_null_ref() {
    let tracker = ExposedProvenanceTracker::new();
    let u8_ty = Ty::Uint(UintTy::U8);
    let u32_ty = Ty::Uint(UintTy::U32);
    let raw_u8 = Ty::RawPtr(Box::new(u8_ty.clone()), Mutability::Not);
    let ref_u8 = Ty::Ref(Box::new(u8_ty.clone()), Mutability::Not);

    // Bool valid: 0 and 1; invalid: 2 and 255
    for valid_b in [0u128, 1u128] {
        assert!(ScalarTy::Bool.is_valid_bits(valid_b, PtrWidth::Bits64));
        let res = eval_transmute(
            TransmuteValue::Scalar(valid_b),
            &u8_ty,
            &Ty::Bool,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .unwrap();
        assert_eq!(res, TransmuteValue::Scalar(valid_b));
    }
    for invalid_b in [2u128, 255u128] {
        assert!(!ScalarTy::Bool.is_valid_bits(invalid_b, PtrWidth::Bits64));
        let err = eval_transmute(
            TransmuteValue::Scalar(invalid_b),
            &u8_ty,
            &Ty::Bool,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .expect_err("invalid bool discriminant must fail");
        assert_eq!(
            err,
            CastEvalError::InvalidBitPattern {
                target_ty: Ty::Bool,
                bits: invalid_b,
            }
        );
    }

    // Char valid: 0, 0xD7FF, 0xE000, 0x10FFFF; invalid: surrogates 0xD800, 0xDFFF, and 0x110000
    for valid_c in [0u128, 0xD7FF, 0xE000, 0x10FFFF] {
        assert!(ScalarTy::Char.is_valid_bits(valid_c, PtrWidth::Bits64));
        let res = eval_transmute(
            TransmuteValue::Scalar(valid_c),
            &u32_ty,
            &Ty::Char,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .unwrap();
        assert_eq!(res, TransmuteValue::Scalar(valid_c));
    }
    for invalid_c in [0xD800u128, 0xDFFFu128, 0x110000u128] {
        assert!(!ScalarTy::Char.is_valid_bits(invalid_c, PtrWidth::Bits64));
        let err = eval_transmute(
            TransmuteValue::Scalar(invalid_c),
            &u32_ty,
            &Ty::Char,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        )
        .expect_err("invalid char codepoint must fail");
        assert_eq!(
            err,
            CastEvalError::InvalidBitPattern {
                target_ty: Ty::Char,
                bits: invalid_c,
            }
        );

        // Also test Ptr -> Char on 32-bit under AllowPtrToIntStripProvenance!
        let bad_ptr = PointerValue::with_provenance(invalid_c as u64, 1, 1);
        let ptr_char_err = eval_transmute(
            TransmuteValue::Ptr(bad_ptr),
            &raw_u8,
            &Ty::Char,
            PtrWidth::Bits32,
            TransmutePolicy::AllowPtrToIntStripProvenance,
            &tracker,
        )
        .expect_err("Ptr -> Char on 32-bit with invalid Unicode scalar must fail");
        assert_eq!(
            ptr_char_err,
            CastEvalError::InvalidBitPattern {
                target_ty: Ty::Char,
                bits: invalid_c,
            }
        );
    }

    // Valid Ptr -> Char on 32-bit under AllowPtrToIntStripProvenance
    let good_ptr = PointerValue::with_provenance(0xE000, 1, 1);
    let ptr_char_ok = eval_transmute(
        TransmuteValue::Ptr(good_ptr),
        &raw_u8,
        &Ty::Char,
        PtrWidth::Bits32,
        TransmutePolicy::AllowPtrToIntStripProvenance,
        &tracker,
    )
    .expect("valid Unicode scalar address in Ptr -> Char on 32-bit must succeed");
    assert_eq!(ptr_char_ok, TransmuteValue::Scalar(0xE000));

    // Null reference rejection on both Ptr -> Ref and Int -> Ref
    let null_ptr = PointerValue::without_provenance(0);
    assert_eq!(
        eval_transmute(
            TransmuteValue::Ptr(null_ptr),
            &raw_u8,
            &ref_u8,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        ),
        Err(CastEvalError::InvalidBitPattern {
            target_ty: ref_u8.clone(),
            bits: 0,
        })
    );
    assert_eq!(
        eval_transmute(
            TransmuteValue::Scalar(0),
            &u32_ty,
            &ref_u8,
            PtrWidth::Bits32,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        ),
        Err(CastEvalError::InvalidBitPattern {
            target_ty: ref_u8,
            bits: 0,
        })
    );
}

#[test]
fn test_composite_aggregate_transmute_bytes() {
    let tracker = ExposedProvenanceTracker::new();
    let u32_ty = Ty::Uint(UintTy::U32);
    let arr_u8_4 = Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 4);
    let arr_bool_4 = Ty::Array(Box::new(Ty::Bool), 4);
    let tuple_u16_2 = Ty::Tuple(vec![Ty::Uint(UintTy::U16), Ty::Uint(UintTy::U16)]);

    // u32 -> [u8; 4] -> (u16, u16) -> u32
    let bytes_val = eval_transmute(
        TransmuteValue::Scalar(0x0100_0100),
        &u32_ty,
        &arr_u8_4,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .unwrap();
    assert_eq!(bytes_val, TransmuteValue::Bytes(vec![0, 1, 0, 1]));

    // Valid [bool; 4]
    let bool_arr_ok = eval_transmute(
        bytes_val.clone(),
        &arr_u8_4,
        &arr_bool_4,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .unwrap();
    assert_eq!(bool_arr_ok, TransmuteValue::Bytes(vec![0, 1, 0, 1]));

    // Invalid [bool; 4] when one byte is 2
    let bad_bool_err = eval_transmute(
        TransmuteValue::Scalar(0x0200_0100),
        &u32_ty,
        &arr_bool_4,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .expect_err("transmute u32 with byte 2 to [bool; 4] must fail");
    assert!(matches!(bad_bool_err, CastEvalError::InvalidBitPattern { .. }));

    // (u16, u16) -> u32 roundtrip
    let back_to_u32 = eval_transmute(
        bytes_val,
        &tuple_u16_2,
        &u32_ty,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .unwrap();
    assert_eq!(back_to_u32, TransmuteValue::Scalar(0x0100_0100));
}
