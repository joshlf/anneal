//! Integration tests for MIR cast lowering, MiniRust provenance correspondence,
//! and same-size `CastKind::Transmute` lowering and evaluation across 32-bit and 64-bit targets.

use anneal_mir::ir::{
    CastKind, Constant, IntTy, Mutability, Operand, PointerValue, Provenance, PtrWidth, ScalarTy,
    Ty, UintTy,
};
use anneal_mir::lower::{
    AbstractByte, CastEvalError, CastLowerError, CastOp, ExposedProvenanceTracker, LoweredCast,
    ProvenanceFrag, TransmutePolicy, TransmuteValue, eval_int_to_int, eval_int_to_ptr,
    eval_ptr_to_int, eval_transmute, lower_cast_rvalue, lower_cast_rvalue_with_ptr_width,
    lower_transmute,
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

// ---------------------------------------------------------------------------------------------
// [adv B1] regression tests
// ---------------------------------------------------------------------------------------------

/// Encodes `addr` as a thin pointer's little-endian bytes carrying ordered provenance fragments.
fn ptr_bytes(addr: u64, prov: Option<Provenance>, ptr_width: PtrWidth) -> Vec<AbstractByte> {
    addr.to_le_bytes()[..ptr_width.byte_size()]
        .iter()
        .enumerate()
        .map(|(position, &data)| AbstractByte {
            data,
            provenance: prov.map(|provenance| ProvenanceFrag {
                provenance,
                position,
            }),
        })
        .collect()
}

#[test]
fn test_b1_tuple_layout_sizes_match_rustc_and_padded_tuples_are_not_transmutable() {
    let tracker = ExposedProvenanceTracker::new();
    let u8_ty = Ty::Uint(UintTy::U8);
    let u16_ty = Ty::Uint(UintTy::U16);
    let u32_ty = Ty::Uint(UintTy::U32);
    let u64_ty = Ty::Uint(UintTy::U64);
    let op = Operand::Constant(Constant::Unit);

    // Sizes/alignments observed from rustc 1.98 on x86_64 (`size_of`/`align_of`). A0 summed
    // field sizes and reported 5, 6, 3, 12, 4, 1 respectively.
    let padded_cases = [
        (Ty::Tuple(vec![u8_ty.clone(), u32_ty.clone()]), 8, 4),
        (Ty::Tuple(vec![u8_ty.clone(), u32_ty.clone(), u8_ty.clone()]), 8, 4),
        (Ty::Tuple(vec![u16_ty.clone(), u8_ty.clone()]), 4, 2),
        (Ty::Tuple(vec![u64_ty.clone(), u32_ty.clone()]), 16, 8),
        (Ty::Tuple(vec![Ty::Never, u32_ty.clone()]), 4, 4),
        (Ty::Tuple(vec![Ty::Array(Box::new(u32_ty.clone()), 0), u8_ty.clone()]), 4, 4),
    ];
    for (ty, size, align) in &padded_cases {
        assert_eq!(ty.byte_size_for(PtrWidth::Bits64), *size, "{ty:?}");
        assert_eq!(ty.byte_size(), *size, "{ty:?}");
        assert_eq!(ty.layout_size_for(PtrWidth::Bits64), Some(*size), "{ty:?}");
        assert_eq!(ty.align_for(PtrWidth::Bits64), *align, "{ty:?}");
        assert!(!ty.has_canonical_byte_layout(PtrWidth::Bits64), "{ty:?}");
    }

    // (u8, u32) -> [u8; 5] is a size mismatch in rustc (8 vs 5 bytes), A0 accepted it.
    let padded = Ty::Tuple(vec![u8_ty.clone(), u32_ty.clone()]);
    let arr_u8_5 = Ty::Array(Box::new(u8_ty.clone()), 5);
    assert_eq!(
        lower_transmute(&op, &padded, &arr_u8_5, PtrWidth::Bits64, TransmutePolicy::RejectPtrToInt),
        Err(CastLowerError::SizeMismatchTransmute {
            src_ty: padded.clone(),
            target_ty: arr_u8_5,
            src_bytes: 8,
            target_bytes: 5,
        })
    );
    // (u8, u32) -> u64 has matching sizes, but padding bytes have no defined byte image.
    assert_eq!(
        lower_transmute(&op, &padded, &u64_ty, PtrWidth::Bits64, TransmutePolicy::RejectPtrToInt),
        Err(CastLowerError::UnsupportedLayout { ty: padded.clone() })
    );
    assert_eq!(
        eval_transmute(
            TransmuteValue::Bytes(vec![0; 8]),
            &padded,
            &u64_ty,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        ),
        Err(CastEvalError::UnsupportedLayout { ty: padded })
    );

    // Canonical tuples round-trip little-endian, in declaration order.
    let canon = Ty::Tuple(vec![u32_ty.clone(), u16_ty.clone(), u16_ty.clone()]);
    assert!(canon.has_canonical_byte_layout(PtrWidth::Bits64));
    let bytes = eval_transmute(
        TransmuteValue::Scalar(0x4444_3333_2222_1111),
        &u64_ty,
        &canon,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .unwrap();
    assert_eq!(
        bytes,
        TransmuteValue::Bytes(vec![0x11, 0x11, 0x22, 0x22, 0x33, 0x33, 0x44, 0x44])
    );
    let back = eval_transmute(
        bytes,
        &canon,
        &u64_ty,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .unwrap();
    assert_eq!(back, TransmuteValue::Scalar(0x4444_3333_2222_1111));

    // Tuples whose fields are not sorted by alignment group are not canonical.
    let unsorted = Ty::Tuple(vec![u32_ty.clone(), u64_ty.clone(), u32_ty.clone()]);
    assert_eq!(unsorted.byte_size_for(PtrWidth::Bits64), 16);
    assert!(!unsorted.has_canonical_byte_layout(PtrWidth::Bits64));

    // Mixed niche tuples are not canonical; identical-field niche tuples are, and keep validity.
    assert!(!Ty::Tuple(vec![u8_ty, Ty::Bool]).has_canonical_byte_layout(PtrWidth::Bits64));
    let bools = Ty::Tuple(vec![Ty::Bool, Ty::Bool]);
    assert!(bools.has_canonical_byte_layout(PtrWidth::Bits64));
    assert_eq!(
        eval_transmute(
            TransmuteValue::Scalar(0x0001),
            &u16_ty,
            &bools,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        ),
        Ok(TransmuteValue::Bytes(vec![1, 0]))
    );
    assert_eq!(
        eval_transmute(
            TransmuteValue::Scalar(0x0200),
            &u16_ty,
            &bools,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        ),
        Err(CastEvalError::InvalidBitPattern {
            target_ty: Ty::Bool,
            bits: 2,
        })
    );
}

#[test]
fn test_b1_transmute_rejects_unrepresentable_layouts_instead_of_saturating() {
    let u8_ty = Ty::Uint(UintTy::U8);
    let u16_ty = Ty::Uint(UintTy::U16);
    let op = Operand::Constant(Constant::Unit);

    // A0 saturated both sizes to usize::MAX and accepted this as a "same-size" transmute.
    let huge_u8 = Ty::Array(Box::new(u8_ty.clone()), usize::MAX);
    let huge_u16 = Ty::Array(Box::new(u16_ty.clone()), usize::MAX);
    assert_eq!(huge_u8.byte_size_for(PtrWidth::Bits64), usize::MAX);
    assert_eq!(huge_u16.byte_size_for(PtrWidth::Bits64), usize::MAX);
    assert_eq!(huge_u8.layout_size_for(PtrWidth::Bits64), None);
    assert_eq!(
        lower_transmute(&op, &huge_u8, &huge_u16, PtrWidth::Bits64, TransmutePolicy::RejectPtrToInt),
        Err(CastLowerError::LayoutTooLarge { ty: huge_u8 })
    );

    // On 32-bit targets objects are limited to isize::MAX = 2^31 - 1 bytes.
    let max32 = Ty::Array(Box::new(u8_ty.clone()), (1 << 31) - 1);
    let big32 = Ty::Array(Box::new(u8_ty.clone()), 1 << 31);
    assert_eq!(max32.layout_size_for(PtrWidth::Bits32), Some((1 << 31) - 1));
    assert_eq!(big32.layout_size_for(PtrWidth::Bits32), None);
    assert_eq!(big32.checked_byte_size(PtrWidth::Bits32), None);
    assert_eq!(big32.layout_size_for(PtrWidth::Bits64), Some(1 << 31));
    let big32_u16 = Ty::Array(Box::new(u16_ty), 1 << 30);
    assert_eq!(
        lower_transmute(&op, &big32, &big32_u16, PtrWidth::Bits32, TransmutePolicy::RejectPtrToInt),
        Err(CastLowerError::LayoutTooLarge { ty: big32.clone() })
    );
    assert!(
        lower_transmute(&op, &big32, &big32_u16, PtrWidth::Bits64, TransmutePolicy::RejectPtrToInt)
            .is_ok()
    );
    // Zero-sized elements: the array length itself must fit in the target's usize.
    let zst_arr = Ty::Array(Box::new(Ty::unit()), 1 << 32);
    assert_eq!(zst_arr.layout_size_for(PtrWidth::Bits32), None);
    assert_eq!(zst_arr.layout_size_for(PtrWidth::Bits64), Some(0));

    // Too many pointers to analyze for the provenance policy is reported as unsupported.
    let many_ptrs = Ty::Array(
        Box::new(Ty::RawPtr(Box::new(u8_ty.clone()), Mutability::Not)),
        1 << 17,
    );
    let many_words = Ty::Array(Box::new(Ty::Uint(UintTy::Usize)), 1 << 17);
    assert_eq!(
        lower_transmute(
            &op,
            &many_ptrs,
            &many_words,
            PtrWidth::Bits64,
            TransmutePolicy::AllowPtrToIntStripProvenance
        ),
        Err(CastLowerError::UnsupportedLayout { ty: many_ptrs })
    );
}

#[test]
fn test_b1_pointer_preserving_aggregate_transmutes_keep_provenance_without_exposing() {
    let tracker = ExposedProvenanceTracker::new();
    let prov = Provenance { alloc_id: 3, tag: 33 };
    let ptr = PointerValue::with_provenance(0x1000, prov.alloc_id, prov.tag);
    let u64_ty = Ty::Uint(UintTy::U64);
    let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let ref_u8 = Ty::Ref(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let arr_ref = Ty::Array(Box::new(ref_u8), 1);
    let op = Operand::Constant(Constant::Ptr(ptr, raw_u8.clone()));

    // A0 rejected this under the default policy: the target is not itself a pointer type,
    // although the pointer lands exactly on a pointer.
    let lowered = lower_cast_rvalue(CastKind::Transmute, &op, &raw_u8, &arr_ref)
        .expect("*const u8 -> [&u8; 1] preserves the pointer");
    assert!(matches!(
        lowered,
        LoweredCast::Transmute {
            op: CastOp::AggregateTransmute { size_bytes: 8 },
            exposes_provenance: false,
            ..
        }
    ));
    let out = eval_transmute(
        TransmuteValue::Ptr(ptr),
        &raw_u8,
        &arr_ref,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .unwrap();
    assert_eq!(
        out,
        TransmuteValue::AbstractBytes(ptr_bytes(0x1000, Some(prov), PtrWidth::Bits64))
    );
    // ... and back again, still carrying the provenance (never exposed).
    let back = eval_transmute(
        out,
        &arr_ref,
        &raw_u8,
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &tracker,
    )
    .unwrap();
    assert_eq!(back, TransmuteValue::Ptr(ptr));

    // (*const u8, u64) -> (*mut u16, u64): pointer lands on a pointer at the same offset.
    let pair = Ty::Tuple(vec![raw_u8.clone(), u64_ty.clone()]);
    let pair_mut = Ty::Tuple(vec![
        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U16)), Mutability::Mut),
        u64_ty.clone(),
    ]);
    assert!(
        lower_transmute(&op, &pair, &pair_mut, PtrWidth::Bits64, TransmutePolicy::RejectPtrToInt)
            .is_ok()
    );
    let mut pair_bytes = ptr_bytes(0x1000, Some(prov), PtrWidth::Bits64);
    pair_bytes.extend(0x2000u64.to_le_bytes().map(AbstractByte::new));
    assert_eq!(
        eval_transmute(
            TransmuteValue::AbstractBytes(pair_bytes.clone()),
            &pair,
            &pair_mut,
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &tracker,
        ),
        Ok(TransmuteValue::AbstractBytes(pair_bytes.clone()))
    );

    // (*const u8, u64) -> (u64, *const u8): the pointer would land on the u64 (Ptr -> Int).
    let swapped = Ty::Tuple(vec![u64_ty, raw_u8]);
    assert_eq!(
        lower_transmute(&op, &pair, &swapped, PtrWidth::Bits64, TransmutePolicy::RejectPtrToInt),
        Err(CastLowerError::PtrToIntTransmuteDisallowed {
            src_ty: pair.clone(),
            target_ty: swapped.clone(),
        })
    );
    // Under the strip policy, the u64 receives the bare address and the pointer built from
    // the old u64 bytes has no provenance; nothing is exposed.
    let stripped = eval_transmute(
        TransmuteValue::AbstractBytes(pair_bytes),
        &pair,
        &swapped,
        PtrWidth::Bits64,
        TransmutePolicy::AllowPtrToIntStripProvenance,
        &tracker,
    )
    .unwrap();
    let mut expected = 0x1000u64.to_le_bytes().to_vec();
    expected.extend(0x2000u64.to_le_bytes());
    assert_eq!(stripped, TransmuteValue::Bytes(expected));
    assert!(tracker.is_empty());
}

#[test]
fn test_b1_pointer_decode_requires_consistent_ordered_provenance_fragments() {
    let tracker = ExposedProvenanceTracker::new();
    let p1 = Provenance { alloc_id: 1, tag: 1 };
    let p2 = Provenance { alloc_id: 2, tag: 2 };
    let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);

    for ptr_width in [PtrWidth::Bits32, PtrWidth::Bits64] {
        let transmute = |bytes: Vec<AbstractByte>| {
            eval_transmute(
                TransmuteValue::AbstractBytes(bytes),
                &raw_u8,
                &raw_u8,
                ptr_width,
                TransmutePolicy::RejectPtrToInt,
                &tracker,
            )
        };
        // Consistent, in-order fragments keep the provenance.
        assert_eq!(
            transmute(ptr_bytes(0x40, Some(p1), ptr_width)),
            Ok(TransmuteValue::Ptr(PointerValue::with_provenance(0x40, 1, 1)))
        );
        // Mixed provenances yield a pointer without provenance.
        let mut mixed = ptr_bytes(0x40, Some(p1), ptr_width);
        let last = mixed.len() - 1;
        mixed[last].provenance = Some(ProvenanceFrag {
            provenance: p2,
            position: last,
        });
        assert_eq!(
            transmute(mixed),
            Ok(TransmuteValue::Ptr(PointerValue::without_provenance(0x40)))
        );
        // Shuffled fragments (wrong positions) also lose the provenance.
        let mut shuffled = ptr_bytes(0x40, Some(p1), ptr_width);
        shuffled.swap(0, 1);
        assert_eq!(
            transmute(shuffled),
            Ok(TransmuteValue::Ptr(PointerValue::without_provenance(0x4000)))
        );
        // A partially provenance-free pointer loses the provenance.
        let mut partial = ptr_bytes(0x40, Some(p1), ptr_width);
        partial[0].provenance = None;
        assert_eq!(
            transmute(partial),
            Ok(TransmuteValue::Ptr(PointerValue::without_provenance(0x40)))
        );
    }
    assert!(tracker.is_empty());
}

#[test]
fn test_b1_eval_int_to_int_validates_char_targets() {
    let u8_ty = Ty::Uint(UintTy::U8);
    let u32_ty = Ty::Uint(UintTy::U32);
    assert_eq!(eval_int_to_int(0x41, &u8_ty, &Ty::Char, PtrWidth::Bits64), Ok(0x41));
    assert_eq!(
        eval_int_to_int(0xD800, &u32_ty, &Ty::Char, PtrWidth::Bits64),
        Err(CastEvalError::InvalidBitPattern {
            target_ty: Ty::Char,
            bits: 0xD800,
        })
    );
    assert_eq!(
        eval_int_to_int(0x11_0000, &u32_ty, &Ty::Char, PtrWidth::Bits64),
        Err(CastEvalError::InvalidBitPattern {
            target_ty: Ty::Char,
            bits: 0x11_0000,
        })
    );
}

// ---------------------------------------------------------------------------------------------
// [adv A1] regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_a1_tuple_canonical_layout_rejects_increasing_field_alignment_with_same_size() {
    let tracker = ExposedProvenanceTracker::new();
    let u8_ty = Ty::Uint(UintTy::U8);
    let u16_ty = Ty::Uint(UintTy::U16);
    let u32_ty = Ty::Uint(UintTy::U32);
    let u64_ty = Ty::Uint(UintTy::U64);
    let op = Operand::Constant(Constant::Unit);

    // `([u8; 4], u32)` has field sizes (4, 4) so `max(align, size)` is 4 for both,
    // but `[u8; 4]` has align 1 < `u32` align 4, so `rustc` reorders `u32` before `[u8; 4]`.
    // Similarly `([u8; 6], u16)` has `max(align, size)` trailing_zeros (1, 1) and unpadded size 8,
    // but `[u8; 6]` has align 1 < `u16` align 2 (which would also place `u16` at offset 6 or reorder).
    // And `((u32, u32), u64)` has field sizes (8, 8), but `(u32, u32)` has align 4 < `u64` align 8.
    let non_canonical = [
        Ty::Tuple(vec![Ty::Array(Box::new(u8_ty.clone()), 4), u32_ty.clone()]),
        Ty::Tuple(vec![Ty::Array(Box::new(u8_ty.clone()), 6), u16_ty.clone()]),
        Ty::Tuple(vec![
            Ty::Tuple(vec![u32_ty.clone(), u32_ty.clone()]),
            u64_ty.clone(),
        ]),
    ];

    for bad_tuple in &non_canonical {
        assert!(
            !bad_tuple.has_canonical_byte_layout(PtrWidth::Bits64),
            "{bad_tuple:?} must not be treated as canonical declaration-order layout"
        );
        let size = bad_tuple.byte_size_for(PtrWidth::Bits64);
        let byte_arr = Ty::Array(Box::new(u8_ty.clone()), size);
        assert_eq!(
            lower_transmute(
                &op,
                bad_tuple,
                &byte_arr,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt,
            ),
            Err(CastLowerError::UnsupportedLayout {
                ty: bad_tuple.clone(),
            })
        );
        assert_eq!(
            eval_transmute(
                TransmuteValue::Bytes(vec![0; size]),
                bad_tuple,
                &byte_arr,
                PtrWidth::Bits64,
                TransmutePolicy::RejectPtrToInt,
                &tracker,
            ),
            Err(CastEvalError::UnsupportedLayout {
                ty: bad_tuple.clone(),
            })
        );
    }

    // Conversely, `(u32, [u8; 4])` and `(u64, (u32, u32))` have non-increasing alignments
    // and zero padding, so they ARE canonical.
    let canon_u32_arr = Ty::Tuple(vec![u32_ty.clone(), Ty::Array(Box::new(u8_ty), 4)]);
    let canon_u64_pair = Ty::Tuple(vec![u64_ty, Ty::Tuple(vec![u32_ty.clone(), u32_ty])]);
    assert!(canon_u32_arr.has_canonical_byte_layout(PtrWidth::Bits64));
    assert!(canon_u64_pair.has_canonical_byte_layout(PtrWidth::Bits64));
}
