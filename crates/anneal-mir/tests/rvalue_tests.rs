//! Integration tests for MIR `Rvalue`, `Statement`, and `Body` lowering and dynamic evaluation.

use anneal_mir::ir::{
    AggregateKind, BasicBlockData, BinOp, Body, CastKind, Constant, IntTy, Local, Mutability,
    Operand, Place, PointerValue, ProjectionElem, PtrWidth, Rvalue, Statement, Ty, UintTy, UnOp,
};
use anneal_mir::lower::{
    ExposedProvenanceTracker, LoweredRvalue, LoweredStatement, MirValue, RvalueEvalError,
    RvalueLowerError, TransmutePolicy, eval_aggregate, eval_binop, eval_checked_binop,
    eval_lowered_rvalue, eval_unop, lower_body, lower_rvalue, lower_statement, resolve_place_ty,
};

#[test]
fn test_signed_and_unsigned_arithmetic_all_widths_and_modes() {
    // 1. i8 boundary values: MIN (-128), MAX (127), 0, -1
    let i8_min = MirValue::signed(-128, IntTy::I8, PtrWidth::Bits64);
    let i8_max = MirValue::signed(127, IntTy::I8, PtrWidth::Bits64);
    let i8_one = MirValue::signed(1, IntTy::I8, PtrWidth::Bits64);
    let i8_neg_one = MirValue::signed(-1, IntTy::I8, PtrWidth::Bits64);

    // MAX + 1 wraps to MIN, overflows in checked, errors in unchecked
    let add_wrap = eval_binop(BinOp::Add, &i8_max, &i8_one, PtrWidth::Bits64).unwrap();
    assert_eq!(add_wrap.as_signed(PtrWidth::Bits64), Some(-128));
    assert_eq!(
        eval_checked_binop(BinOp::Add, &i8_max, &i8_one, PtrWidth::Bits64).unwrap(),
        (0x80, true)
    );
    assert_eq!(
        eval_binop(BinOp::AddUnchecked, &i8_max, &i8_one, PtrWidth::Bits64),
        Err(RvalueEvalError::ArithmeticOverflow {
            op: BinOp::AddUnchecked
        })
    );

    // MIN - 1 wraps to MAX, overflows in checked, errors in unchecked
    let sub_wrap = eval_binop(BinOp::Sub, &i8_min, &i8_one, PtrWidth::Bits64).unwrap();
    assert_eq!(sub_wrap.as_signed(PtrWidth::Bits64), Some(127));
    assert_eq!(
        eval_checked_binop(BinOp::Sub, &i8_min, &i8_one, PtrWidth::Bits64).unwrap(),
        (0x7F, true)
    );
    assert_eq!(
        eval_binop(BinOp::SubUnchecked, &i8_min, &i8_one, PtrWidth::Bits64),
        Err(RvalueEvalError::ArithmeticOverflow {
            op: BinOp::SubUnchecked
        })
    );

    // MIN * -1 wraps to MIN, overflows in checked, errors in unchecked
    let mul_wrap = eval_binop(BinOp::Mul, &i8_min, &i8_neg_one, PtrWidth::Bits64).unwrap();
    assert_eq!(mul_wrap.as_signed(PtrWidth::Bits64), Some(-128));
    assert_eq!(
        eval_checked_binop(BinOp::Mul, &i8_min, &i8_neg_one, PtrWidth::Bits64).unwrap(),
        (0x80, true)
    );
    assert_eq!(
        eval_binop(BinOp::MulUnchecked, &i8_min, &i8_neg_one, PtrWidth::Bits64),
        Err(RvalueEvalError::ArithmeticOverflow {
            op: BinOp::MulUnchecked
        })
    );

    // 2. i128::MIN and u128::MAX boundaries
    let i128_min = MirValue::signed(i128::MIN, IntTy::I128, PtrWidth::Bits64);
    let i128_neg_one = MirValue::signed(-1, IntTy::I128, PtrWidth::Bits64);
    assert_eq!(
        eval_checked_binop(BinOp::Add, &i128_min, &i128_neg_one, PtrWidth::Bits64).unwrap(),
        (i128::MAX as u128, true)
    );
    assert_eq!(
        eval_checked_binop(BinOp::Mul, &i128_min, &i128_neg_one, PtrWidth::Bits64).unwrap(),
        (i128::MIN as u128, true)
    );

    let u128_max = MirValue::unsigned(u128::MAX, UintTy::U128, PtrWidth::Bits64);
    let u128_two = MirValue::unsigned(2, UintTy::U128, PtrWidth::Bits64);
    let u128_zero = MirValue::unsigned(0, UintTy::U128, PtrWidth::Bits64);
    assert_eq!(
        eval_checked_binop(BinOp::Mul, &u128_max, &u128_two, PtrWidth::Bits64).unwrap(),
        (u128::MAX.wrapping_mul(2), true)
    );
    assert_eq!(
        eval_checked_binop(BinOp::Sub, &u128_zero, &u128_two, PtrWidth::Bits64).unwrap(),
        (u128::MAX - 1, true)
    );

    // 3. Bits32 vs Bits64 isize::MIN and usize::MAX
    let isize32_min = MirValue::signed(i32::MIN as i128, IntTy::Isize, PtrWidth::Bits32);
    let isize32_neg1 = MirValue::signed(-1, IntTy::Isize, PtrWidth::Bits32);
    assert_eq!(
        eval_checked_binop(BinOp::Mul, &isize32_min, &isize32_neg1, PtrWidth::Bits32).unwrap(),
        (0x8000_0000, true)
    );
    assert_eq!(
        eval_binop(BinOp::MulUnchecked, &isize32_min, &isize32_neg1, PtrWidth::Bits32),
        Err(RvalueEvalError::ArithmeticOverflow {
            op: BinOp::MulUnchecked
        })
    );
}

#[test]
fn test_division_and_remainder_ub_and_sign_semantics() {
    // 1. Unsigned div/rem by zero
    let u32_ten = MirValue::unsigned(10, UintTy::U32, PtrWidth::Bits64);
    let u32_zero = MirValue::unsigned(0, UintTy::U32, PtrWidth::Bits64);
    assert_eq!(
        eval_binop(BinOp::Div, &u32_ten, &u32_zero, PtrWidth::Bits64),
        Err(RvalueEvalError::DivisionByZero)
    );
    assert_eq!(
        eval_binop(BinOp::Rem, &u32_ten, &u32_zero, PtrWidth::Bits64),
        Err(RvalueEvalError::DivisionByZero)
    );

    // 2. Signed INT_MIN / -1 and INT_MIN % -1 across i16, i128, and 32-bit isize
    let i16_min = MirValue::signed(i16::MIN as i128, IntTy::I16, PtrWidth::Bits64);
    let i16_neg1 = MirValue::signed(-1, IntTy::I16, PtrWidth::Bits64);
    assert_eq!(
        eval_binop(BinOp::Div, &i16_min, &i16_neg1, PtrWidth::Bits64),
        Err(RvalueEvalError::SignedDivisionOverflow {
            min_val: i16::MIN as i128,
            bit_width: 16
        })
    );
    assert_eq!(
        eval_binop(BinOp::Rem, &i16_min, &i16_neg1, PtrWidth::Bits64),
        Err(RvalueEvalError::SignedDivisionOverflow {
            min_val: i16::MIN as i128,
            bit_width: 16
        })
    );

    let i128_min = MirValue::signed(i128::MIN, IntTy::I128, PtrWidth::Bits64);
    let i128_neg1 = MirValue::signed(-1, IntTy::I128, PtrWidth::Bits64);
    assert_eq!(
        eval_binop(BinOp::Div, &i128_min, &i128_neg1, PtrWidth::Bits64),
        Err(RvalueEvalError::SignedDivisionOverflow {
            min_val: i128::MIN,
            bit_width: 128
        })
    );

    let isize32_min = MirValue::signed(i32::MIN as i128, IntTy::Isize, PtrWidth::Bits32);
    let isize32_neg1 = MirValue::signed(-1, IntTy::Isize, PtrWidth::Bits32);
    assert_eq!(
        eval_binop(BinOp::Rem, &isize32_min, &isize32_neg1, PtrWidth::Bits32),
        Err(RvalueEvalError::SignedDivisionOverflow {
            min_val: i32::MIN as i128,
            bit_width: 32
        })
    );

    // 3. Negative dividend / divisor signs:
    // -7 / 2 == -3, -7 % 2 == -1
    // 7 / -2 == -3, 7 % -2 == 1
    // -7 / -2 == 3, -7 % -2 == -1
    let cases = [
        (-7i128, 2i128, -3i128, -1i128),
        (7, -2, -3, 1),
        (-7, -2, 3, -1),
    ];
    for (a, b, expected_q, expected_r) in cases {
        let va = MirValue::signed(a, IntTy::I32, PtrWidth::Bits64);
        let vb = MirValue::signed(b, IntTy::I32, PtrWidth::Bits64);
        let q = eval_binop(BinOp::Div, &va, &vb, PtrWidth::Bits64).unwrap();
        let r = eval_binop(BinOp::Rem, &va, &vb, PtrWidth::Bits64).unwrap();
        assert_eq!(q.as_signed(PtrWidth::Bits64), Some(expected_q));
        assert_eq!(r.as_signed(PtrWidth::Bits64), Some(expected_r));
    }
}

#[test]
fn test_shifts_heterogeneous_rhs_and_unchecked_ub() {
    // Lowering allows LHS and RHS to have different integral types (e.g. u64 << i8)
    let local_decls = vec![Ty::Uint(UintTy::U64), Ty::Int(IntTy::I8)];
    let shl_rv = Rvalue::BinaryOp(
        BinOp::Shl,
        Operand::Copy(Place::from_local(0)),
        Operand::Copy(Place::from_local(1)),
    );
    let lowered = lower_rvalue(&shl_rv, &local_decls, PtrWidth::Bits64)
        .expect("u64 << i8 must lower cleanly");
    assert_eq!(lowered.ty(), &Ty::Uint(UintTy::U64));

    // Dynamic evaluation:
    let neg_16_i8 = MirValue::signed(-16, IntTy::I8, PtrWidth::Bits64);
    let pos_2_u128 = MirValue::unsigned(2, UintTy::U128, PtrWidth::Bits64);
    let neg_1_i8 = MirValue::signed(-1, IntTy::I8, PtrWidth::Bits64);
    let pos_8_u8 = MirValue::unsigned(8, UintTy::U8, PtrWidth::Bits64);

    // Arithmetic right shift on i8: -16 >> 2 == -4
    let shr_res = eval_binop(BinOp::Shr, &neg_16_i8, &pos_2_u128, PtrWidth::Bits64).unwrap();
    assert_eq!(shr_res.as_signed(PtrWidth::Bits64), Some(-4));

    // Wrapping shift with negative signed RHS (-1i8 == 0xFF, masked by 7 == 7): -16i8 >> 7 == -1i8
    let wrapped_neg_shr = eval_binop(BinOp::Shr, &neg_16_i8, &neg_1_i8, PtrWidth::Bits64).unwrap();
    assert_eq!(wrapped_neg_shr.as_signed(PtrWidth::Bits64), Some(-1));

    // Checked shift reports overflowed == true on negative signed RHS or RHS >= bit_width
    let (chk_bits, chk_ov) =
        eval_checked_binop(BinOp::Shr, &neg_16_i8, &neg_1_i8, PtrWidth::Bits64).unwrap();
    assert!(chk_ov);
    assert_eq!(chk_bits, 0xFF);

    let (_, chk_ov_8) =
        eval_checked_binop(BinOp::Shl, &neg_16_i8, &pos_8_u8, PtrWidth::Bits64).unwrap();
    assert!(chk_ov_8);

    // Unchecked shift returns ShiftOverflow on negative signed RHS or RHS >= bit_width
    assert!(matches!(
        eval_binop(BinOp::ShrUnchecked, &neg_16_i8, &neg_1_i8, PtrWidth::Bits64),
        Err(RvalueEvalError::ShiftOverflow {
            rhs_signed: Some(-1),
            lhs_bit_width: 8,
            ..
        })
    ));
    assert!(matches!(
        eval_binop(BinOp::ShlUnchecked, &neg_16_i8, &pos_8_u8, PtrWidth::Bits64),
        Err(RvalueEvalError::ShiftOverflow {
            rhs_signed: None,
            lhs_bit_width: 8,
            ..
        })
    ));
}

#[test]
fn test_comparisons_and_three_way_cmp() {
    // Signed vs unsigned comparison of 0xFF (-1i8 vs 255u8) against 1
    let neg_one_i8 = MirValue::signed(-1, IntTy::I8, PtrWidth::Bits64);
    let pos_one_i8 = MirValue::signed(1, IntTy::I8, PtrWidth::Bits64);
    let max_u8 = MirValue::unsigned(255, UintTy::U8, PtrWidth::Bits64);
    let one_u8 = MirValue::unsigned(1, UintTy::U8, PtrWidth::Bits64);

    assert_eq!(
        eval_binop(BinOp::Lt, &neg_one_i8, &pos_one_i8, PtrWidth::Bits64).unwrap(),
        MirValue::Bool(true)
    );
    assert_eq!(
        eval_binop(BinOp::Lt, &max_u8, &one_u8, PtrWidth::Bits64).unwrap(),
        MirValue::Bool(false)
    );

    // Three-way Cmp returns -1i8, 0i8, 1i8
    let cmp_lt = eval_binop(BinOp::Cmp, &neg_one_i8, &pos_one_i8, PtrWidth::Bits64).unwrap();
    let cmp_eq = eval_binop(BinOp::Cmp, &pos_one_i8, &pos_one_i8, PtrWidth::Bits64).unwrap();
    let cmp_gt = eval_binop(BinOp::Cmp, &pos_one_i8, &neg_one_i8, PtrWidth::Bits64).unwrap();
    assert_eq!(cmp_lt.as_signed(PtrWidth::Bits64), Some(-1));
    assert_eq!(cmp_eq.as_signed(PtrWidth::Bits64), Some(0));
    assert_eq!(cmp_gt.as_signed(PtrWidth::Bits64), Some(1));

    // Cmp rejects pointers during lowering
    let ptr_ty = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let local_decls = vec![ptr_ty.clone(), ptr_ty];
    let cmp_ptrs = Rvalue::BinaryOp(
        BinOp::Cmp,
        Operand::Copy(Place::from_local(0)),
        Operand::Copy(Place::from_local(1)),
    );
    assert!(matches!(
        lower_rvalue(&cmp_ptrs, &local_decls, PtrWidth::Bits64),
        Err(RvalueLowerError::BinaryTypeMismatch { op: BinOp::Cmp, .. })
    ));
}

#[test]
fn test_aggregates_and_pointer_offset() {
    let u32_ty = Ty::Uint(UintTy::U32);
    let u8_ty = Ty::Uint(UintTy::U8);
    let unit_ty = Ty::unit();
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty.clone()), Mutability::Mut);
    let local_decls = vec![
        u32_ty.clone(),
        u32_ty.clone(),
        u8_ty.clone(),
        raw_u32.clone(),
        unit_ty.clone(),
    ];

    // 1. Array aggregate with matching elements vs mismatched element
    let arr_ok = Rvalue::Aggregate(
        AggregateKind::Array(u32_ty.clone()),
        vec![
            Operand::Copy(Place::from_local(0)),
            Operand::Copy(Place::from_local(1)),
        ],
    );
    let lowered_arr = lower_rvalue(&arr_ok, &local_decls, PtrWidth::Bits64).unwrap();
    assert_eq!(lowered_arr.ty(), &Ty::Array(Box::new(u32_ty.clone()), 2));

    let arr_bad = Rvalue::Aggregate(
        AggregateKind::Array(u32_ty.clone()),
        vec![
            Operand::Copy(Place::from_local(0)),
            Operand::Copy(Place::from_local(2)),
        ],
    );
    assert_eq!(
        lower_rvalue(&arr_bad, &local_decls, PtrWidth::Bits64),
        Err(RvalueLowerError::AggregateElementTypeMismatch {
            expected: u32_ty.clone(),
            got: u8_ty.clone(),
        })
    );

    // 2. Adt struct (multiple fields) vs union (active_field: Some(0) requires 1 operand)
    let adt_struct = Rvalue::Aggregate(
        AggregateKind::Adt {
            def_path: "MyStruct".into(),
            variant_idx: 0,
            active_field: None,
        },
        vec![
            Operand::Copy(Place::from_local(0)),
            Operand::Copy(Place::from_local(2)),
        ],
    );
    let lowered_struct = lower_rvalue(&adt_struct, &local_decls, PtrWidth::Bits64).unwrap();
    assert_eq!(
        lowered_struct.ty(),
        &Ty::Tuple(vec![u32_ty.clone(), u8_ty.clone()])
    );

    let adt_union_ok = Rvalue::Aggregate(
        AggregateKind::Adt {
            def_path: "MyUnion".into(),
            variant_idx: 0,
            active_field: Some(0),
        },
        vec![Operand::Copy(Place::from_local(0))],
    );
    assert!(lower_rvalue(&adt_union_ok, &local_decls, PtrWidth::Bits64).is_ok());

    let adt_union_bad = Rvalue::Aggregate(
        AggregateKind::Adt {
            def_path: "MyUnion".into(),
            variant_idx: 0,
            active_field: Some(0),
        },
        vec![
            Operand::Copy(Place::from_local(0)),
            Operand::Copy(Place::from_local(1)),
        ],
    );
    assert!(matches!(
        lower_rvalue(&adt_union_bad, &local_decls, PtrWidth::Bits64),
        Err(RvalueLowerError::InvalidAggregateOperands { count: 2, .. })
    ));

    // 3. RawPtr aggregate construction and PtrMetadata unary op
    let raw_ptr_agg = Rvalue::Aggregate(
        AggregateKind::RawPtr {
            pointee: u32_ty.clone(),
            mutability: Mutability::Mut,
        },
        vec![
            Operand::Copy(Place::from_local(3)),
            Operand::Copy(Place::from_local(4)),
        ],
    );
    let lowered_raw_ptr = lower_rvalue(&raw_ptr_agg, &local_decls, PtrWidth::Bits64).unwrap();
    assert_eq!(lowered_raw_ptr.ty(), &raw_u32);

    let ptr_meta_rv = Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::from_local(3)));
    let lowered_meta = lower_rvalue(&ptr_meta_rv, &local_decls, PtrWidth::Bits64).unwrap();
    assert_eq!(lowered_meta.ty(), &unit_ty);

    let ptr_val = MirValue::ptr(PointerValue::with_provenance(0x2000, 9, 3), raw_u32.clone());
    let meta_val = eval_unop(UnOp::PtrMetadata, &ptr_val, PtrWidth::Bits64).unwrap();
    assert!(meta_val.is_unit());

    let built_ptr = eval_aggregate(
        &AggregateKind::RawPtr {
            pointee: u32_ty.clone(),
            mutability: Mutability::Mut,
        },
        vec![ptr_val.clone(), meta_val],
        PtrWidth::Bits64,
    )
    .unwrap();
    assert_eq!(built_ptr, ptr_val);

    // 4. Offset with negative isize stride on both 32-bit and 64-bit
    for ptr_width in [PtrWidth::Bits32, PtrWidth::Bits64] {
        let neg_three = MirValue::signed(-3, IntTy::Isize, ptr_width);
        let shifted_ptr = eval_binop(BinOp::Offset, &ptr_val, &neg_three, ptr_width).unwrap();
        let out = shifted_ptr.as_ptr().unwrap();
        assert_eq!(out.addr, 0x2000 - 3 * 4);
        assert_eq!(out.provenance, ptr_val.as_ptr().unwrap().provenance);

        // Underflow past address 0 is flagged as PointerOffsetOverflow
        let huge_neg = MirValue::signed(-0x1000, IntTy::Isize, ptr_width);
        assert!(matches!(
            eval_binop(BinOp::Offset, &ptr_val, &huge_neg, ptr_width),
            Err(RvalueEvalError::PointerOffsetOverflow { .. })
        ));
    }
}

#[test]
fn test_place_projections_statement_and_body_lowering() {
    let u32_ty = Ty::Uint(UintTy::U32);
    let usize_ty = Ty::Uint(UintTy::Usize);
    let arr_ty = Ty::Array(Box::new(u32_ty.clone()), 4);
    let tuple_ty = Ty::Tuple(vec![u32_ty.clone(), arr_ty.clone()]);
    let ref_tuple_ty = Ty::Ref(Box::new(tuple_ty.clone()), Mutability::Not);

    let local_decls = vec![
        u32_ty.clone(),       // _0: return place u32
        ref_tuple_ty.clone(), // _1: &(u32, [u32; 4])
        usize_ty.clone(),     // _2: usize index
        Ty::Array(Box::new(u32_ty.clone()), 2), // _3: subslice [u32; 2]
    ];

    // (*_1).1[_2] -> u32
    let elem_place = Place::with_projection(
        1,
        vec![
            ProjectionElem::Deref,
            ProjectionElem::Field(1, arr_ty.clone()),
            ProjectionElem::Index(Local(2)),
        ],
    );
    assert_eq!(resolve_place_ty(&elem_place, &local_decls).unwrap(), u32_ty);

    // (*_1).1[1..3] -> [u32; 2]
    let subslice_place = Place::with_projection(
        1,
        vec![
            ProjectionElem::Deref,
            ProjectionElem::Field(1, arr_ty),
            ProjectionElem::Subslice {
                from: 1,
                to: 3,
                from_end: false,
            },
        ],
    );
    assert_eq!(
        resolve_place_ty(&subslice_place, &local_decls).unwrap(),
        Ty::Array(Box::new(u32_ty.clone()), 2)
    );

    // Lower a complete MIR Body
    let body = Body {
        local_decls: local_decls.clone(),
        basic_blocks: vec![BasicBlockData {
            statements: vec![
                Statement::StorageLive(Local(2)),
                Statement::Assign(
                    Place::from_local(2),
                    Rvalue::Len(Place::from_local(3)),
                ),
                Statement::Assign(
                    Place::from_local(0),
                    Rvalue::Use(Operand::Copy(elem_place)),
                ),
                Statement::StorageDead(Local(2)),
                Statement::Nop,
            ],
            is_cleanup: false,
        }],
    };

    let lowered_body = lower_body(&body, PtrWidth::Bits64).expect("body must lower cleanly");
    assert_eq!(lowered_body.basic_blocks.len(), 1);
    assert_eq!(lowered_body.basic_blocks[0].statements.len(), 5);

    // Evaluate Rvalue::Len via eval_lowered_rvalue
    let mut tracker = ExposedProvenanceTracker::new();
    if let LoweredStatement::Assign { rvalue, .. } = &lowered_body.basic_blocks[0].statements[1] {
        assert!(matches!(rvalue, LoweredRvalue::Len { static_len: 2, .. }));
        let len_val = eval_lowered_rvalue(
            rvalue,
            &[],
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &mut tracker,
        )
        .unwrap();
        assert_eq!(len_val.as_bits(), Some(2));
    } else {
        panic!("expected LoweredStatement::Assign");
    }

    // Type mismatch in Statement::Assign must fail
    let bad_stmt = Statement::Assign(
        Place::from_local(0),
        Rvalue::Use(Operand::Constant(Constant::Bool(true))),
    );
    assert_eq!(
        lower_statement(&bad_stmt, &local_decls, PtrWidth::Bits64),
        Err(RvalueLowerError::AssignmentTypeMismatch {
            place_ty: u32_ty.clone(),
            rvalue_ty: Ty::Bool,
        })
    );

    // Lower and evaluate Rvalue::Cast(CastKind::Transmute) via lower_rvalue & eval_lowered_rvalue
    let transmute_rv = Rvalue::Cast(
        CastKind::Transmute,
        Operand::Constant(Constant::Int(0x0000_0041, u32_ty)),
        Ty::Char,
    );
    let lowered_transmute = lower_rvalue(&transmute_rv, &local_decls, PtrWidth::Bits64).unwrap();
    let char_val = eval_lowered_rvalue(
        &lowered_transmute,
        &[],
        PtrWidth::Bits64,
        TransmutePolicy::RejectPtrToInt,
        &mut tracker,
    )
    .unwrap();
    assert_eq!(char_val, MirValue::Char('A'));
}
