//! Integration tests for MIR `Rvalue`, `Statement`, and `Body` lowering and dynamic evaluation.

use anneal_mir::ir::{
    AggregateKind, BasicBlockData, BinOp, Body, CastKind, Constant, IntTy, Local, Mutability,
    NullOp, Operand, Place, PointerValue, ProjectionElem, PtrWidth, Rvalue, Statement, Ty, UintTy,
    UnOp,
};
use anneal_mir::lower::{
    CastEvalError, CastLowerError, ExposedProvenanceTracker, LocalSlotState,
    LoweredCast, LoweredRvalue, LoweredStatement, MirValue, RvalueEvalError, RvalueLowerError,
    StatementEvalState, TransmutePolicy, eval_aggregate, eval_binop, eval_checked_binop,
    eval_constant, eval_lowered_block, eval_lowered_cast, eval_lowered_rvalue,
    eval_lowered_statement, eval_nullary_op, eval_place_read, eval_place_write, eval_unop,
    lower_body, lower_rvalue, lower_rvalue_with_policy, lower_statement, resolve_offset_of,
    resolve_place_ty,
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
            adt_def: None,
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
            adt_def: None,
        },
        vec![Operand::Copy(Place::from_local(0))],
    );
    assert!(lower_rvalue(&adt_union_ok, &local_decls, PtrWidth::Bits64).is_ok());

    let adt_union_bad = Rvalue::Aggregate(
        AggregateKind::Adt {
            def_path: "MyUnion".into(),
            variant_idx: 0,
            active_field: Some(0),
            adt_def: None,
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
            terminator: None,
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

// ---------------------------------------------------------------------------------------------
// [adv B1] regression tests
// ---------------------------------------------------------------------------------------------

fn eval_rv(
    rvalue: &Rvalue,
    local_decls: &[Ty],
    locals: &[MirValue],
    ptr_width: PtrWidth,
    policy: TransmutePolicy,
    tracker: &mut ExposedProvenanceTracker,
) -> Result<MirValue, RvalueEvalError> {
    let lowered = lower_rvalue_with_policy(rvalue, local_decls, ptr_width, policy)
        .expect("rvalue must lower");
    eval_lowered_rvalue(&lowered, locals, ptr_width, policy, tracker)
}

#[test]
fn test_b1_aggregate_transmutes_evaluate_to_typed_values() {
    let pw = PtrWidth::Bits64;
    let policy = TransmutePolicy::RejectPtrToInt;
    let mut tracker = ExposedProvenanceTracker::new();
    let u8_ty = Ty::Uint(UintTy::U8);
    let u16_ty = Ty::Uint(UintTy::U16);
    let u32_ty = Ty::Uint(UintTy::U32);
    let arr_u8_4 = Ty::Array(Box::new(u8_ty.clone()), 4);
    let local_decls = vec![arr_u8_4.clone(), u32_ty.clone()];
    let locals = vec![
        MirValue::Array {
            elements: [0x11, 0x22, 0x33, 0x44]
                .into_iter()
                .map(|b| MirValue::unsigned(b, UintTy::U8, pw))
                .collect(),
            elem_ty: u8_ty.clone(),
        },
        MirValue::unsigned(0x0100_0001, UintTy::U32, pw),
    ];
    let transmute = |operand: Operand, target: Ty| Rvalue::Cast(CastKind::Transmute, operand, target);

    // [u8; 4] -> u32 (A0: TypeMismatch, aggregate operands were unsupported).
    assert_eq!(
        eval_rv(
            &transmute(Operand::Copy(Place::from_local(0)), u32_ty.clone()),
            &local_decls,
            &locals,
            pw,
            policy,
            &mut tracker
        ),
        Ok(MirValue::unsigned(0x4433_2211, UintTy::U32, pw))
    );

    // u32 -> (u16, u16) yields a typed tuple (A0: a tuple of four u8 bytes).
    let pair = Ty::Tuple(vec![u16_ty.clone(), u16_ty.clone()]);
    let pair_val = eval_rv(
        &transmute(Operand::Copy(Place::from_local(1)), pair.clone()),
        &local_decls,
        &locals,
        pw,
        policy,
        &mut tracker,
    )
    .unwrap();
    assert_eq!(
        pair_val,
        MirValue::Tuple(vec![
            MirValue::unsigned(0x0001, UintTy::U16, pw),
            MirValue::unsigned(0x0100, UintTy::U16, pw),
        ])
    );
    assert_eq!(pair_val.ty(), pair);

    // u32 -> [bool; 4] yields an array of bools (A0: a tuple of u8 bytes).
    let arr_bool_4 = Ty::Array(Box::new(Ty::Bool), 4);
    let bools = eval_rv(
        &transmute(Operand::Copy(Place::from_local(1)), arr_bool_4.clone()),
        &local_decls,
        &locals,
        pw,
        policy,
        &mut tracker,
    )
    .unwrap();
    assert_eq!(
        bools,
        MirValue::Array {
            elements: vec![
                MirValue::Bool(true),
                MirValue::Bool(false),
                MirValue::Bool(false),
                MirValue::Bool(true),
            ],
            elem_ty: Ty::Bool,
        }
    );
    assert_eq!(bools.ty(), arr_bool_4);

    // [u8; 4] -> [bool; 4] with byte 0x11 is an invalid bool.
    assert_eq!(
        eval_rv(
            &transmute(Operand::Copy(Place::from_local(0)), arr_bool_4),
            &local_decls,
            &locals,
            pw,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: Ty::Bool,
            bits: 0x11,
        }))
    );

    // () -> [!; 0] yields an empty array of `!` (A0: an empty tuple).
    let never_arr = Ty::Array(Box::new(Ty::Never), 0);
    assert_eq!(
        eval_rv(
            &transmute(Operand::Constant(Constant::Unit), never_arr),
            &local_decls,
            &locals,
            pw,
            policy,
            &mut tracker
        ),
        Ok(MirValue::Array {
            elements: vec![],
            elem_ty: Ty::Never,
        })
    );

    // A value whose runtime type disagrees with the operand's declared type is rejected.
    let wrong_locals = vec![locals[0].clone(), MirValue::unsigned(1, UintTy::U16, pw)];
    assert!(matches!(
        eval_rv(
            &transmute(Operand::Copy(Place::from_local(1)), pair),
            &local_decls,
            &wrong_locals,
            pw,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(tracker.is_empty());
}

#[test]
fn test_b1_pointer_aggregate_transmutes_preserve_or_strip_provenance() {
    let pw = PtrWidth::Bits64;
    let mut tracker = ExposedProvenanceTracker::new();
    let usize_ty = Ty::Uint(UintTy::Usize);
    let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let pair = Ty::Tuple(vec![raw_u8.clone(), usize_ty.clone()]);
    let local_decls = vec![raw_u8.clone(), pair.clone()];
    let p0 = PointerValue::with_provenance(0x1000, 5, 6);
    let p1 = PointerValue::with_provenance(0x2000, 7, 8);
    let locals = vec![
        MirValue::ptr(p0, raw_u8.clone()),
        MirValue::Tuple(vec![
            MirValue::ptr(p1, raw_u8.clone()),
            MirValue::unsigned(0x3000, UintTy::Usize, pw),
        ]),
    ];

    // *const u8 -> [*const u8; 1] keeps the provenance under the default policy.
    let arr_raw = Ty::Array(Box::new(raw_u8.clone()), 1);
    let wrapped = eval_rv(
        &Rvalue::Cast(CastKind::Transmute, Operand::Copy(Place::from_local(0)), arr_raw),
        &local_decls,
        &locals,
        pw,
        TransmutePolicy::RejectPtrToInt,
        &mut tracker,
    )
    .unwrap();
    assert_eq!(
        wrapped,
        MirValue::Array {
            elements: vec![MirValue::ptr(p0, raw_u8.clone())],
            elem_ty: raw_u8.clone(),
        }
    );

    // (*const u8, usize) -> [usize; 2] is Ptr -> Int: rejected by default ...
    let arr_usize_2 = Ty::Array(Box::new(usize_ty), 2);
    let to_words = Rvalue::Cast(
        CastKind::Transmute,
        Operand::Copy(Place::from_local(1)),
        arr_usize_2.clone(),
    );
    assert_eq!(
        lower_rvalue(&to_words, &local_decls, pw),
        Err(RvalueLowerError::CastError(
            CastLowerError::PtrToIntTransmuteDisallowed {
                src_ty: pair,
                target_ty: arr_usize_2,
            }
        ))
    );
    // ... and strips provenance without exposing it under AllowPtrToIntStripProvenance.
    assert_eq!(
        eval_rv(
            &to_words,
            &local_decls,
            &locals,
            pw,
            TransmutePolicy::AllowPtrToIntStripProvenance,
            &mut tracker
        ),
        Ok(MirValue::Array {
            elements: vec![
                MirValue::unsigned(0x2000, UintTy::Usize, pw),
                MirValue::unsigned(0x3000, UintTy::Usize, pw),
            ],
            elem_ty: Ty::Uint(UintTy::Usize),
        })
    );
    assert!(tracker.is_empty());
}

#[test]
fn test_b1_offset_byte_offset_bounds_provenance_and_strides() {
    let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let base = MirValue::ptr(PointerValue::with_provenance(0x1000, 1, 1), raw_u8.clone());

    // usize counts: byte offset must fit in isize even when the address would not wrap.
    // (A0 accepted both of these.)
    let over32 = MirValue::unsigned(0x8000_0000, UintTy::Usize, PtrWidth::Bits32);
    assert!(matches!(
        eval_binop(BinOp::Offset, &base, &over32, PtrWidth::Bits32),
        Err(RvalueEvalError::PointerOffsetOverflow { .. })
    ));
    let over64 = MirValue::unsigned(1 << 63, UintTy::Usize, PtrWidth::Bits64);
    assert!(matches!(
        eval_binop(BinOp::Offset, &base, &over64, PtrWidth::Bits64),
        Err(RvalueEvalError::PointerOffsetOverflow { .. })
    ));
    let max_ok = MirValue::unsigned(0x7FFF_E000, UintTy::Usize, PtrWidth::Bits32);
    assert_eq!(
        eval_binop(BinOp::Offset, &base, &max_ok, PtrWidth::Bits32)
            .unwrap()
            .as_ptr(),
        Some(PointerValue::with_provenance(0x7FFF_F000, 1, 1))
    );

    // Non-zero offsets require provenance; offsetting by 0 bytes is always allowed.
    let bare = MirValue::ptr(PointerValue::without_provenance(0x1000), raw_u8.clone());
    assert_eq!(
        eval_binop(
            BinOp::Offset,
            &bare,
            &MirValue::unsigned(1, UintTy::Usize, PtrWidth::Bits64),
            PtrWidth::Bits64
        ),
        Err(RvalueEvalError::PointerArithmeticWithoutProvenance {
            addr: 0x1000,
            byte_offset: 1,
        })
    );
    assert_eq!(
        eval_binop(
            BinOp::Offset,
            &bare,
            &MirValue::signed(0, IntTy::Isize, PtrWidth::Bits64),
            PtrWidth::Bits64
        )
        .unwrap()
        .as_ptr(),
        Some(PointerValue::without_provenance(0x1000))
    );

    // `*const (u8, u32)` advances by rustc's 8-byte size (A0: 5 bytes).
    let padded = Ty::Tuple(vec![Ty::Uint(UintTy::U8), Ty::Uint(UintTy::U32)]);
    let raw_padded = Ty::RawPtr(Box::new(padded), Mutability::Not);
    let one = Operand::Constant(Constant::Int(1, Ty::Uint(UintTy::Usize)));
    let offset_rv = Rvalue::BinaryOp(BinOp::Offset, Operand::Copy(Place::from_local(0)), one);
    let lowered =
        lower_rvalue(&offset_rv, std::slice::from_ref(&raw_padded), PtrWidth::Bits64).unwrap();
    assert!(matches!(
        lowered,
        LoweredRvalue::BinaryOp {
            pointee_size: Some(8),
            ..
        }
    ));
    let mut tracker = ExposedProvenanceTracker::new();
    let padded_ptr = MirValue::ptr(PointerValue::with_provenance(0x1000, 2, 2), raw_padded);
    assert_eq!(
        eval_lowered_rvalue(
            &lowered,
            &[padded_ptr],
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &mut tracker
        )
        .unwrap()
        .as_ptr(),
        Some(PointerValue::with_provenance(0x1008, 2, 2))
    );

    // Uninhabited pointees still have a layout-size stride (rustc accepts `<*const !>::add`).
    for (pointee, stride) in [
        (Ty::Never, 0),
        (Ty::Tuple(vec![Ty::Never, Ty::Uint(UintTy::U32)]), 4),
    ] {
        let raw = Ty::RawPtr(Box::new(pointee), Mutability::Not);
        let lowered = lower_rvalue(&offset_rv, &[raw], PtrWidth::Bits64).unwrap();
        assert!(matches!(
            lowered,
            LoweredRvalue::BinaryOp { pointee_size: Some(s), .. } if s == stride
        ));
    }
}

#[test]
fn test_b1_place_projection_type_checks_survive_downcast() {
    let u8_ty = Ty::Uint(UintTy::U8);
    let u16_ty = Ty::Uint(UintTy::U16);
    let u32_ty = Ty::Uint(UintTy::U32);
    let u128_ty = Ty::Uint(UintTy::U128);
    let local_decls = vec![
        Ty::Tuple(vec![u8_ty, u16_ty.clone()]),
        Ty::Array(Box::new(u32_ty.clone()), 4),
    ];

    let downcast_field = |idx: usize, ty: Ty| {
        Place::with_projection(0, vec![ProjectionElem::Downcast(0), ProjectionElem::Field(idx, ty)])
    };
    assert_eq!(resolve_place_ty(&downcast_field(1, u16_ty), &local_decls), Ok(Ty::Uint(UintTy::U16)));
    // A0 accepted any type / index for a field projection after `Downcast`.
    assert!(matches!(
        resolve_place_ty(&downcast_field(1, u128_ty.clone()), &local_decls),
        Err(RvalueLowerError::InvalidProjection { .. })
    ));
    assert!(matches!(
        resolve_place_ty(&downcast_field(5, u128_ty), &local_decls),
        Err(RvalueLowerError::InvalidProjection { .. })
    ));
    // Arrays have no fields in MIR (A0 accepted `_1.0: u32`).
    let array_field = Place::with_projection(1, vec![ProjectionElem::Field(0, u32_ty)]);
    assert!(matches!(
        resolve_place_ty(&array_field, &local_decls),
        Err(RvalueLowerError::InvalidProjection { .. })
    ));
    // Downcast of a non-ADT (array) place is invalid.
    let array_downcast = Place::with_projection(1, vec![ProjectionElem::Downcast(0)]);
    assert!(matches!(
        resolve_place_ty(&array_downcast, &local_decls),
        Err(RvalueLowerError::InvalidProjection { .. })
    ));
}

#[test]
fn test_b1_union_aggregates_check_variant_and_destination_field() {
    let pw = PtrWidth::Bits64;
    let u16_ty = Ty::Uint(UintTy::U16);
    let u32_ty = Ty::Uint(UintTy::U32);
    // `union U { a: u32, b: u16 }`, modeled as the tuple of its declared field types.
    let union_ty = Ty::Tuple(vec![u32_ty, u16_ty.clone()]);
    let local_decls = vec![union_ty, u16_ty];
    let union_init = |variant_idx: usize, field: usize| {
        Rvalue::Aggregate(
            AggregateKind::Adt {
                def_path: "U".into(),
                variant_idx,
                active_field: Some(field),
                adt_def: None,
            },
            vec![Operand::Copy(Place::from_local(1))],
        )
    };
    let assign = |place: usize, rv: Rvalue| Statement::Assign(Place::from_local(place), rv);

    assert!(lower_statement(&assign(0, union_init(0, 1)), &local_decls, pw).is_ok());
    // Unions are single-variant ADTs: rustc requires FIRST_VARIANT.
    assert!(matches!(
        lower_rvalue(&union_init(1, 1), &local_decls, pw),
        Err(RvalueLowerError::InvalidAggregateOperands { count: 1, .. })
    ));
    assert!(matches!(
        eval_aggregate(
            &AggregateKind::Adt {
                def_path: "U".into(),
                variant_idx: 1,
                active_field: Some(1),
                adt_def: None,
            },
            vec![MirValue::unsigned(7, UintTy::U16, pw)],
            pw,
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    // The active field's declared type must match the operand (field 0 is u32, operand u16).
    assert!(matches!(
        lower_statement(&assign(0, union_init(0, 0)), &local_decls, pw),
        Err(RvalueLowerError::AssignmentTypeMismatch { .. })
    ));
    // Out-of-range active field.
    assert!(matches!(
        lower_statement(&assign(0, union_init(0, 5)), &local_decls, pw),
        Err(RvalueLowerError::AssignmentTypeMismatch { .. })
    ));
    // A0 accepted assigning a union initializer with an arbitrary (unchecked) active field
    // index to a place of the operand's own type.
    assert!(matches!(
        lower_statement(&assign(1, union_init(0, 7)), &local_decls, pw),
        Err(RvalueLowerError::AssignmentTypeMismatch { .. })
    ));
}

#[test]
fn test_b1_raw_ptr_aggregate_operand_checks() {
    let pw = PtrWidth::Bits64;
    let u32_ty = Ty::Uint(UintTy::U32);
    let raw_mut = Ty::RawPtr(Box::new(u32_ty.clone()), Mutability::Mut);
    let local_decls = vec![
        raw_mut.clone(),
        Ty::RawPtr(Box::new(u32_ty.clone()), Mutability::Not),
        Ty::Ref(Box::new(u32_ty.clone()), Mutability::Mut),
        Ty::Uint(UintTy::Usize),
        u32_ty.clone(),
        Ty::unit(),
    ];
    let kind = AggregateKind::RawPtr {
        pointee: u32_ty.clone(),
        mutability: Mutability::Mut,
    };
    let build = |data: usize| {
        Rvalue::Aggregate(
            kind.clone(),
            vec![Operand::Copy(Place::from_local(data)), Operand::Copy(Place::from_local(5))],
        )
    };

    assert_eq!(lower_rvalue(&build(0), &local_decls, pw).unwrap().ty(), &raw_mut);
    assert_eq!(lower_rvalue(&build(3), &local_decls, pw).unwrap().ty(), &raw_mut);
    // Mutability mismatch, references, and non-usize integers are rejected (rustc validator).
    for bad in [1, 2, 4] {
        assert!(
            matches!(
                lower_rvalue(&build(bad), &local_decls, pw),
                Err(RvalueLowerError::InvalidAggregateOperands { count: 2, .. })
            ),
            "data operand _{bad} must be rejected"
        );
    }
    // Evaluation mirrors lowering: a usize address yields a pointer without provenance ...
    assert_eq!(
        eval_aggregate(
            &kind,
            vec![MirValue::unsigned(0x40, UintTy::Usize, pw), MirValue::Unit],
            pw
        ),
        Ok(MirValue::ptr(PointerValue::without_provenance(0x40), raw_mut))
    );
    // ... while mismatched mutability and non-usize addresses are rejected.
    let const_ptr = MirValue::ptr(
        PointerValue::with_provenance(0x40, 1, 1),
        Ty::RawPtr(Box::new(u32_ty), Mutability::Not),
    );
    assert!(eval_aggregate(&kind, vec![const_ptr, MirValue::Unit], pw).is_err());
    assert!(
        eval_aggregate(
            &kind,
            vec![MirValue::unsigned(0x40, UintTy::U32, pw), MirValue::Unit],
            pw
        )
        .is_err()
    );
}

#[test]
fn test_b1_place_evaluation_respects_projections() {
    let pw = PtrWidth::Bits64;
    let policy = TransmutePolicy::RejectPtrToInt;
    let mut tracker = ExposedProvenanceTracker::new();
    let u32_ty = Ty::Uint(UintTy::U32);
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty.clone()), Mutability::Mut);
    let inner = Ty::Tuple(vec![]);
    let outer = Ty::Tuple(vec![inner.clone()]);
    let local_decls = vec![
        Ty::Tuple(vec![u32_ty.clone(), u32_ty.clone()]),
        raw_u32.clone(),
        raw_u32.clone(),
        outer.clone(),
    ];
    let p = PointerValue::with_provenance(0x4000, 9, 9);
    let locals = vec![
        MirValue::Tuple(vec![
            MirValue::unsigned(1, UintTy::U32, pw),
            MirValue::unsigned(2, UintTy::U32, pw),
        ]),
        MirValue::ptr(p, raw_u32.clone()),
        MirValue::ptr(PointerValue::without_provenance(0), raw_u32.clone()),
        MirValue::Adt {
            def_path: "Outer".into(),
            variant_idx: 3,
            active_field: None,
            fields: vec![MirValue::Adt {
                def_path: "Inner".into(),
                variant_idx: 1,
                active_field: None,
                fields: vec![],
                adt_def: None,
            }],
            adt_def: None,
        },
    ];
    let deref = |local: usize| Place::with_projection(local, vec![ProjectionElem::Deref]);

    // `&raw mut (*_1)` and `&(*_1)` reborrow `_1`: same address and provenance.
    assert_eq!(
        eval_rv(&Rvalue::RawPtr(Mutability::Mut, deref(1)), &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::ptr(p, raw_u32.clone()))
    );
    let ref_u32 = Ty::Ref(Box::new(u32_ty.clone()), Mutability::Not);
    assert_eq!(
        eval_rv(&Rvalue::Ref(Mutability::Not, deref(1)), &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::ptr(p, ref_u32.clone()))
    );
    // `&(*null)` is a null reference (UB); `&raw const (*null)` is fine.
    assert_eq!(
        eval_rv(&Rvalue::Ref(Mutability::Not, deref(2)), &local_decls, &locals, pw, policy, &mut tracker),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ref_u32,
            bits: 0,
        }))
    );
    assert!(
        eval_rv(&Rvalue::RawPtr(Mutability::Not, deref(2)), &local_decls, &locals, pw, policy, &mut tracker)
            .is_ok()
    );
    // A0 returned `&_0`'s synthetic address for `&_0.1` (and for every other projection).
    let field1 = Place::with_projection(0, vec![ProjectionElem::Field(1, u32_ty)]);
    assert_eq!(
        eval_rv(&Rvalue::Ref(Mutability::Not, field1.clone()), &local_decls, &locals, pw, policy, &mut tracker),
        Err(RvalueEvalError::UnsupportedPlaceProjection(field1))
    );
    // A0 returned the *base local's* discriminant (3) for `discriminant(_3.0)` (truly 1).
    // Without `Downcast(3)`, projecting field 0 of `Outer` (variant 3) is an inactive-variant UB;
    // with `Downcast(3)`, `discriminant((_3 as variant#3).0)` evaluates to the inner variant `1`,
    // and dereferenced discriminant `discriminant(*_1)` requires a memory model.
    let inner_place = Place::with_projection(3, vec![ProjectionElem::Field(0, inner.clone())]);
    assert_eq!(
        eval_rv(&Rvalue::Discriminant(inner_place), &local_decls, &locals, pw, policy, &mut tracker),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 0,
            actual: 3,
        })
    );
    let downcast_inner_place = Place::with_projection(
        3,
        vec![ProjectionElem::Downcast(3), ProjectionElem::Field(0, inner)],
    );
    assert_eq!(
        eval_rv(
            &Rvalue::Discriminant(downcast_inner_place),
            &local_decls,
            &locals,
            pw,
            policy,
            &mut tracker
        ),
        Ok(MirValue::signed(1, IntTy::Isize, pw))
    );
    assert_eq!(
        eval_rv(&Rvalue::Discriminant(deref(1)), &local_decls, &locals, pw, policy, &mut tracker),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(1)))
    );
    assert_eq!(
        eval_rv(&Rvalue::Discriminant(Place::from_local(3)), &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::signed(3, IntTy::Isize, pw))
    );
    // CopyForDeref copies a dereferenceable place; non-pointer places are rejected when lowering.
    assert_eq!(
        eval_rv(&Rvalue::CopyForDeref(Place::from_local(1)), &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::ptr(p, raw_u32))
    );
    assert_eq!(
        lower_rvalue(&Rvalue::CopyForDeref(Place::from_local(3)), &local_decls, pw),
        Err(RvalueLowerError::InvalidCopyForDeref(outer))
    );
    assert!(tracker.is_empty());
}

#[test]
fn test_b1_constants_are_validated_in_lowering_and_evaluation() {
    let local_decls: Vec<Ty> = vec![];
    let use_const = |c: Constant| Rvalue::Use(Operand::Constant(c));

    for (constant, ptr_width) in [
        (Constant::Int(5, Ty::Bool), PtrWidth::Bits64),
        (Constant::Int(256, Ty::Uint(UintTy::U8)), PtrWidth::Bits64),
        (Constant::Int(0x1FF, Ty::Int(IntTy::I8)), PtrWidth::Bits64),
        (Constant::Int(1 << 32, Ty::Uint(UintTy::Usize)), PtrWidth::Bits32),
        (
            Constant::Ptr(
                PointerValue::without_provenance(0),
                Ty::Ref(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not),
            ),
            PtrWidth::Bits64,
        ),
        (
            Constant::Ptr(
                PointerValue::without_provenance(1 << 32),
                Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not),
            ),
            PtrWidth::Bits32,
        ),
        (
            Constant::Ptr(PointerValue::without_provenance(8), Ty::Uint(UintTy::Usize)),
            PtrWidth::Bits64,
        ),
    ] {
        assert!(
            matches!(
                lower_rvalue(&use_const(constant.clone()), &local_decls, ptr_width),
                Err(RvalueLowerError::InvalidConstant { .. })
            ),
            "{constant:?} must be rejected when lowering"
        );
        assert!(
            matches!(
                eval_constant(&constant, ptr_width),
                Err(RvalueEvalError::InvalidConstant(_))
            ),
            "{constant:?} must be rejected when evaluating"
        );
    }

    // Signed constants may be given in sign-extended form.
    let neg_one = Constant::Int(u128::MAX, Ty::Int(IntTy::I8));
    assert!(lower_rvalue(&use_const(neg_one.clone()), &local_decls, PtrWidth::Bits64).is_ok());
    assert_eq!(
        eval_constant(&neg_one, PtrWidth::Bits64).unwrap().as_signed(PtrWidth::Bits64),
        Some(-1)
    );
    // The same 64-bit address is fine on a 64-bit target.
    let wide_ptr = Constant::Ptr(
        PointerValue::without_provenance(1 << 32),
        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not),
    );
    assert!(lower_rvalue(&use_const(wide_ptr), &local_decls, PtrWidth::Bits64).is_ok());
}

#[test]
fn test_b1_layout_limits_for_bodies_len_and_repeat() {
    let u8_ty = Ty::Uint(UintTy::U8);
    let big = Ty::Array(Box::new(u8_ty.clone()), 1 << 31);
    let body = Body {
        local_decls: vec![big.clone()],
        basic_blocks: vec![],
    };
    assert_eq!(lower_body(&body, PtrWidth::Bits32), Err(RvalueLowerError::LayoutTooLarge(big)));
    assert!(lower_body(&body, PtrWidth::Bits64).is_ok());

    // `[(); 1 << 33]` has size 0 but its length does not fit a 32-bit usize.
    let zst_arr = Ty::Array(Box::new(Ty::unit()), 1 << 33);
    let len_rv = Rvalue::Len(Place::from_local(0));
    assert_eq!(
        lower_rvalue(&len_rv, std::slice::from_ref(&zst_arr), PtrWidth::Bits32),
        Err(RvalueLowerError::LayoutTooLarge(zst_arr.clone()))
    );
    assert!(matches!(
        lower_rvalue(&len_rv, &[zst_arr], PtrWidth::Bits64),
        Ok(LoweredRvalue::Len {
            static_len: 0x2_0000_0000,
            ..
        })
    ));

    let zero_u8 = Operand::Constant(Constant::Int(0, u8_ty));
    assert!(matches!(
        lower_rvalue(&Rvalue::Repeat(zero_u8.clone(), 1 << 31), &[], PtrWidth::Bits32),
        Err(RvalueLowerError::LayoutTooLarge(_))
    ));
    // Representable, but beyond what the evaluator materializes.
    let lowered = lower_rvalue(&Rvalue::Repeat(zero_u8, 1 << 21), &[], PtrWidth::Bits64).unwrap();
    let mut tracker = ExposedProvenanceTracker::new();
    assert_eq!(
        eval_lowered_rvalue(
            &lowered,
            &[],
            PtrWidth::Bits64,
            TransmutePolicy::RejectPtrToInt,
            &mut tracker
        ),
        Err(RvalueEvalError::EvaluationLimit { len: 1 << 21 })
    );
}

// ---------------------------------------------------------------------------------------------
// [adv A1] regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_a1_single_field_union_rejects_out_of_bounds_active_field_and_aggregate_layout_overflow() {
    let pw32 = PtrWidth::Bits32;
    let pw64 = PtrWidth::Bits64;
    let u32_ty = Ty::Uint(UintTy::U32);
    let one_field_union = Ty::Tuple(vec![u32_ty.clone()]);
    let local_decls = vec![one_field_union];
    let op_u32 = Operand::Constant(Constant::Int(7, u32_ty));

    // Field 0 is valid on a 1-field union.
    let valid_union_stmt = Statement::Assign(
        Place::from_local(0),
        Rvalue::Aggregate(
            AggregateKind::Adt {
                def_path: "SingleFieldUnion".into(),
                variant_idx: 0,
                active_field: Some(0),
                adt_def: None,
            },
            vec![op_u32.clone()],
        ),
    );
    assert!(lower_statement(&valid_union_stmt, &local_decls, pw64).is_ok());

    // Field 99 is out of bounds on a 1-field union even though `rvalue_ty` is also `(u32,)`.
    let oob_union_stmt = Statement::Assign(
        Place::from_local(0),
        Rvalue::Aggregate(
            AggregateKind::Adt {
                def_path: "SingleFieldUnion".into(),
                variant_idx: 0,
                active_field: Some(99),
                adt_def: None,
            },
            vec![op_u32],
        ),
    );
    assert!(matches!(
        lower_statement(&oob_union_stmt, &local_decls, pw64),
        Err(RvalueLowerError::AssignmentTypeMismatch { .. })
    ));

    // Two 1 GiB arrays each fit in 32-bit `isize::MAX`, but a Tuple/Adt/Closure combining them
    // is 2 GiB > `i32::MAX` and must fail with `LayoutTooLarge` on 32-bit targets.
    let one_gib = Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 1 << 30);
    let half_decls = vec![one_gib.clone(), one_gib];
    let ops = vec![
        Operand::Copy(Place::from_local(0)),
        Operand::Copy(Place::from_local(1)),
    ];
    for kind in [
        AggregateKind::Tuple,
        AggregateKind::Adt {
            def_path: "BigPair".into(),
            variant_idx: 0,
            active_field: None,
            adt_def: None,
        },
        AggregateKind::Closure,
    ] {
        let rv = Rvalue::Aggregate(kind, ops.clone());
        assert!(matches!(
            lower_rvalue(&rv, &half_decls, pw32),
            Err(RvalueLowerError::LayoutTooLarge(_))
        ));
        assert!(lower_rvalue(&rv, &half_decls, pw64).is_ok());
    }
}

#[test]
fn test_a1_eval_lowered_cast_and_null_ref_guards() {
    let pw = PtrWidth::Bits64;
    let policy = TransmutePolicy::RejectPtrToInt;
    let mut tracker = ExposedProvenanceTracker::new();

    let u8_ty = Ty::Uint(UintTy::U8);
    let u32_ty = Ty::Uint(UintTy::U32);
    let i8_ty = Ty::Int(IntTy::I8);
    let usize_ty = Ty::Uint(UintTy::Usize);
    let raw_u8 = Ty::RawPtr(Box::new(u8_ty.clone()), Mutability::Not);
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty.clone()), Mutability::Not);
    let ref_u8 = Ty::Ref(Box::new(u8_ty.clone()), Mutability::Not);
    let dummy_op = Operand::Constant(Constant::Unit);

    // 1. IntToInt must reject a pointer runtime value even though `MirValue::as_bits` returns Some.
    let int_to_int = LoweredCast::IntToInt {
        src_ty: usize_ty.clone(),
        target_ty: u32_ty.clone(),
        operand: dummy_op.clone(),
    };
    let ptr_val = MirValue::ptr(PointerValue::with_provenance(0x1000, 1, 1), raw_u8.clone());
    assert!(eval_lowered_cast(&int_to_int, &ptr_val, pw, policy, &mut tracker).is_err());

    // 2. Signed IntToPtr (`-1i8 as *const u8`) sign-extends to pointer width.
    let i8_to_ptr = LoweredCast::IntToPtr {
        src_ty: i8_ty,
        target_ty: raw_u8.clone(),
        operand: dummy_op.clone(),
        pick_exposed_provenance: true,
    };
    let neg_one_i8 = MirValue::signed(-1, IntTy::I8, pw);
    assert_eq!(
        eval_lowered_cast(&i8_to_ptr, &neg_one_i8, pw, policy, &mut tracker),
        Ok(MirValue::ptr(
            PointerValue::without_provenance(u64::MAX),
            raw_u8.clone()
        ))
    );
    assert_eq!(
        eval_lowered_cast(&i8_to_ptr, &neg_one_i8, PtrWidth::Bits32, policy, &mut tracker),
        Ok(MirValue::ptr(
            PointerValue::without_provenance(0xFFFF_FFFF),
            raw_u8.clone()
        ))
    );

    // 3. PtrToInt and PtrToPtr must reject mismatched runtime pointer types and `Ty::Ref`.
    let ptr_to_int = LoweredCast::PtrToInt {
        src_ty: raw_u8.clone(),
        target_ty: usize_ty,
        operand: dummy_op.clone(),
        expose_provenance: true,
    };
    let wrong_ptr = MirValue::ptr(PointerValue::with_provenance(0x1000, 2, 2), raw_u32.clone());
    assert!(eval_lowered_cast(&ptr_to_int, &wrong_ptr, pw, policy, &mut tracker).is_err());
    assert!(tracker.is_empty());

    let ptr_to_ptr = LoweredCast::PtrToPtr {
        src_ty: raw_u8,
        target_ty: raw_u32,
        operand: dummy_op,
    };
    assert!(eval_lowered_cast(&ptr_to_ptr, &wrong_ptr, pw, policy, &mut tracker).is_err());

    // 4. Null `Ty::Ref` values are rejected in pointer comparisons, `PtrMetadata`, `Offset`,
    // and `&raw const (*null_ref)` reborrows.
    let null_ref = MirValue::ptr(PointerValue::without_provenance(0), ref_u8.clone());
    let valid_ref = MirValue::ptr(PointerValue::with_provenance(0x1000, 3, 3), ref_u8.clone());
    assert!(matches!(
        eval_binop(BinOp::Eq, &null_ref, &valid_ref, pw),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern { .. }))
    ));
    assert!(matches!(
        eval_unop(UnOp::PtrMetadata, &null_ref, pw),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern { .. }))
    ));
    assert!(matches!(
        eval_binop(
            BinOp::Offset,
            &null_ref,
            &MirValue::signed(0, IntTy::Isize, pw),
            pw
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern { .. }))
    ));

    let deref0 = Place::with_projection(0, vec![ProjectionElem::Deref]);
    assert!(matches!(
        eval_rv(
            &Rvalue::RawPtr(Mutability::Not, deref0),
            &[ref_u8],
            &[null_ref],
            pw,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern { .. }))
    ));
}

// ---------------------------------------------------------------------------------------------
// [adv B2] regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_b2_ptr_to_int_evaluates_reference_sources_accepted_by_lowering() {
    let pw = PtrWidth::Bits64;
    let policy = TransmutePolicy::RejectPtrToInt;
    let mut tracker = ExposedProvenanceTracker::new();
    let usize_ty = Ty::Uint(UintTy::Usize);
    let ref_u8 = Ty::Ref(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let p = PointerValue::with_provenance(0x5000, 11, 12);
    let expose = Rvalue::Cast(
        CastKind::PointerExposeProvenance,
        Operand::Copy(Place::from_local(0)),
        usize_ty.clone(),
    );

    // `lower_ptr_to_int` (base API) accepts `&T` sources; A1's evaluator then rejected the
    // very cast it had lowered with `TypeMismatch`.
    let lowered = lower_rvalue(&expose, std::slice::from_ref(&ref_u8), pw).unwrap();
    assert!(matches!(
        lowered,
        LoweredRvalue::Cast {
            cast: LoweredCast::PtrToInt { .. },
            ..
        }
    ));
    assert_eq!(
        eval_lowered_rvalue(&lowered, &[MirValue::ptr(p, ref_u8.clone())], pw, policy, &mut tracker),
        Ok(MirValue::unsigned(0x5000, UintTy::Usize, pw))
    );
    assert!(tracker.is_exposed(&p.provenance.unwrap()));

    // A null `&T` value is invalid and is not exposed.
    let mut fresh = ExposedProvenanceTracker::new();
    assert_eq!(
        eval_lowered_rvalue(
            &lowered,
            &[MirValue::ptr(PointerValue::without_provenance(0), ref_u8.clone())],
            pw,
            policy,
            &mut fresh
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ref_u8,
            bits: 0,
        }))
    );
    assert!(fresh.is_empty());
}

#[test]
fn test_b2_int_to_ptr_predicts_exposed_provenance_so_offset_stays_defined() {
    let pw = PtrWidth::Bits64;
    let policy = TransmutePolicy::RejectPtrToInt;
    let usize_ty = Ty::Uint(UintTy::Usize);
    let raw_u8 = Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not);
    let local_decls = vec![raw_u8.clone(), usize_ty.clone(), raw_u8.clone()];
    let p = PointerValue::with_provenance(0x6000, 21, 22);

    let expose = Rvalue::Cast(
        CastKind::PointerExposeProvenance,
        Operand::Copy(Place::from_local(0)),
        usize_ty.clone(),
    );
    let with_exposed = Rvalue::Cast(
        CastKind::PointerWithExposedProvenance,
        Operand::Copy(Place::from_local(1)),
        raw_u8.clone(),
    );
    let add_one = Rvalue::BinaryOp(
        BinOp::Offset,
        Operand::Copy(Place::from_local(2)),
        Operand::Constant(Constant::Int(1, usize_ty.clone())),
    );

    // `let a = p as usize; let q = a as *const u8; q.add(1)` (`ptr::with_exposed_provenance`)
    // is defined. A0/B1/A1 always predicted `None` provenance for `q`, so the non-zero
    // `Offset` reported `PointerArithmeticWithoutProvenance` (a false UB report).
    let mut tracker = ExposedProvenanceTracker::new();
    let addr = eval_rv(&expose, &local_decls, &[MirValue::ptr(p, raw_u8.clone())], pw, policy, &mut tracker)
        .unwrap();
    let locals = vec![MirValue::ptr(p, raw_u8.clone()), addr.clone(), MirValue::Unit];
    let q = eval_rv(&with_exposed, &local_decls, &locals, pw, policy, &mut tracker).unwrap();
    assert_eq!(q, MirValue::ptr(p, raw_u8.clone()));
    let locals = vec![MirValue::Unit, addr.clone(), q];
    assert_eq!(
        eval_rv(&add_one, &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::ptr(PointerValue::with_provenance(0x6001, 21, 22), raw_u8.clone()))
    );

    // With nothing exposed, `int2ptr` can only predict `None`, so the offset is UB.
    let mut empty = ExposedProvenanceTracker::new();
    let locals = vec![MirValue::Unit, addr.clone(), MirValue::Unit];
    let bare = eval_rv(&with_exposed, &local_decls, &locals, pw, policy, &mut empty).unwrap();
    assert_eq!(bare, MirValue::ptr(PointerValue::without_provenance(0x6000), raw_u8.clone()));
    let locals = vec![MirValue::Unit, addr.clone(), bare];
    assert_eq!(
        eval_rv(&add_one, &local_decls, &locals, pw, policy, &mut empty),
        Err(RvalueEvalError::PointerArithmeticWithoutProvenance {
            addr: 0x6000,
            byte_offset: 1,
        })
    );

    // A lowered cast with `pick_exposed_provenance: false` never picks provenance.
    let no_pick = LoweredCast::IntToPtr {
        src_ty: usize_ty,
        target_ty: raw_u8.clone(),
        operand: Operand::Copy(Place::from_local(1)),
        pick_exposed_provenance: false,
    };
    assert_eq!(
        eval_lowered_cast(&no_pick, &addr, pw, policy, &mut tracker),
        Ok(MirValue::ptr(PointerValue::without_provenance(0x6000), raw_u8))
    );
}

#[test]
fn test_b2_identity_transmute_of_non_canonical_types_returns_validated_value() {
    let pw = PtrWidth::Bits64;
    let policy = TransmutePolicy::RejectPtrToInt;
    let mut tracker = ExposedProvenanceTracker::new();
    let u8_ty = Ty::Uint(UintTy::U8);
    let u32_ty = Ty::Uint(UintTy::U32);
    let ref_u8 = Ty::Ref(Box::new(u8_ty.clone()), Mutability::Not);
    let padded = Ty::Tuple(vec![u8_ty.clone(), u32_ty.clone()]);
    let with_ref = Ty::Tuple(vec![ref_u8.clone(), u8_ty.clone()]);
    let local_decls = vec![padded.clone(), with_ref.clone()];
    let identity = |local: usize, ty: Ty| {
        Rvalue::Cast(CastKind::Transmute, Operand::Copy(Place::from_local(local)), ty)
    };

    let padded_val = MirValue::Tuple(vec![
        MirValue::unsigned(7, UintTy::U8, pw),
        MirValue::unsigned(0xDEAD_BEEF, UintTy::U32, pw),
    ]);
    let r = PointerValue::with_provenance(0x7000, 31, 32);
    let ref_val = MirValue::Tuple(vec![MirValue::ptr(r, ref_u8.clone()), MirValue::unsigned(1, UintTy::U8, pw)]);
    let locals = vec![padded_val.clone(), ref_val.clone()];
    assert_eq!(
        eval_rv(&identity(0, padded.clone()), &local_decls, &locals, pw, policy, &mut tracker),
        Ok(padded_val.clone())
    );
    // Provenance is preserved and never exposed.
    assert_eq!(
        eval_rv(&identity(1, with_ref.clone()), &local_decls, &locals, pw, policy, &mut tracker),
        Ok(ref_val)
    );
    assert!(tracker.is_empty());

    // Struct values (typed as the tuple of their fields) are returned unchanged too.
    let adt_val = MirValue::Adt {
        def_path: "S".into(),
        variant_idx: 0,
        active_field: None,
        fields: vec![
            MirValue::unsigned(1, UintTy::U8, pw),
            MirValue::unsigned(2, UintTy::U32, pw),
        ],
        adt_def: None,
    };
    let locals = vec![adt_val.clone(), MirValue::Unit];
    assert_eq!(
        eval_rv(&identity(0, padded.clone()), &local_decls, &locals, pw, policy, &mut tracker),
        Ok(adt_val)
    );

    // Invalid operands are still rejected: a null reference field ...
    let null_ref_val = MirValue::Tuple(vec![
        MirValue::ptr(PointerValue::without_provenance(0), ref_u8.clone()),
        MirValue::unsigned(1, UintTy::U8, pw),
    ]);
    let locals = vec![padded_val, null_ref_val];
    assert_eq!(
        eval_rv(&identity(1, with_ref), &local_decls, &locals, pw, policy, &mut tracker),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ref_u8,
            bits: 0,
        }))
    );
    // ... and values whose shape does not match the type.
    let locals = vec![MirValue::unsigned(7, UintTy::U8, pw), MirValue::Unit];
    assert!(matches!(
        eval_rv(&identity(0, padded), &local_decls, &locals, pw, policy, &mut tracker),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// [adv A2] regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_a2_identity_transmute_handles_canonical_structs_unions_and_32bit_ptr_masking() {
    let pw64 = PtrWidth::Bits64;
    let pw32 = PtrWidth::Bits32;
    let policy = TransmutePolicy::RejectPtrToInt;
    let mut tracker = ExposedProvenanceTracker::new();

    let u8_ty = Ty::Uint(UintTy::U8);
    let u32_ty = Ty::Uint(UintTy::U32);
    let u64_ty = Ty::Uint(UintTy::U64);
    let raw_u8 = Ty::RawPtr(Box::new(u8_ty.clone()), Mutability::Not);
    let ref_u8 = Ty::Ref(Box::new(u8_ty.clone()), Mutability::Not);

    // 1. Canonical struct (`struct Pair(u32, u32)` or `struct Wrapper(u32)`): B2 only took the
    // `MirValue::Adt` identity branch when `!src_ty.has_canonical_byte_layout(ptr_width)`, so
    // canonical structs fell through to `encode_mir_value` and failed with `TypeMismatch`!
    let canon_pair_ty = Ty::Tuple(vec![u32_ty.clone(), u32_ty.clone()]);
    assert!(canon_pair_ty.has_canonical_byte_layout(pw64));
    let canon_struct_val = MirValue::Adt {
        def_path: "AlignedPair".into(),
        variant_idx: 0,
        active_field: None,
        fields: vec![
            MirValue::unsigned(10, UintTy::U32, pw64),
            MirValue::unsigned(20, UintTy::U32, pw64),
        ],
        adt_def: None,
    };
    let identity_pair = Rvalue::Cast(
        CastKind::Transmute,
        Operand::Copy(Place::from_local(0)),
        canon_pair_ty.clone(),
    );
    assert_eq!(
        eval_rv(
            &identity_pair,
            std::slice::from_ref(&canon_pair_ty),
            std::slice::from_ref(&canon_struct_val),
            pw64,
            policy,
            &mut tracker
        ),
        Ok(canon_struct_val)
    );

    // 2. Union `MirValue::Adt` (`active_field: Some(field_idx)`) identity transmute: validates
    // the active field against `fields[field_idx]` and rejects out-of-bounds `active_field`.
    let union_ty = Ty::Tuple(vec![u32_ty.clone(), u64_ty]);
    let union_val = MirValue::Adt {
        def_path: "MyUnion".into(),
        variant_idx: 0,
        active_field: Some(1),
        fields: vec![MirValue::unsigned(0xCAFE_BABE, UintTy::U64, pw64)],
        adt_def: None,
    };
    let identity_union = Rvalue::Cast(
        CastKind::Transmute,
        Operand::Copy(Place::from_local(0)),
        union_ty.clone(),
    );
    assert_eq!(
        eval_rv(
            &identity_union,
            std::slice::from_ref(&union_ty),
            std::slice::from_ref(&union_val),
            pw64,
            policy,
            &mut tracker
        ),
        Ok(union_val)
    );
    let bad_union_val = MirValue::Adt {
        def_path: "MyUnion".into(),
        variant_idx: 0,
        active_field: Some(5),
        fields: vec![MirValue::unsigned(1, UintTy::U32, pw64)],
        adt_def: None,
    };
    assert!(matches!(
        eval_rv(
            &identity_union,
            std::slice::from_ref(&union_ty),
            &[bad_union_val],
            pw64,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    // 3. On 32-bit targets, identity transmute of a non-canonical tuple containing a pointer
    // masks the pointer's address to 32 bits (B2 cloned the unmasked 64-bit address).
    let non_canon_ptr_tuple = Ty::Tuple(vec![raw_u8.clone(), u8_ty.clone()]);
    assert!(!non_canon_ptr_tuple.has_canonical_byte_layout(pw32));
    let unmasked_ptr = PointerValue::with_provenance(0x1_0000_2000, 41, 42);
    let masked_ptr = PointerValue::with_provenance(0x0000_2000, 41, 42);
    let in_tuple = MirValue::Tuple(vec![
        MirValue::ptr(unmasked_ptr, raw_u8.clone()),
        MirValue::unsigned(9, UintTy::U8, pw32),
    ]);
    let expected_tuple = MirValue::Tuple(vec![
        MirValue::ptr(masked_ptr, raw_u8),
        MirValue::unsigned(9, UintTy::U8, pw32),
    ]);
    let identity_ptr_tuple = Rvalue::Cast(
        CastKind::Transmute,
        Operand::Copy(Place::from_local(0)),
        non_canon_ptr_tuple.clone(),
    );
    assert_eq!(
        eval_rv(
            &identity_ptr_tuple,
            std::slice::from_ref(&non_canon_ptr_tuple),
            &[in_tuple],
            pw32,
            policy,
            &mut tracker
        ),
        Ok(expected_tuple)
    );
    assert!(tracker.is_empty());

    // 4. `LoweredCast::PtrToInt` honors `expose_provenance: false`, and `Repeat`,
    // `CheckedBinaryOp`, and `CopyForDeref` validate runtime operand types and null `&T`.
    let no_expose = LoweredCast::PtrToInt {
        src_ty: ref_u8.clone(),
        target_ty: Ty::Uint(UintTy::Usize),
        operand: Operand::Copy(Place::from_local(0)),
        expose_provenance: false,
    };
    let valid_ref = MirValue::ptr(PointerValue::with_provenance(0x8000, 51, 52), ref_u8.clone());
    assert_eq!(
        eval_lowered_cast(&no_expose, &valid_ref, pw64, policy, &mut tracker),
        Ok(MirValue::unsigned(0x8000, UintTy::Usize, pw64))
    );
    assert!(tracker.is_empty());

    let repeat_u32 = lower_rvalue(
        &Rvalue::Repeat(Operand::Copy(Place::from_local(0)), 2),
        std::slice::from_ref(&u32_ty),
        pw64,
    )
    .unwrap();
    assert!(matches!(
        eval_lowered_rvalue(
            &repeat_u32,
            &[MirValue::unsigned(1, UintTy::U8, pw64)],
            pw64,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    let copy_deref_ref = lower_rvalue(
        &Rvalue::CopyForDeref(Place::from_local(0)),
        std::slice::from_ref(&ref_u8),
        pw64,
    )
    .unwrap();
    let null_ref = MirValue::ptr(PointerValue::without_provenance(0), ref_u8);
    assert!(matches!(
        eval_lowered_rvalue(&copy_deref_ref, &[null_ref], pw64, policy, &mut tracker),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern { .. }))
    ));
}

// ---------------------------------------------------------------------------------------------
// Episode 1 (`ep1-rust-place-proj-nullary-stmt`) tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_ep1_nullary_op_size_of_align_of_offset_of_and_ub_checks() {
    let mut tracker = ExposedProvenanceTracker::new();
    let policy = TransmutePolicy::RejectPtrToInt;

    let u8_ty = Ty::Uint(UintTy::U8);
    let u16_ty = Ty::Uint(UintTy::U16);
    let u32_ty = Ty::Uint(UintTy::U32);
    let u64_ty = Ty::Uint(UintTy::U64);
    let usize_ty = Ty::Uint(UintTy::Usize);
    let raw_u8 = Ty::RawPtr(Box::new(u8_ty.clone()), Mutability::Not);

    // 1. SizeOf and AlignOf across Bits32 and Bits64, including uninhabited types (`!`, `(!, u32)`)
    let layout_cases = [
        (Ty::Never, 0usize, 1usize, 0usize, 1usize),
        (Ty::unit(), 0, 1, 0, 1),
        (Ty::Bool, 1, 1, 1, 1),
        (Ty::Char, 4, 4, 4, 4),
        (usize_ty.clone(), 4, 4, 8, 8),
        (raw_u8.clone(), 4, 4, 8, 8),
        (Ty::Tuple(vec![Ty::Never, u32_ty.clone()]), 4, 4, 4, 4),
        (Ty::Tuple(vec![u8_ty.clone(), u32_ty.clone()]), 8, 4, 8, 4),
        (Ty::Tuple(vec![raw_u8.clone(), u64_ty.clone()]), 16, 8, 16, 8),
    ];

    for (ty, sz32, al32, sz64, al64) in &layout_cases {
        for (pw, exp_sz, exp_al) in [
            (PtrWidth::Bits32, *sz32, *al32),
            (PtrWidth::Bits64, *sz64, *al64),
        ] {
            let size_rv = Rvalue::NullaryOp(NullOp::SizeOf, ty.clone());
            let align_rv = Rvalue::NullaryOp(NullOp::AlignOf, ty.clone());
            assert_eq!(
                eval_rv(&size_rv, &[], &[], pw, policy, &mut tracker),
                Ok(MirValue::unsigned(exp_sz as u128, UintTy::Usize, pw))
            );
            assert_eq!(
                eval_rv(&align_rv, &[], &[], pw, policy, &mut tracker),
                Ok(MirValue::unsigned(exp_al as u128, UintTy::Usize, pw))
            );
        }
    }

    // 2. OffsetOf on canonical tuples and nested canonical tuples
    let canon_triple = Ty::Tuple(vec![u32_ty.clone(), u16_ty.clone(), u16_ty.clone()]);
    let nested_canon = Ty::Tuple(vec![
        Ty::Tuple(vec![u64_ty.clone(), u64_ty.clone()]),
        canon_triple.clone(),
    ]);
    for pw in [PtrWidth::Bits32, PtrWidth::Bits64] {
        assert_eq!(resolve_offset_of(&canon_triple, &[], pw), Ok(0));
        assert_eq!(resolve_offset_of(&canon_triple, &[(0, 0)], pw), Ok(0));
        assert_eq!(resolve_offset_of(&canon_triple, &[(0, 1)], pw), Ok(4));
        assert_eq!(resolve_offset_of(&canon_triple, &[(0, 2)], pw), Ok(6));
        assert_eq!(resolve_offset_of(&nested_canon, &[(0, 1), (0, 2)], pw), Ok(22));

        let off_rv = Rvalue::NullaryOp(
            NullOp::OffsetOf(vec![(0, 1), (0, 2)]),
            nested_canon.clone(),
        );
        assert_eq!(
            eval_rv(&off_rv, &[], &[], pw, policy, &mut tracker),
            Ok(MirValue::unsigned(22, UintTy::Usize, pw))
        );
    }

    // `(*const u8, u64)` is canonical on Bits64 (offset 8 for field 1) but non-canonical on Bits32!
    let ptr_u64 = Ty::Tuple(vec![raw_u8.clone(), u64_ty.clone()]);
    assert_eq!(resolve_offset_of(&ptr_u64, &[(0, 1)], PtrWidth::Bits64), Ok(8));
    assert_eq!(
        resolve_offset_of(&ptr_u64, &[(0, 1)], PtrWidth::Bits32),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(ptr_u64.clone()))
    );

    // 3. Fail-closed OffsetOf rejection on non-canonical tuples and invalid field paths
    for non_canon in [
        Ty::Tuple(vec![u8_ty.clone(), u32_ty.clone()]),
        Ty::Tuple(vec![u8_ty.clone(), Ty::Bool]),
        Ty::Tuple(vec![u32_ty.clone(), u64_ty.clone()]),
        Ty::Tuple(vec![Ty::Array(Box::new(u8_ty.clone()), 4), u32_ty.clone()]),
    ] {
        let rv = Rvalue::NullaryOp(NullOp::OffsetOf(vec![(0, 1)]), non_canon.clone());
        assert_eq!(
            lower_rvalue(&rv, &[], PtrWidth::Bits64),
            Err(RvalueLowerError::UnsupportedOffsetOfLayout(non_canon))
        );
    }

    // Non-zero variant_idx, out-of-bounds field_idx, or non-tuple container rejected
    assert_eq!(
        lower_rvalue(
            &Rvalue::NullaryOp(NullOp::OffsetOf(vec![(1, 0)]), canon_triple.clone()),
            &[],
            PtrWidth::Bits64
        ),
        Err(RvalueLowerError::InvalidOffsetOfField {
            container_ty: canon_triple.clone(),
            variant_idx: 1,
            field_idx: 0,
        })
    );
    assert_eq!(
        lower_rvalue(
            &Rvalue::NullaryOp(NullOp::OffsetOf(vec![(0, 5)]), canon_triple),
            &[],
            PtrWidth::Bits64
        ),
        Err(RvalueLowerError::InvalidOffsetOfField {
            container_ty: Ty::Tuple(vec![u32_ty.clone(), u16_ty.clone(), u16_ty]),
            variant_idx: 0,
            field_idx: 5,
        })
    );
    let arr_u32 = Ty::Array(Box::new(u32_ty.clone()), 4);
    assert_eq!(
        lower_rvalue(
            &Rvalue::NullaryOp(NullOp::OffsetOf(vec![(0, 0)]), arr_u32.clone()),
            &[],
            PtrWidth::Bits64
        ),
        Err(RvalueLowerError::InvalidOffsetOfField {
            container_ty: arr_u32,
            variant_idx: 0,
            field_idx: 0,
        })
    );

    // 4. LayoutTooLarge rejected in SizeOf, AlignOf, OffsetOf
    let too_big_32 = Ty::Array(Box::new(u8_ty), 1 << 31);
    for op in [
        NullOp::SizeOf,
        NullOp::AlignOf,
        NullOp::OffsetOf(vec![]),
    ] {
        assert_eq!(
            lower_rvalue(
                &Rvalue::NullaryOp(op.clone(), too_big_32.clone()),
                &[],
                PtrWidth::Bits32
            ),
            Err(RvalueLowerError::LayoutTooLarge(too_big_32.clone()))
        );
        assert!(matches!(
            eval_nullary_op(&op, &too_big_32, PtrWidth::Bits32),
            Err(RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge { .. }))
        ));
    }

    // 5. UbChecks requires Ty::Bool and evaluates to MirValue::Bool(true)
    let ub_ok = Rvalue::NullaryOp(NullOp::UbChecks, Ty::Bool);
    assert_eq!(
        eval_rv(&ub_ok, &[], &[], PtrWidth::Bits64, policy, &mut tracker),
        Ok(MirValue::Bool(true))
    );
    let ub_bad = Rvalue::NullaryOp(NullOp::UbChecks, u32_ty.clone());
    assert_eq!(
        lower_rvalue(&ub_bad, &[], PtrWidth::Bits64),
        Err(RvalueLowerError::InvalidNullaryOpType {
            op: NullOp::UbChecks,
            arg_ty: u32_ty,
        })
    );
}

#[test]
fn test_ep1_value_tree_place_projections_read_write_and_rvalue_integration() {
    let pw = PtrWidth::Bits64;
    let policy = TransmutePolicy::RejectPtrToInt;
    let mut tracker = ExposedProvenanceTracker::new();

    let u8_ty = Ty::Uint(UintTy::U8);
    let u32_ty = Ty::Uint(UintTy::U32);
    let usize_ty = Ty::Uint(UintTy::Usize);
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty.clone()), Mutability::Mut);
    let pair_ty = Ty::Tuple(vec![u32_ty.clone(), u8_ty.clone()]);
    let arr_pair_ty = Ty::Array(Box::new(pair_ty.clone()), 4);
    let outer_ty = Ty::Tuple(vec![arr_pair_ty.clone(), raw_u32.clone()]);

    let ptr_val = PointerValue::with_provenance(0x9000, 12, 34);
    let make_pair = |a: u128, b: u128| {
        MirValue::Tuple(vec![
            MirValue::unsigned(a, UintTy::U32, pw),
            MirValue::unsigned(b, UintTy::U8, pw),
        ])
    };

    let local_decls = vec![
        outer_ty.clone(), // _0: ([(u32, u8); 4], *mut u32)
        usize_ty.clone(), // _1: dynamic index usize
        pair_ty.clone(),  // _2: enum / union ADT local
    ];

    let mut locals = vec![
        MirValue::Tuple(vec![
            MirValue::Array {
                elements: vec![
                    make_pair(10, 1),
                    make_pair(20, 2),
                    make_pair(30, 3),
                    make_pair(40, 4),
                ],
                elem_ty: pair_ty.clone(),
            },
            MirValue::ptr(ptr_val, raw_u32.clone()),
        ]),
        MirValue::unsigned(2, UintTy::Usize, pw),
        MirValue::Adt {
            def_path: "MyEnum".into(),
            variant_idx: 1,
            active_field: None,
            fields: vec![
                MirValue::unsigned(777, UintTy::U32, pw),
                MirValue::unsigned(9, UintTy::U8, pw),
            ],
            adt_def: None,
        },
    ];

    // 1. Chained Field -> Index -> Field read & write (`_0.0[_1].0`)
    let elem2_field0 = Place::with_projection(
        0,
        vec![
            ProjectionElem::Field(0, arr_pair_ty.clone()),
            ProjectionElem::Index(Local(1)),
            ProjectionElem::Field(0, u32_ty.clone()),
        ],
    );
    assert_eq!(eval_place_read(&elem2_field0, &locals, pw), Ok(MirValue::unsigned(30, UintTy::U32, pw)));
    eval_place_write(
        &elem2_field0,
        MirValue::unsigned(300, UintTy::U32, pw),
        &mut locals,
        pw,
    )
    .unwrap();
    assert_eq!(eval_place_read(&elem2_field0, &locals, pw), Ok(MirValue::unsigned(300, UintTy::U32, pw)));

    // Out-of-bounds dynamic Index (`_1 = 99`)
    locals[1] = MirValue::unsigned(99, UintTy::Usize, pw);
    assert_eq!(
        eval_place_read(&elem2_field0, &locals, pw),
        Err(RvalueEvalError::IndexOutOfBounds { index: 99, len: 4 })
    );
    assert_eq!(
        eval_place_write(
            &elem2_field0,
            MirValue::unsigned(1, UintTy::U32, pw),
            &mut locals,
            pw
        ),
        Err(RvalueEvalError::IndexOutOfBounds { index: 99, len: 4 })
    );
    locals[1] = MirValue::unsigned(2, UintTy::Usize, pw);

    // 2. ConstantIndex (`from_end: false` and `from_end: true`, `offset == 0` with `from_end: true` rejected)
    let const_from_end = Place::with_projection(
        0,
        vec![
            ProjectionElem::Field(0, arr_pair_ty.clone()),
            ProjectionElem::ConstantIndex {
                offset: 1,
                min_length: 4,
                from_end: true,
            },
            ProjectionElem::Field(1, u8_ty.clone()),
        ],
    );
    assert_eq!(eval_place_read(&const_from_end, &locals, pw), Ok(MirValue::unsigned(4, UintTy::U8, pw)));
    eval_place_write(
        &const_from_end,
        MirValue::unsigned(44, UintTy::U8, pw),
        &mut locals,
        pw,
    )
    .unwrap();
    assert_eq!(eval_place_read(&const_from_end, &locals, pw), Ok(MirValue::unsigned(44, UintTy::U8, pw)));

    let bad_const_zero_from_end = Place::with_projection(
        0,
        vec![
            ProjectionElem::Field(0, arr_pair_ty.clone()),
            ProjectionElem::ConstantIndex {
                offset: 0,
                min_length: 1,
                from_end: true,
            },
        ],
    );
    assert_eq!(
        eval_place_read(&bad_const_zero_from_end, &locals, pw),
        Err(RvalueEvalError::IndexOutOfBounds { index: 0, len: 4 })
    );

    // 3. Subslice (`from_end: false` and `from_end: true`, chained indexing, and write splicing)
    let subslice_from_end = Place::with_projection(
        0,
        vec![
            ProjectionElem::Field(0, arr_pair_ty.clone()),
            ProjectionElem::Subslice {
                from: 1,
                to: 1,
                from_end: true,
            },
        ],
    );
    let sub_val = eval_place_read(&subslice_from_end, &locals, pw).unwrap();
    assert_eq!(
        sub_val,
        MirValue::Array {
            elements: vec![make_pair(20, 2), make_pair(300, 3)],
            elem_ty: pair_ty.clone(),
        }
    );

    // Write a new 2-element array into the subslice `_0.0[1..3]`
    eval_place_write(
        &subslice_from_end,
        MirValue::Array {
            elements: vec![make_pair(222, 22), make_pair(333, 33)],
            elem_ty: pair_ty.clone(),
        },
        &mut locals,
        pw,
    )
    .unwrap();
    assert_eq!(
        eval_place_read(&elem2_field0, &locals, pw),
        Ok(MirValue::unsigned(333, UintTy::U32, pw))
    );

    // Subslice write with mismatched array length must fail closed
    assert!(matches!(
        eval_place_write(
            &subslice_from_end,
            MirValue::Array {
                elements: vec![make_pair(1, 1)],
                elem_ty: pair_ty.clone(),
            },
            &mut locals,
            pw,
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    // 4. Downcast + Field on Enum ADT and Union active_field read/write
    let enum_downcast_ok = Place::with_projection(
        2,
        vec![
            ProjectionElem::Downcast(1),
            ProjectionElem::Field(0, u32_ty.clone()),
        ],
    );
    let enum_downcast_wrong = Place::with_projection(
        2,
        vec![
            ProjectionElem::Downcast(0),
            ProjectionElem::Field(0, u32_ty.clone()),
        ],
    );
    let enum_no_downcast = Place::with_projection(2, vec![ProjectionElem::Field(0, u32_ty.clone())]);

    assert_eq!(
        eval_place_read(&enum_downcast_ok, &locals, pw),
        Ok(MirValue::unsigned(777, UintTy::U32, pw))
    );
    assert_eq!(
        eval_place_read(&enum_downcast_wrong, &locals, pw),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 0,
            actual: 1,
        })
    );
    assert_eq!(
        eval_place_read(&enum_no_downcast, &locals, pw),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 0,
            actual: 1,
        })
    );
    eval_place_write(
        &enum_downcast_ok,
        MirValue::unsigned(888, UintTy::U32, pw),
        &mut locals,
        pw,
    )
    .unwrap();
    assert_eq!(
        eval_place_read(&enum_downcast_ok, &locals, pw),
        Ok(MirValue::unsigned(888, UintTy::U32, pw))
    );

    // Union active_field: reading active field 0 succeeds, reading inactive field 1 fails,
    // writing field 1 switches active_field to Some(1)!
    locals[2] = MirValue::Adt {
        def_path: "MyUnion".into(),
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![MirValue::unsigned(0x1234, UintTy::U32, pw)],
        adt_def: None,
    };
    let union_f0 = Place::with_projection(2, vec![ProjectionElem::Field(0, u32_ty.clone())]);
    let union_f1 = Place::with_projection(2, vec![ProjectionElem::Field(1, u8_ty)]);
    assert_eq!(
        eval_place_read(&union_f0, &locals, pw),
        Ok(MirValue::unsigned(0x1234, UintTy::U32, pw))
    );
    assert_eq!(
        eval_place_read(&union_f1, &locals, pw),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 0,
            requested_field: 1,
        })
    );
    eval_place_write(
        &union_f1,
        MirValue::unsigned(0xAB, UintTy::U8, pw),
        &mut locals,
        pw,
    )
    .unwrap();
    assert_eq!(
        eval_place_read(&union_f1, &locals, pw),
        Ok(MirValue::unsigned(0xAB, UintTy::U8, pw))
    );
    assert_eq!(
        eval_place_read(&union_f0, &locals, pw),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 1,
            requested_field: 0,
        })
    );

    // 5. Projected places wired into `eval_lowered_rvalue` (`Len`, `CopyForDeref`, `BinaryOp`)
    let len_subslice = Rvalue::Len(subslice_from_end);
    assert_eq!(
        eval_rv(&len_subslice, &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::unsigned(2, UintTy::Usize, pw))
    );

    let ptr_field_place = Place::with_projection(0, vec![ProjectionElem::Field(1, raw_u32.clone())]);
    let copy_for_deref_proj = Rvalue::CopyForDeref(ptr_field_place);
    assert_eq!(
        eval_rv(&copy_for_deref_proj, &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::ptr(ptr_val, raw_u32))
    );

    let add_proj = Rvalue::BinaryOp(
        BinOp::Add,
        Operand::Copy(elem2_field0),
        Operand::Constant(Constant::Int(67, u32_ty.clone())),
    );
    assert_eq!(
        eval_rv(&add_proj, &local_decls, &locals, pw, policy, &mut tracker),
        Ok(MirValue::unsigned(400, UintTy::U32, pw))
    );
}

#[test]
fn test_ep1_statement_and_block_evaluation_d9_d13b_set_discriminant_assume_and_move() {
    let pw = PtrWidth::Bits64;
    let u8_ty = Ty::Uint(UintTy::U8);
    let u32_ty = Ty::Uint(UintTy::U32);
    let usize_ty = Ty::Uint(UintTy::Usize);
    let unit_ty = Ty::unit();
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty.clone()), Mutability::Not);
    let inner_pair_ty = Ty::Tuple(vec![u32_ty.clone(), unit_ty.clone()]);
    let nested_tuple_ty = Ty::Tuple(vec![inner_pair_ty.clone(), u8_ty.clone()]);
    let arr_u32_2 = Ty::Array(Box::new(u32_ty.clone()), 2);

    let local_decls = vec![
        nested_tuple_ty.clone(), // _0: ((u32, ()), u8)
        u32_ty.clone(),          // _1: argument u32
        arr_u32_2.clone(),       // _2: [u32; 2]
        usize_ty.clone(),        // _3: usize index
        raw_u32.clone(),         // _4: *const u32
        Ty::Bool,                // _5: bool
        Ty::Tuple(vec![u32_ty.clone()]), // _6: enum local (1 payload field)
    ];

    // 1. StorageLive / StorageDead lifecycle & D9 PlaceMention
    let mut state = StatementEvalState::from_local_decls(local_decls.clone(), pw);
    state.slots[1] = LocalSlotState::Init(MirValue::unsigned(42, UintTy::U32, pw));
    state.slots[2] = LocalSlotState::Dead;

    // Accessing or mentioning a Dead local fails with DeadLocal
    let mention_dead =
        lower_statement(&Statement::PlaceMention(Place::from_local(2)), &local_decls, pw).unwrap();
    assert_eq!(
        eval_lowered_statement(&mention_dead, &mut state),
        Err(RvalueEvalError::DeadLocal(Local(2)))
    );

    // StorageLive(2) transitions _2 to Uninit; PlaceMention(_2) and PlaceMention(_0.0.1) succeed!
    let live_2 = lower_statement(&Statement::StorageLive(Local(2)), &local_decls, pw).unwrap();
    eval_lowered_statement(&live_2, &mut state).unwrap();
    assert_eq!(state.get_local(Local(2)), Some(&LocalSlotState::Uninit));
    eval_lowered_statement(&mention_dead, &mut state).unwrap();

    let uninit_field_place = Place::with_projection(
        0,
        vec![
            ProjectionElem::Field(0, inner_pair_ty.clone()),
            ProjectionElem::Field(1, unit_ty.clone()),
        ],
    );
    let mention_uninit_field =
        lower_statement(&Statement::PlaceMention(uninit_field_place.clone()), &local_decls, pw)
            .unwrap();
    eval_lowered_statement(&mention_uninit_field, &mut state).unwrap();

    // PlaceMention(*_4) when _4 is Uninit fails with UninitializedLocal(Local(4));
    // once _4 is initialized to a pointer, PlaceMention(*_4) succeeds without dereferencing!
    let deref_4 = Place::with_projection(4, vec![ProjectionElem::Deref]);
    let mention_deref_4 =
        lower_statement(&Statement::PlaceMention(deref_4), &local_decls, pw).unwrap();
    assert_eq!(
        eval_lowered_statement(&mention_deref_4, &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(4)))
    );
    state.slots[4] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(0xDEAD_0000),
        raw_u32.clone(),
    ));
    eval_lowered_statement(&mention_deref_4, &mut state).unwrap();

    // PlaceMention(_2[_3]) when _3 is Uninit fails with UninitializedLocal(Local(3));
    // when _3 is initialized to 0usize, PlaceMention(_2[_3]) succeeds even while _2 is Uninit!
    let arr_idx_place = Place::with_projection(2, vec![ProjectionElem::Index(Local(3))]);
    let mention_arr_idx =
        lower_statement(&Statement::PlaceMention(arr_idx_place.clone()), &local_decls, pw).unwrap();
    assert_eq!(
        eval_lowered_statement(&mention_arr_idx, &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(3)))
    );
    state.slots[3] = LocalSlotState::Init(MirValue::unsigned(0, UintTy::Usize, pw));
    eval_lowered_statement(&mention_arr_idx, &mut state).unwrap();

    // 2. C6d2ad74 parity: writing `_2[_3] = 42` when `_2` (an array) is Uninit MUST fail!
    let write_uninit_arr = lower_statement(
        &Statement::Assign(arr_idx_place, Rvalue::Use(Operand::Copy(Place::from_local(1)))),
        &local_decls,
        pw,
    )
    .unwrap();
    assert_eq!(
        eval_lowered_statement(&write_uninit_arr, &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(2)))
    );

    // 3. D13b nested field-by-field initialization & unwritten `()` sibling field check:
    // Write `_0.0.0 = Move(_1)` (moves _1 -> Uninit, initializes _0.0.0 while _0.0.1: () is Uninit!)
    let place_0_0_0 = Place::with_projection(
        0,
        vec![
            ProjectionElem::Field(0, inner_pair_ty.clone()),
            ProjectionElem::Field(0, u32_ty.clone()),
        ],
    );
    let place_0_0 = Place::with_projection(0, vec![ProjectionElem::Field(0, inner_pair_ty.clone())]);
    let place_0_1 = Place::with_projection(0, vec![ProjectionElem::Field(1, u8_ty.clone())]);

    let assign_0_0_0 = lower_statement(
        &Statement::Assign(place_0_0_0.clone(), Rvalue::Use(Operand::Move(Place::from_local(1)))),
        &local_decls,
        pw,
    )
    .unwrap();
    eval_lowered_statement(&assign_0_0_0, &mut state).unwrap();

    // _1 was moved so it is now Uninit!
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));
    assert_eq!(
        state.read_place(&Place::from_local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    // Reading `_0.0.0` succeeds (42u32), but reading unwritten `()` sibling `_0.0.1`,
    // inner pair `_0.0`, or root `_0` MUST fail with `UninitializedLocal(Local(0))`!
    assert_eq!(
        state.read_place(&place_0_0_0),
        Ok(MirValue::unsigned(42, UintTy::U32, pw))
    );
    assert_eq!(
        state.read_place(&uninit_field_place),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    assert_eq!(
        state.read_place(&place_0_0),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    assert_eq!(
        state.read_place(&Place::from_local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );

    // Now initialize `_0.0.1 = ()`: `_0.0` promotes to `FieldSlot::Init`, so reading `_0.0` succeeds,
    // while reading `_0` still fails because `_0.1` is still `Uninit`!
    let assign_0_0_1 = lower_statement(
        &Statement::Assign(
            uninit_field_place.clone(),
            Rvalue::Use(Operand::Constant(Constant::Unit)),
        ),
        &local_decls,
        pw,
    )
    .unwrap();
    eval_lowered_statement(&assign_0_0_1, &mut state).unwrap();
    assert_eq!(
        state.read_place(&uninit_field_place),
        Ok(MirValue::Unit)
    );
    assert_eq!(
        state.read_place(&place_0_0),
        Ok(MirValue::Tuple(vec![
            MirValue::unsigned(42, UintTy::U32, pw),
            MirValue::Unit,
        ]))
    );
    assert_eq!(
        state.read_place(&Place::from_local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );

    // Now initialize `_0.1 = 7u8`: `_0` promotes to `LocalSlotState::Init`!
    let assign_0_1 = lower_statement(
        &Statement::Assign(
            place_0_1.clone(),
            Rvalue::Use(Operand::Constant(Constant::Int(7, u8_ty.clone()))),
        ),
        &local_decls,
        pw,
    )
    .unwrap();
    eval_lowered_statement(&assign_0_1, &mut state).unwrap();
    let expected_full_0 = MirValue::Tuple(vec![
        MirValue::Tuple(vec![
            MirValue::unsigned(42, UintTy::U32, pw),
            MirValue::Unit,
        ]),
        MirValue::unsigned(7, UintTy::U8, pw),
    ]);
    assert_eq!(state.get_init(Local(0)), Some(&expected_full_0));

    // A projected move out of `_0.1` reads the field and, as in `Trusted.MirSemantics.evalOperand`
    // (`.move` with a non-empty projection), leaves the parent `_0` fully initialized.
    assert_eq!(
        state.move_place(&place_0_1),
        Ok(MirValue::unsigned(7, UintTy::U8, pw))
    );
    assert_eq!(state.get_init(Local(0)), Some(&expected_full_0));
    assert_eq!(
        state.read_place(&place_0_1),
        Ok(MirValue::unsigned(7, UintTy::U8, pw))
    );
    assert!(state.read_place(&place_0_0).is_ok());

    // 4. SetDiscriminant & enum variant initialization (`((_6 as Variant2).0) = 99; discriminant(_6) = 2;`)
    // SetDiscriminant on Uninit local _6 must fail with UninitializedLocal(Local(6))!
    let set_discr_6 = lower_statement(
        &Statement::SetDiscriminant {
            place: Place::from_local(6),
            variant_index: 2,
        },
        &local_decls,
        pw,
    )
    .unwrap();
    assert_eq!(
        eval_lowered_statement(&set_discr_6, &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(6)))
    );

    let enum_v2_f0 = Place::with_projection(
        6,
        vec![
            ProjectionElem::Downcast(2),
            ProjectionElem::Field(0, u32_ty.clone()),
        ],
    );
    let init_enum_f0 = lower_statement(
        &Statement::Assign(
            enum_v2_f0,
            Rvalue::Use(Operand::Constant(Constant::Int(99, u32_ty.clone()))),
        ),
        &local_decls,
        pw,
    )
    .unwrap();
    eval_lowered_statement(&init_enum_f0, &mut state).unwrap();
    eval_lowered_statement(&set_discr_6, &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(6)),
        Some(&MirValue::Adt {
            def_path: String::new(),
            variant_idx: 2,
            active_field: None,
            fields: vec![MirValue::unsigned(99, UintTy::U32, pw)],
            adt_def: None,
        })
    );

    // SetDiscriminant on non-tuple place type is rejected statically
    assert_eq!(
        lower_statement(
            &Statement::SetDiscriminant {
                place: Place::from_local(1),
                variant_index: 0,
            },
            &local_decls,
            pw,
        ),
        Err(RvalueLowerError::InvalidSetDiscriminantTarget(u32_ty.clone()))
    );

    // 5. Assume(true) vs Assume(false) and Assume static type check
    assert_eq!(
        lower_statement(
            &Statement::Assume(Operand::Constant(Constant::Int(1, u32_ty.clone()))),
            &local_decls,
            pw,
        ),
        Err(RvalueLowerError::InvalidAssumeType(u32_ty))
    );
    state.slots[5] = LocalSlotState::Init(MirValue::Bool(true));
    let assume_move_5 = lower_statement(
        &Statement::Assume(Operand::Move(Place::from_local(5))),
        &local_decls,
        pw,
    )
    .unwrap();
    eval_lowered_statement(&assume_move_5, &mut state).unwrap();
    assert_eq!(state.get_local(Local(5)), Some(&LocalSlotState::Uninit));

    let assume_false = lower_statement(
        &Statement::Assume(Operand::Constant(Constant::Bool(false))),
        &local_decls,
        pw,
    )
    .unwrap();
    assert_eq!(
        eval_lowered_statement(&assume_false, &mut state),
        Err(RvalueEvalError::AssumeFalse)
    );

    // 6. End-to-end LoweredBody + eval_lowered_block execution
    let body = Body {
        local_decls: vec![
            Ty::Uint(UintTy::Usize), // _0: return usize
            Ty::Char,                // _1: arg char
            Ty::Uint(UintTy::Usize), // _2: temp usize
            Ty::Bool,                // _3: temp bool
        ],
        basic_blocks: vec![BasicBlockData {
            statements: vec![
                Statement::StorageLive(Local(2)),
                Statement::StorageLive(Local(3)),
                Statement::Assign(
                    Place::from_local(3),
                    Rvalue::NullaryOp(NullOp::UbChecks, Ty::Bool),
                ),
                Statement::Assume(Operand::Move(Place::from_local(3))),
                Statement::Assign(
                    Place::from_local(2),
                    Rvalue::Cast(
                        CastKind::CharToInt,
                        Operand::Move(Place::from_local(1)),
                        Ty::Uint(UintTy::Usize),
                    ),
                ),
                Statement::Assign(
                    Place::from_local(0),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Move(Place::from_local(2)),
                        Operand::Constant(Constant::Int(10, Ty::Uint(UintTy::Usize))),
                    ),
                ),
                Statement::StorageDead(Local(3)),
                Statement::StorageDead(Local(2)),
            ],
            is_cleanup: false,
            terminator: None,
        }],
    };
    let lowered_body = lower_body(&body, pw).unwrap();
    let mut body_state =
        StatementEvalState::from_body(&lowered_body, &[MirValue::Char('A')]).unwrap();
    eval_lowered_block(&lowered_body.basic_blocks[0], &mut body_state).unwrap();
    assert_eq!(
        body_state.get_init(Local(0)),
        Some(&MirValue::unsigned(75, UintTy::Usize, pw))
    );
    assert_eq!(body_state.get_local(Local(1)), Some(&LocalSlotState::Uninit));
    assert_eq!(body_state.get_local(Local(2)), Some(&LocalSlotState::Dead));
    assert_eq!(body_state.get_local(Local(3)), Some(&LocalSlotState::Dead));
}
