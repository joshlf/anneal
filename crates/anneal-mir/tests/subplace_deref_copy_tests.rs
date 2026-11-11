//! Comprehensive unit and adversarial integration tests for Episode 1:
//! - Layout-offset synthetic sub-place borrows (`Rvalue::Ref` & `Rvalue::RawPtr`, reborrows
//!   `&((*_p).proj)`, and collision-free large-local base addresses when locals exceed `0x1000`
//!   bytes).
//! - Synthetic sub-place `ProjectionElem::Deref` evaluation (`*_p`, `(*_p).tail`, `(**_pp).tail`)
//!   across `read_place`, `move_place`, `write_place`, `deinit_place`, `retag_place`,
//!   `check_retagged_reference` (dangling sub-place `DeadLocal`), `SetDiscriminant`,
//!   `Discriminant`, `Len`, `PlaceMention`, and `LoweredTerminator::{Drop, Call}`.
//! - Sub-place (`count == 1`, preserving `Uninit`/`PartialShell`/`Init`) and contiguous
//!   array-window (`count >= 1`) `eval_copy_nonoverlapping`.

use std::sync::Arc;

use anneal_mir::ir::{
    AdtDef, AdtRepr, AdtReprKind, BasicBlockData, BinOp, Body, CastKind, Constant, Local,
    Mutability, Operand, Place, PointerValue, ProjectionElem, PtrWidth, RetagKind, Rvalue,
    ScalarTy, Statement, Terminator, Ty, UintTy, UnwindAction, VariantDef,
};
use anneal_mir::lower::{
    CallOutcome, CfgEvalError, CfgEvalOutcome, CastEvalError, ExposedProvenanceTracker,
    LocalSlotState, MirValue, RvalueEvalError, StatementEvalState, TransmutePolicy,
    eval_lowered_body_cfg_with_calls, eval_lowered_rvalue, eval_lowered_statement,
    eval_place_read, eval_place_write, lower_body, lower_rvalue, lower_statement,
};

const PW: PtrWidth = PtrWidth::Bits64;

fn u8_ty() -> Ty {
    Ty::Uint(UintTy::U8)
}

fn u16_ty() -> Ty {
    Ty::Uint(UintTy::U16)
}

fn u32_ty() -> Ty {
    Ty::Uint(UintTy::U32)
}

fn u64_ty() -> Ty {
    Ty::Uint(UintTy::U64)
}

fn usize_ty() -> Ty {
    Ty::Uint(UintTy::Usize)
}

fn u8v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U8, PW)
}

fn u16v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U16, PW)
}

fn u32v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U32, PW)
}

fn u64v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U64, PW)
}

fn usizev(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::Usize, PW)
}

fn local(idx: usize) -> Place {
    Place::from_local(idx)
}

fn proj(idx: usize, elems: Vec<ProjectionElem>) -> Place {
    Place::with_projection(idx, elems)
}

fn field(idx: usize, ty: Ty) -> ProjectionElem {
    ProjectionElem::Field(idx, ty)
}

fn run(stmt: Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = lower_statement(&stmt, &state.local_decls, state.ptr_width)
        .expect("statement must lower cleanly");
    eval_lowered_statement(&lowered, state)
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign(place, rvalue)
}

fn repr_c() -> AdtRepr {
    AdtRepr {
        kind: AdtReprKind::C,
        align: None,
    }
}

#[test]
fn test_subplace_borrows_and_reborrows_compute_exact_layout_offsets() {
    // `#[repr(C)] struct Inner { a: u16, b: u32 }` -> size 8, align 4 (`a` at 0, `b` at 4).
    let inner_def = Arc::new(
        AdtDef::new_struct("Inner", vec![u16_ty(), u32_ty()]).with_repr(repr_c()),
    );
    let inner_ty = Ty::Adt(inner_def.clone());
    // `#[repr(C)] struct Outer { x: u32, inner: Inner, arr: [u32; 4] }` ->
    // `x` at 0, `inner` at 4 (`inner.a` at 4, `inner.b` at 8), `arr` at 12 (`arr[i]` at 12 + 4*i).
    let arr4_ty = Ty::Array(Box::new(u32_ty()), 4);
    let arr2_ty = Ty::Array(Box::new(u32_ty()), 2);
    let outer_def = Arc::new(
        AdtDef::new_struct("Outer", vec![u32_ty(), inner_ty.clone(), arr4_ty.clone()])
            .with_repr(repr_c()),
    );
    let outer_ty = Ty::Adt(outer_def.clone());

    // `#[repr(u8)] enum Tagged { V0(u32), V1(u64, u32) }` ->
    // V0.0 at offset 4, V1.0 at offset 8, V1.1 at offset 16.
    let enum_def = Arc::new(AdtDef::new_enum(
        "Tagged",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("V0", vec![u32_ty()]),
            VariantDef::new("V1", vec![u64_ty(), u32_ty()]),
        ],
    ));
    let enum_ty = Ty::Adt(enum_def.clone());

    let ref_inner = Ty::Ref(Box::new(inner_ty.clone()), Mutability::Not);
    let raw_u32_mut = Ty::RawPtr(Box::new(u32_ty()), Mutability::Mut);
    let ref_u32 = Ty::Ref(Box::new(u32_ty()), Mutability::Not);
    let ref_arr2 = Ty::Ref(Box::new(arr2_ty.clone()), Mutability::Not);

    let decls = vec![
        outer_ty.clone(),       // _0 at 0x1000
        usize_ty(),             // _1 at 0x2000 (dynamic index)
        enum_ty.clone(),        // _2 at 0x3000
        ref_inner.clone(),      // _3: &Inner
        raw_u32_mut.clone(),    // _4: *mut u32
        ref_u32.clone(),        // _5: &u32
        ref_arr2.clone(),       // _6: &[u32; 2]
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[1] = LocalSlotState::Init(usizev(2));
    state.slots[2] = LocalSlotState::Init(MirValue::adt(&enum_def, 1, vec![u64v(10), u32v(20)]));

    // 1. `&_0.inner` -> 0x1000 + 4 = 0x1004
    run(
        assign(
            local(3),
            Rvalue::Ref(Mutability::Not, proj(0, vec![field(1, inner_ty.clone())])),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1004, 1, 1),
            ref_inner
        ))
    );

    // 2. `&raw mut _0.inner.b` -> 0x1000 + 4 + 4 = 0x1008
    run(
        assign(
            local(4),
            Rvalue::RawPtr(
                Mutability::Mut,
                proj(0, vec![field(1, inner_ty.clone()), field(1, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1008, 1, 1),
            raw_u32_mut.clone()
        ))
    );

    // 3. Reborrow `&((*_3).b)` through `_3: &Inner` -> 0x1004 + 4 = 0x1008
    run(
        assign(
            local(5),
            Rvalue::Ref(
                Mutability::Not,
                proj(3, vec![ProjectionElem::Deref, field(1, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(5)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1008, 1, 1),
            ref_u32.clone()
        ))
    );

    // 4. `&_0.arr[_1]` with `_1 = 2` -> 0x1000 + 12 + 2*4 = 0x1014
    run(
        assign(
            local(5),
            Rvalue::Ref(
                Mutability::Not,
                proj(
                    0,
                    vec![field(2, arr4_ty.clone()), ProjectionElem::Index(Local(1))],
                ),
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(5)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1014, 1, 1),
            ref_u32.clone()
        ))
    );

    // 5. `&_0.arr[1..3]` -> 0x1000 + 12 + 1*4 = 0x1010
    run(
        assign(
            local(6),
            Rvalue::Ref(
                Mutability::Not,
                proj(
                    0,
                    vec![
                        field(2, arr4_ty),
                        ProjectionElem::Subslice {
                            from: 1,
                            to: 3,
                            from_end: false,
                        },
                    ],
                ),
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(6)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1010, 1, 1),
            ref_arr2
        ))
    );

    // 6. `&((_2 as V1).1)` on active variant 1 -> 0x3000 + 16 = 0x3010
    run(
        assign(
            local(5),
            Rvalue::Ref(
                Mutability::Not,
                proj(2, vec![ProjectionElem::Downcast(1), field(1, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(5)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x3010, 3, 1),
            ref_u32
        ))
    );

    // Inactive variant borrow `&((_2 as V0).0)` faults with `InactiveVariantProjection`.
    assert_eq!(
        run(
            assign(
                local(4),
                Rvalue::RawPtr(
                    Mutability::Mut,
                    proj(2, vec![ProjectionElem::Downcast(0), field(0, u32_ty())]),
                ),
            ),
            &mut state,
        ),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 0,
            actual: 1,
        })
    );
}

#[test]
fn test_large_local_synthetic_addresses_do_not_collide() {
    // `_0`: u32 (size 4 <= 0x1000 -> base 0x1000, stride 0x1000)
    // `_1`: [u8; 0x2500] (size 0x2500 > 0x1000 -> base 0x2000, stride 0x3000)
    // `_2`: u32 (base 0x5000, NOT 0x3000!)
    let large_arr_ty = Ty::Array(Box::new(u8_ty()), 0x2500);
    let raw_u8 = Ty::RawPtr(Box::new(u8_ty()), Mutability::Mut);
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty()), Mutability::Mut);
    let decls = vec![
        u32_ty(),
        large_arr_ty,
        u32_ty(),
        usize_ty(),
        raw_u8.clone(),
        raw_u32.clone(),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[2] = LocalSlotState::Init(u32v(77));
    state.slots[3] = LocalSlotState::Init(usizev(0x2400));

    // `&raw mut _1[_3]` at index 0x2400 -> 0x2000 + 0x2400 = 0x4400
    run(
        assign(
            local(4),
            Rvalue::RawPtr(Mutability::Mut, proj(1, vec![ProjectionElem::Index(Local(3))])),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x4400, 2, 1),
            raw_u8
        ))
    );

    // `&raw mut _2` -> 0x5000 (no overlap with `_1`'s `[0x2000, 0x4500)` range!)
    run(
        assign(local(5), Rvalue::RawPtr(Mutability::Mut, local(2))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(5)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x5000, 3, 1),
            raw_u32
        ))
    );

    // Dereferencing `*_5` reads `_2` (77) and writing `*_5 = 88` updates `_2`.
    assert_eq!(
        state.read_place(&proj(5, vec![ProjectionElem::Deref])),
        Ok(u32v(77))
    );
    state
        .write_place(&proj(5, vec![ProjectionElem::Deref]), &u32_ty(), u32v(88))
        .unwrap();
    assert_eq!(state.get_init(Local(2)), Some(&u32v(88)));
}

#[test]
fn test_deref_read_write_deinit_retag_discriminant_len_and_multi_level_chains() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let outer_ty = Ty::Tuple(vec![pair_ty.clone(), Ty::Array(Box::new(u32_ty()), 3)]);
    let ref_pair_mut = Ty::Ref(Box::new(pair_ty.clone()), Mutability::Mut);
    let ref_ref_pair_mut = Ty::Ref(Box::new(ref_pair_mut.clone()), Mutability::Not);
    let ref_u32 = Ty::Ref(Box::new(u32_ty()), Mutability::Not);
    let ref_arr3 = Ty::Ref(Box::new(Ty::Array(Box::new(u32_ty()), 3)), Mutability::Not);

    let enum_def = Arc::new(AdtDef::new_enum(
        "OptU32",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("None", vec![]),
            VariantDef::new("Some", vec![u32_ty()]),
        ],
    ));
    let enum_ty = Ty::Adt(enum_def.clone());
    let raw_enum_mut = Ty::RawPtr(Box::new(enum_ty.clone()), Mutability::Mut);

    let decls = vec![
        outer_ty.clone(),        // _0: ((u32, u32), [u32; 3])
        ref_pair_mut.clone(),    // _1: &mut (u32, u32)
        ref_ref_pair_mut,        // _2: &&mut (u32, u32)
        ref_u32.clone(),         // _3: &u32
        ref_arr3,                // _4: &[u32; 3]
        usize_ty(),              // _5: usize
        enum_ty.clone(),         // _6: OptU32
        raw_enum_mut,            // _7: *mut OptU32
        u8_ty(),                 // _8: u8 discriminant
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);

    // Borrow `_1 = &mut _0.0` and `_2 = &_1` while `_0` is still `Uninit`.
    run(
        assign(
            local(1),
            Rvalue::Ref(Mutability::Mut, proj(0, vec![field(0, pair_ty.clone())])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(2), Rvalue::Ref(Mutability::Not, local(1))),
        &mut state,
    )
    .unwrap();

    // Write `(**_2).0 = 10` and `(*_1).1 = 20`: `_0.0` promotes to `Init((10, 20))` inside `_0`'s `PartialShell`.
    let pp_f0 = proj(
        2,
        vec![
            ProjectionElem::Deref,
            ProjectionElem::Deref,
            field(0, u32_ty()),
        ],
    );
    let p_f1 = proj(1, vec![ProjectionElem::Deref, field(1, u32_ty())]);
    state.write_place(&pp_f0, &u32_ty(), u32v(10)).unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    state.write_place(&p_f1, &u32_ty(), u32v(20)).unwrap();
    assert_eq!(
        state.read_place(&proj(1, vec![ProjectionElem::Deref])),
        Ok(MirValue::Tuple(vec![u32v(10), u32v(20)]))
    );

    // Initialize `_0.1` via `&_0.1` -> `_0` promotes to full `LocalSlotState::Init`!
    state
        .write_place(
            &proj(0, vec![field(1, Ty::Array(Box::new(u32_ty()), 3))]),
            &Ty::Array(Box::new(u32_ty()), 3),
            MirValue::Array {
                elements: vec![u32v(1), u32v(2), u32v(3)],
                elem_ty: u32_ty(),
            },
        )
        .unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::Init(_))
    ));

    // `Len(*_4)` on `_4 = &_0.1` evaluates to `3usize`.
    run(
        assign(
            local(4),
            Rvalue::Ref(
                Mutability::Not,
                proj(0, vec![field(1, Ty::Array(Box::new(u32_ty()), 3))]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(5),
            Rvalue::Len(proj(4, vec![ProjectionElem::Deref])),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(5)), Some(&usizev(3)));

    // `Deinit((**_2).1)` demotes `_0` back to `PartialShell` with `_0.0.1` uninitialized.
    run(Statement::Deinit(p_f1.clone()), &mut state).unwrap();
    assert_eq!(
        state.read_place(&p_f1),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    assert_eq!(state.read_place(&pp_f0), Ok(u32v(10)));

    // `PlaceMention((**_2).1)` succeeds without loading the uninitialized target field.
    run(Statement::PlaceMention(p_f1), &mut state).unwrap();

    // Sub-place reference retag: `_3 = &(*_1).0` (offset 0) and `_3 = &(*_1).1` (offset 4).
    // When `_0` becomes `StorageDead`, `Retag(_3)` at non-zero offset `rel_off = 4` faults with `DeadLocal(Local(0))`.
    run(
        assign(
            local(3),
            Rvalue::Ref(
                Mutability::Not,
                proj(1, vec![ProjectionElem::Deref, field(1, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    run(
        Statement::Retag(RetagKind::Default, local(3)),
        &mut state,
    )
    .unwrap();
    run(Statement::StorageDead(Local(0)), &mut state).unwrap();
    assert_eq!(
        run(Statement::Retag(RetagKind::Default, local(3)), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(0)))
    );

    // `SetDiscriminant` and `Discriminant` through `*_7` (`*mut OptU32`).
    run(
        assign(local(7), Rvalue::RawPtr(Mutability::Mut, local(6))),
        &mut state,
    )
    .unwrap();
    let deref_7_some_0 = proj(
        7,
        vec![
            ProjectionElem::Deref,
            ProjectionElem::Downcast(1),
            field(0, u32_ty()),
        ],
    );
    state
        .write_place(&deref_7_some_0, &u32_ty(), u32v(99))
        .unwrap();
    run(
        Statement::SetDiscriminant {
            place: proj(7, vec![ProjectionElem::Deref]),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(6)),
        Some(&MirValue::adt(&enum_def, 1, vec![u32v(99)]))
    );
    run(
        assign(
            local(8),
            Rvalue::Discriminant(proj(7, vec![ProjectionElem::Deref])),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(8)), Some(&u8v(1)));
}

#[test]
fn test_terminator_drop_and_call_destination_with_deref_subplaces() {
    // Test CFG with `Drop((*_1).0)` and `Call { destination: (*_1).1, .. }`.
    let pair_ty = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let ref_pair_mut = Ty::Ref(Box::new(pair_ty.clone()), Mutability::Mut);
    let body = Body {
        local_decls: vec![
            u32_ty(),       // _0: return place
            ref_pair_mut,   // _1: &mut (u32, u32)
            pair_ty,        // _2: (u32, u32)
        ],
        basic_blocks: vec![
            BasicBlockData {
                statements: vec![
                    Statement::StorageLive(Local(2)),
                    assign(
                        proj(2, vec![field(0, u32_ty())]),
                        Rvalue::Use(Operand::Constant(Constant::Int(10, u32_ty()))),
                    ),
                    assign(
                        local(1),
                        Rvalue::Ref(Mutability::Mut, local(2)),
                    ),
                ],
                terminator: Some(Terminator::Drop {
                    place: proj(1, vec![ProjectionElem::Deref, field(0, u32_ty())]),
                    target: 1,
                    unwind: UnwindAction::Continue,
                }),
                is_cleanup: false,
            },
            BasicBlockData {
                statements: vec![],
                terminator: Some(Terminator::Call {
                    func: Operand::Constant(Constant::Int(1, usize_ty())),
                    args: vec![Operand::Copy(proj(
                        1,
                        vec![ProjectionElem::Deref, field(0, u32_ty())],
                    ))],
                    destination: proj(1, vec![ProjectionElem::Deref, field(1, u32_ty())]),
                    target: Some(2),
                    unwind: UnwindAction::Continue,
                }),
                is_cleanup: false,
            },
            BasicBlockData {
                statements: vec![assign(
                    local(0),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(proj(2, vec![field(0, u32_ty())])),
                        Operand::Copy(proj(2, vec![field(1, u32_ty())])),
                    ),
                )],
                terminator: Some(Terminator::Return),
                is_cleanup: false,
            },
        ],
    };
    let lowered = lower_body(&body, PW).unwrap();
    let ptr_arg = MirValue::ptr(
        PointerValue::with_provenance(0x3000, 3, 1),
        Ty::Ref(Box::new(Ty::Tuple(vec![u32_ty(), u32_ty()])), Mutability::Mut),
    );
    let outcome = eval_lowered_body_cfg_with_calls(
        &lowered,
        std::slice::from_ref(&ptr_arg),
        10,
        |_bb, _f, args| {
            assert_eq!(args, &[u32v(10)]);
            Ok(CallOutcome::Return(u32v(32)))
        },
    )
    .unwrap();
    assert_eq!(outcome, CfgEvalOutcome::Returned(u32v(42)));

    // If `_2` is `StorageDead` before `Drop((*_1).0)`, `Drop` faults with `DeadLocal(Local(2))`.
    let dead_drop_body = Body {
        local_decls: body.local_decls.clone(),
        basic_blocks: vec![BasicBlockData {
            statements: vec![
                Statement::StorageLive(Local(2)),
                assign(local(1), Rvalue::Ref(Mutability::Mut, local(2))),
                Statement::StorageDead(Local(2)),
            ],
            terminator: Some(Terminator::Drop {
                place: proj(1, vec![ProjectionElem::Deref, field(0, u32_ty())]),
                target: 0,
                unwind: UnwindAction::Continue,
            }),
            is_cleanup: false,
        }],
    };
    let lowered_dead = lower_body(&dead_drop_body, PW).unwrap();
    assert_eq!(
        eval_lowered_body_cfg_with_calls(&lowered_dead, &[ptr_arg], 10, |_, _, _| {
            unreachable!()
        }),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::DeadLocal(Local(2)),
        })
    );
}

#[test]
fn test_copy_nonoverlapping_subplaces_partial_shells_and_array_windows() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    // `#[repr(C)] struct Outer { x: u32, pair: (u32, u32) }` (`pair` at offset 4). A repr(Rust)
    // `(u32, (u32, u32))` would not do: `rustc` lays it out pair-first, so its declaration-order
    // field offsets are unspecified.
    let outer_def = Arc::new(
        AdtDef::new_struct("Outer", vec![u32_ty(), pair_ty.clone()]).with_repr(repr_c()),
    );
    let outer_ty = Ty::Adt(outer_def.clone());
    let arr4_ty = Ty::Array(Box::new(u32_ty()), 4);
    let raw_u32_const = Ty::RawPtr(Box::new(u32_ty()), Mutability::Not);
    let raw_u32_mut = Ty::RawPtr(Box::new(u32_ty()), Mutability::Mut);
    let raw_pair_const = Ty::RawPtr(Box::new(pair_ty.clone()), Mutability::Not);
    let raw_pair_mut = Ty::RawPtr(Box::new(pair_ty.clone()), Mutability::Mut);

    let decls = vec![
        outer_ty.clone(),       // _0: Outer
        outer_ty.clone(),       // _1: Outer
        arr4_ty.clone(),        // _2: [u32; 4]
        arr4_ty.clone(),        // _3: [u32; 4]
        u32_ty(),               // _4: u32
        raw_u32_const.clone(),  // _5: *const u32
        raw_u32_mut.clone(),    // _6: *mut u32
        raw_pair_const.clone(), // _7: *const (u32, u32)
        raw_pair_mut.clone(),   // _8: *mut (u32, u32)
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);

    // 1. Copy `PartialShell` sub-place `_0.1` (where `_0.1.0 = 11`, `_0.1.1 = Uninit`) into
    // initialized `_1.1`, demoting `_1` to `PartialShell`.
    state
        .write_place(
            &proj(0, vec![field(1, pair_ty.clone()), field(0, u32_ty())]),
            &u32_ty(),
            u32v(11),
        )
        .unwrap();
    state.slots[1] = LocalSlotState::Init(MirValue::adt(
        &outer_def,
        0,
        vec![u32v(1), MirValue::Tuple(vec![u32v(2), u32v(3)])],
    ));
    run(
        assign(
            local(7),
            Rvalue::RawPtr(Mutability::Not, proj(0, vec![field(1, pair_ty.clone())])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(8),
            Rvalue::RawPtr(Mutability::Mut, proj(1, vec![field(1, pair_ty.clone())])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        Statement::CopyNonOverlapping {
            src: Operand::Copy(local(7)),
            dst: Operand::Copy(local(8)),
            count: Operand::Constant(Constant::Int(1, usize_ty())),
        },
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(1)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        state.read_place(&proj(1, vec![field(1, pair_ty.clone()), field(0, u32_ty())])),
        Ok(u32v(11))
    );
    assert_eq!(
        state.read_place(&proj(1, vec![field(1, pair_ty.clone()), field(1, u32_ty())])),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );

    // 2. Copy scalar `_4 = 22` into `_1.1.1` via `copy_nonoverlapping` -> promotes `_1` back to `Init`!
    state.slots[4] = LocalSlotState::Init(u32v(22));
    run(
        assign(local(5), Rvalue::RawPtr(Mutability::Not, local(4))),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(6),
            Rvalue::RawPtr(
                Mutability::Mut,
                proj(1, vec![field(1, pair_ty), field(1, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    run(
        Statement::CopyNonOverlapping {
            src: Operand::Copy(local(5)),
            dst: Operand::Copy(local(6)),
            count: Operand::Constant(Constant::Int(1, usize_ty())),
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::adt(
            &outer_def,
            0,
            vec![u32v(1), MirValue::Tuple(vec![u32v(11), u32v(22)])],
        ))
    );

    // 3. Contiguous array-window copies (`count >= 1`):
    // Initialize `_2 = [10, 20, 30, 40]` and `_3 = [1, 2, 3, 4]`.
    state.slots[2] = LocalSlotState::Init(MirValue::Array {
        elements: vec![u32v(10), u32v(20), u32v(30), u32v(40)],
        elem_ty: u32_ty(),
    });
    state.slots[3] = LocalSlotState::Init(MirValue::Array {
        elements: vec![u32v(1), u32v(2), u32v(3), u32v(4)],
        elem_ty: u32_ty(),
    });

    // Copy 2 elements from `&_2[1]` to `&mut _3[2]` -> `_3` becomes `[1, 2, 20, 30]`.
    let idx1 = ProjectionElem::ConstantIndex {
        offset: 1,
        min_length: 4,
        from_end: false,
    };
    let idx2 = ProjectionElem::ConstantIndex {
        offset: 2,
        min_length: 4,
        from_end: false,
    };
    run(
        assign(
            local(5),
            Rvalue::RawPtr(Mutability::Not, proj(2, vec![idx1.clone()])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(6),
            Rvalue::RawPtr(Mutability::Mut, proj(3, vec![idx2.clone()])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        Statement::CopyNonOverlapping {
            src: Operand::Copy(local(5)),
            dst: Operand::Copy(local(6)),
            count: Operand::Constant(Constant::Int(2, usize_ty())),
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::Array {
            elements: vec![u32v(1), u32v(2), u32v(20), u32v(30)],
            elem_ty: u32_ty(),
        })
    );

    // Non-overlapping copy within the SAME array `_3`: copy `&_3[2..4]` into `&mut _3[0..2]`.
    let idx0 = ProjectionElem::ConstantIndex {
        offset: 0,
        min_length: 4,
        from_end: false,
    };
    run(
        assign(
            local(5),
            Rvalue::RawPtr(Mutability::Not, proj(3, vec![idx2])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(6),
            Rvalue::RawPtr(Mutability::Mut, proj(3, vec![idx0.clone()])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        Statement::CopyNonOverlapping {
            src: Operand::Copy(local(5)),
            dst: Operand::Copy(local(6)),
            count: Operand::Constant(Constant::Int(2, usize_ty())),
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::Array {
            elements: vec![u32v(20), u32v(30), u32v(20), u32v(30)],
            elem_ty: u32_ty(),
        })
    );

    // Overlapping copy within `_3` (`&_3[0..3]` and `&mut _3[1..4]`) faults with `CopyNonOverlappingOverlap`.
    run(
        assign(local(5), Rvalue::RawPtr(Mutability::Not, proj(3, vec![idx0]))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(6), Rvalue::RawPtr(Mutability::Mut, proj(3, vec![idx1]))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        run(
            Statement::CopyNonOverlapping {
                src: Operand::Copy(local(5)),
                dst: Operand::Copy(local(6)),
                count: Operand::Constant(Constant::Int(3, usize_ty())),
            },
            &mut state,
        ),
        Err(RvalueEvalError::CopyNonOverlappingOverlap { .. })
    ));

    // Copying an `Uninit` scalar into an array element fails closed with `UninitializedLocal` (`c6d2ad74`).
    state.slots[4] = LocalSlotState::Uninit;
    run(
        assign(local(5), Rvalue::RawPtr(Mutability::Not, local(4))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        run(
            Statement::CopyNonOverlapping {
                src: Operand::Copy(local(5)),
                dst: Operand::Copy(local(6)),
                count: Operand::Constant(Constant::Int(1, usize_ty())),
            },
            &mut state,
        ),
        Err(RvalueEvalError::UninitializedLocal(Local(4)))
    );
}

#[test]
fn test_adversarial_deref_errors_and_zst_disambiguation() {
    let zst_pair = Ty::Tuple(vec![Ty::unit(), Ty::unit()]);
    let raw_unit_mut = Ty::RawPtr(Box::new(Ty::unit()), Mutability::Mut);
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty()), Mutability::Not);
    let ref_u32 = Ty::Ref(Box::new(u32_ty()), Mutability::Not);
    let ref_never = Ty::Ref(Box::new(Ty::Never), Mutability::Not);

    let decls = vec![
        zst_pair.clone(),       // _0: ((), ())
        raw_unit_mut.clone(),   // _1: *mut ()
        raw_unit_mut,           // _2: *mut ()
        u32_ty(),               // _3: u32
        raw_u32.clone(),        // _4: *const u32
        ref_u32.clone(),        // _5: &u32
        ref_never.clone(),      // _6: &!
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::Tuple(vec![MirValue::Unit, MirValue::Unit]));

    // Disambiguate same-offset ZST sibling fields `_0.0` and `_0.1` via provenance tag:
    // deinitializing `*_1` (`&raw mut _0.0`) leaves `_0.1` initialized and `_0.0` uninitialized!
    run(
        assign(
            local(1),
            Rvalue::RawPtr(Mutability::Mut, proj(0, vec![field(0, Ty::unit())])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(2),
            Rvalue::RawPtr(Mutability::Mut, proj(0, vec![field(1, Ty::unit())])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        Statement::Deinit(proj(1, vec![ProjectionElem::Deref])),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.read_place(&proj(1, vec![ProjectionElem::Deref])),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    assert_eq!(
        state.read_place(&proj(2, vec![ProjectionElem::Deref])),
        Ok(MirValue::Unit)
    );

    // Null raw pointer deref -> `NullPointerAccess`; null reference deref -> `InvalidBitPattern`.
    state.slots[4] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(0),
        raw_u32.clone(),
    ));
    assert_eq!(
        state.read_place(&proj(4, vec![ProjectionElem::Deref])),
        Err(RvalueEvalError::NullPointerAccess)
    );
    state.slots[5] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(0),
        ref_u32.clone(),
    ));
    assert_eq!(
        state.read_place(&proj(5, vec![ProjectionElem::Deref])),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ref_u32,
            bits: 0,
        }))
    );

    // Misaligned pointer deref -> `MisalignedPointer`.
    state.slots[4] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::with_provenance(0x4002, 4, 1),
        raw_u32.clone(),
    ));
    assert_eq!(
        state.read_place(&proj(4, vec![ProjectionElem::Deref])),
        Err(RvalueEvalError::MisalignedPointer {
            addr: 0x4002,
            required_align: 4,
        })
    );

    // Uninhabited reference pointee `&!` -> `UninhabitedPointee`.
    state.slots[6] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::with_provenance(0x4000, 4, 1),
        ref_never,
    ));
    assert_eq!(
        state.read_place(&proj(6, vec![ProjectionElem::Deref])),
        Err(RvalueEvalError::UninhabitedPointee(Ty::Never))
    );

    // Out-of-bounds offset in `_3: u32` (at `0x4000`, size 4): `0x4004` -> `UnsupportedPlaceProjection`.
    state.slots[4] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::with_provenance(0x4004, 4, 1),
        raw_u32,
    ));
    let deref4 = proj(4, vec![ProjectionElem::Deref]);
    assert_eq!(
        state.read_place(&deref4),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref4))
    );

    // Stateless `eval_place_read`, `eval_place_write`, and `eval_lowered_rvalue` with `Deref`.
    // (`(u32, u16, u16)` is canonical, so `_0.1` sits at its declaration offset 4; a padded
    // `(u32, u16)` has no committed repr(Rust) field offsets.)
    let mut locals = vec![
        MirValue::Tuple(vec![u32v(100), u16v(200), u16v(0)]),
        MirValue::ptr(
            PointerValue::with_provenance(0x1004, 1, 1),
            Ty::Ref(Box::new(u16_ty()), Mutability::Mut),
        ),
    ];
    let deref1 = proj(1, vec![ProjectionElem::Deref]);
    assert_eq!(eval_place_read(&deref1, &locals, PW), Ok(u16v(200)));
    eval_place_write(&deref1, u16v(300), &mut locals, PW).unwrap();
    assert_eq!(
        locals[0],
        MirValue::Tuple(vec![u32v(100), u16v(300), u16v(0)])
    );
    let mut tracker = ExposedProvenanceTracker::new();
    let rval = lower_rvalue(
        &Rvalue::Use(Operand::Copy(deref1)),
        &[
            Ty::Tuple(vec![u32_ty(), u16_ty(), u16_ty()]),
            Ty::Ref(Box::new(u16_ty()), Mutability::Mut),
        ],
        PW,
    )
    .unwrap();
    assert_eq!(
        eval_lowered_rvalue(&rval, &locals, PW, TransmutePolicy::RejectPtrToInt, &mut tracker),
        Ok(u16v(300))
    );
    let _ = CastKind::PtrToPtr;
}

#[test]
fn a1_union_whole_field_overwrite_via_deref_and_copy_nonoverlapping_switches_active_field() {
    // Heterogeneous `union U { a: u64, b: u32 }` initialized to `a = 0x1_0000_0002`:
    // writing `*(&raw mut u.b) = 42` or `copy_nonoverlapping(&src, &raw mut u.b, 1)` overwrites
    // union field `b` and switches the active union field to `b` (`active_field == Some(1)`),
    // while reading `*(&raw const u.b)` while `a` is active remains unsupported.
    let u_def = Arc::new(AdtDef::new_union("U", vec![u64_ty(), u32_ty()]));
    let u_ty = Ty::Adt(u_def.clone());
    // Homogeneous `union U2 { a: u32, b: u32 }` initialized to `a = 10`:
    // `&raw mut u2.b` carries the sub-place tag for field `1`, so `*p = 99` switches `u2`'s
    // active field to `b` (`Some(1)`).
    let u2_def = Arc::new(AdtDef::new_union("U2", vec![u32_ty(), u32_ty()]));
    let u2_ty = Ty::Adt(u2_def.clone());
    let decls = vec![
        u_ty.clone(),                               // _0: U
        Ty::RawPtr(Box::new(u32_ty()), Mutability::Mut), // _1: *mut u32
        u32_ty(),                                   // _2: u32
        Ty::RawPtr(Box::new(u32_ty()), Mutability::Not), // _3: *const u32
        u2_ty.clone(),                              // _4: U2
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&u_def, 0, u64v(0x1_0000_0002)));
    run(
        assign(
            local(1),
            Rvalue::RawPtr(Mutability::Mut, proj(0, vec![field(1, u32_ty())])),
        ),
        &mut state,
    )
    .unwrap();
    // Reading `*(&raw mut _0.b)` while `_0.a` (`u64`) is active is unsupported (no byte punning).
    let deref1 = proj(1, vec![ProjectionElem::Deref]);
    assert_eq!(
        state.read_place(&deref1),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref1.clone()))
    );
    // Whole-field write `*_1 = 42` switches active union field to `b` (`1`).
    state.write_place(&deref1, &u32_ty(), u32v(42)).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&u_def, 1, u32v(42)))
    );
    assert_eq!(state.read_place(&deref1), Ok(u32v(42)));

    // Reset `_0` to `a = 0x1_0000_0002` and overwrite `_0.b` via `copy_nonoverlapping` (`count == 1`).
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&u_def, 0, u64v(0x1_0000_0002)));
    state.slots[2] = LocalSlotState::Init(u32v(77));
    run(
        assign(local(3), Rvalue::RawPtr(Mutability::Not, local(2))),
        &mut state,
    )
    .unwrap();
    run(
        Statement::CopyNonOverlapping {
            src: Operand::Copy(local(3)),
            dst: Operand::Copy(local(1)),
            count: Operand::Constant(Constant::Int(1, usize_ty())),
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&u_def, 1, u32v(77)))
    );

    // Same-type union `U2 { a: u32, b: u32 }`: `&raw mut _4.b` switches active field from `0` to `1`.
    state.slots[4] = LocalSlotState::Init(MirValue::union_value(&u2_def, 0, u32v(10)));
    run(
        assign(
            local(1),
            Rvalue::RawPtr(Mutability::Mut, proj(4, vec![field(1, u32_ty())])),
        ),
        &mut state,
    )
    .unwrap();
    state.write_place(&deref1, &u32_ty(), u32v(99)).unwrap();
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::union_value(&u2_def, 1, u32v(99)))
    );
    assert_eq!(
        state.read_place(&proj(4, vec![field(1, u32_ty())])),
        Ok(u32v(99))
    );
}

#[test]
fn a1_exposed_provenance_prediction_selects_matching_local_allocation() {
    // When multiple locals have exposed provenance (`_0` at `0x1000` with `alloc_id = 1` and
    // `_1` at `0x2000` with `alloc_id = 2`), `PointerWithExposedProvenance` on `_1`'s address
    // (`0x2004` for `_1.1`) must predict `_1`'s provenance (`alloc_id = 2`), not `_0`'s.
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty()), Mutability::Mut);
    let decls = vec![
        u32_ty(),       // _0 at 0x1000
        pair.clone(),   // _1 at 0x2000
        raw_u32.clone(), // _2
        usize_ty(),     // _3
        usize_ty(),     // _4
        raw_u32,        // _5
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u32v(1));
    state.slots[1] = LocalSlotState::Init(MirValue::Tuple(vec![u32v(10), u32v(20)]));

    // Expose `_0`'s provenance first (`alloc_id = 1`).
    run(
        assign(local(2), Rvalue::RawPtr(Mutability::Mut, local(0))),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(3),
            Rvalue::Cast(
                CastKind::PointerExposeProvenance,
                Operand::Copy(local(2)),
                usize_ty(),
            ),
        ),
        &mut state,
    )
    .unwrap();

    // Expose `_1.1`'s provenance second (`alloc_id = 2` at `0x2004`).
    run(
        assign(
            local(2),
            Rvalue::RawPtr(Mutability::Mut, proj(1, vec![field(1, u32_ty())])),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(4),
            Rvalue::Cast(
                CastKind::PointerExposeProvenance,
                Operand::Copy(local(2)),
                usize_ty(),
            ),
        ),
        &mut state,
    )
    .unwrap();

    // Reconstruct a pointer from `_4` (`0x2004`) via `PointerWithExposedProvenance` and write through it.
    run(
        assign(
            local(5),
            Rvalue::Cast(
                CastKind::PointerWithExposedProvenance,
                Operand::Copy(local(4)),
                Ty::RawPtr(Box::new(u32_ty()), Mutability::Mut),
            ),
        ),
        &mut state,
    )
    .unwrap();
    state
        .write_place(&proj(5, vec![ProjectionElem::Deref]), &u32_ty(), u32v(55))
        .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::Tuple(vec![u32v(10), u32v(55)]))
    );
}

#[test]
fn a1_out_of_width_pointer_rejected_in_reborrow_copy_for_deref_and_ptr_metadata_on_32bit() {
    let pw = PtrWidth::Bits32;
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty()), Mutability::Not);
    let ref_u32 = Ty::Ref(Box::new(u32_ty()), Mutability::Not);
    let decls = vec![raw_u32.clone(), ref_u32.clone(), Ty::unit()];
    let mut state = StatementEvalState::from_local_decls(decls, pw);
    let bad_addr: u64 = 0x1_0000_1000;
    state.slots[0] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::with_provenance(bad_addr, 1, 1),
        raw_u32.clone(),
    ));
    let expected_err = RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
        target_ty: raw_u32.clone(),
        bits: u128::from(bad_addr),
    });
    // `&raw const (*_0)` must reject out-of-width `_0` rather than masking to `0x1000`.
    assert_eq!(
        run(
            assign(
                local(0),
                Rvalue::RawPtr(Mutability::Not, proj(0, vec![ProjectionElem::Deref])),
            ),
            &mut state
        ),
        Err(expected_err.clone())
    );
    // `CopyForDeref(_0)` must reject out-of-width `_0`.
    assert_eq!(
        run(assign(local(0), Rvalue::CopyForDeref(local(0))), &mut state),
        Err(expected_err.clone())
    );
    // `UnOp::PtrMetadata(_0)` must reject out-of-width `_0`.
    assert_eq!(
        run(
            assign(
                local(2),
                Rvalue::UnaryOp(anneal_mir::ir::UnOp::PtrMetadata, Operand::Copy(local(0))),
            ),
            &mut state
        ),
        Err(expected_err.clone())
    );

    // Stateless `eval_lowered_rvalue` must also reject out-of-width pointers on `&(*_0)` and `CopyForDeref`.
    let locals = vec![MirValue::ptr(
        PointerValue::with_provenance(bad_addr, 1, 1),
        raw_u32.clone(),
    )];
    let mut tracker = ExposedProvenanceTracker::new();
    for rval in [
        Rvalue::RawPtr(Mutability::Not, proj(0, vec![ProjectionElem::Deref])),
        Rvalue::CopyForDeref(local(0)),
    ] {
        let lowered = lower_rvalue(&rval, std::slice::from_ref(&raw_u32), pw).unwrap();
        assert_eq!(
            eval_lowered_rvalue(
                &lowered,
                &locals,
                pw,
                TransmutePolicy::RejectPtrToInt,
                &mut tracker
            ),
            Err(expected_err.clone())
        );
    }
}

#[test]
fn a1_retag_rejects_reference_wrapping_address_space_with_pointer_range_overflow() {
    let arr_ty = Ty::Array(Box::new(u64_ty()), 4); // size 32, align 8
    let ref_arr = Ty::Ref(Box::new(arr_ty), Mutability::Not);
    let mut state = StatementEvalState::from_local_decls(vec![ref_arr.clone()], PW);
    // Aligned non-null address `0xFFFF_FFFF_FFFF_FFF8`: `addr + 32` wraps past `u64::MAX`.
    let high_addr = 0xFFFF_FFFF_FFFF_FFF8u64;
    state.slots[0] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(high_addr),
        ref_arr,
    ));
    assert_eq!(
        run(Statement::Retag(RetagKind::Default, local(0)), &mut state),
        Err(RvalueEvalError::PointerRangeOverflow {
            addr: high_addr,
            byte_len: 32,
        })
    );
}
