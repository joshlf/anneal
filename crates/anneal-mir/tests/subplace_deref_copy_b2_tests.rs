//! Pass `B2` adversarial regression tests for Episode 1 (on top of `[adv A1]`):
//! - a `Call` whose destination is `*p` with `p = &raw mut u.b` (an inactive union field)
//!   must evaluate the destination place exactly like the later write (`write_place` may
//!   overwrite the leaf union field), so the pre-call `check_place_access` must not reject it;
//! - the stateless `eval_place_write` follows the stateful `write_place` for such writes;
//! - range checks against the end of the address space never claim undefined behavior from a
//!   mere upper bound of an unspecified pointee layout (`PointerRangeOverflow` needs an exact
//!   size; an undecidable range is unsupported instead).

use std::sync::Arc;

use anneal_mir::ir::{
    AdtDef, BasicBlockData, Body, Constant, Mutability, Operand, Place, PointerValue,
    ProjectionElem, PtrWidth, RetagKind, Rvalue, Statement, Terminator, Ty, UintTy, UnwindAction,
    VariantDef,
};
use anneal_mir::lower::{
    CallOutcome, CfgStep, LocalSlotState, MirValue, RvalueEvalError, StatementEvalState,
    eval_lowered_statement, eval_lowered_terminator, eval_place_write, lower_body,
    lower_statement,
};

const PW: PtrWidth = PtrWidth::Bits64;

fn u32_ty() -> Ty {
    Ty::Uint(UintTy::U32)
}

fn u64_ty() -> Ty {
    Ty::Uint(UintTy::U64)
}

fn usize_ty() -> Ty {
    Ty::Uint(UintTy::Usize)
}

fn u32v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U32, PW)
}

fn u64v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U64, PW)
}

fn raw(pointee: Ty, m: Mutability) -> Ty {
    Ty::RawPtr(Box::new(pointee), m)
}

fn local(idx: usize) -> Place {
    Place::from_local(idx)
}

fn proj(idx: usize, elems: Vec<ProjectionElem>) -> Place {
    Place::with_projection(idx, elems)
}

fn deref(idx: usize) -> Place {
    proj(idx, vec![ProjectionElem::Deref])
}

fn run(stmt: Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = lower_statement(&stmt, &state.local_decls, state.ptr_width)
        .expect("statement must lower cleanly");
    eval_lowered_statement(&lowered, state)
}

/// `union U { a: u64, b: u32 }`.
fn union_u() -> Arc<AdtDef> {
    Arc::new(AdtDef::new_union("U", vec![u64_ty(), u32_ty()]))
}

#[test]
fn b2_call_destination_through_inactive_union_field_pointer_is_written() {
    // `_2 = &raw mut _1.b` (while `_1.a` is active), then `*_2 = f()`: like `*_2 = 42` via an
    // assignment, the call's return value overwrites the leaf union field `b`, so the pre-call
    // destination check must resolve `*_2` the same way the post-call write does.
    let u_def = union_u();
    let body = Body {
        local_decls: vec![u32_ty(), Ty::Adt(u_def.clone()), raw(u32_ty(), Mutability::Mut)],
        basic_blocks: vec![
            BasicBlockData {
                statements: vec![],
                terminator: Some(Terminator::Call {
                    func: Operand::Constant(Constant::Int(1, usize_ty())),
                    args: vec![],
                    destination: deref(2),
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                }),
                is_cleanup: false,
            },
            BasicBlockData {
                statements: vec![],
                terminator: Some(Terminator::Return),
                is_cleanup: false,
            },
        ],
    };
    let lowered = lower_body(&body, PW).unwrap();
    let mut state = StatementEvalState::new(
        lowered.local_decls.clone(),
        vec![
            LocalSlotState::Uninit,
            LocalSlotState::Init(MirValue::union_value(&u_def, 0, u64v(0x1_0000_0002))),
            LocalSlotState::Uninit,
        ],
        PW,
    );
    run(
        Statement::Assign(
            local(2),
            Rvalue::RawPtr(
                Mutability::Mut,
                proj(1, vec![ProjectionElem::Field(1, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    let term = lowered.basic_blocks[0]
        .terminator
        .clone()
        .expect("lowered call terminator");
    let mut handler = |_bb: usize, _f: &MirValue, _args: &[MirValue]| {
        Ok(CallOutcome::Return(u32v(42)))
    };
    assert_eq!(
        eval_lowered_terminator(&lowered, 0, &term, &mut state, &mut None, Some(&mut handler)),
        Ok(CfgStep::Goto(1))
    );
    assert_eq!(
        state.get_init(anneal_mir::ir::Local(1)),
        Some(&MirValue::union_value(&u_def, 1, u32v(42)))
    );
}

#[test]
fn b2_stateless_write_through_inactive_union_field_pointer_matches_stateful_write() {
    let u_def = union_u();
    let union_val = MirValue::union_value(&u_def, 0, u64v(0x1_0000_0002));
    // `_1 = &raw mut _0.b` at `0x1000` (offset 0, unique `u32` candidate, tag 1).
    let ptr = MirValue::ptr(
        PointerValue::with_provenance(0x1000, 1, 1),
        raw(u32_ty(), Mutability::Mut),
    );
    let mut locals = vec![union_val.clone(), ptr.clone()];
    eval_place_write(&deref(1), u32v(42), &mut locals, PW).unwrap();
    assert_eq!(locals[0], MirValue::union_value(&u_def, 1, u32v(42)));

    let mut state = StatementEvalState::new(
        vec![Ty::Adt(u_def.clone()), raw(u32_ty(), Mutability::Mut)],
        vec![LocalSlotState::Init(union_val), LocalSlotState::Init(ptr)],
        PW,
    );
    state.write_place(&deref(1), &u32_ty(), u32v(42)).unwrap();
    assert_eq!(
        state.get_init(anneal_mir::ir::Local(0)),
        Some(&MirValue::union_value(&u_def, 1, u32v(42)))
    );
}

#[test]
fn b2_address_space_end_checks_never_claim_ub_from_layout_upper_bounds() {
    // `enum E { A(bool), B }` without an explicit tag has an unspecified layout: its upper bound
    // is the 2-byte tagged layout, while `rustc`'s niche layout is 1 byte. A `&E` at
    // `usize::MAX - 1` therefore fits the address space or not depending on the layout:
    // claiming `PointerRangeOverflow` from the upper bound would be an unfounded UB verdict.
    let e_def = Arc::new(AdtDef::new_enum(
        "E",
        None,
        vec![
            VariantDef::new("A", vec![Ty::Bool]),
            VariantDef::new("B", vec![]),
        ],
    ));
    let e_ty = Ty::Adt(e_def);
    assert!(e_ty.layout_for(PW).is_err());
    let top = 0xFFFF_FFFF_FFFF_FFFEu64;
    let ref_e = Ty::Ref(Box::new(e_ty.clone()), Mutability::Not);
    let raw_e = raw(e_ty, Mutability::Not);
    let mut state = StatementEvalState::from_local_decls(vec![ref_e.clone(), raw_e.clone()], PW);
    state.slots[0] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(top),
        ref_e,
    ));
    assert!(matches!(
        run(Statement::Retag(RetagKind::Default, local(0)), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
    state.slots[1] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(top),
        raw_e,
    ));
    assert_eq!(
        state.read_place(&deref(1)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(1)))
    );

    // Exact layouts still report the overflow: `&[u64; 4]` at `usize::MAX - 7`.
    let arr = Ty::Array(Box::new(u64_ty()), 4);
    let ref_arr = Ty::Ref(Box::new(arr), Mutability::Not);
    let high = 0xFFFF_FFFF_FFFF_FFF8u64;
    let mut state = StatementEvalState::from_local_decls(vec![ref_arr.clone()], PW);
    state.slots[0] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(high),
        ref_arr,
    ));
    assert_eq!(
        run(Statement::Retag(RetagKind::Default, local(0)), &mut state),
        Err(RvalueEvalError::PointerRangeOverflow {
            addr: high,
            byte_len: 32,
        })
    );
}

fn copy_stmt(src: usize, dst: usize, count: u128) -> Statement {
    Statement::CopyNonOverlapping {
        src: Operand::Copy(local(src)),
        dst: Operand::Copy(local(dst)),
        count: Operand::Constant(Constant::Int(count, usize_ty())),
    }
}

fn elem(base: usize, idx: u64, len: u64) -> Place {
    proj(
        base,
        vec![ProjectionElem::ConstantIndex {
            offset: idx,
            min_length: len,
            from_end: false,
        }],
    )
}

#[test]
fn b2_copying_uninitialized_array_windows_is_defined_where_representable() {
    // Copying uninitialized bytes is defined (`copy_nonoverlapping` is an untyped copy). The
    // value tree represents it exactly when the destination array is uninitialized already (a
    // no-op) or overwritten as a whole (it becomes uninitialized); only a partial overwrite of
    // an initialized array fails closed (`c6d2ad74`).
    let arr = Ty::Array(Box::new(u32_ty()), 4);
    let init_arr = || {
        LocalSlotState::Init(MirValue::Array {
            elements: vec![u32v(1), u32v(2), u32v(3), u32v(4)],
            elem_ty: u32_ty(),
        })
    };
    let decls = vec![
        arr.clone(),
        arr.clone(),
        raw(u32_ty(), Mutability::Not),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let setup = |state: &mut StatementEvalState, src_idx: u64, dst_idx: u64| {
        run(
            Statement::Assign(local(2), Rvalue::RawPtr(Mutability::Not, elem(0, src_idx, 4))),
            state,
        )
        .unwrap();
        run(
            Statement::Assign(local(3), Rvalue::RawPtr(Mutability::Mut, elem(1, dst_idx, 4))),
            state,
        )
        .unwrap();
    };

    // Uninitialized `_0[0..2]` into uninitialized `_1[1..3]` (and a single element): no change.
    setup(&mut state, 0, 1);
    run(copy_stmt(2, 3, 2), &mut state).unwrap();
    run(copy_stmt(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_local(anneal_mir::ir::Local(1)), Some(&LocalSlotState::Uninit));

    // Uninitialized `_0[0..4]` over the whole initialized `_1`: `_1` becomes uninitialized.
    state.slots[1] = init_arr();
    setup(&mut state, 0, 0);
    run(copy_stmt(2, 3, 4), &mut state).unwrap();
    assert_eq!(state.get_local(anneal_mir::ir::Local(1)), Some(&LocalSlotState::Uninit));

    // Uninitialized `_0[0..2]` over part of the initialized `_1`: fails closed (`c6d2ad74`).
    state.slots[1] = init_arr();
    setup(&mut state, 0, 1);
    assert_eq!(
        run(copy_stmt(2, 3, 2), &mut state),
        Err(RvalueEvalError::UninitializedLocal(anneal_mir::ir::Local(0)))
    );
    assert_eq!(state.get_local(anneal_mir::ir::Local(1)), Some(&init_arr()));

    // Initialized `_0[1..3]` into `_1[2..4]` still copies the values.
    state.slots[0] = init_arr();
    setup(&mut state, 1, 2);
    run(copy_stmt(2, 3, 2), &mut state).unwrap();
    assert_eq!(
        state.get_init(anneal_mir::ir::Local(1)),
        Some(&MirValue::Array {
            elements: vec![u32v(1), u32v(2), u32v(2), u32v(3)],
            elem_ty: u32_ty(),
        })
    );
}

#[test]
fn b2_zero_sized_array_sub_places_are_enumerated_in_bounded_time() {
    // Every element of a zero-sized-element array designates an equivalent sub-place (equal
    // values, no per-element state). Enumerating each element as a separate candidate made
    // borrows and derefs inside nested zero-sized arrays take `O(len^depth)` time (`10^12`
    // candidate paths for `[[(); 1 << 20]; 1 << 20]`); element 0 is now the canonical one.
    let inner = Ty::Array(Box::new(Ty::unit()), 1 << 20);
    let outer = Ty::Array(Box::new(inner), 1 << 20);
    let decls = vec![outer, raw(Ty::unit(), Mutability::Not)];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let place = proj(
        0,
        vec![
            ProjectionElem::ConstantIndex {
                offset: 5,
                min_length: 1 << 20,
                from_end: false,
            },
            ProjectionElem::ConstantIndex {
                offset: 7,
                min_length: 1 << 20,
                from_end: false,
            },
        ],
    );
    run(
        Statement::Assign(local(1), Rvalue::RawPtr(Mutability::Not, place)),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(anneal_mir::ir::Local(1)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1000, 1, 1),
            raw(Ty::unit(), Mutability::Not)
        ))
    );
    assert_eq!(
        state.read_place(&deref(1)),
        Err(RvalueEvalError::UninitializedLocal(anneal_mir::ir::Local(0)))
    );

    // `&raw const _2[3]` / `copy_nonoverlapping(&_2[3], &mut _3[1], 3)` on `[(); 4]` arrays.
    let zarr = Ty::Array(Box::new(Ty::unit()), 4);
    let zarr_val = || {
        LocalSlotState::Init(MirValue::Array {
            elements: vec![MirValue::Unit; 4],
            elem_ty: Ty::unit(),
        })
    };
    let decls = vec![
        zarr.clone(),
        zarr,
        raw(Ty::unit(), Mutability::Not),
        raw(Ty::unit(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = zarr_val();
    state.slots[1] = zarr_val();
    run(
        Statement::Assign(local(2), Rvalue::RawPtr(Mutability::Not, elem(0, 3, 4))),
        &mut state,
    )
    .unwrap();
    run(
        Statement::Assign(local(3), Rvalue::RawPtr(Mutability::Mut, elem(1, 1, 4))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.read_place(&deref(2)), Ok(MirValue::Unit));
    run(copy_stmt(2, 3, 3), &mut state).unwrap();
    run(copy_stmt(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_local(anneal_mir::ir::Local(1)), Some(&zarr_val()));
}
