//! Pass `B3` adversarial regression tests for Episode 1 (on top of `[adv A2]`):
//! - the stateless evaluators (`eval_place_read` / `eval_place_write` / `eval_lowered_rvalue`)
//!   and `StatementEvalState` now share one `Deref` resolver (`FrameView`); these tests pin
//!   that both agree on reads, whole-union-field overwrites, and address-only reborrows;
//! - a zero-byte `copy_nonoverlapping` (`count > 1` zero-sized elements) accesses no memory,
//!   so (like the explicit storage-dead pre-check, which only covers `count == 1`) it never
//!   faults on a storage-dead local.

use std::sync::Arc;

use anneal_mir::ir::{
    AdtDef, AdtRepr, AdtReprKind, Constant, Local, Mutability, Operand, Place, PointerValue,
    ProjectionElem, PtrWidth, Rvalue, Statement, Ty, UintTy,
};
use anneal_mir::lower::{
    ExposedProvenanceTracker, LocalSlotState, MirValue, RvalueEvalError, StatementEvalState,
    TransmutePolicy, eval_lowered_rvalue, eval_lowered_statement, eval_place_read,
    eval_place_write, lower_rvalue, lower_statement,
};

const PW: PtrWidth = PtrWidth::Bits64;

fn u8_ty() -> Ty {
    Ty::Uint(UintTy::U8)
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

/// Evaluates `rvalue` both statelessly over `locals` and in a `StatementEvalState` whose slots
/// hold `locals` (all initialized), asserting that both evaluators agree.
fn eval_both(rvalue: &Rvalue, locals: &[MirValue]) -> Result<MirValue, RvalueEvalError> {
    let decls: Vec<Ty> = locals.iter().map(MirValue::ty).collect();
    let lowered = lower_rvalue(rvalue, &decls, PW).expect("rvalue must lower cleanly");
    let mut tracker = ExposedProvenanceTracker::new();
    let stateless = eval_lowered_rvalue(
        &lowered,
        locals,
        PW,
        TransmutePolicy::RejectPtrToInt,
        &mut tracker,
    );
    let mut state = StatementEvalState::new(
        decls,
        locals.iter().cloned().map(LocalSlotState::Init).collect(),
        PW,
    );
    let stateful = anneal_mir::lower::eval_lowered_rvalue_in_state(&lowered, &mut state);
    assert_eq!(stateless, stateful, "stateless and stateful evaluation of {rvalue:?} differ");
    stateless
}

#[test]
fn b3_stateless_and_stateful_deref_evaluation_agree() {
    // `_0: #[repr(C)] struct S { a: u32, b: u8 }` (`b` at 4), `_1: [u8; 16]`, and raw pointers
    // into both: reads, address-only reborrows (also through a misaligned `*const S` into the
    // byte array), and reference reborrows must agree between both evaluators.
    let s_def = Arc::new(
        AdtDef::new_struct("S", vec![u32_ty(), u8_ty()]).with_repr(AdtRepr {
            kind: AdtReprKind::C,
            align: None,
        }),
    );
    let s_ty = Ty::Adt(s_def.clone());
    let bytes: Vec<MirValue> = (0..16).map(u8v).collect();
    let locals = vec![
        MirValue::adt(&s_def, 0, vec![u32v(7), u8v(9)]),
        MirValue::Array {
            elements: bytes,
            elem_ty: u8_ty(),
        },
        // `_2 = &raw const _0` (0x1000), `_3 = (&raw const _1[1]) as *const S` (0x2001).
        MirValue::ptr(
            PointerValue::with_provenance(0x1000, 1, 1),
            raw(s_ty.clone(), Mutability::Not),
        ),
        MirValue::ptr(
            PointerValue::with_provenance(0x2001, 2, 1),
            raw(s_ty.clone(), Mutability::Not),
        ),
    ];
    let field_b = ProjectionElem::Field(1, u8_ty());
    let b_through = |p: usize| proj(p, vec![ProjectionElem::Deref, field_b.clone()]);
    assert_eq!(
        eval_both(&Rvalue::Use(Operand::Copy(b_through(2))), &locals),
        Ok(u8v(9))
    );
    assert_eq!(
        eval_both(&Rvalue::RawPtr(Mutability::Not, b_through(2)), &locals),
        Ok(MirValue::ptr(
            PointerValue::with_provenance(0x1004, 1, 1),
            raw(u8_ty(), Mutability::Not)
        ))
    );
    // Address-only: `&raw const (*_3).b` = 0x2001 + 4 inside `_1` (misaligned `_3` is fine).
    assert_eq!(
        eval_both(&Rvalue::RawPtr(Mutability::Not, b_through(3)), &locals),
        Ok(MirValue::ptr(
            PointerValue::with_provenance(0x2005, 2, 1),
            raw(u8_ty(), Mutability::Not)
        ))
    );
    // Loading through the misaligned `*const S` is a misaligned access.
    assert_eq!(
        eval_both(&Rvalue::Use(Operand::Copy(b_through(3))), &locals),
        Err(RvalueEvalError::MisalignedPointer {
            addr: 0x2001,
            required_align: 4,
        })
    );
    assert_eq!(
        eval_both(&Rvalue::Ref(Mutability::Not, b_through(3)), &locals),
        Err(RvalueEvalError::MisalignedPointer {
            addr: 0x2001,
            required_align: 4,
        })
    );
}

#[test]
fn b3_stateless_and_stateful_whole_union_field_writes_agree() {
    // `union U { a: u64, b: u32 }` with `a` active; `*(&raw mut _0.b) = 42` switches the active
    // field in both evaluators, and a mistyped whole-`Deref` write is rejected by both.
    let u_def = Arc::new(AdtDef::new_union("U", vec![u64_ty(), u32_ty()]));
    let locals = vec![
        MirValue::union_value(&u_def, 0, u64v(0x1_0000_0002)),
        MirValue::ptr(
            PointerValue::with_provenance(0x1000, 1, 1),
            raw(u32_ty(), Mutability::Mut),
        ),
    ];
    let mut stateless = locals.clone();
    eval_place_write(&deref(1), u32v(42), &mut stateless, PW).unwrap();
    let mut state = StatementEvalState::new(
        locals.iter().map(MirValue::ty).collect(),
        locals.iter().cloned().map(LocalSlotState::Init).collect(),
        PW,
    );
    state.write_place(&deref(1), &u32_ty(), u32v(42)).unwrap();
    assert_eq!(stateless[0], MirValue::union_value(&u_def, 1, u32v(42)));
    assert_eq!(state.get_init(Local(0)), Some(&stateless[0]));
    assert_eq!(eval_place_read(&deref(1), &stateless, PW), Ok(u32v(42)));
    assert_eq!(state.read_place(&deref(1)), Ok(u32v(42)));

    let mut mistyped = locals.clone();
    assert!(matches!(
        eval_place_write(&deref(1), u64v(1), &mut mistyped, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(mistyped, locals);
}

#[test]
fn b3_zero_byte_copies_never_fault_on_storage_dead_locals() {
    // `copy_nonoverlapping::<()>(&raw const _0, &raw mut _1, n)` after `StorageDead(_1)`: the
    // explicit storage-dead pre-check covers non-empty copies and `count == 1`; a `count > 1`
    // zero-byte copy accesses no memory and is a no-op (it used to surface the resolver's
    // `DeadLocal` for the destination).
    let decls = vec![
        Ty::unit(),
        Ty::unit(),
        raw(Ty::unit(), Mutability::Not),
        raw(Ty::unit(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::Unit);
    state.slots[1] = LocalSlotState::Init(MirValue::Unit);
    run(Statement::Assign(local(2), Rvalue::RawPtr(Mutability::Not, local(0))), &mut state)
        .unwrap();
    run(Statement::Assign(local(3), Rvalue::RawPtr(Mutability::Mut, local(1))), &mut state)
        .unwrap();
    run(Statement::StorageDead(Local(1)), &mut state).unwrap();
    let copy = |count: u128| Statement::CopyNonOverlapping {
        src: Operand::Copy(local(2)),
        dst: Operand::Copy(local(3)),
        count: Operand::Constant(Constant::Int(count, usize_ty())),
    };
    run(copy(5), &mut state).unwrap();
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Dead));
    assert_eq!(
        run(copy(1), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(1)))
    );
    run(copy(0), &mut state).unwrap();
}

#[test]
fn b3_copying_uninitialized_bytes_into_a_union_field_is_unsupported_not_ub() {
    // `union U { a: u32, b: u32 }` (active `a = 5`) and `struct P { x: u32, y: u32 }`: copying
    // an uninitialized `u32` or a partially initialized `P` into a union field is defined in
    // Rust (the union just holds uninitialized bytes), but the value tree holds one
    // initialized union field, so the copy is unsupported -- never `UninitializedLocal` UB.
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let u_def = Arc::new(AdtDef::new_union("U", vec![u32_ty(), u32_ty()]));
    let w_def = Arc::new(AdtDef::new_union("W", vec![pair.clone(), u64_ty()]));
    let decls = vec![
        Ty::Adt(u_def.clone()),
        u32_ty(),
        raw(u32_ty(), Mutability::Not),
        raw(u32_ty(), Mutability::Mut),
        Ty::Adt(w_def.clone()),
        pair.clone(),
        raw(pair.clone(), Mutability::Not),
        raw(pair.clone(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&u_def, 0, u32v(5)));
    run(Statement::Assign(local(2), Rvalue::RawPtr(Mutability::Not, local(1))), &mut state)
        .unwrap();
    let copy = |src: usize, dst: usize| Statement::CopyNonOverlapping {
        src: Operand::Copy(local(src)),
        dst: Operand::Copy(local(dst)),
        count: Operand::Constant(Constant::Int(1, usize_ty())),
    };
    for field_idx in [0, 1] {
        run(
            Statement::Assign(
                local(3),
                Rvalue::RawPtr(
                    Mutability::Mut,
                    proj(0, vec![ProjectionElem::Field(field_idx, u32_ty())]),
                ),
            ),
            &mut state,
        )
        .unwrap();
        assert!(matches!(
            run(copy(2, 3), &mut state),
            Err(RvalueEvalError::UnsupportedMemoryAccess(_))
        ));
        assert_eq!(
            state.get_init(Local(0)),
            Some(&MirValue::union_value(&u_def, 0, u32v(5)))
        );
    }

    // A partially initialized `(u32, u32)` copied into `W.0` (active `W.1 = 9u64`).
    state.slots[4] = LocalSlotState::Init(MirValue::union_value(&w_def, 1, u64v(9)));
    state
        .write_place(
            &proj(5, vec![ProjectionElem::Field(0, u32_ty())]),
            &u32_ty(),
            u32v(1),
        )
        .unwrap();
    run(Statement::Assign(local(6), Rvalue::RawPtr(Mutability::Not, local(5))), &mut state)
        .unwrap();
    run(
        Statement::Assign(
            local(7),
            Rvalue::RawPtr(Mutability::Mut, proj(4, vec![ProjectionElem::Field(0, pair)])),
        ),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        run(copy(6, 7), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::union_value(&w_def, 1, u64v(9)))
    );
}
