//! Pass `B4` adversarial regression tests for Episode 1 (on top of `[adv A3]`):
//! - writing an uninitialized slot through a `Subslice { from: 0, to: 1 }` destination (a
//!   `[T; 1]` window at the start of a longer array: canonical sub-places never contain a
//!   full-length subslice) must not deinitialize the whole parent array;
//! - an address-only raw reborrow `&raw const (*p)[i]` through a null or dangling `p` is
//!   defined for offset `0` (MiniRust `offset_inbounds`), and its fault order with an
//!   unreadable index operand matches the corresponding load (the pointer's fault first).

use anneal_mir::ir::{
    Constant, Local, Mutability, Operand, Place, PointerValue, ProjectionElem, PtrWidth, Rvalue,
    Statement, Ty, UintTy,
};
use anneal_mir::lower::{
    LocalSlotState, MirValue, RvalueEvalError, StatementEvalState, eval_lowered_statement,
    lower_statement,
};

const PW: PtrWidth = PtrWidth::Bits64;

fn u32_ty() -> Ty {
    Ty::Uint(UintTy::U32)
}

fn usize_ty() -> Ty {
    Ty::Uint(UintTy::Usize)
}

fn u32v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U32, PW)
}

fn usizev(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::Usize, PW)
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

fn run(stmt: Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = lower_statement(&stmt, &state.local_decls, state.ptr_width)
        .expect("statement must lower cleanly");
    eval_lowered_statement(&lowered, state)
}

#[test]
fn b4_uninit_copy_into_leading_one_element_window_does_not_deinit_the_whole_array() {
    // `copy_nonoverlapping::<[u32; 1]>(&raw const _1, (&raw mut _0) as *mut [u32; 1], 1)` with
    // `_1` uninitialized and `_0: [u32; 4] = [1, 2, 3, 4]`: the destination resolves to the
    // window `_0[0..1]`. Only element 0 receives uninitialized bytes, which an array value
    // cannot represent, so the copy fails closed (`c6d2ad74`) and `_0` stays intact (it used
    // to strip the `Subslice` and deinitialize all four elements).
    let one = Ty::Array(Box::new(u32_ty()), 1);
    let four = Ty::Array(Box::new(u32_ty()), 4);
    let decls = vec![
        four.clone(),
        one.clone(),
        raw(four.clone(), Mutability::Mut),
        raw(one.clone(), Mutability::Mut),
        raw(one.clone(), Mutability::Not),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let init_four = LocalSlotState::Init(MirValue::Array {
        elements: vec![u32v(1), u32v(2), u32v(3), u32v(4)],
        elem_ty: u32_ty(),
    });
    state.slots[0] = init_four.clone();
    run(Statement::Assign(local(2), Rvalue::RawPtr(Mutability::Mut, local(0))), &mut state)
        .unwrap();
    run(
        Statement::Assign(
            local(3),
            Rvalue::Cast(
                anneal_mir::ir::CastKind::PtrToPtr,
                Operand::Copy(local(2)),
                raw(one.clone(), Mutability::Mut),
            ),
        ),
        &mut state,
    )
    .unwrap();
    run(Statement::Assign(local(4), Rvalue::RawPtr(Mutability::Not, local(1))), &mut state)
        .unwrap();
    let copy = Statement::CopyNonOverlapping {
        src: Operand::Copy(local(4)),
        dst: Operand::Copy(local(3)),
        count: Operand::Constant(Constant::Int(1, usize_ty())),
    };
    assert_eq!(
        run(copy.clone(), &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(state.get_local(Local(0)), Some(&init_four));

    // An initialized `[u32; 1]` source writes just the leading window.
    state.slots[1] = LocalSlotState::Init(MirValue::Array {
        elements: vec![u32v(9)],
        elem_ty: u32_ty(),
    });
    run(copy, &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::Array {
            elements: vec![u32v(9), u32v(2), u32v(3), u32v(4)],
            elem_ty: u32_ty(),
        })
    );
}

#[test]
fn b4_address_only_reborrow_fault_order_matches_loads() {
    // `&raw const (*_1)[_2]` with `_1: *const [u32; 4]` null (or pointing into storage-dead
    // `_0`): as for the load `(*_1)[_2]` (which resolves `*_1` before reading `_2`), the
    // pointer's fault is reported before an uninitialized index operand; with `_2 = 0` the
    // address-only reborrow is an offset-0 `offset_inbounds`, defined even for such pointers,
    // while the load still faults.
    let four = Ty::Array(Box::new(u32_ty()), 4);
    let decls = vec![
        four.clone(),
        raw(four.clone(), Mutability::Not),
        usize_ty(),
        raw(u32_ty(), Mutability::Not),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let elem = proj(1, vec![ProjectionElem::Deref, ProjectionElem::Index(Local(2))]);
    let reborrow = Statement::Assign(local(3), Rvalue::RawPtr(Mutability::Not, elem.clone()));
    for (base, fault) in [
        (
            PointerValue::without_provenance(0),
            RvalueEvalError::NullPointerAccess,
        ),
        (
            PointerValue::with_provenance(0x1000, 1, 1),
            RvalueEvalError::DeadLocal(Local(0)),
        ),
    ] {
        state.slots[0] = LocalSlotState::Dead;
        state.slots[1] = LocalSlotState::Init(MirValue::ptr(base, raw(four.clone(), Mutability::Not)));
        state.slots[2] = LocalSlotState::Uninit;
        assert_eq!(run(reborrow.clone(), &mut state), Err(fault.clone()));
        assert_eq!(state.read_place(&elem), Err(fault.clone()));
        state.slots[2] = LocalSlotState::Init(usizev(0));
        run(reborrow.clone(), &mut state).unwrap();
        assert_eq!(
            state.get_init(Local(3)),
            Some(&MirValue::ptr(base, raw(u32_ty(), Mutability::Not)))
        );
        assert_eq!(state.read_place(&elem), Err(fault));
    }
}
