//! Pass `B1` adversarial regression tests for Episode 1 sub-place borrows, `Deref`, and
//! `copy_nonoverlapping`:
//! - repr(Rust) tuple field offsets follow the canonical layout rule shared with repr(Rust)
//!   structs (`(u32, (u32, u32))` is laid out pair-first by `rustc`, so its declaration-order
//!   offsets must not be committed to), and zero-sized fields at non-zero declaration offsets of
//!   reorderable field lists are unspecified (`rustc` places 1-ZSTs first);
//! - synthetic local allocations must fit the target address space (no wrapped or colliding
//!   base addresses on 32-bit targets);
//! - same-offset sub-place disambiguation never guesses: stale provenance tags (after a pointer
//!   cast) are ignored, the runtime state (active union field / enum variant) selects among
//!   same-typed candidates, and ambiguous non-zero-sized candidates are unsupported.

use std::sync::Arc;

use anneal_mir::ir::{
    AdtDef, AdtRepr, AdtReprKind, BinOp, CastKind, Local, Mutability, Operand, Place,
    PointerValue, ProjectionElem, PtrWidth, Rvalue, ScalarTy, Statement, Ty, UintTy, VariantDef,
};
use anneal_mir::lower::{
    LocalSlotState, MirValue, RvalueEvalError, StatementEvalState, eval_lowered_statement,
    lower_statement,
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

fn usize_ty() -> Ty {
    Ty::Uint(UintTy::Usize)
}

fn u16v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U16, PW)
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

fn field(idx: usize, ty: Ty) -> ProjectionElem {
    ProjectionElem::Field(idx, ty)
}

fn deref(idx: usize) -> Place {
    proj(idx, vec![ProjectionElem::Deref])
}

fn run(stmt: Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = lower_statement(&stmt, &state.local_decls, state.ptr_width)
        .expect("statement must lower cleanly");
    eval_lowered_statement(&lowered, state)
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign(place, rvalue)
}

fn ptr_cast(src: usize, target_ty: Ty) -> Rvalue {
    Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(local(src)), target_ty)
}

fn repr_c() -> AdtRepr {
    AdtRepr {
        kind: AdtReprKind::C,
        align: None,
    }
}

#[test]
fn b1_non_canonical_tuple_field_offsets_are_unspecified() {
    // `rustc` sorts the fields of `(u32, (u32, u32))` by descending alignment group (the 8-byte
    // pair first: `.1` at offset 0, `.0` at offset 8), so declaration-order offsets (`.1` at 4)
    // must not be committed to: the repr(Rust) struct with the same fields is unspecified too.
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let outer = Ty::Tuple(vec![u32_ty(), pair.clone()]);
    let s_def = Arc::new(AdtDef::new_struct("S", vec![u32_ty(), pair.clone()]));
    let s_ty = Ty::Adt(s_def.clone());
    let decls = vec![
        outer.clone(),               // _0: (u32, (u32, u32))
        raw(pair.clone(), Mutability::Mut), // _1
        raw(u32_ty(), Mutability::Mut),     // _2
        raw(outer.clone(), Mutability::Mut), // _3
        usize_ty(),                  // _4
        s_ty,                        // _5: S { u32, (u32, u32) }
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::Tuple(vec![
        u32v(1),
        MirValue::Tuple(vec![u32v(2), u32v(3)]),
    ]));
    state.slots[4] = LocalSlotState::Init(usizev(1));

    for place in [
        proj(0, vec![field(1, pair.clone())]),
        proj(5, vec![field(1, pair.clone())]),
    ] {
        assert_eq!(
            run(assign(local(1), Rvalue::RawPtr(Mutability::Mut, place.clone())), &mut state),
            Err(RvalueEvalError::UnsupportedPlaceProjection(place))
        );
    }
    let first = proj(0, vec![field(0, u32_ty())]);
    assert_eq!(
        run(assign(local(2), Rvalue::RawPtr(Mutability::Mut, first.clone())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(first))
    );

    // A `*mut u32` at byte offset 4 of the whole tuple designates `_0.1.1` under `rustc`'s
    // layout, never `_0.1.0`: it must not resolve through declaration-order offsets.
    run(assign(local(3), Rvalue::RawPtr(Mutability::Mut, local(0))), &mut state).unwrap();
    run(assign(local(2), ptr_cast(3, raw(u32_ty(), Mutability::Mut))), &mut state).unwrap();
    run(
        assign(
            local(2),
            Rvalue::BinaryOp(BinOp::Offset, Operand::Copy(local(2)), Operand::Copy(local(4))),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(2)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1004, 1, 1),
            raw(u32_ty(), Mutability::Mut)
        ))
    );
    assert_eq!(
        state.read_place(&deref(2)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(2)))
    );

    // Canonical tuples keep their declaration-order offsets: `((u32, u32), u32)` puts `.1` at 8.
    let canon = Ty::Tuple(vec![pair.clone(), u32_ty()]);
    let mut state = StatementEvalState::from_local_decls(
        vec![canon, raw(u32_ty(), Mutability::Mut)],
        PW,
    );
    run(
        assign(
            local(1),
            Rvalue::RawPtr(Mutability::Mut, proj(0, vec![field(1, u32_ty())])),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x1008, 1, 1),
            raw(u32_ty(), Mutability::Mut)
        ))
    );
}

#[test]
fn b1_reorderable_zero_sized_field_offsets_are_unspecified() {
    // `rustc` places 1-ZST fields of repr(Rust) field lists first (offset 0), so the trailing
    // `()` of `(u32, ())` / `struct S { a: u32, z: () }` is not at its declaration offset 4.
    let tuple = Ty::Tuple(vec![u32_ty(), Ty::unit()]);
    let s_def = Arc::new(AdtDef::new_struct("S", vec![u32_ty(), Ty::unit()]));
    let c_def = Arc::new(AdtDef::new_struct("C", vec![u32_ty(), Ty::unit()]).with_repr(repr_c()));
    let decls = vec![
        tuple,
        Ty::Adt(s_def),
        Ty::Adt(c_def),
        raw(Ty::unit(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    for base in [0, 1] {
        let place = proj(base, vec![field(1, Ty::unit())]);
        assert_eq!(
            run(assign(local(3), Rvalue::RawPtr(Mutability::Mut, place.clone())), &mut state),
            Err(RvalueEvalError::UnsupportedPlaceProjection(place))
        );
        // The non-ZST field keeps its (canonical) offset 0.
        run(
            assign(
                local(4),
                Rvalue::RawPtr(Mutability::Mut, proj(base, vec![field(0, u32_ty())])),
            ),
            &mut state,
        )
        .unwrap();
    }
    // `#[repr(C)]` fixes declaration order: `C.z` is at offset 4 (`_2` at `0x3000`).
    run(
        assign(
            local(3),
            Rvalue::RawPtr(Mutability::Mut, proj(2, vec![field(1, Ty::unit())])),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x3004, 3, 1),
            raw(Ty::unit(), Mutability::Mut)
        ))
    );
}

#[test]
fn b1_synthetic_allocations_must_fit_the_32_bit_address_space() {
    let pw = PtrWidth::Bits32;
    // Three `[u8; 0x7000_0000]` locals: `_0` at 0x1000 and `_1` at 0x7000_1000 fit, but `_2`
    // would start at 0xE000_1000 and wrap past 2^32 (its elements would alias `_0`'s range).
    let big = Ty::Array(Box::new(u8_ty()), 0x7000_0000);
    let decls = vec![
        big.clone(),
        big.clone(),
        big.clone(),
        raw(big.clone(), Mutability::Not),
        raw(u8_ty(), Mutability::Not),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, pw);
    run(assign(local(3), Rvalue::RawPtr(Mutability::Not, local(1))), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x7000_1000, 2, 1),
            raw(big.clone(), Mutability::Not)
        ))
    );
    assert!(matches!(
        run(assign(local(3), Rvalue::RawPtr(Mutability::Not, local(2))), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
    let elem = proj(
        2,
        vec![ProjectionElem::ConstantIndex {
            offset: 0x2000_0000,
            min_length: 0x7000_0000,
            from_end: false,
        }],
    );
    assert!(matches!(
        run(assign(local(4), Rvalue::RawPtr(Mutability::Not, elem)), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
    // A forged pointer carrying `_2`'s provenance never resolves into the wrapped allocation.
    state.slots[2] = LocalSlotState::Uninit;
    state.slots[4] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::with_provenance(0x1000, 3, 1),
        raw(u8_ty(), Mutability::Not),
    ));
    assert!(matches!(
        state.read_place(&deref(4)),
        Err(RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
}

#[test]
fn b1_stale_tag_after_pointer_cast_does_not_select_an_inactive_union_field() {
    // `union U { a: (u16, u16), b: u16, c: (u16, u16) }` with active field `c = (1, 2)`.
    // `&raw mut _0.c` is tagged as the 2nd `(u16, u16)` candidate at offset 0; after the cast
    // to `*mut u16` that ordinal must not select `_0.b` (the 2nd `u16` candidate): the write
    // goes through the active field `_0.c.0`, leaving `_0.c.1` intact (as in a byte memory).
    let pair16 = Ty::Tuple(vec![u16_ty(), u16_ty()]);
    let u_def = Arc::new(AdtDef::new_union(
        "U",
        vec![pair16.clone(), u16_ty(), pair16.clone()],
    ));
    let decls = vec![
        Ty::Adt(u_def.clone()),
        raw(pair16.clone(), Mutability::Mut),
        raw(u16_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(
        &u_def,
        2,
        MirValue::Tuple(vec![u16v(1), u16v(2)]),
    ));
    run(
        assign(
            local(1),
            Rvalue::RawPtr(Mutability::Mut, proj(0, vec![field(2, pair16.clone())])),
        ),
        &mut state,
    )
    .unwrap();
    run(assign(local(2), ptr_cast(1, raw(u16_ty(), Mutability::Mut))), &mut state).unwrap();
    state.write_place(&deref(2), &u16_ty(), u16v(7)).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(
            &u_def,
            2,
            MirValue::Tuple(vec![u16v(7), u16v(2)])
        ))
    );
    // The uncast `(u16, u16)` pointer still designates `_0.c` exactly.
    assert_eq!(
        state.read_place(&deref(1)),
        Ok(MirValue::Tuple(vec![u16v(7), u16v(2)]))
    );
}

#[test]
fn b1_ambiguous_same_offset_variant_fields_are_not_guessed() {
    // `#[repr(u8)] enum E { A(u32), B(u32) }`: `(_0 as A).0` and `(_0 as B).0` both sit at
    // offset 4 with type `u32`. A `*mut u32` derived from the whole enum (tag-free) at offset
    // 4 is ambiguous while `_0` is uninitialized: picking `A` would make a later
    // `SetDiscriminant(B)` lose the write, so the access is unsupported rather than guessed.
    let e_def = Arc::new(AdtDef::new_enum(
        "E",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u32_ty()]),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    ));
    let e_ty = Ty::Adt(e_def.clone());
    let decls = vec![
        e_ty.clone(),
        raw(e_ty, Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
        usize_ty(),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[3] = LocalSlotState::Init(usizev(1));
    run(assign(local(1), Rvalue::RawPtr(Mutability::Mut, local(0))), &mut state).unwrap();
    run(assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))), &mut state).unwrap();
    run(
        assign(
            local(2),
            Rvalue::BinaryOp(BinOp::Offset, Operand::Copy(local(2)), Operand::Copy(local(3))),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.write_place(&deref(2), &u32_ty(), u32v(5)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(2)))
    );
    assert_eq!(state.get_local(Local(0)), Some(&LocalSlotState::Uninit));

    // Once `_0 = B(9)`, the runtime variant selects `(_0 as B).0` (as a byte memory would).
    state.slots[0] = LocalSlotState::Init(MirValue::adt(&e_def, 1, vec![u32v(9)]));
    assert_eq!(state.read_place(&deref(2)), Ok(u32v(9)));
    state.write_place(&deref(2), &u32_ty(), u32v(5)).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&e_def, 1, vec![u32v(5)]))
    );

    // A borrow of `(_0 as A).0` taken while `_0` was uninitialized carries a valid tag, but once
    // `_0` holds variant `B` the runtime state wins: the bytes at offset 4 are `B`'s field.
    state.slots[0] = LocalSlotState::Uninit;
    run(
        assign(
            local(2),
            Rvalue::RawPtr(
                Mutability::Mut,
                proj(0, vec![ProjectionElem::Downcast(0), field(0, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    state.write_place(&deref(2), &u32_ty(), u32v(11)).unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    state.slots[0] = LocalSlotState::Init(MirValue::adt(&e_def, 1, vec![u32v(9)]));
    assert_eq!(state.read_place(&deref(2)), Ok(u32v(9)));
}

#[test]
fn b1_zero_sized_ambiguity_prefers_initialized_candidates() {
    // `_0: [(); 4]` and `_1: ((), ())` borrowed whole and cast to `*const ()`: every candidate
    // holds the unique `()` value, so a read never depends on which one is chosen.
    let zarr = Ty::Array(Box::new(Ty::unit()), 4);
    let zpair = Ty::Tuple(vec![Ty::unit(), Ty::unit()]);
    let decls = vec![
        zarr.clone(),
        zpair.clone(),
        raw(zarr, Mutability::Not),
        raw(zpair, Mutability::Not),
        raw(Ty::unit(), Mutability::Not),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::Array {
        elements: vec![MirValue::Unit; 4],
        elem_ty: Ty::unit(),
    });
    state.slots[1] = LocalSlotState::Init(MirValue::Tuple(vec![MirValue::Unit, MirValue::Unit]));
    run(assign(local(2), Rvalue::RawPtr(Mutability::Not, local(0))), &mut state).unwrap();
    run(assign(local(4), ptr_cast(2, raw(Ty::unit(), Mutability::Not))), &mut state).unwrap();
    assert_eq!(state.read_place(&deref(4)), Ok(MirValue::Unit));
    run(assign(local(3), Rvalue::RawPtr(Mutability::Not, local(1))), &mut state).unwrap();
    run(assign(local(4), ptr_cast(3, raw(Ty::unit(), Mutability::Not))), &mut state).unwrap();
    assert_eq!(state.read_place(&deref(4)), Ok(MirValue::Unit));
    // With `_1.0` deinitialized, the initialized sibling `_1.1` is preferred for the read.
    run(Statement::Deinit(proj(1, vec![field(0, Ty::unit())])), &mut state).unwrap();
    assert_eq!(state.read_place(&deref(4)), Ok(MirValue::Unit));
}

#[test]
fn b1_pointer_into_inactive_union_field_or_variant_is_unsupported_not_ub() {
    // `union U { a: (u32, u32), b: u64 }` with active field `b`: a `*const u32` at offset 0
    // only matches `_0.a.0`, which would pun `b`'s bytes. A byte memory reads the low half of
    // `b` (defined), so the value tree must not claim `InactiveUnionField` undefined behavior.
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let u64_ty = Ty::Uint(UintTy::U64);
    let u_def = Arc::new(AdtDef::new_union("U", vec![pair.clone(), u64_ty.clone()]));
    // `#[repr(u8)] enum F { A(u8), B(u32) }`: `(F as B).0` at offset 4, `(F as A).0` at 1.
    let f_def = Arc::new(AdtDef::new_enum(
        "F",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u8_ty()]),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    ));
    let decls = vec![
        Ty::Adt(u_def.clone()),
        raw(u64_ty.clone(), Mutability::Not),
        raw(u32_ty(), Mutability::Not),
        Ty::Adt(f_def.clone()),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(
        &u_def,
        1,
        MirValue::unsigned(0x1_0000_0002, UintTy::U64, PW),
    ));
    run(
        assign(
            local(1),
            Rvalue::RawPtr(Mutability::Not, proj(0, vec![field(1, u64_ty)])),
        ),
        &mut state,
    )
    .unwrap();
    run(assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Not))), &mut state).unwrap();
    assert_eq!(
        state.read_place(&deref(2)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(2)))
    );
    // With `a` active, the same pointer designates `_0.a.0`.
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(
        &u_def,
        0,
        MirValue::Tuple(vec![u32v(5), u32v(6)]),
    ));
    assert_eq!(state.read_place(&deref(2)), Ok(u32v(5)));

    // `_4 = &raw mut (_3 as B).0` while `_3` is uninitialized, then `_3 = A(7)`: a write of 4
    // bytes at offset 4 lands in `A`'s tail padding (defined in a byte memory, `_3` stays `A`),
    // so it must not report `InactiveVariantProjection`.
    run(
        assign(
            local(4),
            Rvalue::RawPtr(
                Mutability::Mut,
                proj(3, vec![ProjectionElem::Downcast(1), field(0, u32_ty())]),
            ),
        ),
        &mut state,
    )
    .unwrap();
    state.slots[3] = LocalSlotState::Init(MirValue::adt(
        &f_def,
        0,
        vec![MirValue::unsigned(7, UintTy::U8, PW)],
    ));
    assert_eq!(
        state.write_place(&deref(4), &u32_ty(), u32v(5)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(4)))
    );
    // Once `_3 = B(1)`, the borrowed sub-place is active again.
    state.slots[3] = LocalSlotState::Init(MirValue::adt(&f_def, 1, vec![u32v(1)]));
    state.write_place(&deref(4), &u32_ty(), u32v(5)).unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::adt(&f_def, 1, vec![u32v(5)]))
    );
}

#[test]
fn b1_reborrow_resolves_the_pointer_before_reading_tail_index_operands() {
    // `&raw const (*_1)[_2]`: place evaluation reads `_1` and resolves `*_1` before reading the
    // index operand `_2` (as `read_place` does), so a dangling `_1` (target `_0` storage-dead)
    // reports `DeadLocal(_0)` even when `_2` is also uninitialized.
    let arr = Ty::Array(Box::new(u32_ty()), 4);
    let decls = vec![
        arr.clone(),
        raw(arr.clone(), Mutability::Not),
        usize_ty(),
        raw(u32_ty(), Mutability::Not),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    run(assign(local(1), Rvalue::RawPtr(Mutability::Not, local(0))), &mut state).unwrap();
    state.slots[0] = LocalSlotState::Dead;
    let elem = proj(1, vec![ProjectionElem::Deref, ProjectionElem::Index(Local(2))]);
    assert_eq!(
        run(assign(local(3), Rvalue::RawPtr(Mutability::Not, elem.clone())), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(0)))
    );
    assert_eq!(
        state.read_place(&elem),
        Err(RvalueEvalError::DeadLocal(Local(0)))
    );
    // With `_0` live again, the uninitialized index operand is reported, and once it holds `3`
    // the reborrow addresses `_0[3]` at `0x1000 + 12`.
    state.slots[0] = LocalSlotState::Uninit;
    assert_eq!(
        run(assign(local(3), Rvalue::RawPtr(Mutability::Not, elem.clone())), &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(2)))
    );
    state.slots[2] = LocalSlotState::Init(usizev(3));
    run(assign(local(3), Rvalue::RawPtr(Mutability::Not, elem)), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x100c, 1, 1),
            raw(u32_ty(), Mutability::Not)
        ))
    );
}
