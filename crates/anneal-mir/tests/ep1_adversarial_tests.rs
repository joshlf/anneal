//! Episode 1 adversarial regression and property tests for value-tree place projections,
//! `CastKind::CharToInt`, `Rvalue::NullaryOp`, and stateful statement evaluation.
//!
//! Each `test_ep1_b<k>_*` / `test_ep1_a<k>_*` test pins behavior that an adversarial review
//! pass found missing or wrong, and cites the `Trusted.Rustc.V2026_06_01.MirSemantics`
//! definition (or `rustc` behavior) it is checked against.

use anneal_mir::ir::{
    AggregateKind, CastKind, Constant, IntTy, Local, Mutability, NullOp, Operand, Place,
    PointerValue, ProjectionElem, PtrWidth, Rvalue, Statement, Ty, UintTy,
};
use anneal_mir::lower::{
    ExposedProvenanceTracker, LocalSlotState, LoweredStatement, MirValue, RvalueEvalError,
    RvalueLowerError, StatementEvalState, TransmutePolicy, eval_lowered_rvalue,
    eval_lowered_statement, eval_place_read, eval_place_write, lower_rvalue, lower_statement,
    resolve_offset_of,
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

fn u8v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U8, PW)
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

fn field(idx: usize, ty: Ty) -> ProjectionElem {
    ProjectionElem::Field(idx, ty)
}

fn proj(local: usize, projection: Vec<ProjectionElem>) -> Place {
    Place::with_projection(local, projection)
}

fn stmt(s: Statement, local_decls: &[Ty]) -> LoweredStatement {
    lower_statement(&s, local_decls, PW).expect("statement must lower")
}

fn run(s: Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = stmt(s, &state.local_decls.clone());
    eval_lowered_statement(&lowered, state)
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign(place, rvalue)
}

fn use_copy(place: Place) -> Rvalue {
    Rvalue::Use(Operand::Copy(place))
}

fn use_move(place: Place) -> Rvalue {
    Rvalue::Use(Operand::Move(place))
}

fn use_const(c: Constant) -> Rvalue {
    Rvalue::Use(Operand::Constant(c))
}

/// Deterministic xorshift64* generator for property tests (the crate has no dependencies).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }
}

// ---------------------------------------------------------------------------------------------
// [adv B1] `Operand::Move` parity with `Trusted.MirSemantics.evalOperand`
// ---------------------------------------------------------------------------------------------

/// `Trusted.MirSemantics.evalOperand` (`Places.lean`, `.move p`): a root-local move sets the
/// slot to `.uninit`, whereas a projected (non-`Deref`) move reads the sub-value and keeps the
/// parent aggregate slot initialized. A0 deinitialized the moved field instead, which made
/// later reads of the field (and of the whole local) fail where the trusted semantics steps.
#[test]
fn test_ep1_b1_projected_move_keeps_parent_initialized_like_trusted_eval_operand() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let local_decls = vec![
        pair_ty.clone(),                     // _0: (u32, u8)
        u32_ty(),                            // _1: u32
        Ty::Tuple(vec![u32_ty(), u32_ty()]), // _2: (u32, u32)
        u8_ty(),                             // _3: u8
    ];
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    let pair = MirValue::Tuple(vec![u32v(5), u8v(7)]);
    state.slots[0] = LocalSlotState::Init(pair.clone());

    let p00 = proj(0, vec![field(0, u32_ty())]);
    let p01 = proj(0, vec![field(1, u8_ty())]);

    // `_1 = move _0.0` reads 5 and leaves `_0` fully initialized.
    run(
        assign(Place::from_local(1), use_move(p00.clone())),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&u32v(5)));
    assert_eq!(
        state.get_local(Local(0)),
        Some(&LocalSlotState::Init(pair.clone()))
    );

    // `_2 = (move _0.0, copy _0.0)`: the second operand still reads the field.
    run(
        assign(
            Place::from_local(2),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![Operand::Move(p00.clone()), Operand::Copy(p00.clone())],
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(2)),
        Some(&MirValue::Tuple(vec![u32v(5), u32v(5)]))
    );

    // `_0.1 = move _0.1` and `_0.0 = move _1` keep `_0` a fully initialized tuple.
    run(assign(p01.clone(), use_move(p01.clone())), &mut state).unwrap();
    run(
        assign(p00.clone(), use_move(Place::from_local(1))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_local(Local(0)),
        Some(&LocalSlotState::Init(pair.clone()))
    );
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));
    assert_eq!(state.read_place(&Place::from_local(0)), Ok(pair.clone()));

    // `_3 = move _0.1` is another projected move. `_1` was moved out as a bare local above, so
    // `_1 = Add(move _1, 1)` faults on the uninitialized `_1`.
    run(assign(Place::from_local(3), use_move(p01)), &mut state).unwrap();
    assert_eq!(state.get_init(Local(3)), Some(&u8v(7)));
    assert_eq!(
        run(
            assign(
                Place::from_local(1),
                Rvalue::BinaryOp(
                    anneal_mir::ir::BinOp::Add,
                    Operand::Move(Place::from_local(1)),
                    Operand::Constant(Constant::Int(1, u32_ty())),
                ),
            ),
            &mut state,
        ),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );

    // Left-to-right operand order: `Add(move _1, copy _1)` reads `_1` after moving it.
    state.slots[1] = LocalSlotState::Init(u32v(9));
    assert_eq!(
        run(
            assign(
                Place::from_local(1),
                Rvalue::BinaryOp(
                    anneal_mir::ir::BinOp::Add,
                    Operand::Move(Place::from_local(1)),
                    Operand::Copy(Place::from_local(1)),
                ),
            ),
            &mut state,
        ),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
}

/// A projected move out of a partially initialized shell (`D13b`) reads the initialized field
/// and leaves the shell unchanged.
#[test]
fn test_ep1_b1_projected_move_out_of_partial_shell_leaves_shell_unchanged() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let local_decls = vec![pair_ty, u32_ty()];
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    let p00 = proj(0, vec![field(0, u32_ty())]);
    run(
        assign(p00.clone(), use_const(Constant::Int(11, u32_ty()))),
        &mut state,
    )
    .unwrap();
    let before = state.get_local(Local(0)).cloned();
    assert!(matches!(before, Some(LocalSlotState::PartialShell(_))));

    run(
        assign(Place::from_local(1), use_move(p00.clone())),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&u32v(11)));
    assert_eq!(state.get_local(Local(0)).cloned(), before);
    assert_eq!(state.read_place(&p00), Ok(u32v(11)));
    assert_eq!(
        state.read_place(&Place::from_local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
}

// ---------------------------------------------------------------------------------------------
// [adv B1] Enum shells: the tag is uninitialized until `SetDiscriminant`
// ---------------------------------------------------------------------------------------------

/// `rustc` MIR builds enum values in place as `((_1 as V).0) = x; discriminant(_1) = V;`.
/// Until `SetDiscriminant` runs, the enum's tag bytes are uninitialized, so a typed copy of
/// `_1` or `Rvalue::Discriminant(_1)` is undefined behavior (Miri reports a read of
/// uninitialized memory). A0 promoted a `Downcast`-written shell to an initialized
/// `MirValue::Adt` as soon as its fields were written, false-accepting both reads.
#[test]
fn test_ep1_b1_downcast_field_writes_do_not_initialize_enum_tag_until_set_discriminant() {
    let enum1_ty = Ty::Tuple(vec![u32_ty()]); // variant fields modeled as a tuple
    let enum2_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let local_decls = vec![
        Ty::Int(IntTy::Isize),                      // _0: discriminant result
        enum1_ty.clone(),                           // _1: one-field variant enum
        enum1_ty.clone(),                           // _2: copy target
        u32_ty(),                                   // _3: field copy target
        enum2_ty.clone(),                           // _4: two-field variant enum
        Ty::Tuple(vec![enum2_ty.clone(), u8_ty()]), // _5: (enum2, u8)
    ];
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);

    let v1_f0 = proj(1, vec![ProjectionElem::Downcast(1), field(0, u32_ty())]);
    run(
        assign(v1_f0.clone(), use_const(Constant::Int(99, u32_ty()))),
        &mut state,
    )
    .unwrap();

    // The tag has not been written: whole-value reads and `Discriminant` fail closed.
    assert_eq!(state.get_init(Local(1)), None);
    assert_eq!(
        state.read_place(&Place::from_local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(
        run(
            assign(Place::from_local(2), use_copy(Place::from_local(1))),
            &mut state
        ),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(
        run(
            assign(
                Place::from_local(0),
                Rvalue::Discriminant(Place::from_local(1))
            ),
            &mut state
        ),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    // The written variant field itself is readable.
    run(
        assign(Place::from_local(3), use_copy(v1_f0.clone())),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(3)), Some(&u32v(99)));

    // `discriminant(_1) = 1` writes the tag and completes the value.
    run(
        Statement::SetDiscriminant {
            place: Place::from_local(1),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    let full = MirValue::Adt {
        def_path: String::new(),
        variant_idx: 1,
        active_field: None,
        fields: vec![u32v(99)],
    };
    assert_eq!(state.get_init(Local(1)), Some(&full));
    run(
        assign(Place::from_local(2), use_copy(Place::from_local(1))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(2)), Some(&full));
    run(
        assign(
            Place::from_local(0),
            Rvalue::Discriminant(Place::from_local(1)),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::signed(1, IntTy::Isize, PW))
    );

    // Tag written before the last field: the discriminant is readable while the value is not.
    let v2_f0 = proj(4, vec![ProjectionElem::Downcast(2), field(0, u32_ty())]);
    let v2_f1 = proj(4, vec![ProjectionElem::Downcast(2), field(1, u8_ty())]);
    run(
        assign(v2_f1, use_const(Constant::Int(7, u8_ty()))),
        &mut state,
    )
    .unwrap();
    run(
        Statement::SetDiscriminant {
            place: Place::from_local(4),
            variant_index: 2,
        },
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(4)),
        Some(LocalSlotState::PartialShell(_))
    ));
    run(
        assign(
            Place::from_local(0),
            Rvalue::Discriminant(Place::from_local(4)),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::signed(2, IntTy::Isize, PW))
    );
    assert_eq!(
        state.read_place(&Place::from_local(4)),
        Err(RvalueEvalError::UninitializedLocal(Local(4)))
    );
    run(
        assign(v2_f0, use_const(Constant::Int(5, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::Adt {
            def_path: String::new(),
            variant_idx: 2,
            active_field: None,
            fields: vec![u32v(5), u8v(7)],
        })
    );

    // Nested enum shell `_5.0`: the tag set through a projection is readable before the
    // variant's second field is written, and `_5` only becomes initialized at the end.
    let p50 = proj(5, vec![field(0, enum2_ty.clone())]);
    let p50_v1_f0 = proj(
        5,
        vec![
            field(0, enum2_ty.clone()),
            ProjectionElem::Downcast(1),
            field(0, u32_ty()),
        ],
    );
    let p50_v1_f1 = proj(
        5,
        vec![
            field(0, enum2_ty.clone()),
            ProjectionElem::Downcast(1),
            field(1, u8_ty()),
        ],
    );
    let p51 = proj(5, vec![field(1, u8_ty())]);
    run(
        assign(p50_v1_f0, use_const(Constant::Int(1, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        run(
            assign(Place::from_local(0), Rvalue::Discriminant(p50.clone())),
            &mut state
        ),
        Err(RvalueEvalError::UninitializedLocal(Local(5)))
    );
    run(
        Statement::SetDiscriminant {
            place: p50.clone(),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    run(
        assign(Place::from_local(0), Rvalue::Discriminant(p50.clone())),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::signed(1, IntTy::Isize, PW))
    );
    run(
        assign(p51, use_const(Constant::Int(3, u8_ty()))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(5)),
        Some(LocalSlotState::PartialShell(_))
    ));
    run(
        assign(p50_v1_f1, use_const(Constant::Int(2, u8_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(5)),
        Some(&MirValue::Tuple(vec![
            MirValue::Adt {
                def_path: String::new(),
                variant_idx: 1,
                active_field: None,
                fields: vec![u32v(1), u8v(2)],
            },
            u8v(3),
        ]))
    );
}

// ---------------------------------------------------------------------------------------------
// [adv B1] Value-tree writes preserve the container's field types
// ---------------------------------------------------------------------------------------------

/// `eval_place_read` checks a projected tuple/ADT field's runtime type against the
/// projection's `Field(idx, ty)`; the leaf write path only checked the *new* value, so a
/// mistyped `Field(1, u16)` projection silently changed a `(u32, u8)` value into a
/// `(u32, u16)` value. Writes must leave every container's type unchanged.
#[test]
fn test_ep1_b1_projected_leaf_writes_preserve_field_types() {
    let original = vec![
        MirValue::Tuple(vec![u32v(1), u8v(2)]),
        MirValue::Adt {
            def_path: "S".into(),
            variant_idx: 0,
            active_field: None,
            fields: vec![u32v(3), u8v(4)],
        },
    ];
    for local in 0..2 {
        let mut locals = original.clone();
        let bad = proj(local, vec![field(1, u16_ty())]);
        assert!(matches!(
            eval_place_write(&bad, u16v(0x1234), &mut locals, PW),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
        assert_eq!(locals, original, "failed writes must not modify locals");
        assert!(matches!(
            eval_place_read(&bad, &locals, PW),
            Err(RvalueEvalError::TypeMismatch(_))
        ));

        let good = proj(local, vec![field(1, u8_ty())]);
        eval_place_write(&good, u8v(0xAB), &mut locals, PW).unwrap();
        assert_eq!(eval_place_read(&good, &locals, PW), Ok(u8v(0xAB)));
        assert_eq!(locals[local].ty(), original[local].ty());
    }
}

// ---------------------------------------------------------------------------------------------
// [adv B1] Property tests: projection lens laws over random arrays, windows, and indices
// ---------------------------------------------------------------------------------------------

fn subslice_bounds(len: u64, from: u64, to: u64, from_end: bool) -> Option<(usize, usize)> {
    if from_end {
        let sum = from.checked_add(to)?;
        (sum <= len).then(|| (from as usize, (len - to) as usize))
    } else {
        (from <= to && to <= len).then(|| (from as usize, to as usize))
    }
}

fn constant_index(len: u64, offset: u64, min_length: u64, from_end: bool) -> Option<usize> {
    if len < min_length {
        return None;
    }
    if from_end {
        (offset >= 1 && offset <= len).then(|| (len - offset) as usize)
    } else {
        (offset < len).then_some(offset as usize)
    }
}

/// Random `Subslice` windows followed by `ConstantIndex` / `Index` / `Field` steps on
/// `[(u32, u8); n]` arrays: reads agree with direct index arithmetic, out-of-bounds steps fail
/// with `IndexOutOfBounds`, and successful writes satisfy the lens laws
/// (`get(put(v)) == v`, `put(get()) == id`, `put(b, put(a)) == put(b)`).
#[test]
fn test_ep1_b1_property_chained_subslice_constant_index_lens_laws() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    for _ in 0..600 {
        let len = rng.below(7) as usize;
        let elems: Vec<MirValue> = (0..len)
            .map(|i| MirValue::Tuple(vec![u32v(100 + i as u128), u8v(i as u128)]))
            .collect();
        let arr = MirValue::Array {
            elements: elems.clone(),
            elem_ty: pair_ty.clone(),
        };
        let from = rng.below(len as u64 + 2);
        let to = rng.below(len as u64 + 2);
        let from_end = rng.below(2) == 1;
        let offset = rng.below(len as u64 + 2);
        let min_length = rng.below(len as u64 + 2);
        let ci_from_end = rng.below(2) == 1;
        let use_dynamic_index = rng.below(3) == 0;

        let window = subslice_bounds(len as u64, from, to, from_end);
        let sub_len = window.map(|(s, e)| e - s);
        let mut projection = vec![ProjectionElem::Subslice { from, to, from_end }];
        let inner = if use_dynamic_index {
            projection.push(ProjectionElem::Index(Local(1)));
            sub_len.and_then(|n| (offset < n as u64).then_some(offset as usize))
        } else {
            projection.push(ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end: ci_from_end,
            });
            sub_len.and_then(|n| constant_index(n as u64, offset, min_length, ci_from_end))
        };
        projection.push(field(1, u8_ty()));
        let place = proj(0, projection);
        let mut locals = vec![arr.clone(), usizev(u128::from(offset))];

        let expected = window.zip(inner).map(|((start, _), i)| start + i);
        match expected {
            Some(abs) => {
                assert_eq!(eval_place_read(&place, &locals, PW), Ok(u8v(abs as u128)));
                // put(get()) == id
                let cur = eval_place_read(&place, &locals, PW).unwrap();
                eval_place_write(&place, cur, &mut locals, PW).unwrap();
                assert_eq!(locals[0], arr);
                // get(put(v)) == v, and only element `abs` changes.
                eval_place_write(&place, u8v(0xEE), &mut locals, PW).unwrap();
                assert_eq!(eval_place_read(&place, &locals, PW), Ok(u8v(0xEE)));
                let MirValue::Array { elements, .. } = &locals[0] else {
                    panic!("array local must stay an array");
                };
                for (i, e) in elements.iter().enumerate() {
                    if i == abs {
                        assert_eq!(e, &MirValue::Tuple(vec![u32v(100 + i as u128), u8v(0xEE)]));
                    } else {
                        assert_eq!(e, &elems[i]);
                    }
                }
                // put(b, put(a)) == put(b)
                eval_place_write(&place, u8v(0x11), &mut locals, PW).unwrap();
                let mut fresh = vec![arr.clone(), usizev(u128::from(offset))];
                eval_place_write(&place, u8v(0x11), &mut fresh, PW).unwrap();
                assert_eq!(locals, fresh);
            }
            None => {
                assert!(
                    matches!(
                        eval_place_read(&place, &locals, PW),
                        Err(RvalueEvalError::IndexOutOfBounds { .. })
                    ),
                    "len={len} from={from} to={to} from_end={from_end} offset={offset} \
                     min_length={min_length} ci_from_end={ci_from_end} dyn={use_dynamic_index}"
                );
                let before = locals.clone();
                assert!(matches!(
                    eval_place_write(&place, u8v(0xEE), &mut locals, PW),
                    Err(RvalueEvalError::IndexOutOfBounds { .. })
                ));
                assert_eq!(locals, before);
            }
        }
    }
}

/// `Subslice` writes splice exactly `end - start` elements back into the parent array, and a
/// whole-window write of the wrong length or element type fails without modifying the array.
#[test]
fn test_ep1_b1_property_subslice_window_writes_splice_exactly() {
    let mut rng = Rng(0xD1B5_4A32_D192_ED03);
    for _ in 0..300 {
        let len = 1 + rng.below(6) as usize;
        let elems: Vec<MirValue> = (0..len).map(|i| u32v(i as u128)).collect();
        let arr = MirValue::Array {
            elements: elems.clone(),
            elem_ty: u32_ty(),
        };
        let from = rng.below(len as u64 + 1);
        let to = rng.below(len as u64 + 1);
        let from_end = rng.below(2) == 1;
        let Some((start, end)) = subslice_bounds(len as u64, from, to, from_end) else {
            continue;
        };
        let place = proj(0, vec![ProjectionElem::Subslice { from, to, from_end }]);
        let mut locals = vec![arr.clone()];
        let replacement: Vec<MirValue> = (start..end).map(|i| u32v(1000 + i as u128)).collect();
        eval_place_write(
            &place,
            MirValue::Array {
                elements: replacement.clone(),
                elem_ty: u32_ty(),
            },
            &mut locals,
            PW,
        )
        .unwrap();
        let mut expected = elems.clone();
        expected.splice(start..end, replacement);
        assert_eq!(
            locals[0],
            MirValue::Array {
                elements: expected,
                elem_ty: u32_ty(),
            }
        );

        let mut locals = vec![arr.clone()];
        let wrong_len = MirValue::Array {
            elements: vec![u32v(0); end - start + 1],
            elem_ty: u32_ty(),
        };
        assert!(matches!(
            eval_place_write(&place, wrong_len, &mut locals, PW),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
        let wrong_elem = MirValue::Array {
            elements: vec![u8v(0); end - start],
            elem_ty: u8_ty(),
        };
        assert!(matches!(
            eval_place_write(&place, wrong_elem, &mut locals, PW),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
        assert_eq!(locals[0], arr);
    }
}

// ---------------------------------------------------------------------------------------------
// [adv B1] `CastKind::CharToInt` differential check against `CastKind::IntToInt`
// ---------------------------------------------------------------------------------------------

/// `char as T` lowered as `CastKind::CharToInt` must agree with the pre-existing
/// `CastKind::IntToInt` path (which zero-extends `char` sources) on every integer target and
/// both pointer widths, and with Rust's own `as` casts for the fixed-width targets.
#[test]
fn test_ep1_b1_char_to_int_agrees_with_int_to_int_and_rust_as_casts() {
    let targets = [
        Ty::Uint(UintTy::U8),
        Ty::Uint(UintTy::U16),
        Ty::Uint(UintTy::U32),
        Ty::Uint(UintTy::U64),
        Ty::Uint(UintTy::U128),
        Ty::Uint(UintTy::Usize),
        Ty::Int(IntTy::I8),
        Ty::Int(IntTy::I16),
        Ty::Int(IntTy::I32),
        Ty::Int(IntTy::I64),
        Ty::Int(IntTy::I128),
        Ty::Int(IntTy::Isize),
    ];
    let mut tracker = ExposedProvenanceTracker::new();
    let mut rng = Rng(0xA076_1D64_78BD_642F);
    let mut chars = vec![
        '\0', '\u{7F}', '\u{80}', '\u{FF}', '\u{100}', '\u{D7FF}', '\u{E000}',
    ];
    chars.extend(['\u{FFFF}', '\u{10000}', '\u{1F600}', '\u{10FFFF}']);
    while chars.len() < 200 {
        if let Some(c) = char::from_u32(rng.below(0x11_0000) as u32) {
            chars.push(c);
        }
    }
    for pw in [PtrWidth::Bits32, PtrWidth::Bits64] {
        for target in &targets {
            for &c in &chars {
                let op = Operand::Constant(Constant::Char(c));
                let via_char = lower_rvalue(
                    &Rvalue::Cast(CastKind::CharToInt, op.clone(), target.clone()),
                    &[],
                    pw,
                )
                .unwrap();
                let via_int = lower_rvalue(
                    &Rvalue::Cast(CastKind::IntToInt, op, target.clone()),
                    &[],
                    pw,
                )
                .unwrap();
                let policy = TransmutePolicy::RejectPtrToInt;
                let a = eval_lowered_rvalue(&via_char, &[], pw, policy, &mut tracker).unwrap();
                let b = eval_lowered_rvalue(&via_int, &[], pw, policy, &mut tracker).unwrap();
                assert_eq!(a, b, "char {c:?} as {target:?} on {pw:?}");
                let code = u32::from(c);
                let rust_bits: Option<u128> = match target {
                    Ty::Uint(UintTy::U8) => Some(u128::from(code as u8)),
                    Ty::Uint(UintTy::U16) => Some(u128::from(code as u16)),
                    Ty::Int(IntTy::I8) => Some(u128::from(code as i8 as u8)),
                    Ty::Int(IntTy::I16) => Some(u128::from(code as i16 as u16)),
                    Ty::Uint(_) | Ty::Int(_) => Some(u128::from(code)),
                    _ => None,
                };
                assert_eq!(a.as_bits(), rust_bits, "char {c:?} as {target:?} on {pw:?}");
            }
        }
    }
    assert!(tracker.is_empty());
}

// ---------------------------------------------------------------------------------------------
// [adv B1] `NullOp::OffsetOf` matches `rustc` on canonical tuples with trailing ZST fields
// ---------------------------------------------------------------------------------------------

/// Offsets observed with `core::mem::offset_of!` on `rustc` `nightly-2026-06-01` (the
/// workspace toolchain) for canonical tuples, including trailing zero-sized fields, which
/// `rustc` keeps in declaration order for these layouts.
#[test]
fn test_ep1_b1_offset_of_matches_rustc_for_canonical_tuples_with_zst_fields() {
    let unit = Ty::unit();
    let cases: Vec<(Ty, usize, usize)> = vec![
        (Ty::Tuple(vec![u32_ty(), unit.clone()]), 1, 4),
        (Ty::Tuple(vec![u32_ty(), u32_ty(), unit.clone()]), 2, 8),
        (
            Ty::Tuple(vec![u32_ty(), Ty::Array(Box::new(u32_ty()), 0)]),
            1,
            4,
        ),
        (
            Ty::Tuple(vec![
                u32_ty(),
                u8_ty(),
                u8_ty(),
                u8_ty(),
                u8_ty(),
                unit.clone(),
            ]),
            5,
            8,
        ),
        (Ty::Tuple(vec![u32_ty(), u16_ty(), u16_ty()]), 2, 6),
    ];
    for (ty, field_idx, offset) in cases {
        assert!(ty.has_canonical_byte_layout(PW), "{ty:?} must be canonical");
        assert_eq!(
            resolve_offset_of(&ty, &[(0, field_idx)], PW),
            Ok(offset),
            "{ty:?}"
        );
    }
    // `((), u32)` and `(u32, (), u32)` are not canonical (alignment increases after the ZST),
    // so `OffsetOf` fails closed instead of guessing `rustc`'s placement.
    for ty in [
        Ty::Tuple(vec![unit.clone(), u32_ty()]),
        Ty::Tuple(vec![u32_ty(), unit.clone(), u32_ty()]),
    ] {
        assert_eq!(
            lower_rvalue(
                &Rvalue::NullaryOp(NullOp::OffsetOf(vec![(0, 1)]), ty.clone()),
                &[],
                PW
            ),
            Err(RvalueLowerError::UnsupportedOffsetOfLayout(ty))
        );
    }
}

// ---------------------------------------------------------------------------------------------
// [adv B1] Union writes: defined-but-unmodeled writes are unsupported, not undefined behavior
// ---------------------------------------------------------------------------------------------

/// Writing a whole union field switches the active field, and a nested write into the
/// active field updates it in place. A nested write into an *inactive* field (`u.b.0 = x`
/// while `u.a` is active) is defined in Rust, but the value tree has no bytes for `u.b`, so it
/// must report `UnsupportedPlaceProjection` (A0 reported `InactiveUnionField`, i.e. claimed
/// undefined behavior). Reads of the inactive field keep failing with `InactiveUnionField`.
#[test]
fn test_ep1_b1_union_nested_write_to_inactive_field_is_unsupported_not_ub() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let union_val = MirValue::Adt {
        def_path: "U".into(),
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![u32v(0x1234)],
    };
    let mut locals = vec![union_val.clone()];
    let a = proj(0, vec![field(0, u32_ty())]);
    let b = proj(0, vec![field(1, pair_ty.clone())]);
    let b0 = proj(0, vec![field(1, pair_ty.clone()), field(0, u32_ty())]);

    assert_eq!(
        eval_place_write(&b0, u32v(5), &mut locals, PW),
        Err(RvalueEvalError::UnsupportedPlaceProjection(b0.clone()))
    );
    assert_eq!(locals[0], union_val);
    assert_eq!(
        eval_place_read(&b0, &locals, PW),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 0,
            requested_field: 1,
        })
    );

    // Whole-field write of `u.b` switches the active field; then the nested write succeeds.
    eval_place_write(&b, MirValue::Tuple(vec![u32v(1), u8v(2)]), &mut locals, PW).unwrap();
    eval_place_write(&b0, u32v(5), &mut locals, PW).unwrap();
    assert_eq!(
        eval_place_read(&b, &locals, PW),
        Ok(MirValue::Tuple(vec![u32v(5), u8v(2)]))
    );
    assert_eq!(
        eval_place_read(&a, &locals, PW),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 1,
            requested_field: 0,
        })
    );

    // The stateful evaluator classifies the same write identically.
    let local_decls = vec![Ty::Tuple(vec![u32_ty(), pair_ty])];
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    state.slots[0] = LocalSlotState::Init(union_val.clone());
    assert_eq!(
        run(
            assign(b0.clone(), use_const(Constant::Int(5, u32_ty()))),
            &mut state
        ),
        Err(RvalueEvalError::UnsupportedPlaceProjection(b0))
    );
    assert_eq!(state.get_init(Local(0)), Some(&union_val));
}

// ---------------------------------------------------------------------------------------------
// [adv B1] Shell misuse is a static type error, not an uninitialized read
// ---------------------------------------------------------------------------------------------

/// Hand-built `LoweredStatement`s that bypass `lower_statement`'s type checks must not be
/// reported as undefined behavior: an array projection on a tuple shell, a `Downcast` that is
/// not followed by `Field`, and a `Field` on a non-tuple declared type are static type errors.
/// An element write into an uninitialized array stays `UninitializedLocal` (`c6d2ad74`).
#[test]
fn test_ep1_b1_shell_misuse_is_type_error_while_uninit_array_writes_stay_ub() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let arr_ty = Ty::Array(Box::new(u32_ty()), 2);
    let local_decls = vec![pair_ty.clone(), arr_ty.clone(), usize_ty()];
    let mut state = StatementEvalState::from_local_decls(local_decls.clone(), PW);
    state.slots[2] = LocalSlotState::Init(usizev(0));
    run(
        assign(
            proj(0, vec![field(0, u32_ty())]),
            use_const(Constant::Int(1, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    let shell_before = state.get_local(Local(0)).cloned();

    let one = Rvalue::Use(Operand::Constant(Constant::Int(9, u32_ty())));
    let lowered_one = lower_rvalue(&one, &local_decls, PW).unwrap();
    let hand_built = |place: Place, place_ty: Ty| LoweredStatement::Assign {
        place,
        place_ty,
        rvalue: lowered_one.clone(),
    };

    // `_0[_2] = 9` on a tuple shell.
    let bad_index = hand_built(proj(0, vec![ProjectionElem::Index(Local(2))]), u32_ty());
    assert!(matches!(
        eval_lowered_statement(&bad_index, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    // `(_1 as V0)[_2] = 9`: `Downcast` not followed by `Field`.
    let bad_downcast = hand_built(
        proj(
            1,
            vec![ProjectionElem::Downcast(0), ProjectionElem::Index(Local(2))],
        ),
        u32_ty(),
    );
    assert!(matches!(
        eval_lowered_statement(&bad_downcast, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    // `_1.0 = 9` on an uninitialized array local.
    let bad_field = hand_built(proj(1, vec![field(0, u32_ty())]), u32_ty());
    assert!(matches!(
        eval_lowered_statement(&bad_field, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    // Reading `_0[_2]` from the shell is also a type error, not an uninitialized read.
    assert!(matches!(
        state.read_place(&proj(0, vec![ProjectionElem::Index(Local(2))])),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(state.get_local(Local(0)).cloned(), shell_before);

    // `_1[_2] = 9` on the uninitialized array: undefined behavior per `c6d2ad74`.
    let uninit_elem = stmt(
        assign(proj(1, vec![ProjectionElem::Index(Local(2))]), one.clone()),
        &local_decls,
    );
    assert_eq!(
        eval_lowered_statement(&uninit_elem, &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    let uninit_const = stmt(
        assign(
            proj(
                1,
                vec![ProjectionElem::ConstantIndex {
                    offset: 1,
                    min_length: 2,
                    from_end: true,
                }],
            ),
            one,
        ),
        &local_decls,
    );
    assert_eq!(
        eval_lowered_statement(&uninit_const, &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
}

// ---------------------------------------------------------------------------------------------
// [adv B1] Property test: `D13b` field-by-field initialization in random orders
// ---------------------------------------------------------------------------------------------

/// Field types used by the random `D13b` shapes: scalars, `()` (whose unwritten slot must not
/// read as `MirValue::Unit`), whole `[u8; 2]` arrays, and nested tuples.
#[derive(Clone, Debug)]
enum Shape {
    U8,
    U32,
    Unit,
    Arr2,
    Tup(Vec<Shape>),
}

impl Shape {
    fn random(rng: &mut Rng, depth: u32) -> Shape {
        match rng.below(if depth == 0 { 4 } else { 6 }) {
            0 => Shape::U8,
            1 => Shape::U32,
            2 => Shape::Unit,
            3 => Shape::Arr2,
            _ => Shape::random_tuple(rng, depth - 1),
        }
    }

    fn random_tuple(rng: &mut Rng, depth: u32) -> Shape {
        let n = 1 + rng.below(3) as usize;
        Shape::Tup((0..n).map(|_| Shape::random(rng, depth)).collect())
    }

    fn ty(&self) -> Ty {
        match self {
            Shape::U8 => u8_ty(),
            Shape::U32 => u32_ty(),
            Shape::Unit => Ty::unit(),
            Shape::Arr2 => Ty::Array(Box::new(u8_ty()), 2),
            Shape::Tup(fields) => Ty::Tuple(fields.iter().map(Shape::ty).collect()),
        }
    }

    fn value(&self, rng: &mut Rng) -> MirValue {
        match self {
            Shape::U8 => u8v(u128::from(rng.below(256))),
            Shape::U32 => u32v(u128::from(rng.below(1 << 32))),
            Shape::Unit => MirValue::Unit,
            Shape::Arr2 => MirValue::Array {
                elements: vec![
                    u8v(u128::from(rng.below(256))),
                    u8v(u128::from(rng.below(256))),
                ],
                elem_ty: u8_ty(),
            },
            Shape::Tup(fields) => MirValue::Tuple(fields.iter().map(|f| f.value(rng)).collect()),
        }
    }

    /// Collects `(field path, is_leaf)` for every sub-place below `self` (excluding `self`).
    fn paths(&self, prefix: &mut Vec<ProjectionElem>, out: &mut Vec<(Vec<ProjectionElem>, bool)>) {
        if let Shape::Tup(fields) = self {
            for (i, f) in fields.iter().enumerate() {
                prefix.push(field(i, f.ty()));
                out.push((prefix.clone(), !matches!(f, Shape::Tup(_))));
                f.paths(prefix, out);
                prefix.pop();
            }
        }
    }
}

fn sub_value<'a>(val: &'a MirValue, path: &[ProjectionElem]) -> &'a MirValue {
    path.iter().fold(val, |v, p| match (v, p) {
        (MirValue::Tuple(fields), ProjectionElem::Field(i, _)) => &fields[*i],
        _ => panic!("path must follow tuple fields"),
    })
}

fn leaf_rvalue(val: &MirValue) -> Rvalue {
    match val {
        MirValue::Int { bits, ty } => use_const(Constant::Int(*bits, ty.clone())),
        MirValue::Unit => use_const(Constant::Unit),
        MirValue::Array { elements, elem_ty } => Rvalue::Aggregate(
            AggregateKind::Array(elem_ty.clone()),
            elements
                .iter()
                .map(|e| Operand::Constant(Constant::Int(e.as_bits().unwrap(), elem_ty.clone())))
                .collect(),
        ),
        other => panic!("unexpected leaf value {other:?}"),
    }
}

/// Builds random nested tuple values field by field into an uninitialized local, in a random
/// leaf order, either as a plain tuple or as an enum variant (`Downcast(v)` paths plus a
/// `SetDiscriminant` at a random point after the first write). After every step:
/// - a written leaf reads back its value and an unwritten leaf (including `()`) fails with
///   `UninitializedLocal`;
/// - an intermediate tuple (and the root) is readable iff all of its leaves are written (and,
///   for the enum root, the tag has been written);
/// - `Rvalue::Discriminant` of the enum root is defined iff the tag has been written.
#[test]
fn test_ep1_b1_property_d13b_random_field_orders_never_false_accept() {
    let mut rng = Rng(0x5851_F42D_4C95_7F2D);
    for _ in 0..250 {
        let shape = Shape::random_tuple(&mut rng, 2);
        let ty = shape.ty();
        let expected = shape.value(&mut rng);
        let as_enum = rng.below(2) == 1;
        let variant = rng.below(3) as usize;
        let root_prefix: Vec<ProjectionElem> = if as_enum {
            vec![ProjectionElem::Downcast(variant)]
        } else {
            Vec::new()
        };
        let mut paths = Vec::new();
        shape.paths(&mut Vec::new(), &mut paths);
        let mut leaves: Vec<Vec<ProjectionElem>> = paths
            .iter()
            .filter(|(_, leaf)| *leaf)
            .map(|(p, _)| p.clone())
            .collect();
        for i in (1..leaves.len()).rev() {
            let j = rng.below(i as u64 + 1) as usize;
            leaves.swap(i, j);
        }
        let set_discr_after = 1 + rng.below(leaves.len() as u64) as usize;
        // Actions: `Some(leaf)` writes a leaf, `None` runs `SetDiscriminant` (enum mode only).
        let mut actions: Vec<Option<Vec<ProjectionElem>>> = Vec::new();
        for (step, leaf) in leaves.iter().enumerate() {
            actions.push(Some(leaf.clone()));
            if as_enum && step + 1 == set_discr_after {
                actions.push(None);
            }
        }

        let local_decls = vec![Ty::Int(IntTy::Isize), ty.clone()];
        let mut state = StatementEvalState::from_local_decls(local_decls, PW);
        let mut written: Vec<Vec<ProjectionElem>> = Vec::new();
        let mut tag_written = false;
        let full_place = |path: &[ProjectionElem]| {
            let mut projection = root_prefix.clone();
            projection.extend_from_slice(path);
            proj(1, projection)
        };
        for action in &actions {
            match action {
                Some(leaf) => {
                    let value = sub_value(&expected, leaf);
                    run(assign(full_place(leaf), leaf_rvalue(value)), &mut state).unwrap();
                    written.push(leaf.clone());
                }
                None => {
                    run(
                        Statement::SetDiscriminant {
                            place: Place::from_local(1),
                            variant_index: variant,
                        },
                        &mut state,
                    )
                    .unwrap();
                    tag_written = true;
                }
            }

            for (path, is_leaf) in &paths {
                let complete = written.iter().any(|w| w == path)
                    || (!*is_leaf
                        && written.iter().filter(|w| w.starts_with(path)).count()
                            == paths
                                .iter()
                                .filter(|(p, l)| *l && p.starts_with(path))
                                .count());
                let got = state.read_place(&full_place(path));
                if complete {
                    assert_eq!(
                        got,
                        Ok(sub_value(&expected, path).clone()),
                        "{shape:?} {path:?}"
                    );
                } else {
                    assert_eq!(
                        got,
                        Err(RvalueEvalError::UninitializedLocal(Local(1))),
                        "{shape:?} {path:?}"
                    );
                }
            }
            let all_written = written.len() == leaves.len();
            let root_readable = all_written && (!as_enum || tag_written);
            let root = state.read_place(&Place::from_local(1));
            let expected_root = if as_enum {
                let MirValue::Tuple(fields) = expected.clone() else {
                    unreachable!()
                };
                MirValue::Adt {
                    def_path: String::new(),
                    variant_idx: variant,
                    active_field: None,
                    fields,
                }
            } else {
                expected.clone()
            };
            if root_readable {
                assert_eq!(root, Ok(expected_root.clone()), "{shape:?}");
                assert_eq!(state.get_init(Local(1)), Some(&expected_root));
            } else {
                assert_eq!(
                    root,
                    Err(RvalueEvalError::UninitializedLocal(Local(1))),
                    "{shape:?}"
                );
            }
            if as_enum {
                let discr = run(
                    assign(
                        Place::from_local(0),
                        Rvalue::Discriminant(Place::from_local(1)),
                    ),
                    &mut state,
                );
                if tag_written {
                    discr.unwrap();
                    assert_eq!(
                        state.get_init(Local(0)),
                        Some(&MirValue::signed(variant as i128, IntTy::Isize, PW))
                    );
                } else {
                    assert_eq!(discr, Err(RvalueEvalError::UninitializedLocal(Local(1))));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// [adv B1] `PlaceMention` matrix against `Trusted.MirSemantics.placeMentionOperandsInit`
// ---------------------------------------------------------------------------------------------

/// `evalStmt` on `.placeMention place` faults iff the root slot is `.dead`, a dereferenced
/// root is not initialized, or an `Index` local is not an initialized scalar; it never loads
/// the mentioned place itself.
#[test]
fn test_ep1_b1_place_mention_matrix_matches_place_mention_operands_init() {
    let raw_u32 = Ty::RawPtr(Box::new(u32_ty()), Mutability::Not);
    let arr_ty = Ty::Array(Box::new(u32_ty()), 2);
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let local_decls = vec![
        arr_ty.clone(),  // _0: [u32; 2]
        usize_ty(),      // _1: index
        raw_u32.clone(), // _2: *const u32
        pair_ty.clone(), // _3: (u32, u8)
    ];
    let ptr = MirValue::ptr(PointerValue::without_provenance(0xDEAD_BEE0), raw_u32);
    let mention = |p: Place| Statement::PlaceMention(p);

    // (root slot of `_0`/`_3`, index slot, pointer slot)
    let root_states = [
        LocalSlotState::Dead,
        LocalSlotState::Uninit,
        LocalSlotState::Init(MirValue::Array {
            elements: vec![u32v(1), u32v(2)],
            elem_ty: u32_ty(),
        }),
    ];
    let idx_states = [
        LocalSlotState::Dead,
        LocalSlotState::Uninit,
        LocalSlotState::Init(usizev(7)), // out of bounds: never loaded, so still fine
    ];
    for root in &root_states {
        for idx in &idx_states {
            let mut state = StatementEvalState::from_local_decls(local_decls.clone(), PW);
            state.slots[0] = root.clone();
            state.slots[1] = idx.clone();
            let root_dead = matches!(root, LocalSlotState::Dead);
            let idx_init = matches!(idx, LocalSlotState::Init(_));

            let bare = run(mention(Place::from_local(0)), &mut state);
            assert_eq!(bare.is_ok(), !root_dead, "bare mention root={root:?}");
            let indexed = run(
                mention(proj(0, vec![ProjectionElem::Index(Local(1))])),
                &mut state,
            );
            assert_eq!(
                indexed.is_ok(),
                !root_dead && idx_init,
                "root={root:?} idx={idx:?}"
            );
            let constant = run(
                mention(proj(
                    0,
                    vec![ProjectionElem::ConstantIndex {
                        offset: 1,
                        min_length: 2,
                        from_end: false,
                    }],
                )),
                &mut state,
            );
            assert_eq!(constant.is_ok(), !root_dead, "constant index root={root:?}");
        }
    }

    // Deref roots: initialized pointer ok (even dangling), uninit/dead pointer faults.
    for (ptr_state, ok) in [
        (LocalSlotState::Init(ptr.clone()), true),
        (LocalSlotState::Uninit, false),
        (LocalSlotState::Dead, false),
    ] {
        let mut state = StatementEvalState::from_local_decls(local_decls.clone(), PW);
        state.slots[2] = ptr_state.clone();
        let deref = run(mention(proj(2, vec![ProjectionElem::Deref])), &mut state);
        assert_eq!(deref.is_ok(), ok, "deref ptr={ptr_state:?}");
    }

    // Field mentions of an uninitialized or partially initialized tuple never load the field.
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    run(mention(proj(3, vec![field(1, u8_ty())])), &mut state).unwrap();
    run(
        assign(
            proj(3, vec![field(0, u32_ty())]),
            use_const(Constant::Int(1, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    run(mention(proj(3, vec![field(1, u8_ty())])), &mut state).unwrap();
    run(mention(Place::from_local(3)), &mut state).unwrap();
}

// ---------------------------------------------------------------------------------------------
// [adv A1] `SetDiscriminant` through `Downcast` on nested enum shells & variant switching
// ---------------------------------------------------------------------------------------------

/// When an outer enum shell `_1` already has its discriminant tag set (`discriminant(_1) = 1`)
/// and its sole field `(_1 as V1).0` is an inner enum shell whose field `(((_1 as V1).0 as V2).0)`
/// has been written, running `SetDiscriminant { place: (_1 as V1).0, variant_index: 2 }`
/// completes both the inner and outer enum shells, promoting `_1` to `LocalSlotState::Init`.
/// (In B1, `set_discriminant_in_slot` cloned `outer_shell` into `temp` on `Downcast`, and when
/// `temp` promoted to `FieldSlot::Init`, `if let FieldSlot::Partial(updated_shell) = temp` was
/// false, silently discarding the `SetDiscriminant` update.)
#[test]
fn test_ep1_a1_set_discriminant_through_downcast_promotes_nested_and_outer_enum_shells() {
    let inner_enum_ty = Ty::Tuple(vec![u32_ty()]);
    let outer_enum_ty = Ty::Tuple(vec![inner_enum_ty.clone()]);
    let local_decls = vec![
        Ty::Int(IntTy::Isize), // _0: discriminant scratch
        outer_enum_ty.clone(), // _1: outer enum
        outer_enum_ty.clone(), // _2: copy target
    ];
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);

    let inner_place = proj(
        1,
        vec![ProjectionElem::Downcast(1), field(0, inner_enum_ty)],
    );
    let inner_leaf = proj(
        1,
        vec![
            ProjectionElem::Downcast(1),
            field(0, Ty::Tuple(vec![u32_ty()])),
            ProjectionElem::Downcast(2),
            field(0, u32_ty()),
        ],
    );

    // 1. Write the leaf payload of the inner enum variant.
    run(
        assign(inner_leaf, use_const(Constant::Int(42, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(1)),
        Some(LocalSlotState::PartialShell(_))
    ));

    // 2. Write the outer enum's discriminant tag FIRST; `_1` stays a `PartialShell` because the
    // inner enum's tag is still unwritten.
    run(
        Statement::SetDiscriminant {
            place: Place::from_local(1),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(1)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        state.read_place(&Place::from_local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );

    // 3. Write the inner enum's discriminant tag through `(_1 as V1).0`: both shells are now
    // complete, so `_1` promotes to `LocalSlotState::Init`.
    run(
        Statement::SetDiscriminant {
            place: inner_place.clone(),
            variant_index: 2,
        },
        &mut state,
    )
    .unwrap();
    let expected = MirValue::Adt {
        def_path: String::new(),
        variant_idx: 1,
        active_field: None,
        fields: vec![MirValue::Adt {
            def_path: String::new(),
            variant_idx: 2,
            active_field: None,
            fields: vec![u32v(42)],
        }],
    };
    assert_eq!(state.get_init(Local(1)), Some(&expected));
    run(
        assign(Place::from_local(2), use_copy(Place::from_local(1))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(2)), Some(&expected));
    run(
        assign(Place::from_local(0), Rvalue::Discriminant(inner_place)),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::signed(2, IntTy::Isize, PW))
    );
}

/// If a shell's fields were written under `Downcast(v)` and `SetDiscriminant(w)` then sets a
/// *different* variant `w != v`, those fields belong to variant `v` and must not initialize
/// variant `w`: the shell's tag becomes `w` (`Rvalue::Discriminant` returns `w`), while reading
/// the whole enum or variant `w`'s fields fails with `UninitializedLocal` until variant `w`'s
/// fields are written. Also verifies that a `SetDiscriminant` target ending in `Downcast` is
/// rejected with `TypeMismatch` in all slot states (`Uninit`, `PartialShell`, `Init`).
#[test]
fn test_ep1_a1_set_discriminant_variant_switch_on_partial_shell_clears_old_variant_fields() {
    let enum_ty = Ty::Tuple(vec![u32_ty()]);
    let local_decls = vec![Ty::Int(IntTy::Isize), enum_ty.clone()];
    let mut state = StatementEvalState::from_local_decls(local_decls.clone(), PW);

    let v1_f0 = proj(1, vec![ProjectionElem::Downcast(1), field(0, u32_ty())]);
    let v2_f0 = proj(1, vec![ProjectionElem::Downcast(2), field(0, u32_ty())]);

    // Write variant 1's field, then set discriminant to variant 2 (`2 != 1`).
    run(
        assign(v1_f0.clone(), use_const(Constant::Int(42, u32_ty()))),
        &mut state,
    )
    .unwrap();
    run(
        Statement::SetDiscriminant {
            place: Place::from_local(1),
            variant_index: 2,
        },
        &mut state,
    )
    .unwrap();

    // Tag is now 2, so `Discriminant(_1)` returns 2, and `Downcast(1)` fails with
    // `InactiveVariantProjection`.
    run(
        assign(
            Place::from_local(0),
            Rvalue::Discriminant(Place::from_local(1)),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::signed(2, IntTy::Isize, PW))
    );
    assert_eq!(
        state.read_place(&v1_f0),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 2,
        })
    );
    // Variant 2's field was never written, so reading `_1` or `(_1 as V2).0` must fail closed!
    assert_eq!(state.get_init(Local(1)), None);
    assert_eq!(
        state.read_place(&Place::from_local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(
        state.read_place(&v2_f0),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );

    // Writing `(_1 as V2).0 = 77` completes variant 2 and promotes `_1` to `Init`.
    run(
        assign(v2_f0.clone(), use_const(Constant::Int(77, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::Adt {
            def_path: String::new(),
            variant_idx: 2,
            active_field: None,
            fields: vec![u32v(77)],
        })
    );

    // A `SetDiscriminant` target ending in `Downcast` is rejected with `TypeMismatch` in all
    // slot states (`Init`, `PartialShell`, `Uninit`).
    let bad_set_discr = LoweredStatement::SetDiscriminant {
        place: proj(1, vec![ProjectionElem::Downcast(2)]),
        place_ty: enum_ty,
        variant_index: 2,
    };
    assert!(matches!(
        eval_lowered_statement(&bad_set_discr, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    state.slots[1] = LocalSlotState::Uninit;
    assert!(matches!(
        eval_lowered_statement(&bad_set_discr, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    run(
        assign(v2_f0, use_const(Constant::Int(1, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        eval_lowered_statement(&bad_set_discr, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// [adv A1] Union field bounds, declared field types, and inactive-field tail validation
// ---------------------------------------------------------------------------------------------

/// In `StatementEvalState`, an initialized union local (`MirValue::Adt { active_field: Some(_), .. }`)
/// stores only its single active operand in `fields`, so field reads and writes must check the
/// union local's declared `Ty::Tuple(union_field_tys)` to reject out-of-bounds field indices and
/// mistyped `Field` projections without corrupting the local. Nested accesses through an
/// inactive union field must also validate the remaining projection tail before reporting
/// `InactiveUnionField` or `UnsupportedPlaceProjection`.
#[test]
fn test_ep1_a1_union_reads_and_writes_validate_declared_fields_and_inactive_tail_types() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let union_ty = Ty::Tuple(vec![u32_ty(), pair_ty.clone()]);
    let local_decls = vec![union_ty];
    let union_val = MirValue::Adt {
        def_path: "U".into(),
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![u32v(0x1234)],
    };
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    state.slots[0] = LocalSlotState::Init(union_val.clone());

    // 1. Out-of-bounds union field `_0.99` fails with `FieldOutOfBounds` on both read and write
    // (B1 accepted the write and set `active_field = Some(99)`, and returned `InactiveUnionField`
    // on read).
    let oob_place = proj(0, vec![field(99, u32_ty())]);
    assert_eq!(
        state.read_place(&oob_place),
        Err(RvalueEvalError::FieldOutOfBounds {
            field_idx: 99,
            field_count: 2,
        })
    );
    assert_eq!(
        state.write_place(&oob_place, &u32_ty(), u32v(7)),
        Err(RvalueEvalError::FieldOutOfBounds {
            field_idx: 99,
            field_count: 2,
        })
    );
    assert_eq!(state.get_init(Local(0)), Some(&union_val));

    // 2. Mistyped union field `Field(1, Ty::Bool)` (declared field 1 is `(u32, u8)`) fails with
    // `TypeMismatch` on both read and write without modifying `_0`.
    let wrong_ty_place = proj(0, vec![field(1, Ty::Bool)]);
    assert!(matches!(
        state.read_place(&wrong_ty_place),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.write_place(&wrong_ty_place, &Ty::Bool, MirValue::Bool(true)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(state.get_init(Local(0)), Some(&union_val));

    // 3. Ill-typed nested projections on an inactive union field are rejected with
    // `TypeMismatch` / `FieldOutOfBounds` before `InactiveUnionField` / `UnsupportedPlaceProjection`.
    let mut locals = vec![union_val.clone()];
    let bad_nested_ty = proj(0, vec![field(1, u8_ty()), field(0, u32_ty())]);
    assert!(matches!(
        eval_place_read(&bad_nested_ty, &locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        eval_place_write(&bad_nested_ty, u32v(1), &mut locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    let bad_nested_oob = proj(0, vec![field(1, pair_ty.clone()), field(5, u32_ty())]);
    assert_eq!(
        eval_place_read(&bad_nested_oob, &locals, PW),
        Err(RvalueEvalError::FieldOutOfBounds {
            field_idx: 5,
            field_count: 2,
        })
    );
    assert_eq!(
        eval_place_write(&bad_nested_oob, u32v(1), &mut locals, PW),
        Err(RvalueEvalError::FieldOutOfBounds {
            field_idx: 5,
            field_count: 2,
        })
    );

    let valid_nested_place = proj(0, vec![field(1, pair_ty), field(0, u32_ty())]);
    assert!(matches!(
        eval_place_write(&valid_nested_place, MirValue::Bool(true), &mut locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(locals[0], union_val);

    // 4. An ill-formed union `MirValue::Adt` with `fields: vec![]` is rejected with `TypeMismatch`.
    let empty_union = MirValue::Adt {
        def_path: "U".into(),
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![],
    };
    let mut bad_locals = vec![empty_union];
    assert!(matches!(
        eval_place_write(
            &proj(0, vec![field(0, u32_ty())]),
            u32v(1),
            &mut bad_locals,
            PW
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// [adv A1] `PartialShell` and `Uninit` projection type & tail validation
// ---------------------------------------------------------------------------------------------

/// Reading, computing `Discriminant`, or running `SetDiscriminant` through a `PartialShell` or
/// `Uninit` local must validate every `Field(idx, expected_ty)` against `local_decls` and
/// validate trailing projections on uninitialized sub-places so static type errors are never
/// misclassified as `UninitializedLocal` or falsely accepted.
#[test]
fn test_ep1_a1_partial_shell_and_uninit_projections_validate_field_types_and_tails() {
    let inner_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let outer_ty = Ty::Tuple(vec![inner_ty.clone(), u8_ty()]);
    let arr_ty = Ty::Array(Box::new(u32_ty()), 2);
    let local_decls = vec![
        outer_ty,   // _0: ((u32, u8), u8)
        arr_ty,     // _1: [u32; 2]
        usize_ty(), // _2: usize
    ];
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    state.slots[2] = LocalSlotState::Init(usizev(0));

    // Initialize `_0.0.0 = 10u32` and tag `_0.0` with variant 2 (`_0.0` is now a tagged
    // `PartialShell` because `_0.0.1` is still `Uninit`).
    let p00_v2_f0 = proj(
        0,
        vec![
            field(0, inner_ty.clone()),
            ProjectionElem::Downcast(2),
            field(0, u32_ty()),
        ],
    );
    run(
        assign(p00_v2_f0, use_const(Constant::Int(10, u32_ty()))),
        &mut state,
    )
    .unwrap();
    run(
        Statement::SetDiscriminant {
            place: proj(0, vec![field(0, inner_ty)]),
            variant_index: 2,
        },
        &mut state,
    )
    .unwrap();

    // 1. Reading `_0.0.0` through a mistyped outer `Field(0, Ty::Bool)` must fail with
    // `TypeMismatch` (B1 ignored `expected_ty` on `FieldSlot::Partial` and returned `Ok(10u32)`!).
    let mistyped_read = proj(
        0,
        vec![
            field(0, Ty::Bool),
            ProjectionElem::Downcast(2),
            field(0, u32_ty()),
        ],
    );
    assert!(matches!(
        state.read_place(&mistyped_read),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    // 2. `Rvalue::Discriminant` and `Statement::SetDiscriminant` through a mistyped
    // `Field(0, Ty::Bool)` on a tagged `PartialShell` must fail with `TypeMismatch` (B1
    // ignored `expected_ty` in `partial_shell_at` and `set_discriminant_in_slot` and succeeded!).
    let mistyped_inner = proj(0, vec![field(0, Ty::Bool)]);
    let bad_discr_stmt = LoweredStatement::Assign {
        place: Place::from_local(2),
        place_ty: Ty::Int(IntTy::Isize),
        rvalue: anneal_mir::lower::LoweredRvalue::Discriminant {
            place: mistyped_inner.clone(),
            place_ty: Ty::Bool,
            ty: Ty::Int(IntTy::Isize),
        },
    };
    assert!(matches!(
        eval_lowered_statement(&bad_discr_stmt, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    let bad_set_discr = LoweredStatement::SetDiscriminant {
        place: mistyped_inner,
        place_ty: Ty::Bool,
        variant_index: 1,
    };
    assert!(matches!(
        eval_lowered_statement(&bad_set_discr, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    // 3. On an uninitialized field `_0.1` (`u8`) or uninitialized array `_1` (`[u32; 2]`),
    // ill-typed trailing projections fail with `TypeMismatch` rather than `UninitializedLocal`.
    let bad_uninit_field_index = proj(0, vec![field(1, u8_ty()), ProjectionElem::Index(Local(2))]);
    assert!(matches!(
        state.read_place(&bad_uninit_field_index),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    let bad_uninit_arr_elem_field =
        proj(1, vec![ProjectionElem::Index(Local(2)), field(0, u32_ty())]);
    assert!(matches!(
        state.read_place(&bad_uninit_arr_elem_field),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.write_place(&bad_uninit_arr_elem_field, &u32_ty(), u32v(5)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// [adv A1] Array aggregates of unions & `LoweredRvalue` runtime operand type guards
// ---------------------------------------------------------------------------------------------

/// `Rvalue::Aggregate(AggregateKind::Array(union_ty), ...)` must accept union elements whose
/// runtime `MirValue::Adt { active_field: Some(idx), fields: vec![val] }` has 1 active operand
/// while `union_ty` is the multi-field `Ty::Tuple` of all declared union fields ( matching
/// `Rvalue::Repeat`). Also checks that hand-built `LoweredRvalue`s with mismatched runtime
/// operand types are rejected with `TypeMismatch`.
#[test]
fn test_ep1_a1_array_aggregates_of_unions_and_lowered_rvalue_runtime_type_guards() {
    let union_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let arr_union_ty = Ty::Array(Box::new(union_ty.clone()), 2);
    let local_decls = vec![union_ty.clone(), arr_union_ty.clone(), u32_ty()];
    let mut state = StatementEvalState::from_local_decls(local_decls.clone(), PW);

    let init_u = assign(
        Place::from_local(0),
        Rvalue::Aggregate(
            AggregateKind::Adt {
                def_path: "U".into(),
                variant_idx: 0,
                active_field: Some(1),
            },
            vec![Operand::Constant(Constant::Int(0x7F, u8_ty()))],
        ),
    );
    run(init_u, &mut state).unwrap();

    // `_1 = [copy _0, copy _0]` via `AggregateKind::Array(union_ty)` must succeed and match
    // `_1 = [copy _0; 2]` (`Rvalue::Repeat`).
    let init_arr = assign(
        Place::from_local(1),
        Rvalue::Aggregate(
            AggregateKind::Array(union_ty.clone()),
            vec![
                Operand::Copy(Place::from_local(0)),
                Operand::Copy(Place::from_local(0)),
            ],
        ),
    );
    run(init_arr, &mut state).unwrap();
    let elem0_f1 = proj(
        1,
        vec![
            ProjectionElem::ConstantIndex {
                offset: 0,
                min_length: 2,
                from_end: false,
            },
            field(1, u8_ty()),
        ],
    );
    assert_eq!(state.read_place(&elem0_f1), Ok(u8v(0x7F)));

    // Runtime operand type mismatches in `eval_lowered_rvalue` (`Use`, `BinaryOp`, `UnaryOp`,
    // `Aggregate`) must fail closed with `TypeMismatch`.
    let mut tracker = ExposedProvenanceTracker::new();
    let policy = TransmutePolicy::RejectPtrToInt;
    let lowered_use = lower_rvalue(&use_copy(Place::from_local(2)), &local_decls, PW).unwrap();
    assert!(matches!(
        eval_lowered_rvalue(
            &lowered_use,
            &[MirValue::Unit, MirValue::Unit, u8v(1)],
            PW,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    let lowered_add = lower_rvalue(
        &Rvalue::BinaryOp(
            anneal_mir::ir::BinOp::Add,
            Operand::Copy(Place::from_local(2)),
            Operand::Copy(Place::from_local(2)),
        ),
        &local_decls,
        PW,
    )
    .unwrap();
    assert!(matches!(
        eval_lowered_rvalue(
            &lowered_add,
            &[MirValue::Unit, MirValue::Unit, u8v(1)],
            PW,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    let lowered_not = lower_rvalue(
        &Rvalue::UnaryOp(
            anneal_mir::ir::UnOp::Not,
            Operand::Copy(Place::from_local(2)),
        ),
        &local_decls,
        PW,
    )
    .unwrap();
    assert!(matches!(
        eval_lowered_rvalue(
            &lowered_not,
            &[MirValue::Unit, MirValue::Unit, MirValue::Bool(true)],
            PW,
            policy,
            &mut tracker
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// [adv B2] Projected reads cost O(path + result), not O(size of the local)
// ---------------------------------------------------------------------------------------------

/// A1 deep-checked the whole root value against its declaration on every
/// `StatementEvalState::read_place`, and A0 deep-checked every intermediate tuple field, so
/// reading each element of an `n`-element array (bare or inside a tuple) cost `O(n^2)`.
/// Projected reads now check intermediate values by their outermost constructor and the
/// returned value in full. This loop over 32768 elements is instant with that bound (and
/// took on the order of a billion element comparisons before).
///
/// A projected read still rejects a malformed root constructor (wrong array element type)
/// and a malformed returned element; a malformed element that the read does not select is
/// detected by reads that return it, including a whole-local read.
#[test]
fn test_ep1_b2_projected_reads_do_not_traverse_the_whole_local() {
    const N: usize = 1 << 15;
    let arr_ty = Ty::Array(Box::new(u32_ty()), N);
    let local_decls = vec![
        arr_ty.clone(),                           // _0: [u32; N]
        usize_ty(),                               // _1: index
        Ty::Tuple(vec![arr_ty.clone(), u8_ty()]), // _2: ([u32; N], u8)
    ];
    let arr = MirValue::Array {
        elements: (0..N).map(|i| u32v(i as u128)).collect(),
        elem_ty: u32_ty(),
    };
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    state.slots[0] = LocalSlotState::Init(arr.clone());
    state.slots[2] = LocalSlotState::Init(MirValue::Tuple(vec![arr.clone(), u8v(1)]));
    let bare = proj(0, vec![ProjectionElem::Index(Local(1))]);
    let nested = proj(
        2,
        vec![field(0, arr_ty.clone()), ProjectionElem::Index(Local(1))],
    );
    for i in 0..N {
        state.slots[1] = LocalSlotState::Init(usizev(i as u128));
        assert_eq!(state.read_place(&bare), Ok(u32v(i as u128)));
        assert_eq!(state.read_place(&nested), Ok(u32v(i as u128)));
    }

    // Malformed root constructor: element type `u8` where `[u32; N]` is declared.
    state.slots[0] = LocalSlotState::Init(MirValue::Array {
        elements: vec![u8v(0); N],
        elem_ty: u8_ty(),
    });
    state.slots[1] = LocalSlotState::Init(usizev(0));
    assert!(matches!(
        state.read_place(&bare),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    // Malformed element `7` (a `u8`) inside a well-formed `[u32; N]` root.
    let mut elements: Vec<MirValue> = (0..N).map(|i| u32v(i as u128)).collect();
    elements[7] = u8v(7);
    state.slots[0] = LocalSlotState::Init(MirValue::Array {
        elements,
        elem_ty: u32_ty(),
    });
    state.slots[1] = LocalSlotState::Init(usizev(7));
    assert!(matches!(
        state.read_place(&bare),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    state.slots[1] = LocalSlotState::Init(usizev(8));
    assert_eq!(state.read_place(&bare), Ok(u32v(8)));
    assert!(matches!(
        state.read_place(&Place::from_local(0)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// [adv B2] `Assign` reads destination `Index` locals after the rvalue (`evalStmt` order)
// ---------------------------------------------------------------------------------------------

/// `Trusted.MirSemantics.evalStmt` on `.assign dst rv` evaluates `rv` first (threading the
/// moved-out locals into `locals₁`) and then writes `dst` with `writeProjectedValue locals₁`,
/// which reads `Index` locals of `dst` from `locals₁`. So `_0[_1] = move _1` faults on the
/// uninitialized `_1` (and leaves `_0` unchanged), while `_0[_1] = copy _1` writes `_0[_1]`.
#[test]
fn test_ep1_b2_assign_reads_destination_index_locals_after_the_rvalue() {
    let arr_ty = Ty::Array(Box::new(usize_ty()), 3);
    let local_decls = vec![arr_ty.clone(), usize_ty()];
    let arr = MirValue::Array {
        elements: vec![usizev(0), usizev(0), usizev(0)],
        elem_ty: usize_ty(),
    };
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);
    state.slots[0] = LocalSlotState::Init(arr.clone());
    state.slots[1] = LocalSlotState::Init(usizev(2));
    let dst = proj(0, vec![ProjectionElem::Index(Local(1))]);

    run(
        assign(dst.clone(), use_copy(Place::from_local(1))),
        &mut state,
    )
    .unwrap();
    let written = MirValue::Array {
        elements: vec![usizev(0), usizev(0), usizev(2)],
        elem_ty: usize_ty(),
    };
    assert_eq!(state.get_init(Local(0)), Some(&written));

    assert_eq!(
        run(assign(dst, use_move(Place::from_local(1))), &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(state.get_init(Local(0)), Some(&written));
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));
}

// ---------------------------------------------------------------------------------------------
// [adv B2] Property test: union active-field reads and writes against a reference model
// ---------------------------------------------------------------------------------------------

/// Random sequences of whole-field writes, nested writes, whole-field and nested reads, and
/// whole-union copies on a union local `U { a: u32, b: (u32, u8), c: [u8; 2] }`, checked
/// against a reference model holding `(active_field, value)`:
/// - a whole-field write of field `i` makes `i` active;
/// - a nested write into the active field updates it in place, while a nested write into an
///   inactive field is `UnsupportedPlaceProjection` and leaves the union unchanged;
/// - reads of the active field (whole or nested) return the model's value, reads of an
///   inactive field fail with `InactiveUnionField`;
/// - `_1 = copy _0` copies the union value with its active field.
#[test]
fn test_ep1_b2_property_union_active_field_reads_and_writes_match_reference_model() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let arr_ty = Ty::Array(Box::new(u8_ty()), 2);
    let field_tys = [u32_ty(), pair_ty.clone(), arr_ty.clone()];
    let union_ty = Ty::Tuple(field_tys.to_vec());
    let local_decls = vec![union_ty.clone(), union_ty.clone()];

    // Nested sub-places of each field: (projection below the field, leaf type).
    let nested: [Vec<(Vec<ProjectionElem>, Ty)>; 3] = [
        vec![],
        vec![
            (vec![field(0, u32_ty())], u32_ty()),
            (vec![field(1, u8_ty())], u8_ty()),
        ],
        vec![
            (
                vec![ProjectionElem::ConstantIndex {
                    offset: 0,
                    min_length: 2,
                    from_end: false,
                }],
                u8_ty(),
            ),
            (
                vec![ProjectionElem::ConstantIndex {
                    offset: 1,
                    min_length: 2,
                    from_end: true,
                }],
                u8_ty(),
            ),
        ],
    ];
    let random_value = |rng: &mut Rng, ty: &Ty| -> MirValue {
        match ty {
            Ty::Uint(UintTy::U32) => u32v(u128::from(rng.below(1 << 32))),
            Ty::Uint(UintTy::U8) => u8v(u128::from(rng.below(256))),
            Ty::Tuple(_) => MirValue::Tuple(vec![
                u32v(u128::from(rng.below(1 << 32))),
                u8v(u128::from(rng.below(256))),
            ]),
            Ty::Array(_, _) => MirValue::Array {
                elements: vec![
                    u8v(u128::from(rng.below(256))),
                    u8v(u128::from(rng.below(256))),
                ],
                elem_ty: u8_ty(),
            },
            other => panic!("unexpected field type {other:?}"),
        }
    };
    let value_rvalue = |val: &MirValue| -> Rvalue {
        match val {
            MirValue::Int { bits, ty } => use_const(Constant::Int(*bits, ty.clone())),
            MirValue::Tuple(vals) => Rvalue::Aggregate(
                AggregateKind::Tuple,
                vals.iter()
                    .map(|v| match v {
                        MirValue::Int { bits, ty } => {
                            Operand::Constant(Constant::Int(*bits, ty.clone()))
                        }
                        other => panic!("unexpected tuple element {other:?}"),
                    })
                    .collect(),
            ),
            MirValue::Array { elements, elem_ty } => Rvalue::Aggregate(
                AggregateKind::Array(elem_ty.clone()),
                elements
                    .iter()
                    .map(|e| {
                        Operand::Constant(Constant::Int(e.as_bits().unwrap(), elem_ty.clone()))
                    })
                    .collect(),
            ),
            other => panic!("unexpected value {other:?}"),
        }
    };
    let sub = |val: &MirValue, path: &[ProjectionElem]| -> MirValue {
        match (val, path) {
            (v, []) => v.clone(),
            (MirValue::Tuple(vals), [ProjectionElem::Field(i, _)]) => vals[*i].clone(),
            (
                MirValue::Array { elements, .. },
                [
                    ProjectionElem::ConstantIndex {
                        offset, from_end, ..
                    },
                ],
            ) => {
                let idx = if *from_end {
                    elements.len() - *offset as usize
                } else {
                    *offset as usize
                };
                elements[idx].clone()
            }
            other => panic!("unexpected sub-place {other:?}"),
        }
    };
    let set_sub = |val: &mut MirValue, path: &[ProjectionElem], new: MirValue| match (val, path) {
        (MirValue::Tuple(vals), [ProjectionElem::Field(i, _)]) => vals[*i] = new,
        (
            MirValue::Array { elements, .. },
            [
                ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                },
            ],
        ) => {
            let idx = if *from_end {
                elements.len() - *offset as usize
            } else {
                *offset as usize
            };
            elements[idx] = new;
        }
        other => panic!("unexpected sub-place {other:?}"),
    };

    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    for _ in 0..60 {
        let mut state = StatementEvalState::from_local_decls(local_decls.clone(), PW);
        let mut active = 0usize;
        let mut model = random_value(&mut rng, &field_tys[0]);
        run(
            assign(
                Place::from_local(0),
                Rvalue::Aggregate(
                    AggregateKind::Adt {
                        def_path: "U".into(),
                        variant_idx: 0,
                        active_field: Some(0),
                    },
                    vec![Operand::Constant(Constant::Int(
                        model.as_bits().unwrap(),
                        u32_ty(),
                    ))],
                ),
            ),
            &mut state,
        )
        .unwrap();
        for _ in 0..40 {
            let i = rng.below(3) as usize;
            let field_place = |extra: &[ProjectionElem]| {
                let mut projection = vec![field(i, field_tys[i].clone())];
                projection.extend_from_slice(extra);
                proj(0, projection)
            };
            let before = state.get_local(Local(0)).cloned();
            match rng.below(5) {
                0 => {
                    let v = random_value(&mut rng, &field_tys[i]);
                    run(assign(field_place(&[]), value_rvalue(&v)), &mut state).unwrap();
                    active = i;
                    model = v;
                }
                1 if !nested[i].is_empty() => {
                    let (path, leaf_ty) = &nested[i][rng.below(nested[i].len() as u64) as usize];
                    let v = random_value(&mut rng, leaf_ty);
                    let res = run(assign(field_place(path), value_rvalue(&v)), &mut state);
                    if i == active {
                        res.unwrap();
                        set_sub(&mut model, path, v);
                    } else {
                        assert_eq!(
                            res,
                            Err(RvalueEvalError::UnsupportedPlaceProjection(field_place(
                                path
                            )))
                        );
                        assert_eq!(state.get_local(Local(0)).cloned(), before);
                    }
                }
                2 if !nested[i].is_empty() => {
                    let (path, _) = &nested[i][rng.below(nested[i].len() as u64) as usize];
                    let got = state.read_place(&field_place(path));
                    if i == active {
                        assert_eq!(got, Ok(sub(&model, path)));
                    } else {
                        assert_eq!(
                            got,
                            Err(RvalueEvalError::InactiveUnionField {
                                active_field: active,
                                requested_field: i,
                            })
                        );
                    }
                }
                3 => {
                    run(
                        assign(Place::from_local(1), use_copy(Place::from_local(0))),
                        &mut state,
                    )
                    .unwrap();
                    assert_eq!(state.get_local(Local(1)), state.get_local(Local(0)));
                }
                _ => {
                    let got = state.read_place(&field_place(&[]));
                    if i == active {
                        assert_eq!(got, Ok(model.clone()));
                    } else {
                        assert_eq!(
                            got,
                            Err(RvalueEvalError::InactiveUnionField {
                                active_field: active,
                                requested_field: i,
                            })
                        );
                    }
                }
            }
            assert_eq!(
                state.get_init(Local(0)),
                Some(&MirValue::Adt {
                    def_path: "U".into(),
                    variant_idx: 0,
                    active_field: Some(active),
                    fields: vec![model.clone()],
                })
            );
        }
    }
}

// ---------------------------------------------------------------------------------------------
// [adv A2] Projected writes, `Subslice` steps, `Rvalue::Len`, and `SetDiscriminant` are O(path)
//          and atomic on error, and leaf array writes validate replaced element runtime types
// ---------------------------------------------------------------------------------------------

/// In B2, `StatementEvalState::write_place`, `eval_place_write`, and `SetDiscriminant` cloned
/// the entire root local and ran `mir_value_matches_ty` across the whole root container (and
/// `PartialAggregate::try_into_mir_value` cloned initialized sibling fields before checking
/// whether remaining fields were `Uninit`), `Subslice` cloned and scanned all `end - start`
/// elements even when followed by `Index`/`ConstantIndex`, and `Rvalue::Len` cloned and
/// deep-checked the entire target array. Additionally, leaf `Index`/`ConstantIndex` writes did
/// not check `mir_value_matches_ty(elem_slot, elem_ty)` on the replaced array element.
#[test]
fn test_ep1_a2_projected_writes_subslice_steps_and_len_are_linear_and_atomic() {
    const N: usize = 1 << 15;
    let arr_ty = Ty::Array(Box::new(u32_ty()), N);
    let inner_uninit_ty = Ty::Tuple(vec![u32_ty(), Ty::Array(Box::new(u32_ty()), 2)]);
    let shell_tuple_ty = Ty::Tuple(vec![arr_ty.clone(), inner_uninit_ty.clone()]);
    let local_decls = vec![
        arr_ty.clone(),                           // _0: [u32; N]
        usize_ty(),                               // _1: index / len target
        Ty::Tuple(vec![arr_ty.clone(), u8_ty()]), // _2: ([u32; N], u8)
        shell_tuple_ty.clone(),                   // _3: ([u32; N], (u32, [u32; 2])) partial shell
    ];
    let arr = MirValue::Array {
        elements: (0..N).map(|i| u32v(i as u128)).collect(),
        elem_ty: u32_ty(),
    };
    let mut state = StatementEvalState::from_local_decls(local_decls.clone(), PW);
    state.slots[0] = LocalSlotState::Init(arr.clone());
    state.slots[2] = LocalSlotState::Init(MirValue::Tuple(vec![arr.clone(), u8v(1)]));
    // Initialize `_3.0` to the N-element array while leaving `_3.1` uninitialized (`PartialShell`).
    state
        .write_place(&proj(3, vec![field(0, arr_ty.clone())]), &arr_ty, arr)
        .unwrap();
    assert!(matches!(
        state.get_local(Local(3)),
        Some(LocalSlotState::PartialShell(_))
    ));

    let bare_idx = proj(0, vec![ProjectionElem::Index(Local(1))]);
    let nested_idx = proj(
        2,
        vec![field(0, arr_ty.clone()), ProjectionElem::Index(Local(1))],
    );
    let shell_idx = proj(
        3,
        vec![field(0, arr_ty.clone()), ProjectionElem::Index(Local(1))],
    );
    let subslice_idx = proj(
        0,
        vec![
            ProjectionElem::Subslice {
                from: 1,
                to: (N - 1) as u64,
                from_end: false,
            },
            ProjectionElem::Index(Local(1)),
        ],
    );
    let subslice_place = proj(
        0,
        vec![ProjectionElem::Subslice {
            from: 1,
            to: (N - 1) as u64,
            from_end: false,
        }],
    );
    let lowered_len_subslice =
        lower_rvalue(&Rvalue::Len(subslice_place), &local_decls, PW).unwrap();
    let lowered_len_shell = lower_rvalue(
        &Rvalue::Len(proj(3, vec![field(0, arr_ty.clone())])),
        &local_decls,
        PW,
    )
    .unwrap();

    for i in 0..(N - 2) {
        state.slots[1] = LocalSlotState::Init(usizev(i as u128));
        let v = u32v((i + 100) as u128);
        state.write_place(&bare_idx, &u32_ty(), v.clone()).unwrap();
        state
            .write_place(&nested_idx, &u32_ty(), v.clone())
            .unwrap();
        state.write_place(&shell_idx, &u32_ty(), v.clone()).unwrap();
        state.write_place(&subslice_idx, &u32_ty(), v).unwrap();
        assert_eq!(
            state.read_place(&subslice_idx),
            Ok(u32v((i + 100) as u128))
        );
        if i < 64 {
            assert_eq!(
                anneal_mir::lower::eval_lowered_rvalue_in_state(&lowered_len_subslice, &mut state),
                Ok(usizev((N - 2) as u128))
            );
            assert_eq!(
                anneal_mir::lower::eval_lowered_rvalue_in_state(&lowered_len_shell, &mut state),
                Ok(usizev(N as u128))
            );
        }
    }

    // Failed nested writes into an uninitialized sub-field of `_3` must not materialize a child
    // `PartialShell` on `_3.1` (`_3` must remain unchanged).
    let shell_before = state.get_local(Local(3)).cloned();
    let bad_uninit_arr_write = proj(
        3,
        vec![
            field(1, inner_uninit_ty.clone()),
            field(1, Ty::Array(Box::new(u32_ty()), 2)),
            ProjectionElem::ConstantIndex {
                offset: 0,
                min_length: 2,
                from_end: false,
            },
        ],
    );
    assert_eq!(
        state.write_place(&bad_uninit_arr_write, &u32_ty(), u32v(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(3)))
    );
    assert_eq!(state.get_local(Local(3)).cloned(), shell_before);

    // Leaf `Index` and `ConstantIndex` writes must check the replaced element's runtime type:
    // if element 7 is malformed (`u8v(7)` in a `[u32; N]` array), replacing element 7 fails with
    // `TypeMismatch` without modifying the array, while replacing well-formed element 8 succeeds.
    let mut elements: Vec<MirValue> = (0..N).map(|i| u32v(i as u128)).collect();
    elements[7] = u8v(7);
    let malformed_arr = MirValue::Array {
        elements,
        elem_ty: u32_ty(),
    };
    state.slots[0] = LocalSlotState::Init(malformed_arr.clone());
    state.slots[1] = LocalSlotState::Init(usizev(7));
    assert!(matches!(
        state.write_place(&bare_idx, &u32_ty(), u32v(99)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    let const_idx_7 = proj(
        0,
        vec![ProjectionElem::ConstantIndex {
            offset: 7,
            min_length: 8,
            from_end: false,
        }],
    );
    assert!(matches!(
        state.write_place(&const_idx_7, &u32_ty(), u32v(99)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(state.get_init(Local(0)), Some(&malformed_arr));

    state.slots[1] = LocalSlotState::Init(usizev(8));
    state.write_place(&bare_idx, &u32_ty(), u32v(888)).unwrap();
    assert_eq!(state.read_place(&bare_idx), Ok(u32v(888)));
}

// ---------------------------------------------------------------------------------------------
// [adv A2] Union head and active-field checks reject malformed active fields on all accesses
// ---------------------------------------------------------------------------------------------

/// When a union local's currently active field holds a malformed value (wrong head type or
/// wrong nested field type), reading an inactive field or overwriting any field of the union
/// must fail with `RvalueEvalError::TypeMismatch` rather than reporting `InactiveUnionField`,
/// `UnsupportedPlaceProjection`, or silently overwriting the corrupted union.
#[test]
fn test_ep1_a2_union_head_and_active_field_checks_reject_malformed_active_field() {
    let pair_ty = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let union_ty = Ty::Tuple(vec![pair_ty.clone(), u32_ty()]);
    let local_decls = vec![union_ty];
    let mut state = StatementEvalState::from_local_decls(local_decls, PW);

    // 1. Active field 0 has wrong head constructor (`MirValue::Bool(true)` instead of `(u32, u8)`).
    let bad_head_union = MirValue::Adt {
        def_path: "U".into(),
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![MirValue::Bool(true)],
    };
    state.slots[0] = LocalSlotState::Init(bad_head_union.clone());
    let f0 = proj(0, vec![field(0, pair_ty.clone())]);
    let f1 = proj(0, vec![field(1, u32_ty())]);
    assert!(matches!(
        state.read_place(&f1),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.write_place(&f1, &u32_ty(), u32v(42)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(state.get_init(Local(0)), Some(&bad_head_union));

    // 2. Active field 0 has matching outer `MirValue::Tuple` length (2) but a malformed inner
    // element `(Bool(true), 7u8)` instead of `(u32, u8)`. Reading inactive field 1 or replacing
    // field 0 or field 1 must still reject the malformed active field with `TypeMismatch`.
    let bad_nested_union = MirValue::Adt {
        def_path: "U".into(),
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![MirValue::Tuple(vec![MirValue::Bool(true), u8v(7)])],
    };
    state.slots[0] = LocalSlotState::Init(bad_nested_union.clone());
    assert!(matches!(
        state.read_place(&f1),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.write_place(&f1, &u32_ty(), u32v(42)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.write_place(&f0, &pair_ty, MirValue::Tuple(vec![u32v(1), u8v(2)])),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(state.get_init(Local(0)), Some(&bad_nested_union));
}
