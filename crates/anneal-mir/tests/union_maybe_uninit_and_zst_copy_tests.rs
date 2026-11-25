// Copyright 2026 The Fuchsia Authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0>, the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, or the BSD-2-Clause
// license <LICENSE-BSD or https://opensource.org/license/bsd-2-clause>, at your
// option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Episode 1 (`ep1-anneal-mir-union-offset0-and-zst-copy`) regression tests for unions,
//! `MaybeUninit<T>`, and zero-sized union fields in the value-tree evaluator:
//! - an inhabited zero-sized union field other than the active one occupies no bytes of the
//!   union's storage, so reading it (or a place inside it, with every step still checked)
//!   yields its unique value, while uninhabited and non-zero-sized inactive fields keep failing
//!   with `InactiveUnionField` (Rust reference, "Unions": a union access interprets the
//!   storage at the field's type; `Trusted.MirSemantics`' `readProjectedValueUnionAware`
//!   decodes a zero-sized field from zero bytes);
//! - writing an inhabited zero-sized union field stores no bytes, so an initialized union
//!   keeps its active field (`u.zst = ()` never makes `u.val` unreadable);
//! - uninitialized bytes copied over a whole union (or over every byte that its inhabited
//!   fields can read) leave a union without initialized bytes, which the value tree holds as
//!   that union with its inhabited zero-sized field active (`MaybeUninit::uninit()`), also as
//!   an element of `[MaybeUninit<T>; N]`; partially initialized or partially overwritten union
//!   storage keeps failing closed (`UnsupportedMemoryAccess`);
//! - typed copies of padded `#[repr(C)]` unions with `[(); N]` fields (`kani#5176`) work.

use std::sync::Arc;

use anneal_mir::ir::{
    AdtDef, AdtRepr, AggregateKind, CastKind, Constant, IntTy, IntrinsicOp, Local, Mutability,
    Operand, Place, PointerValue, ProjectionElem, PtrWidth, Rvalue, Statement, Ty, UintTy,
    VariantDef,
};
use anneal_mir::lower::{
    CastLowerError, IntrinsicOutcome, LocalSlotState, MirValue, RvalueEvalError, RvalueLowerError,
    StatementEvalState, eval_intrinsic_call, eval_lowered_statement, lower_rvalue, lower_statement,
};

const PW: PtrWidth = PtrWidth::Bits64;
const PWS: [PtrWidth; 2] = [PtrWidth::Bits32, PtrWidth::Bits64];
const UNINIT_UNION_COPY: &str =
    "copy of uninitialized bytes into a union field needs a byte-level memory model";

// ---------------------------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------------------------

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

fn unit() -> Ty {
    Ty::unit()
}

fn arr(elem: Ty, len: usize) -> Ty {
    Ty::Array(Box::new(elem), len)
}

fn raw(pointee: Ty, m: Mutability) -> Ty {
    Ty::RawPtr(Box::new(pointee), m)
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

fn units(n: usize) -> MirValue {
    MirValue::Array {
        elements: vec![MirValue::Unit; n],
        elem_ty: unit(),
    }
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

fn cidx(offset: u64, min_length: u64) -> ProjectionElem {
    ProjectionElem::ConstantIndex {
        offset,
        min_length,
        from_end: false,
    }
}

fn deref(idx: usize) -> Place {
    proj(idx, vec![ProjectionElem::Deref])
}

fn adt(def: AdtDef) -> (Arc<AdtDef>, Ty) {
    let def = Arc::new(def);
    let ty = Ty::Adt(def.clone());
    (def, ty)
}

fn run(stmt: Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = lower_statement(&stmt, &state.local_decls, state.ptr_width)
        .expect("statement must lower cleanly");
    eval_lowered_statement(&lowered, state)
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign(place, rvalue)
}

fn copy_of(place: Place) -> Rvalue {
    Rvalue::Use(Operand::Copy(place))
}

fn unit_rvalue() -> Rvalue {
    Rvalue::Use(Operand::Constant(Constant::Unit))
}

fn int(bits: u128, ty: Ty) -> Rvalue {
    Rvalue::Use(Operand::Constant(Constant::Int(bits, ty)))
}

fn union_agg(def: &Arc<AdtDef>, field_idx: usize, operand: Operand) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt {
            def_path: def.def_path.clone(),
            variant_idx: 0,
            active_field: Some(field_idx),
            adt_def: Some(def.clone()),
        },
        vec![operand],
    )
}

fn raw_mut(place: Place) -> Rvalue {
    Rvalue::RawPtr(Mutability::Mut, place)
}

fn raw_const(place: Place) -> Rvalue {
    Rvalue::RawPtr(Mutability::Not, place)
}

fn ptr_cast(src: usize, target_ty: Ty) -> Rvalue {
    Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(local(src)), target_ty)
}

fn copy_nonoverlapping(src: usize, dst: usize, count: u128) -> Statement {
    Statement::CopyNonOverlapping {
        src: Operand::Copy(local(src)),
        dst: Operand::Copy(local(dst)),
        count: Operand::Constant(Constant::Int(count, usize_ty())),
    }
}

/// `core::mem::ManuallyDrop<T>` (`#[repr(transparent)] struct ManuallyDrop<T> { value: T }`).
fn manually_drop(t: Ty) -> (Arc<AdtDef>, Ty) {
    adt(AdtDef::new_struct("core::mem::ManuallyDrop", vec![t]).with_repr(AdtRepr::transparent()))
}

/// `core::mem::MaybeUninit<T>` (`#[repr(transparent)] union MaybeUninit<T> { uninit: (),
/// value: ManuallyDrop<T> }`), with its `ManuallyDrop<T>` definition.
struct MaybeUninitTy {
    def: Arc<AdtDef>,
    ty: Ty,
    md_def: Arc<AdtDef>,
    md_ty: Ty,
    t: Ty,
}

impl MaybeUninitTy {
    fn new(t: Ty) -> Self {
        let (md_def, md_ty) = manually_drop(t.clone());
        let (def, ty) = adt(AdtDef::new_union(
            "core::mem::MaybeUninit",
            vec![unit(), md_ty.clone()],
        )
        .with_repr(AdtRepr::transparent()));
        MaybeUninitTy {
            def,
            ty,
            md_def,
            md_ty,
            t,
        }
    }

    /// `MaybeUninit::new(v)`.
    fn init(&self, v: MirValue) -> MirValue {
        MirValue::union_value(&self.def, 1, MirValue::adt(&self.md_def, 0, vec![v]))
    }

    /// `MaybeUninit::uninit()`: no initialized byte (its `uninit: ()` field active).
    fn uninit(&self) -> MirValue {
        MirValue::union_value(&self.def, 0, MirValue::Unit)
    }

    /// `[uninit: ()]` field projection.
    fn uninit_field(&self) -> ProjectionElem {
        field(0, unit())
    }

    /// `.value.value` (the `T` inside), as `mu.as_mut_ptr()` designates it.
    fn inner(&self) -> Vec<ProjectionElem> {
        vec![field(1, self.md_ty.clone()), field(0, self.t.clone())]
    }
}

/// A union exercising every kind of field: `val: u32` (`0`), inhabited zero-sized fields
/// (`1..=9`), uninhabited zero-sized fields (`10..=13`), and non-zero-sized ones (`14`, `15`).
struct ShapesUnion {
    def: Arc<AdtDef>,
    ty: Ty,
    fields: Vec<Ty>,
    phantom: Arc<AdtDef>,
    zst_struct: Arc<AdtDef>,
    zst_enum: Arc<AdtDef>,
    absent_enum: Arc<AdtDef>,
}

const VAL: usize = 0;
const UNIT: usize = 1;
const ZST_ARR: usize = 2;
const EMPTY_U32: usize = 3;
const NEVER_0: usize = 4;
const PHANTOM: usize = 5;
const NESTED: usize = 6;
const ZST_STRUCT: usize = 7;
const ZST_ENUM: usize = 8;
const ABSENT_ENUM: usize = 9;
const NEVER: usize = 10;
const VOID: usize = 11;
const NEVER_1: usize = 12;
const NEVER_PAIR: usize = 13;
const SMALL: usize = 14;
const PAIR: usize = 15;

impl ShapesUnion {
    fn new() -> Self {
        let (phantom, phantom_ty) = adt(AdtDef::new_struct("core::marker::PhantomData", vec![]));
        let (zst_struct, zst_struct_ty) =
            adt(AdtDef::new_struct("Z", vec![unit(), arr(unit(), 1)]));
        // `enum E { A }`: tagless and univariant, so zero-sized.
        let (zst_enum, zst_enum_ty) = adt(AdtDef::new_enum(
            "E",
            None,
            vec![VariantDef::new("A", vec![])],
        ));
        // `enum F { A(()), B(!) }`: `B` is absent, so `F` is laid out like `A`'s fields.
        let (absent_enum, absent_enum_ty) = adt(AdtDef::new_enum(
            "F",
            None,
            vec![
                VariantDef::new("A", vec![unit()]),
                VariantDef::new("B", vec![Ty::Never]),
            ],
        ));
        let (_, void_ty) = adt(AdtDef::new_enum("Void", None, vec![]));
        let fields = vec![
            u32_ty(),
            unit(),
            arr(unit(), 3),
            arr(u32_ty(), 0),
            arr(Ty::Never, 0),
            phantom_ty,
            Ty::Tuple(vec![unit(), arr(unit(), 2)]),
            zst_struct_ty,
            zst_enum_ty,
            absent_enum_ty,
            Ty::Never,
            void_ty,
            arr(Ty::Never, 1),
            Ty::Tuple(vec![unit(), Ty::Never]),
            u8_ty(),
            Ty::Tuple(vec![u16_ty(), u16_ty()]),
        ];
        let (def, ty) = adt(AdtDef::new_union("Shapes", fields.clone()));
        ShapesUnion {
            def,
            ty,
            fields,
            phantom,
            zst_struct,
            zst_enum,
            absent_enum,
        }
    }

    fn f(&self, idx: usize) -> ProjectionElem {
        field(idx, self.fields[idx].clone())
    }

    fn with_val(&self, v: u128) -> MirValue {
        MirValue::union_value(&self.def, VAL, u32v(v))
    }

    /// The unique value of every inhabited zero-sized field.
    fn zst_values(&self) -> Vec<(usize, MirValue)> {
        vec![
            (UNIT, MirValue::Unit),
            (ZST_ARR, units(3)),
            (
                EMPTY_U32,
                MirValue::Array {
                    elements: vec![],
                    elem_ty: u32_ty(),
                },
            ),
            (
                NEVER_0,
                MirValue::Array {
                    elements: vec![],
                    elem_ty: Ty::Never,
                },
            ),
            (PHANTOM, MirValue::adt(&self.phantom, 0, vec![])),
            (NESTED, MirValue::Tuple(vec![MirValue::Unit, units(2)])),
            (
                ZST_STRUCT,
                MirValue::adt(&self.zst_struct, 0, vec![MirValue::Unit, units(1)]),
            ),
            (ZST_ENUM, MirValue::adt(&self.zst_enum, 0, vec![])),
            (
                ABSENT_ENUM,
                MirValue::adt(&self.absent_enum, 0, vec![MirValue::Unit]),
            ),
        ]
    }
}

// ---------------------------------------------------------------------------------------------
// Goal 2: reading inhabited zero-sized union fields other than the active one
// ---------------------------------------------------------------------------------------------

#[test]
fn maybe_uninit_new_reads_its_inactive_uninit_field() {
    for t in [u32_ty(), u8_ty(), Ty::Bool, raw(u8_ty(), Mutability::Not)] {
        let mu = MaybeUninitTy::new(t.clone());
        let decls = vec![mu.ty.clone(), unit(), t.clone()];
        let mut state = StatementEvalState::from_local_decls(decls, PW);
        let v = match &t {
            Ty::Bool => MirValue::Bool(true),
            Ty::RawPtr(..) => MirValue::ptr(PointerValue::with_provenance(0x2000, 1, 1), t.clone()),
            Ty::Uint(UintTy::U8) => u8v(0xAB),
            _ => u32v(0xDEAD_BEEF),
        };
        state.slots[0] = LocalSlotState::Init(mu.init(v.clone()));
        // `mu.uninit` (`()`) is not the active field, but it occupies no bytes.
        let uninit = proj(0, vec![mu.uninit_field()]);
        assert_eq!(state.read_place(&uninit), Ok(MirValue::Unit));
        run(assign(local(1), copy_of(uninit)), &mut state).unwrap();
        assert_eq!(state.get_init(Local(1)), Some(&MirValue::Unit));
        // The active field and the whole union are untouched.
        run(assign(local(2), copy_of(proj(0, mu.inner()))), &mut state).unwrap();
        assert_eq!(state.get_init(Local(2)), Some(&v));
        assert_eq!(state.get_init(Local(0)), Some(&mu.init(v)));
    }
}

#[test]
fn inactive_inhabited_zst_union_fields_of_every_shape_read_their_unique_value() {
    let u = ShapesUnion::new();
    for pw in PWS {
        let mut state = StatementEvalState::from_local_decls(vec![u.ty.clone()], pw);
        state.slots[0] = LocalSlotState::Init(MirValue::union_value(
            &u.def,
            VAL,
            MirValue::unsigned(42, UintTy::U32, pw),
        ));
        for (idx, expected) in u.zst_values() {
            assert_eq!(
                state.read_place(&proj(0, vec![u.f(idx)])),
                Ok(expected),
                "field {idx} on {pw:?}"
            );
        }
        // Also while another zero-sized field (or a non-zero-sized one) is active.
        state.slots[0] = LocalSlotState::Init(MirValue::union_value(&u.def, UNIT, MirValue::Unit));
        assert_eq!(state.read_place(&proj(0, vec![u.f(ZST_ARR)])), Ok(units(3)));
        state.slots[0] = LocalSlotState::Init(MirValue::union_value(
            &u.def,
            PAIR,
            MirValue::Tuple(vec![u16v(1), u16v(2)]),
        ));
        assert_eq!(
            state.read_place(&proj(0, vec![u.f(UNIT)])),
            Ok(MirValue::Unit)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![u.f(PAIR), field(1, u16_ty())])),
            Ok(u16v(2))
        );
    }
}

#[test]
fn nested_projections_inside_inactive_zst_union_fields_are_checked() {
    let u = ShapesUnion::new();
    let decls = vec![u.ty.clone(), usize_ty(), usize_ty(), Ty::Int(IntTy::Isize)];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(7));
    // `u.zst_arr[_1]`: in bounds reads `()`, out of bounds is still undefined behavior.
    let indexed = proj(0, vec![u.f(ZST_ARR), ProjectionElem::Index(Local(1))]);
    state.slots[1] = LocalSlotState::Init(usizev(2));
    assert_eq!(state.read_place(&indexed), Ok(MirValue::Unit));
    state.slots[1] = LocalSlotState::Init(usizev(3));
    assert_eq!(
        state.read_place(&indexed),
        Err(RvalueEvalError::IndexOutOfBounds { index: 3, len: 3 })
    );
    // Constant indices and subslices.
    assert_eq!(
        state.read_place(&proj(0, vec![u.f(ZST_ARR), cidx(1, 3)])),
        Ok(MirValue::Unit)
    );
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![
                u.f(ZST_ARR),
                ProjectionElem::ConstantIndex {
                    offset: 1,
                    min_length: 1,
                    from_end: true,
                },
            ],
        )),
        Ok(MirValue::Unit)
    );
    assert!(matches!(
        state.read_place(&proj(0, vec![u.f(ZST_ARR), cidx(3, 4)])),
        Err(RvalueEvalError::IndexOutOfBounds { .. })
    ));
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![
                u.f(ZST_ARR),
                ProjectionElem::Subslice {
                    from: 1,
                    to: 3,
                    from_end: false,
                },
            ],
        )),
        Ok(units(2))
    );
    // Tuple / struct fields inside the zero-sized field.
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![u.f(NESTED), field(1, arr(unit(), 2)), cidx(1, 2)]
        )),
        Ok(MirValue::Unit)
    );
    assert_eq!(
        state.read_place(&proj(0, vec![u.f(ZST_STRUCT), field(1, arr(unit(), 1))])),
        Ok(units(1))
    );
    // `(u.absent_enum as A).0` reads `()`; `B` is absent, so its downcast is inactive.
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![
                u.f(ABSENT_ENUM),
                ProjectionElem::Downcast(0),
                field(0, unit())
            ],
        )),
        Ok(MirValue::Unit)
    );
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![
                u.f(ABSENT_ENUM),
                ProjectionElem::Downcast(1),
                field(0, Ty::Never)
            ],
        )),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0
        })
    );
    // A field type that is not the declared one is a static type error.
    assert!(matches!(
        state.read_place(&proj(0, vec![field(ZST_ARR, arr(unit(), 4))])),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    // `Len` and `Discriminant` of zero-sized places inside an inactive union field.
    run(
        assign(local(2), Rvalue::Len(proj(0, vec![u.f(ZST_ARR)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(2)), Some(&usizev(3)));
    run(
        assign(local(3), Rvalue::Discriminant(proj(0, vec![u.f(ZST_ENUM)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::signed(0, IntTy::Isize, PW))
    );
    // The union is never modified by these reads.
    assert_eq!(state.get_init(Local(0)), Some(&u.with_val(7)));
}

#[test]
fn uninhabited_and_non_zero_sized_inactive_union_fields_still_fail_closed() {
    let u = ShapesUnion::new();
    let mut state = StatementEvalState::from_local_decls(vec![u.ty.clone()], PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(7));
    // `!`, `enum Void {}`, `[!; 1]`, and `((), !)` are zero-sized but uninhabited: reading them
    // is undefined behavior; `u8` and `(u16, u16)` read bytes of the active `u32`.
    for idx in [NEVER, VOID, NEVER_1, NEVER_PAIR, SMALL, PAIR] {
        assert_eq!(
            state.read_place(&proj(0, vec![u.f(idx)])),
            Err(RvalueEvalError::InactiveUnionField {
                active_field: VAL,
                requested_field: idx,
            }),
            "field {idx}"
        );
    }
    assert_eq!(
        state.read_place(&proj(0, vec![u.f(NEVER_PAIR), field(0, unit())])),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: VAL,
            requested_field: NEVER_PAIR,
        })
    );
    assert_eq!(
        state.read_place(&proj(0, vec![u.f(PAIR), field(0, u16_ty())])),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: VAL,
            requested_field: PAIR,
        })
    );
    // While a zero-sized field is active, non-zero-sized fields hold no initialized bytes.
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&u.def, UNIT, MirValue::Unit));
    assert_eq!(
        state.read_place(&proj(0, vec![u.f(VAL)])),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: UNIT,
            requested_field: VAL,
        })
    );
}

#[test]
fn zst_field_reads_of_an_uninitialized_union_local_keep_the_uninit_local_semantics() {
    // `Trusted.MirSemantics`' `evalPlaceRead` faults on any projected read of an `.uninit`
    // local (`Places.lean`, `| .some .uninit => .ub`), and the value tree treats every
    // projected read of an `Uninit` local alike; borrow-checked Rust never reads a field of a
    // never-initialized local. (A union whose bytes were *copied* uninitialized is initialized
    // in the value tree; see `copy_nonoverlapping_whole_maybe_uninit_values`.)
    let mu = MaybeUninitTy::new(u32_ty());
    let state = StatementEvalState::from_local_decls(vec![mu.ty.clone()], PW);
    assert_eq!(
        state.read_place(&proj(0, vec![mu.uninit_field()])),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
}

#[test]
fn zst_union_field_reads_through_structs_shells_and_arrays() {
    let mu = MaybeUninitTy::new(u32_ty());
    let (s_def, s_ty) =
        adt(AdtDef::new_struct("S", vec![u8_ty(), mu.ty.clone()]).with_repr(AdtRepr::c()));
    let decls = vec![s_ty.clone(), arr(mu.ty.clone(), 2)];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::adt(&s_def, 0, vec![u8v(1), mu.init(u32v(9))]));
    let in_struct = proj(0, vec![field(1, mu.ty.clone()), mu.uninit_field()]);
    assert_eq!(state.read_place(&in_struct), Ok(MirValue::Unit));
    // With a sibling field deinitialized, `S` is a partially initialized shell.
    run(
        Statement::Deinit(proj(0, vec![field(0, u8_ty())])),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(state.read_place(&in_struct), Ok(MirValue::Unit));
    let mut inner = vec![field(1, mu.ty.clone())];
    inner.extend(mu.inner());
    assert_eq!(state.read_place(&proj(0, inner)), Ok(u32v(9)));
    // Elements of `[MaybeUninit<u32>; 2]`.
    state.slots[1] = LocalSlotState::Init(MirValue::Array {
        elements: vec![mu.init(u32v(1)), mu.init(u32v(2))],
        elem_ty: mu.ty.clone(),
    });
    assert_eq!(
        state.read_place(&proj(1, vec![cidx(1, 2), mu.uninit_field()])),
        Ok(MirValue::Unit)
    );
}

#[test]
fn pointers_into_inactive_zst_union_fields_resolve_and_read() {
    let u = ShapesUnion::new();
    let decls = vec![
        u.ty.clone(),
        raw(unit(), Mutability::Not),
        raw(arr(unit(), 3), Mutability::Not),
        raw(unit(), Mutability::Not),
        unit(),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(42));
    run(
        assign(local(1), raw_const(proj(0, vec![u.f(UNIT)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.read_place(&deref(1)), Ok(MirValue::Unit));
    run(assign(local(4), copy_of(deref(1))), &mut state).unwrap();
    assert_eq!(state.get_init(Local(4)), Some(&MirValue::Unit));
    run(
        assign(local(2), raw_const(proj(0, vec![u.f(ZST_ARR)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.read_place(&deref(2)), Ok(units(3)));
    run(
        assign(local(3), raw_const(proj(0, vec![u.f(ZST_ARR), cidx(2, 3)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.read_place(&deref(3)), Ok(MirValue::Unit));
    // A write through such a pointer stores nothing: the active field is untouched.
    let decls = vec![
        u.ty.clone(),
        raw(unit(), Mutability::Mut),
        raw(unit(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(42));
    run(
        assign(local(1), raw_mut(proj(0, vec![u.f(UNIT)]))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(1), unit_rvalue()), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&u.with_val(42)));
    run(
        assign(local(2), raw_mut(proj(0, vec![u.f(ZST_ARR), cidx(1, 3)]))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), unit_rvalue()), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&u.with_val(42)));
}

#[test]
fn pointer_provenance_survives_zst_reads_writes_and_whole_union_copies() {
    let ptr_ty = raw(u8_ty(), Mutability::Not);
    let (p_def, p_ty) = adt(AdtDef::new_union("P", vec![ptr_ty.clone(), unit()]));
    let decls = vec![p_ty.clone(), p_ty.clone(), unit(), ptr_ty.clone()];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let ptr = MirValue::ptr(PointerValue::with_provenance(0x5000, 9, 3), ptr_ty.clone());
    let with_ptr = MirValue::union_value(&p_def, 0, ptr.clone());
    state.slots[0] = LocalSlotState::Init(with_ptr.clone());
    run(
        assign(local(2), copy_of(proj(0, vec![field(1, unit())]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(2)), Some(&MirValue::Unit));
    run(
        assign(proj(0, vec![field(1, unit())]), unit_rvalue()),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&with_ptr));
    run(assign(local(1), copy_of(local(0))), &mut state).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&with_ptr));
    run(
        assign(local(3), copy_of(proj(1, vec![field(0, ptr_ty)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(3)), Some(&ptr));
}

// ---------------------------------------------------------------------------------------------
// Goal 3: writing zero-sized union fields stores no bytes
// ---------------------------------------------------------------------------------------------

#[test]
fn zst_field_writes_leave_an_initialized_union_unchanged() {
    let mu = MaybeUninitTy::new(u32_ty());
    let decls = vec![mu.ty.clone(), u32_ty()];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(mu.init(u32v(5)));
    // `mu.uninit = ()` writes no bytes: `mu.value` stays initialized (in Miri and in
    // `Trusted.MirSemantics`, which only sets the zero-sized field's `.unit` slot).
    run(
        assign(proj(0, vec![mu.uninit_field()]), unit_rvalue()),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(5))));
    run(assign(local(1), copy_of(proj(0, mu.inner()))), &mut state).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&u32v(5)));

    let u = ShapesUnion::new();
    let mut state = StatementEvalState::from_local_decls(vec![u.ty.clone()], PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(7));
    for (idx, value) in u.zst_values() {
        state
            .write_place(&proj(0, vec![u.f(idx)]), &u.fields[idx], value)
            .unwrap();
        assert_eq!(
            state.get_init(Local(0)),
            Some(&u.with_val(7)),
            "field {idx}"
        );
    }
    // Nested writes inside an inactive zero-sized field also store nothing, with every step
    // still checked.
    run(
        assign(proj(0, vec![u.f(ZST_ARR), cidx(1, 3)]), unit_rvalue()),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            proj(
                0,
                vec![
                    u.f(ABSENT_ENUM),
                    ProjectionElem::Downcast(0),
                    field(0, unit()),
                ],
            ),
            unit_rvalue(),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&u.with_val(7)));
    assert!(matches!(
        state.write_place(
            &proj(0, vec![u.f(ZST_ARR), cidx(3, 4)]),
            &unit(),
            MirValue::Unit
        ),
        Err(RvalueEvalError::IndexOutOfBounds { .. })
    ));
    assert_eq!(
        state.write_place(
            &proj(
                0,
                vec![
                    u.f(ABSENT_ENUM),
                    ProjectionElem::Downcast(1),
                    field(0, Ty::Never)
                ]
            ),
            &Ty::Never,
            MirValue::Unit
        ),
        Err(RvalueEvalError::TypeMismatch(
            "assigned value runtime type does not match destination place type"
        ))
    );
    assert_eq!(state.get_init(Local(0)), Some(&u.with_val(7)));
    // A whole write of a non-zero-sized field still switches the active field, and a nested
    // write into an inactive non-zero-sized field stays unsupported.
    run(
        assign(proj(0, vec![u.f(SMALL)]), int(3, u8_ty())),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&u.def, SMALL, u8v(3)))
    );
    let nested = proj(0, vec![u.f(PAIR), field(0, u16_ty())]);
    assert_eq!(
        run(assign(nested.clone(), int(1, u16_ty())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(nested))
    );
}

#[test]
fn zst_field_writes_on_an_uninitialized_union_activate_that_field() {
    let u = ShapesUnion::new();
    let mut state = StatementEvalState::from_local_decls(vec![u.ty.clone()], PW);
    run(assign(proj(0, vec![u.f(UNIT)]), unit_rvalue()), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&u.def, UNIT, MirValue::Unit))
    );
    // A nested write inside a zero-sized field of an uninitialized union holds that field's
    // unique value.
    let mut state = StatementEvalState::from_local_decls(vec![u.ty.clone()], PW);
    run(
        assign(proj(0, vec![u.f(ZST_ARR), cidx(2, 3)]), unit_rvalue()),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&u.def, ZST_ARR, units(3)))
    );
    // A nested write into a non-zero-sized field of an uninitialized union stays unsupported.
    let mut state = StatementEvalState::from_local_decls(vec![u.ty.clone()], PW);
    let nested = proj(0, vec![u.f(PAIR), field(0, u16_ty())]);
    assert_eq!(
        run(assign(nested.clone(), int(1, u16_ty())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(nested))
    );
    assert_eq!(state.get_local(Local(0)), Some(&LocalSlotState::Uninit));
}

// ---------------------------------------------------------------------------------------------
// Goal 3: whole-union `copy_nonoverlapping` of `MaybeUninit<T>` values
// ---------------------------------------------------------------------------------------------

/// `_0, _1: MaybeUninit<u32>`, `_2: *const MaybeUninit<u32> = &raw const _0`,
/// `_3: *mut MaybeUninit<u32> = &raw mut _1`, `_4: MaybeUninit<u32>`, `_5: u32`.
fn mu_copy_state(mu: &MaybeUninitTy) -> StatementEvalState {
    let decls = vec![
        mu.ty.clone(),
        mu.ty.clone(),
        raw(mu.ty.clone(), Mutability::Not),
        raw(mu.ty.clone(), Mutability::Mut),
        mu.ty.clone(),
        u32_ty(),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    run(assign(local(2), raw_const(local(0))), &mut state).unwrap();
    run(assign(local(3), raw_mut(local(1))), &mut state).unwrap();
    state
}

#[test]
fn copy_nonoverlapping_whole_maybe_uninit_values() {
    let mu = MaybeUninitTy::new(u32_ty());
    // Initialized over initialized.
    let mut state = mu_copy_state(&mu);
    state.slots[0] = LocalSlotState::Init(mu.init(u32v(7)));
    state.slots[1] = LocalSlotState::Init(mu.init(u32v(1)));
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&mu.init(u32v(7))));
    // `MaybeUninit::uninit()` over initialized.
    state.slots[0] = LocalSlotState::Init(mu.uninit());
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&mu.uninit()));
    // Uninitialized bytes over an initialized union: a union without initialized bytes, which
    // can still be copied as a whole (it was `Uninit`, so `_4 = _1` was undefined behavior).
    let mut state = mu_copy_state(&mu);
    state.slots[1] = LocalSlotState::Init(mu.init(u32v(1)));
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&mu.uninit()));
    run(assign(local(4), copy_of(local(1))), &mut state).unwrap();
    assert_eq!(state.get_init(Local(4)), Some(&mu.uninit()));
    assert_eq!(
        state.read_place(&proj(1, vec![mu.uninit_field()])),
        Ok(MirValue::Unit)
    );
    assert_eq!(
        state.read_place(&proj(1, mu.inner())),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 0,
            requested_field: 1,
        })
    );
    // Uninitialized bytes over uninitialized bytes change nothing.
    let mut state = mu_copy_state(&mu);
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));
}

#[test]
fn copy_nonoverlapping_into_a_struct_wrapping_maybe_uninit() {
    let mu = MaybeUninitTy::new(u32_ty());
    let (w_def, w_ty) =
        adt(AdtDef::new_struct("Wrapper", vec![mu.ty.clone(), u8_ty()]).with_repr(AdtRepr::c()));
    let decls = vec![
        mu.ty.clone(),
        w_ty.clone(),
        raw(mu.ty.clone(), Mutability::Not),
        raw(mu.ty.clone(), Mutability::Mut),
    ];
    let wrapped = |buf: MirValue| MirValue::adt(&w_def, 0, vec![buf, u8v(3)]);
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(mu.init(u32v(11)));
    state.slots[1] = LocalSlotState::Init(wrapped(mu.init(u32v(1))));
    run(assign(local(2), raw_const(local(0))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(proj(1, vec![field(0, mu.ty.clone())]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&wrapped(mu.init(u32v(11)))));
    // An uninitialized source leaves `w.buf` a union without initialized bytes; `w` stays a
    // whole initialized value (no partial shell needed).
    state.slots[0] = LocalSlotState::Uninit;
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&wrapped(mu.uninit())));
}

#[test]
fn copy_nonoverlapping_maybe_uninit_array_elements_and_windows() {
    let mu = MaybeUninitTy::new(u32_ty());
    let arr_ty = arr(mu.ty.clone(), 4);
    let decls = vec![
        arr_ty.clone(),
        arr_ty.clone(),
        mu.ty.clone(),
        raw(mu.ty.clone(), Mutability::Not),
        raw(mu.ty.clone(), Mutability::Mut),
    ];
    let elems = |vals: [Option<u128>; 4]| MirValue::Array {
        elements: vals
            .iter()
            .map(|v| v.map_or_else(|| mu.uninit(), |v| mu.init(u32v(v))))
            .collect(),
        elem_ty: mu.ty.clone(),
    };
    let fresh = || {
        let mut state = StatementEvalState::from_local_decls(decls.clone(), PW);
        state.slots[0] = LocalSlotState::Init(elems([Some(10), Some(11), Some(12), Some(13)]));
        state
    };
    // One element from an uninitialized `MaybeUninit<u32>` (an array has no per-element
    // `Uninit` slot, but its union element can hold no initialized bytes).
    let mut state = fresh();
    run(assign(local(3), raw_const(local(2))), &mut state).unwrap();
    run(
        assign(local(4), raw_mut(proj(0, vec![cidx(2, 4)]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(3, 4, 1), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&elems([Some(10), Some(11), None, Some(13)]))
    );
    // A window of two elements from an uninitialized `[MaybeUninit<u32>; 4]`.
    let mut state = fresh();
    run(
        assign(local(3), raw_const(proj(1, vec![cidx(0, 4)]))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(4), raw_mut(proj(0, vec![cidx(1, 4)]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(3, 4, 2), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&elems([Some(10), None, None, Some(13)]))
    );
    // The whole array from an uninitialized one.
    run(
        assign(local(4), raw_mut(proj(0, vec![cidx(0, 4)]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(3, 4, 4), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&elems([None, None, None, None]))
    );
    // Initialized windows are copied as is.
    state.slots[1] = LocalSlotState::Init(elems([Some(1), None, Some(3), Some(4)]));
    run(copy_nonoverlapping(3, 4, 4), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&elems([Some(1), None, Some(3), Some(4)]))
    );
    run(
        assign(local(3), raw_const(proj(1, vec![cidx(1, 4)]))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(4), raw_mut(proj(0, vec![cidx(2, 4)]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(3, 4, 2), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&elems([Some(1), None, None, Some(3)]))
    );
    // Uninitialized elements over an uninitialized destination array change nothing.
    let mut state = StatementEvalState::from_local_decls(decls.clone(), PW);
    run(assign(local(3), raw_const(local(2))), &mut state).unwrap();
    run(
        assign(local(4), raw_mut(proj(0, vec![cidx(2, 4)]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(3, 4, 1), &mut state).unwrap();
    assert_eq!(state.get_local(Local(0)), Some(&LocalSlotState::Uninit));
}

#[test]
fn copy_nonoverlapping_uninit_bytes_covering_every_readable_union_byte() {
    // `copy_nonoverlapping::<u32>(uninit, mu.as_mut_ptr(), 1)` over `MaybeUninit::new(5)`.
    let mu = MaybeUninitTy::new(u32_ty());
    let decls = vec![
        mu.ty.clone(),
        u32_ty(),
        raw(u32_ty(), Mutability::Not),
        raw(mu.ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(mu.init(u32v(5)));
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(assign(local(3), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(4), ptr_cast(3, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 4, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));

    // `#[repr(C)] union P { a: u8, z: [u32; 0] }` (4 bytes, 3 of them padding): `a` is the
    // largest readable field, so uninitialized bytes over `a` leave no initialized byte.
    let (p_def, p_ty) =
        adt(AdtDef::new_union("P", vec![u8_ty(), arr(u32_ty(), 0)]).with_repr(AdtRepr::c()));
    let decls = vec![
        p_ty.clone(),
        u8_ty(),
        raw(u8_ty(), Mutability::Not),
        raw(u8_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&p_def, 0, u8v(7)));
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(proj(0, vec![field(0, u8_ty())]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(
            &p_def,
            1,
            MirValue::Array {
                elements: vec![],
                elem_ty: u32_ty(),
            }
        ))
    );

    // `union W { z: (), a: u8, b: u32 }` with `b` active: uninitialized bytes over `a` leave
    // `b`'s other three bytes initialized, which the value tree cannot hold.
    let (w_def, w_ty) = adt(AdtDef::new_union("W", vec![unit(), u8_ty(), u32_ty()]));
    let decls = vec![
        w_ty.clone(),
        u8_ty(),
        raw(u8_ty(), Mutability::Not),
        raw(u8_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = MirValue::union_value(&w_def, 2, u32v(0xAABB_CCDD));
    state.slots[0] = LocalSlotState::Init(before.clone());
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(proj(0, vec![field(1, u8_ty())]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        run(copy_nonoverlapping(2, 3, 1), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY))
    );
    assert_eq!(state.get_init(Local(0)), Some(&before));

    // `union Q { a: u32, b: [u8; 4] }` has no zero-sized field to hold "no initialized byte".
    let (q_def, q_ty) = adt(AdtDef::new_union("Q", vec![u32_ty(), arr(u8_ty(), 4)]));
    let decls = vec![
        q_ty.clone(),
        u32_ty(),
        raw(u32_ty(), Mutability::Not),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = MirValue::union_value(&q_def, 0, u32v(9));
    state.slots[0] = LocalSlotState::Init(before.clone());
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(proj(0, vec![field(0, u32_ty())]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        run(copy_nonoverlapping(2, 3, 1), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY))
    );
    assert_eq!(state.get_init(Local(0)), Some(&before));
}

#[test]
fn copy_nonoverlapping_partial_or_zero_sized_values_into_union_fields() {
    // A partially initialized `(u32, u32)` copied into `MaybeUninit<(u32, u32)>`'s value
    // would leave the union's bytes partially initialized: unsupported, nothing written.
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let mu = MaybeUninitTy::new(pair.clone());
    let decls = vec![
        mu.ty.clone(),
        pair.clone(),
        raw(pair.clone(), Mutability::Not),
        raw(pair.clone(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = mu.init(MirValue::Tuple(vec![u32v(1), u32v(2)]));
    state.slots[0] = LocalSlotState::Init(before.clone());
    state.slots[1] = LocalSlotState::Init(MirValue::Tuple(vec![u32v(8), u32v(9)]));
    run(
        Statement::Deinit(proj(1, vec![field(1, u32_ty())])),
        &mut state,
    )
    .unwrap();
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(assign(local(3), raw_mut(proj(0, mu.inner()))), &mut state).unwrap();
    assert_eq!(
        run(copy_nonoverlapping(2, 3, 1), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY))
    );
    assert_eq!(state.get_init(Local(0)), Some(&before));

    // Zero-sized values (initialized, uninitialized, or a partially initialized zero-sized
    // pair) copied into a zero-sized union field store no bytes.
    let zpair = Ty::Tuple(vec![unit(), unit()]);
    let (z_def, z_ty) = adt(AdtDef::new_union(
        "Z",
        vec![u32_ty(), unit(), zpair.clone()],
    ));
    let decls = vec![
        z_ty.clone(),
        unit(),
        zpair.clone(),
        raw(unit(), Mutability::Not),
        raw(unit(), Mutability::Mut),
        raw(zpair.clone(), Mutability::Not),
        raw(zpair.clone(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = MirValue::union_value(&z_def, 0, u32v(77));
    state.slots[0] = LocalSlotState::Init(before.clone());
    run(assign(local(3), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(4), raw_mut(proj(0, vec![field(1, unit())]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(3, 4, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&before));
    state.slots[1] = LocalSlotState::Init(MirValue::Unit);
    run(copy_nonoverlapping(3, 4, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&before));
    state.slots[2] = LocalSlotState::Init(MirValue::Tuple(vec![MirValue::Unit, MirValue::Unit]));
    run(
        Statement::Deinit(proj(2, vec![field(0, unit())])),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(2)),
        Some(LocalSlotState::PartialShell(_))
    ));
    run(assign(local(5), raw_const(local(2))), &mut state).unwrap();
    run(
        assign(local(6), raw_mut(proj(0, vec![field(2, zpair.clone())]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(5, 6, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&before));
    assert_eq!(
        state.read_place(&proj(0, vec![field(0, u32_ty())])),
        Ok(u32v(77))
    );
}

// ---------------------------------------------------------------------------------------------
// `kani#5176`: typed copies of padded unions with zero-sized array fields
// ---------------------------------------------------------------------------------------------

/// `src = U { zst_array: [(); 2] }; dst = U { zst_array: [(); 2] };
/// write_bytes(&mut src as *mut U as *mut u8, 0x5a, 8); copy_nonoverlapping(&src, &mut dst, 1);
/// assert_eq!(dst.bytes, [0x5a; 8])` for `union U { bytes: [u8; 8], zst_array: [(); 2] }`.
fn kani_5176_array_union(repr: AdtRepr) {
    let bytes_ty = arr(u8_ty(), 8);
    let zst_ty = arr(unit(), 2);
    let (u_def, u_ty) =
        adt(
            AdtDef::new_union("ArrayUnion", vec![bytes_ty.clone(), zst_ty.clone()]).with_repr(repr),
        );
    let decls = vec![
        u_ty.clone(),
        u_ty.clone(),
        raw(u_ty.clone(), Mutability::Mut),
        raw(u8_ty(), Mutability::Mut),
        raw(u_ty.clone(), Mutability::Not),
        raw(u_ty.clone(), Mutability::Mut),
        bytes_ty.clone(),
        zst_ty.clone(),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    // `U { zst_array: [(); 2] }` for both locals.
    for l in [0, 1] {
        state.slots[7] = LocalSlotState::Init(units(2));
        run(
            assign(local(l), union_agg(&u_def, 1, Operand::Copy(local(7)))),
            &mut state,
        )
        .unwrap();
        assert_eq!(
            state.get_init(Local(l)),
            Some(&MirValue::union_value(&u_def, 1, units(2)))
        );
    }
    run(assign(local(2), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(3), ptr_cast(2, raw(u8_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    let ptr_val = state.get_init(Local(3)).unwrap().clone();
    let outcome = eval_intrinsic_call(
        IntrinsicOp::WriteBytes,
        &[ptr_val, u8v(0x5a), usizev(8)],
        &[raw(u8_ty(), Mutability::Mut), u8_ty(), usize_ty()],
        &unit(),
        &mut state,
    )
    .unwrap();
    assert_eq!(outcome, IntrinsicOutcome::Return(MirValue::Unit));
    let bytes = MirValue::Array {
        elements: vec![u8v(0x5a); 8],
        elem_ty: u8_ty(),
    };
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&u_def, 0, bytes.clone()))
    );
    // `ptr::write(&mut dst, ptr::read(&src))` as a typed copy.
    run(assign(local(4), raw_const(local(0))), &mut state).unwrap();
    run(assign(local(5), raw_mut(local(1))), &mut state).unwrap();
    run(copy_nonoverlapping(4, 5, 1), &mut state).unwrap();
    run(
        assign(local(6), copy_of(proj(1, vec![field(0, bytes_ty.clone())]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(6)), Some(&bytes));
    // The zero-sized field stays readable, and writing it keeps the bytes.
    run(
        assign(local(7), copy_of(proj(1, vec![field(1, zst_ty.clone())]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(7)), Some(&units(2)));
    run(
        assign(proj(1, vec![field(1, zst_ty.clone())]), copy_of(local(7))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::union_value(&u_def, 0, bytes))
    );
}

#[test]
fn kani_5176_typed_copy_of_a_union_with_a_zst_array_field() {
    kani_5176_array_union(AdtRepr::c());
    kani_5176_array_union(AdtRepr::rust());
}

#[test]
fn kani_5176_padded_repr_c_payload_and_aligned_zst_fields() {
    // `#[repr(C)] struct Padded { a: u8, b: u32 }` (bytes 1..4 are padding) in
    // `#[repr(C)] union PU { payload: Padded, zst: [(); 2] }`.
    let (padded_def, padded_ty) =
        adt(AdtDef::new_struct("Padded", vec![u8_ty(), u32_ty()]).with_repr(AdtRepr::c()));
    let zst_ty = arr(unit(), 2);
    let (pu_def, pu_ty) = adt(
        AdtDef::new_union("PU", vec![padded_ty.clone(), zst_ty.clone()]).with_repr(AdtRepr::c()),
    );
    let decls = vec![
        pu_ty.clone(),
        pu_ty.clone(),
        raw(pu_ty.clone(), Mutability::Not),
        raw(pu_ty.clone(), Mutability::Mut),
        u32_ty(),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let payload = MirValue::adt(&padded_def, 0, vec![u8v(1), u32v(2)]);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&pu_def, 0, payload.clone()));
    state.slots[1] = LocalSlotState::Init(MirValue::union_value(&pu_def, 1, units(2)));
    run(assign(local(2), raw_const(local(0))), &mut state).unwrap();
    run(assign(local(3), raw_mut(local(1))), &mut state).unwrap();
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::union_value(&pu_def, 0, payload.clone()))
    );
    assert_eq!(
        state.read_place(&proj(1, vec![field(1, zst_ty.clone()), cidx(1, 2)])),
        Ok(MirValue::Unit)
    );
    run(
        assign(
            local(4),
            copy_of(proj(1, vec![field(0, padded_ty), field(1, u32_ty())])),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(4)), Some(&u32v(2)));
    // An over-aligned zero-sized field (`[u64; 0]`) is readable as well.
    let (al_def, al_ty) = adt(AdtDef::new_union(
        "Aligned",
        vec![u8_ty(), arr(Ty::Uint(UintTy::U64), 0)],
    )
    .with_repr(AdtRepr::c()));
    let mut state = StatementEvalState::from_local_decls(vec![al_ty], PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&al_def, 0, u8v(3)));
    assert_eq!(
        state.read_place(&proj(0, vec![field(1, arr(Ty::Uint(UintTy::U64), 0))])),
        Ok(MirValue::Array {
            elements: vec![],
            elem_ty: Ty::Uint(UintTy::U64),
        })
    );
    // An all-zero-sized union.
    let (all_def, all_ty) = adt(AdtDef::new_union("AllZst", vec![unit(), zst_ty.clone()]));
    let mut state = StatementEvalState::from_local_decls(vec![all_ty], PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&all_def, 0, MirValue::Unit));
    assert_eq!(
        state.read_place(&proj(0, vec![field(1, zst_ty)])),
        Ok(units(2))
    );
}

// ---------------------------------------------------------------------------------------------
// Byte-level entry points: `transmute` and `write_bytes`
// ---------------------------------------------------------------------------------------------

#[test]
fn transmutes_into_unions_keep_the_canonical_layout_boundary() {
    // A single-field niche-free union is canonical: its field is decoded at offset 0.
    let (u1_def, u1_ty) = adt(AdtDef::new_union("U1", vec![u32_ty()]));
    let mut state = StatementEvalState::from_local_decls(vec![u1_ty.clone()], PW);
    run(
        assign(
            local(0),
            Rvalue::Cast(
                CastKind::Transmute,
                Operand::Constant(Constant::Int(0xABCD, u32_ty())),
                u1_ty.clone(),
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&u1_def, 0, u32v(0xABCD)))
    );
    // A union with several fields (`MaybeUninit<u32>`) has no canonical byte layout, so the
    // transmute fails closed at lowering rather than guessing an active field.
    let mu = MaybeUninitTy::new(u32_ty());
    assert_eq!(
        lower_rvalue(
            &Rvalue::Cast(
                CastKind::Transmute,
                Operand::Constant(Constant::Int(5, u32_ty())),
                mu.ty.clone(),
            ),
            &[],
            PW,
        ),
        Err(RvalueLowerError::CastError(
            CastLowerError::UnsupportedLayout { ty: mu.ty.clone() }
        ))
    );
}

#[test]
fn write_bytes_through_maybe_uninit_pointers() {
    let mu = MaybeUninitTy::new(u32_ty());
    let decls = vec![
        mu.ty.clone(),
        raw(mu.ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let write_bytes = |state: &mut StatementEvalState, ptr: usize, ptr_ty: Ty, count: u128| {
        let ptr_val = state.get_init(Local(ptr)).unwrap().clone();
        eval_intrinsic_call(
            IntrinsicOp::WriteBytes,
            &[ptr_val, u8v(0xAB), usizev(count)],
            &[ptr_ty, u8_ty(), usize_ty()],
            &unit(),
            state,
        )
    };
    // Through `mu.as_mut_ptr()` while `value` is active: the `u32` inside is overwritten.
    let mut state = StatementEvalState::from_local_decls(decls.clone(), PW);
    state.slots[0] = LocalSlotState::Init(mu.init(u32v(5)));
    run(assign(local(1), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    write_bytes(&mut state, 2, raw(u32_ty(), Mutability::Mut), 1).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(0xABAB_ABAB))));
    // `MaybeUninit<u32>` itself has no canonical byte layout to decode the bytes into.
    assert_eq!(
        write_bytes(&mut state, 1, raw(mu.ty.clone(), Mutability::Mut), 1),
        Err(RvalueEvalError::UnsupportedMemoryAccess(
            "write_bytes into an element type without a canonical byte layout"
        ))
    );
    // Zero bytes (`count == 0`) touch nothing.
    write_bytes(&mut state, 1, raw(mu.ty.clone(), Mutability::Mut), 0).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(0xABAB_ABAB))));
}

// ---------------------------------------------------------------------------------------------
// Goal 3: writes covering the whole `T` of a `MaybeUninit<T>` without initialized bytes
// ---------------------------------------------------------------------------------------------

/// `_0: MaybeUninit<T> = MaybeUninit { uninit: () }`, `_1: *mut MaybeUninit<T> = &raw mut _0`,
/// `_2: *mut T = _1 as *mut T` (`mu.as_mut_ptr()`), `_3: T`, `_4: ()`, then `extra` locals.
fn as_mut_ptr_state(mu: &MaybeUninitTy, extra: Vec<Ty>) -> StatementEvalState {
    let mut decls = vec![
        mu.ty.clone(),
        raw(mu.ty.clone(), Mutability::Mut),
        raw(mu.t.clone(), Mutability::Mut),
        mu.t.clone(),
        unit(),
    ];
    decls.extend(extra);
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[4] = LocalSlotState::Init(MirValue::Unit);
    run(
        assign(local(0), union_agg(&mu.def, 0, Operand::Copy(local(4)))),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));
    run(assign(local(1), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(mu.t.clone(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    state
}

#[test]
fn ptr_write_through_as_mut_ptr_initializes_maybe_uninit_uninit() {
    // `let mut mu = MaybeUninit::<u32>::uninit(); mu.as_mut_ptr().write(5); mu.assume_init()`:
    // the write determines every initialized byte of `mu` (Miri: bytes `0..4` become `5`).
    let mu = MaybeUninitTy::new(u32_ty());
    let mut state = as_mut_ptr_state(&mu, vec![]);
    // Before the write, `mu` holds no initialized byte to read.
    assert!(matches!(
        state.read_place(&deref(2)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(_))
    ));
    assert_eq!(
        state.read_place(&proj(0, mu.inner())),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 0,
            requested_field: 1,
        })
    );
    run(assign(deref(2), int(5, u32_ty())), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(5))));
    run(assign(local(3), copy_of(deref(2))), &mut state).unwrap();
    assert_eq!(state.get_init(Local(3)), Some(&u32v(5)));
    // The zero-sized `uninit` field stays readable, and a second write overwrites the value.
    assert_eq!(
        state.read_place(&proj(0, vec![mu.uninit_field()])),
        Ok(MirValue::Unit)
    );
    run(assign(deref(2), int(6, u32_ty())), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(6))));

    // A direct write of the same place (`mu.value.value = 7`) behaves alike.
    let mut state = as_mut_ptr_state(&mu, vec![]);
    run(assign(proj(0, mu.inner()), int(7, u32_ty())), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(7))));
    // So does a write into a never-initialized local (whose bytes are all uninitialized).
    let decls = vec![mu.ty.clone()];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    run(assign(proj(0, mu.inner()), int(8, u32_ty())), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(8))));
}

#[test]
fn ptr_write_through_as_mut_ptr_of_structs_arrays_and_nested_maybe_uninit() {
    // `T = #[repr(C)] struct Pair { a: u16, b: u16 }`.
    let (pair_def, pair_ty) =
        adt(AdtDef::new_struct("Pair", vec![u16_ty(), u16_ty()]).with_repr(AdtRepr::c()));
    let mu = MaybeUninitTy::new(pair_ty.clone());
    let mut state = as_mut_ptr_state(&mu, vec![]);
    let pair = MirValue::adt(&pair_def, 0, vec![u16v(1), u16v(2)]);
    state.slots[3] = LocalSlotState::Init(pair.clone());
    run(assign(deref(2), copy_of(local(3))), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(pair)));

    // `T = [u8; 4]`.
    let bytes_ty = arr(u8_ty(), 4);
    let mu = MaybeUninitTy::new(bytes_ty.clone());
    let mut state = as_mut_ptr_state(&mu, vec![]);
    let bytes = MirValue::Array {
        elements: vec![u8v(1), u8v(2), u8v(3), u8v(4)],
        elem_ty: u8_ty(),
    };
    state.slots[3] = LocalSlotState::Init(bytes.clone());
    run(assign(deref(2), copy_of(local(3))), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(bytes)));

    // `MaybeUninit<MaybeUninit<u32>>`: a `*mut u32` into the inner value covers both unions.
    let inner = MaybeUninitTy::new(u32_ty());
    let outer = MaybeUninitTy::new(inner.ty.clone());
    let decls = vec![
        outer.ty.clone(),
        raw(outer.ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(outer.uninit());
    run(assign(local(1), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), int(9, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&outer.init(inner.init(u32v(9))))
    );
    // `MaybeUninit::new(MaybeUninit::uninit())`: only the inner union is without bytes.
    state.slots[0] = LocalSlotState::Init(outer.init(inner.uninit()));
    run(assign(deref(2), int(10, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&outer.init(inner.init(u32v(10))))
    );
}

#[test]
fn ptr_write_through_as_mut_ptr_inside_structs_and_arrays_of_maybe_uninit() {
    let mu = MaybeUninitTy::new(u32_ty());
    // `w.buf.as_mut_ptr().write(3)` for `#[repr(C)] struct Wrapper { buf: MaybeUninit<u32>,
    // tag: u8 }`.
    let (w_def, w_ty) =
        adt(AdtDef::new_struct("Wrapper", vec![mu.ty.clone(), u8_ty()]).with_repr(AdtRepr::c()));
    let decls = vec![
        w_ty.clone(),
        raw(mu.ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
        arr(mu.ty.clone(), 2),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::adt(&w_def, 0, vec![mu.uninit(), u8v(1)]));
    run(
        assign(local(1), raw_mut(proj(0, vec![field(0, mu.ty.clone())]))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), int(3, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&w_def, 0, vec![mu.init(u32v(3)), u8v(1)]))
    );
    // `arr[1].as_mut_ptr().write(4)` for `[MaybeUninit<u32>; 2]`.
    state.slots[3] = LocalSlotState::Init(MirValue::Array {
        elements: vec![mu.init(u32v(1)), mu.uninit()],
        elem_ty: mu.ty.clone(),
    });
    run(
        assign(local(1), raw_mut(proj(3, vec![cidx(1, 2)]))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), int(4, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::Array {
            elements: vec![mu.init(u32v(1)), mu.init(u32v(4))],
            elem_ty: mu.ty.clone(),
        })
    );
}

#[test]
fn copy_nonoverlapping_and_write_bytes_through_as_mut_ptr_of_maybe_uninit_uninit() {
    // `copy_nonoverlapping::<u32>(&src, mu.as_mut_ptr(), 1)`.
    let mu = MaybeUninitTy::new(u32_ty());
    let mut state = as_mut_ptr_state(&mu, vec![raw(u32_ty(), Mutability::Not)]);
    state.slots[3] = LocalSlotState::Init(u32v(0x1234));
    run(assign(local(5), raw_const(local(3))), &mut state).unwrap();
    run(copy_nonoverlapping(5, 2, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(0x1234))));
    // Uninitialized source bytes leave (or make) `mu` a union without initialized bytes.
    state.slots[3] = LocalSlotState::Uninit;
    run(copy_nonoverlapping(5, 2, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));

    // `MaybeUninit::<u32>::zeroed()`: `u.as_mut_ptr().write_bytes(0, 1)` on `uninit()`.
    let write_bytes =
        |state: &mut StatementEvalState, ptr: usize, ptr_ty: Ty, byte: u128, count: u128| {
            let ptr_val = state.get_init(Local(ptr)).unwrap().clone();
            eval_intrinsic_call(
                IntrinsicOp::WriteBytes,
                &[ptr_val, u8v(byte), usizev(count)],
                &[ptr_ty, u8_ty(), usize_ty()],
                &unit(),
                state,
            )
        };
    let mut state = as_mut_ptr_state(&mu, vec![]);
    write_bytes(&mut state, 2, raw(u32_ty(), Mutability::Mut), 0, 1).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(0))));
    let mut state = as_mut_ptr_state(&mu, vec![]);
    write_bytes(&mut state, 2, raw(u32_ty(), Mutability::Mut), 0xAB, 1).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(u32v(0xABAB_ABAB))));

    // `MaybeUninit<[u32; 4]>`: element-wise writes through `mu.as_mut_ptr() as *mut u32` that
    // cover the whole array initialize it; a partial window stays unsupported.
    let arr_ty = arr(u32_ty(), 4);
    let mu = MaybeUninitTy::new(arr_ty.clone());
    let extra = vec![
        raw(u32_ty(), Mutability::Mut),
        arr_ty.clone(),
        raw(u32_ty(), Mutability::Not),
    ];
    let fresh = || {
        let mut state = as_mut_ptr_state(&mu, extra.clone());
        run(
            assign(local(5), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
            &mut state,
        )
        .unwrap();
        state.slots[6] = LocalSlotState::Init(MirValue::Array {
            elements: vec![u32v(1), u32v(2), u32v(3), u32v(4)],
            elem_ty: u32_ty(),
        });
        run(
            assign(local(7), raw_const(proj(6, vec![cidx(0, 4)]))),
            &mut state,
        )
        .unwrap();
        state
    };
    let words = |vals: [u128; 4]| MirValue::Array {
        elements: vals.iter().map(|v| u32v(*v)).collect(),
        elem_ty: u32_ty(),
    };
    let mut state = fresh();
    run(copy_nonoverlapping(7, 5, 4), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&mu.init(words([1, 2, 3, 4])))
    );
    let mut state = fresh();
    write_bytes(&mut state, 5, raw(u32_ty(), Mutability::Mut), 0, 4).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&mu.init(words([0, 0, 0, 0])))
    );
    let mut state = fresh();
    assert_eq!(
        run(copy_nonoverlapping(7, 5, 2), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(
            "copy_nonoverlapping outside of whole-local copies"
        ))
    );
    assert_eq!(
        write_bytes(&mut state, 5, raw(u32_ty(), Mutability::Mut), 0, 2),
        Err(RvalueEvalError::UnsupportedMemoryAccess(
            "write_bytes outside of resolvable sub-places"
        ))
    );
    assert!(matches!(
        run(assign(deref(5), int(1, u32_ty())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(_))
    ));
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));
}

#[test]
fn partial_or_punning_writes_into_union_fields_still_fail_closed() {
    // A partially initialized `(u32, u32)` copied through `mu.as_mut_ptr()` would leave `mu`
    // partially initialized.
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let mu = MaybeUninitTy::new(pair.clone());
    let mut state = as_mut_ptr_state(&mu, vec![raw(pair.clone(), Mutability::Not)]);
    state.slots[3] = LocalSlotState::Init(MirValue::Tuple(vec![u32v(1), u32v(2)]));
    run(
        Statement::Deinit(proj(3, vec![field(1, u32_ty())])),
        &mut state,
    )
    .unwrap();
    run(assign(local(5), raw_const(local(3))), &mut state).unwrap();
    assert_eq!(
        run(copy_nonoverlapping(5, 2, 1), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY))
    );
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));
    // A `u32` written into the first half of `MaybeUninit<(u32, u32)>` initializes only part
    // of it (through a pointer and directly).
    let mut state = as_mut_ptr_state(&mu, vec![raw(u32_ty(), Mutability::Mut)]);
    run(
        assign(local(5), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        run(assign(deref(5), int(1, u32_ty())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(_))
    ));
    let mut first = mu.inner();
    first.push(field(0, u32_ty()));
    assert_eq!(
        run(assign(proj(0, first.clone()), int(1, u32_ty())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(proj(0, first)))
    );
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));

    // `union W { z: (), a: u16, b: ManuallyDrop<u32> }` with `a` initialized: a `u32` written
    // over `b.value` puns `a`'s bytes, which the value tree cannot hold (no guessed field).
    let (md_def, md_ty) = manually_drop(u32_ty());
    let (w_def, w_ty) = adt(AdtDef::new_union(
        "W",
        vec![unit(), u16_ty(), md_ty.clone()],
    ));
    let decls = vec![
        w_ty.clone(),
        raw(w_ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = MirValue::union_value(&w_def, 1, u16v(7));
    state.slots[0] = LocalSlotState::Init(before.clone());
    run(assign(local(1), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        run(assign(deref(2), int(1, u32_ty())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(_))
    ));
    let b_value = proj(0, vec![field(2, md_ty.clone()), field(0, u32_ty())]);
    assert_eq!(
        run(assign(b_value.clone(), int(1, u32_ty())), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(b_value))
    );
    assert_eq!(state.get_init(Local(0)), Some(&before));
    // With `z` active (no initialized byte), the same writes initialize `b`.
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&w_def, 0, MirValue::Unit));
    run(assign(deref(2), int(1, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(
            &w_def,
            2,
            MirValue::adt(&md_def, 0, vec![u32v(1)])
        ))
    );
}

#[test]
fn leaf_union_field_overwrites_keep_priority_over_covering_writes() {
    // `union V { z: (), a: u32, b: (u32,) }` with `z` active: `*(p as *mut u32) = 5` keeps
    // overwriting the leaf field `a` (as before covering writes existed) rather than becoming
    // ambiguous with `b.0`.
    let one = Ty::Tuple(vec![u32_ty()]);
    let (v_def, v_ty) = adt(AdtDef::new_union("V", vec![unit(), u32_ty(), one.clone()]));
    let decls = vec![
        v_ty.clone(),
        raw(v_ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&v_def, 0, MirValue::Unit));
    run(assign(local(1), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), int(5, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&v_def, 1, u32v(5)))
    );
    // Once `b` is active, a field-borrow pointer to `b.0` designates the active `b.0`.
    run(
        assign(
            proj(0, vec![field(2, one.clone())]),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![Operand::Constant(Constant::Int(6, u32_ty()))],
            ),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            local(2),
            raw_mut(proj(0, vec![field(2, one.clone()), field(0, u32_ty())])),
        ),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), int(7, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(
            &v_def,
            2,
            MirValue::Tuple(vec![u32v(7)])
        ))
    );
}

// ---------------------------------------------------------------------------------------------
// `Deinit` of zero-sized places inside union storage
// ---------------------------------------------------------------------------------------------

#[test]
fn deinit_of_zero_sized_union_places_stores_nothing() {
    let u = ShapesUnion::new();
    let decls = vec![u.ty.clone()];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(7));
    for place in [
        proj(0, vec![u.f(UNIT)]),
        proj(0, vec![u.f(ZST_ARR)]),
        proj(0, vec![u.f(ZST_ARR), cidx(1, 3)]),
        proj(0, vec![u.f(NESTED), field(0, unit())]),
        proj(0, vec![u.f(NEVER_PAIR), field(0, unit())]),
    ] {
        run(Statement::Deinit(place.clone()), &mut state).unwrap();
        assert_eq!(state.get_init(Local(0)), Some(&u.with_val(7)), "{place:?}");
    }
    // Out-of-bounds zero-sized places are still rejected.
    assert!(matches!(
        state.deinit_place(&proj(0, vec![u.f(ZST_ARR), cidx(3, 4)]), &unit()),
        Err(RvalueEvalError::IndexOutOfBounds { .. })
    ));
    // Uninitialized bytes over (part of) a non-zero-sized field need a byte memory.
    for place in [
        proj(0, vec![u.f(VAL)]),
        proj(0, vec![u.f(PAIR), field(0, u16_ty())]),
    ] {
        assert_eq!(
            run(Statement::Deinit(place.clone()), &mut state),
            Err(RvalueEvalError::UnsupportedPlaceProjection(place))
        );
    }
    assert_eq!(state.get_init(Local(0)), Some(&u.with_val(7)));
    // `Deinit` of the whole union makes it uninitialized.
    run(Statement::Deinit(local(0)), &mut state).unwrap();
    assert_eq!(state.get_local(Local(0)), Some(&LocalSlotState::Uninit));
}

// ---------------------------------------------------------------------------------------------
// Adversarial Round ep1-B1 Regression Tests
// ---------------------------------------------------------------------------------------------

#[test]
fn b1_zst_subplaces_inside_inactive_non_zst_union_fields_read_write_and_resolve() {
    let zst2 = arr(unit(), 2);
    let (_, pair_zst) =
        adt(AdtDef::new_struct("PairZst", vec![u32_ty(), zst2.clone()]).with_repr(AdtRepr::c()));
    let arr4 = arr(u32_ty(), 4);
    let (u_def, u_ty) = adt(AdtDef::new_union(
        "UWithNestedZst",
        vec![u32_ty(), pair_zst.clone(), arr4.clone()],
    ));
    let decls = vec![
        u_ty.clone(),
        raw(zst2.clone(), Mutability::Not),
        raw(unit(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let active_u = MirValue::union_value(&u_def, 0, u32v(42));
    state.slots[0] = LocalSlotState::Init(active_u.clone());

    // Reading the inhabited ZST sub-place `u.pair_with_zst.1` (`[(); 2]`), its element
    // `u.pair_with_zst.1[1]`, and the empty subslice `u.arr[2..2]` (`[u32; 0]`) succeeds,
    // while `u.pair_with_zst.0` (`u32`) and `u.arr[1..2]` (`[u32; 1]`) stay `InactiveUnionField`
    // and out-of-bounds `u.pair_with_zst.1[2]` is `IndexOutOfBounds`.
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![field(1, pair_zst.clone()), field(1, zst2.clone())]
        )),
        Ok(units(2))
    );
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![
                field(1, pair_zst.clone()),
                field(1, zst2.clone()),
                cidx(1, 2)
            ]
        )),
        Ok(MirValue::Unit)
    );
    assert!(matches!(
        state.read_place(&proj(
            0,
            vec![
                field(1, pair_zst.clone()),
                field(1, zst2.clone()),
                cidx(2, 3)
            ]
        )),
        Err(RvalueEvalError::IndexOutOfBounds { .. })
    ));
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![
                field(2, arr4.clone()),
                ProjectionElem::Subslice {
                    from: 2,
                    to: 2,
                    from_end: false,
                },
            ],
        )),
        Ok(MirValue::Array {
            elements: vec![],
            elem_ty: u32_ty(),
        })
    );
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![field(1, pair_zst.clone()), field(0, u32_ty())]
        )),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 0,
            requested_field: 1,
        })
    );
    assert_eq!(
        state.read_place(&proj(
            0,
            vec![
                field(2, arr4),
                ProjectionElem::Subslice {
                    from: 1,
                    to: 2,
                    from_end: false,
                },
            ],
        )),
        Err(RvalueEvalError::InactiveUnionField {
            active_field: 0,
            requested_field: 2,
        })
    );

    // Writing to `u.pair_with_zst.1` or `u.pair_with_zst.1[0]` (directly and through pointers)
    // stores 0 bytes and preserves `u.val == 42`.
    run(
        assign(
            proj(
                0,
                vec![
                    field(1, pair_zst.clone()),
                    field(1, zst2.clone()),
                    cidx(0, 2),
                ],
            ),
            unit_rvalue(),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&active_u));
    run(
        assign(
            local(1),
            raw_const(proj(
                0,
                vec![field(1, pair_zst.clone()), field(1, zst2.clone())],
            )),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.read_place(&deref(1)), Ok(units(2)));
    run(
        assign(
            local(2),
            raw_mut(proj(
                0,
                vec![field(1, pair_zst), field(1, zst2), cidx(1, 2)],
            )),
        ),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), unit_rvalue()), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&active_u));

    // `MaybeUninit<PairUnit>`: writing `.1: ()` first while `mu` is `uninit()` and then `.0: u32`
    // second initializes `mu` to `MaybeUninit::new(PairUnit(99, ()))`.
    let (pu_def, pu_ty) =
        adt(AdtDef::new_struct("PairUnit", vec![u32_ty(), unit()]).with_repr(AdtRepr::c()));
    let mu = MaybeUninitTy::new(pu_ty);
    let mut state = as_mut_ptr_state(
        &mu,
        vec![raw(unit(), Mutability::Mut), raw(u32_ty(), Mutability::Mut)],
    );
    let mut zst_sub = mu.inner();
    zst_sub.push(field(1, unit()));
    run(assign(local(5), raw_mut(proj(0, zst_sub))), &mut state).unwrap();
    run(assign(deref(5), unit_rvalue()), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));
    run(
        assign(local(6), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(6), int(99, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&mu.init(MirValue::adt(&pu_def, 0, vec![u32v(99), MirValue::Unit])))
    );
}

#[test]
fn b1_deinit_and_uninit_zst_writes_validate_dead_locals_indices_and_enum_variants() {
    let u = ShapesUnion::new();
    let (e_def, e_ty) = adt(AdtDef::new_enum(
        "TaggedE",
        Some(anneal_mir::ir::ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u32_ty()]),
            VariantDef::new("B", vec![unit()]),
        ],
    ));
    let (ue_def, ue_ty) = adt(AdtDef::new_union("UE", vec![e_ty.clone(), unit()]));
    let decls = vec![u.ty.clone(), ue_ty.clone(), unit()];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(7));
    state.slots[1] = LocalSlotState::Init(MirValue::union_value(
        &ue_def,
        0,
        MirValue::adt(&e_def, 0, vec![u32v(42)]),
    ));

    // `Deinit` on an absent variant of a ZST enum inside an inactive union field is rejected.
    assert_eq!(
        state.deinit_place(
            &proj(
                0,
                vec![
                    u.f(ABSENT_ENUM),
                    ProjectionElem::Downcast(1),
                    field(0, Ty::Never),
                ],
            ),
            &Ty::Never,
        ),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0,
        })
    );

    // `Deinit((ue.e as B).0)` while `ue.e` is active in variant `A(42)` fails with
    // `InactiveVariantProjection`; while `ue.unit` is active (`ue.e` inactive), downcasting the
    // non-ZST enum `ue.e` fails with `UnsupportedPlaceProjection`.
    let b_zst = proj(
        1,
        vec![
            field(0, e_ty.clone()),
            ProjectionElem::Downcast(1),
            field(0, unit()),
        ],
    );
    assert_eq!(
        run(Statement::Deinit(b_zst.clone()), &mut state),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0,
        })
    );
    state.slots[1] = LocalSlotState::Init(MirValue::union_value(&ue_def, 1, MirValue::Unit));
    assert_eq!(
        run(Statement::Deinit(b_zst.clone()), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(b_zst))
    );
}

#[test]
fn b1_copy_nonoverlapping_whole_array_uninit_into_maybe_uninit_and_zst_union_arrays() {
    // 1. `copy_nonoverlapping::<u32>(&uninit_arr[0], mu.as_mut_ptr() as *mut u32, 4)` covers all
    // 16 bytes of `MaybeUninit<[u32; 4]>` and leaves `mu` as `MaybeUninit::uninit()`.
    let arr4 = arr(u32_ty(), 4);
    let mu = MaybeUninitTy::new(arr4.clone());
    let decls = vec![
        mu.ty.clone(),
        arr4.clone(),
        raw(u32_ty(), Mutability::Not),
        raw(mu.ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(mu.init(MirValue::Array {
        elements: vec![u32v(1), u32v(2), u32v(3), u32v(4)],
        elem_ty: u32_ty(),
    }));
    run(
        assign(local(2), raw_const(proj(1, vec![cidx(0, 4)]))),
        &mut state,
    )
    .unwrap();
    run(assign(local(3), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(4), ptr_cast(3, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 4, 4), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));

    // 2. `copy_nonoverlapping::<()>(&uninit_units[0], &raw mut u.zst_arr[0], 2)` into an
    // inhabited ZST union array field stores 0 bytes and leaves `u.val` untouched.
    let u = ShapesUnion::new();
    let zst3 = arr(unit(), 3);
    let decls = vec![
        u.ty.clone(),
        zst3,
        raw(unit(), Mutability::Not),
        raw(unit(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(77));
    run(
        assign(local(2), raw_const(proj(1, vec![cidx(0, 3)]))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(3), raw_mut(proj(0, vec![u.f(ZST_ARR), cidx(0, 3)]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 3, 2), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&u.with_val(77)));

    // 3. Copying an uninitialized `[MaybeUninit<u32>; 2]` as 1 element (`count = 1`) into an
    // outer array `[[MaybeUninit<u32>; 2]; 2]` produces `[MaybeUninit::uninit(); 2]`.
    let mu_u32 = MaybeUninitTy::new(u32_ty());
    let inner_arr = arr(mu_u32.ty.clone(), 2);
    let outer_arr = arr(inner_arr.clone(), 2);
    let decls = vec![
        outer_arr.clone(),
        inner_arr.clone(),
        raw(inner_arr.clone(), Mutability::Not),
        raw(inner_arr.clone(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let init_pair = MirValue::Array {
        elements: vec![mu_u32.init(u32v(10)), mu_u32.init(u32v(20))],
        elem_ty: mu_u32.ty.clone(),
    };
    let uninit_pair = MirValue::Array {
        elements: vec![mu_u32.uninit(), mu_u32.uninit()],
        elem_ty: mu_u32.ty.clone(),
    };
    state.slots[0] = LocalSlotState::Init(MirValue::Array {
        elements: vec![init_pair.clone(), init_pair.clone()],
        elem_ty: inner_arr.clone(),
    });
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(proj(0, vec![cidx(0, 2)]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::Array {
            elements: vec![uninit_pair, init_pair],
            elem_ty: inner_arr,
        })
    );

    // 4. A `PartialShell` of `Packet { header: u32, payload: MaybeUninit<u32> }` where `header`
    // is `Init(9)` and `payload` is `Uninit` materializes `payload` as `MaybeUninit::uninit()`
    // when copied into `MaybeUninit<Packet>`.
    let (pkt_def, pkt_ty) = adt(
        AdtDef::new_struct("Packet", vec![u32_ty(), mu_u32.ty.clone()]).with_repr(AdtRepr::c()),
    );
    let mu_pkt = MaybeUninitTy::new(pkt_ty.clone());
    let mut state = as_mut_ptr_state(&mu_pkt, vec![raw(pkt_ty.clone(), Mutability::Not)]);
    run(
        assign(proj(3, vec![field(0, u32_ty())]), int(9, u32_ty())),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(3)),
        Some(LocalSlotState::PartialShell(_))
    ));
    run(assign(local(5), raw_const(local(3))), &mut state).unwrap();
    run(copy_nonoverlapping(5, 2, 1), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&mu_pkt.init(MirValue::adt(&pkt_def, 0, vec![u32v(9), mu_u32.uninit()])))
    );
}

#[test]
fn b1_uninit_unions_uncast_covering_tags_and_write_bytes_on_non_canonical_zsts() {
    // 1. On `union V { z: (), a: u32, b: (u32,) }`:
    // - when `v` is `Uninit`, `*(&raw mut v as *mut u32) = 5` resolves to the leaf field `v.a`;
    // - when `v` is `V { z: () }` or `Uninit`, an uncast field-borrow pointer `&raw mut v.b.0`
    //   honors its subplace tag and activates `v.b = (7,)` rather than overwriting `v.a`.
    let one = Ty::Tuple(vec![u32_ty()]);
    let (v_def, v_ty) = adt(AdtDef::new_union("V", vec![unit(), u32_ty(), one.clone()]));
    let decls = vec![
        v_ty.clone(),
        raw(v_ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    run(assign(local(1), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), int(5, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(&v_def, 1, u32v(5)))
    );

    state.slots[0] = LocalSlotState::Init(MirValue::union_value(&v_def, 0, MirValue::Unit));
    run(
        assign(
            local(2),
            raw_mut(proj(0, vec![field(2, one.clone()), field(0, u32_ty())])),
        ),
        &mut state,
    )
    .unwrap();
    run(assign(deref(2), int(7, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::union_value(
            &v_def,
            2,
            MirValue::Tuple(vec![u32v(7)])
        ))
    );

    // 2. Partial array write on an `Uninit` `MaybeUninit<[u32; 4]>` fails with
    // `UnsupportedMemoryAccess` (not `UnsupportedPlaceProjection`).
    let arr4 = arr(u32_ty(), 4);
    let mu_arr = MaybeUninitTy::new(arr4.clone());
    let decls = vec![
        mu_arr.ty.clone(),
        arr4,
        raw(mu_arr.ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
        raw(u32_ty(), Mutability::Not),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[1] = LocalSlotState::Init(MirValue::Array {
        elements: vec![u32v(1), u32v(2), u32v(3), u32v(4)],
        elem_ty: u32_ty(),
    });
    run(assign(local(2), raw_mut(local(0))), &mut state).unwrap();
    run(
        assign(local(3), ptr_cast(2, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(4), raw_const(proj(1, vec![cidx(0, 4)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        run(copy_nonoverlapping(4, 3, 2), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(
            "copy_nonoverlapping outside of whole-local copies"
        ))
    );

    // 3. `write_bytes` of 0 bytes (`count = 1`) on an inhabited ZST without a canonical byte
    // layout (`MaybeUninit<()>`) initializes the destination to its unique ZST value.
    let mu_unit = MaybeUninitTy::new(unit());
    let decls = vec![mu_unit.ty.clone(), raw(mu_unit.ty.clone(), Mutability::Mut)];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    run(assign(local(1), raw_mut(local(0))), &mut state).unwrap();
    let ptr_val = state.get_init(Local(1)).unwrap().clone();
    let outcome = eval_intrinsic_call(
        IntrinsicOp::WriteBytes,
        &[ptr_val, u8v(0xFF), usizev(1)],
        &[
            raw(mu_unit.ty.clone(), Mutability::Mut),
            u8_ty(),
            usize_ty(),
        ],
        &unit(),
        &mut state,
    )
    .unwrap();
    assert_eq!(outcome, IntrinsicOutcome::Return(MirValue::Unit));
    assert_eq!(state.get_init(Local(0)), Some(&mu_unit.uninit()));
}

// ---------------------------------------------------------------------------------------------
// Adversarial round ep1-A1 regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn a1_zero_sized_stores_into_union_fields_inside_array_elements_store_nothing() {
    // `[MaybeUninit<u32>; 2]`: copying an uninitialized `()` (zero bytes) into `arr[1].uninit`,
    // or `Deinit(arr[1].uninit)`, stores nothing (a zero-byte access in Miri); deinitializing
    // the non-zero-sized `arr[0].value` still needs a byte memory.
    let mu = MaybeUninitTy::new(u32_ty());
    let decls = vec![
        arr(mu.ty.clone(), 2),
        unit(),
        raw(unit(), Mutability::Not),
        raw(unit(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = MirValue::Array {
        elements: vec![mu.init(u32v(1)), mu.init(u32v(2))],
        elem_ty: mu.ty.clone(),
    };
    state.slots[0] = LocalSlotState::Init(before.clone());
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(
            local(3),
            raw_mut(proj(0, vec![cidx(1, 2), mu.uninit_field()])),
        ),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&before));
    run(
        Statement::Deinit(proj(0, vec![cidx(1, 2), mu.uninit_field()])),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&before));
    let value = proj(0, vec![cidx(0, 2), field(1, mu.md_ty.clone())]);
    assert_eq!(
        run(Statement::Deinit(value.clone()), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(value))
    );
    assert_eq!(state.get_init(Local(0)), Some(&before));

    // `[Shapes; 2]`: zero-sized places of inactive fields (also inside an uninhabited one),
    // with dynamic indices still bounds-checked.
    let u = ShapesUnion::new();
    let decls = vec![arr(u.ty.clone(), 2), usize_ty()];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = MirValue::Array {
        elements: vec![u.with_val(7), u.with_val(8)],
        elem_ty: u.ty.clone(),
    };
    state.slots[0] = LocalSlotState::Init(before.clone());
    state.slots[1] = LocalSlotState::Init(usizev(2));
    let indexed = proj(
        0,
        vec![cidx(0, 2), u.f(ZST_ARR), ProjectionElem::Index(Local(1))],
    );
    for place in [
        proj(0, vec![cidx(1, 2), u.f(UNIT)]),
        indexed.clone(),
        proj(0, vec![cidx(1, 2), u.f(NEVER_PAIR), field(0, unit())]),
    ] {
        run(Statement::Deinit(place.clone()), &mut state).unwrap();
        assert_eq!(state.get_init(Local(0)), Some(&before), "{place:?}");
    }
    state.slots[1] = LocalSlotState::Init(usizev(3));
    assert_eq!(
        run(Statement::Deinit(indexed), &mut state),
        Err(RvalueEvalError::IndexOutOfBounds { index: 3, len: 3 })
    );
    assert_eq!(state.get_init(Local(0)), Some(&before));
}

#[test]
fn a1_pointer_reads_into_inactive_union_fields_resolve_alike_in_whole_and_partial_locals() {
    // `#[repr(C)] struct S { u: U, x: u8 }` with `union U { a: u32, b: (u16, u16) }`: a
    // `*const (u16, u16)` at offset 0 names `s.u.b`, an inactive field punning `s.u.a`, which
    // is unsupported whether `s` is initialized or a shell (with `x` deinitialized).
    let pair = Ty::Tuple(vec![u16_ty(), u16_ty()]);
    let (u_def, u_ty) = adt(AdtDef::new_union("U", vec![u32_ty(), pair.clone()]));
    let (s_def, s_ty) =
        adt(AdtDef::new_struct("S", vec![u_ty.clone(), u8_ty()]).with_repr(AdtRepr::c()));
    let decls = vec![
        s_ty.clone(),
        raw(s_ty.clone(), Mutability::Not),
        raw(pair.clone(), Mutability::Not),
        raw(u32_ty(), Mutability::Not),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(MirValue::adt(
        &s_def,
        0,
        vec![MirValue::union_value(&u_def, 0, u32v(5)), u8v(1)],
    ));
    run(assign(local(1), raw_const(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(pair.clone(), Mutability::Not))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(3), ptr_cast(1, raw(u32_ty(), Mutability::Not))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.read_place(&deref(2)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(2)))
    );
    run(
        Statement::Deinit(proj(0, vec![field(1, u8_ty())])),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        state.read_place(&deref(2)),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref(2)))
    );
    // The active field stays readable through a pointer.
    assert_eq!(state.read_place(&deref(3)), Ok(u32v(5)));
    // An uninitialized union inside a shell is named like any uninitialized place.
    run(
        assign(proj(0, vec![field(1, u8_ty())]), int(1, u8_ty())),
        &mut state,
    )
    .unwrap();
    run(
        Statement::Deinit(proj(0, vec![field(0, u_ty.clone())])),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        state.read_place(&deref(3)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
}

#[test]
fn a1_partial_shells_with_uninitialized_zero_sized_fields_copy_into_union_fields() {
    // `#[repr(C)] struct P { a: u32, z: () }` with `z` deinitialized (a shell): its bytes are
    // all of `a`'s, so a typed copy into `MaybeUninit<P>` is the whole value.
    let (p_def, p_ty) =
        adt(AdtDef::new_struct("P", vec![u32_ty(), unit()]).with_repr(AdtRepr::c()));
    let p_val = MirValue::adt(&p_def, 0, vec![u32v(9), MirValue::Unit]);
    let mu = MaybeUninitTy::new(p_ty.clone());
    let mut state = as_mut_ptr_state(&mu, vec![raw(p_ty.clone(), Mutability::Not)]);
    state.slots[3] = LocalSlotState::Init(p_val.clone());
    run(
        Statement::Deinit(proj(3, vec![field(1, unit())])),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(3)),
        Some(LocalSlotState::PartialShell(_))
    ));
    run(assign(local(5), raw_const(local(3))), &mut state).unwrap();
    run(copy_nonoverlapping(5, 2, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&mu.init(p_val.clone())));
    // With `a` deinitialized instead, `mu` would hold uninitialized bytes of `P`.
    let mut state = as_mut_ptr_state(&mu, vec![raw(p_ty.clone(), Mutability::Not)]);
    state.slots[3] = LocalSlotState::Init(p_val);
    run(
        Statement::Deinit(proj(3, vec![field(0, u32_ty())])),
        &mut state,
    )
    .unwrap();
    run(assign(local(5), raw_const(local(3))), &mut state).unwrap();
    assert_eq!(
        run(copy_nonoverlapping(5, 2, 1), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY))
    );
    assert_eq!(state.get_init(Local(0)), Some(&mu.uninit()));
}

// ---------------------------------------------------------------------------------------------
// Adversarial round ep1-B2 regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn b2_enum_wrapped_union_zst_deinit_preserves_discriminant_and_allows_outer_downcasts() {
    // 1. `Option<MaybeUninit<u32>> = Some(MaybeUninit::new(42))`: `Deinit((opt as Some).0.uninit)`
    // and a 0-byte `copy_nonoverlapping` of uninitialized `()` into `(opt as Some).0.uninit`
    // store 0 bytes and must keep `opt` initialized as `Some(MaybeUninit::new(42))` rather than
    // clearing `discriminant_set` on the outer `Option`.
    let mu = MaybeUninitTy::new(u32_ty());
    let (opt_def, opt_ty) = adt(AdtDef::new_enum(
        "OptionMu",
        None,
        vec![
            VariantDef::new("None", vec![]),
            VariantDef::new("Some", vec![mu.ty.clone()]),
        ],
    ));
    let (tagged_opt_def, tagged_opt_ty) = adt(AdtDef::new_enum(
        "TaggedOptionMu",
        Some(anneal_mir::ir::ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("None", vec![]),
            VariantDef::new("Some", vec![mu.ty.clone()]),
        ],
    ));
    let decls = vec![
        opt_ty.clone(),
        unit(),
        raw(unit(), Mutability::Not),
        raw(unit(), Mutability::Mut),
        tagged_opt_ty.clone(),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let some_val = MirValue::adt(&opt_def, 1, vec![mu.init(u32v(42))]);
    let tagged_some_val = MirValue::adt(&tagged_opt_def, 1, vec![mu.init(u32v(42))]);
    state.slots[0] = LocalSlotState::Init(some_val.clone());
    state.slots[4] = LocalSlotState::Init(tagged_some_val.clone());

    let some_uninit_place = proj(
        0,
        vec![
            ProjectionElem::Downcast(1),
            field(0, mu.ty.clone()),
            mu.uninit_field(),
        ],
    );
    run(Statement::Deinit(some_uninit_place), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&some_val));

    let tagged_some_uninit_place = proj(
        4,
        vec![
            ProjectionElem::Downcast(1),
            field(0, mu.ty.clone()),
            mu.uninit_field(),
        ],
    );
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(tagged_some_uninit_place)),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_init(Local(4)), Some(&tagged_some_val));

    // 2. `[Option<Shapes>; 1]`: `Deinit((arr[0] as Some).0.never_pair.0)` has a valid `Downcast`
    // on the outer initialized `Option` *before* the inactive union field `never_pair` and no
    // `Downcast` after it, so it succeeds as a 0-byte no-op.
    let u = ShapesUnion::new();
    let (opt_u_def, opt_u_ty) = adt(AdtDef::new_enum(
        "OptionShapes",
        None,
        vec![
            VariantDef::new("None", vec![]),
            VariantDef::new("Some", vec![u.ty.clone()]),
        ],
    ));
    let arr_opt_u = arr(opt_u_ty.clone(), 1);
    let mut state = StatementEvalState::from_local_decls(vec![arr_opt_u], PW);
    let arr_val = MirValue::Array {
        elements: vec![MirValue::adt(&opt_u_def, 1, vec![u.with_val(7)])],
        elem_ty: opt_u_ty,
    };
    state.slots[0] = LocalSlotState::Init(arr_val.clone());
    let place = proj(
        0,
        vec![
            cidx(0, 1),
            ProjectionElem::Downcast(1),
            field(0, u.ty.clone()),
            u.f(NEVER_PAIR),
            field(0, unit()),
        ],
    );
    run(Statement::Deinit(place), &mut state).unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&arr_val));
}

#[test]
fn b2_partial_zst_stores_into_uninit_unions_and_non_union_arrays_keep_invariants() {
    // 1. Copying a partially initialized 0-byte ZST `((), ())` (with `.0` deinitialized) into a
    // 0-byte ZST union field `z.zpair` of an *uninitialized* union `z: Z` copies 0 bytes, so `z`
    // remains `LocalSlotState::Uninit` (matching an uninitialized `((), ())` copy).
    let zpair = Ty::Tuple(vec![unit(), unit()]);
    let (_z_def, z_ty) = adt(AdtDef::new_union(
        "Z",
        vec![u32_ty(), unit(), zpair.clone()],
    ));
    let decls = vec![
        z_ty.clone(),
        zpair.clone(),
        raw(zpair.clone(), Mutability::Not),
        raw(zpair.clone(), Mutability::Mut),
        arr(zpair.clone(), 2),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[1] = LocalSlotState::Init(MirValue::Tuple(vec![MirValue::Unit, MirValue::Unit]));
    run(
        Statement::Deinit(proj(1, vec![field(0, unit())])),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(1)),
        Some(LocalSlotState::PartialShell(_))
    ));
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(proj(0, vec![field(2, zpair.clone())]))),
        &mut state,
    )
    .unwrap();
    run(copy_nonoverlapping(2, 3, 1), &mut state).unwrap();
    assert_eq!(state.get_local(Local(0)), Some(&LocalSlotState::Uninit));

    // 2. Copying a `PartialShell` with a deinitialized `()` field into a *non-union* array
    // element `arr[0]` still fails closed with `UninitializedLocal(src_local)` (`c6d2ad74`).
    let pair = MirValue::Tuple(vec![MirValue::Unit, MirValue::Unit]);
    state.slots[4] = LocalSlotState::Init(MirValue::Array {
        elements: vec![pair.clone(), pair],
        elem_ty: zpair.clone(),
    });
    run(
        assign(local(3), raw_mut(proj(4, vec![cidx(0, 2)]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        run(copy_nonoverlapping(2, 3, 1), &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
}

#[test]
fn b2_zst_subplace_writes_on_uninit_unions() {
    // On an `Uninit` `MaybeUninit<(u32, ())>`, writing the 0-byte ZST sub-place
    // `(*mu.as_mut_ptr()).1 = ()` succeeds and leaves `mu` `Uninit` until `(*mu.as_mut_ptr()).0`
    // is written.
    let pair_ty = Ty::Tuple(vec![u32_ty(), unit()]);
    let mu = MaybeUninitTy::new(pair_ty.clone());
    let mut state = StatementEvalState::from_local_decls(vec![mu.ty.clone()], PW);
    let mut second = mu.inner();
    second.push(field(1, unit()));
    let mut first = mu.inner();
    first.push(field(0, u32_ty()));
    run(assign(proj(0, second), unit_rvalue()), &mut state).unwrap();
    assert_eq!(state.get_local(Local(0)), Some(&LocalSlotState::Uninit));
    run(assign(proj(0, first), int(55, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&mu.init(MirValue::Tuple(vec![u32v(55), MirValue::Unit])))
    );
}

#[test]
fn b2_nested_uninit_union_copies_and_pointer_resolution_edge_cases() {
    // 1. Borrowing `(u.absent_enum as Absent).0` on an initialized union where `absent_enum` is
    // inactive is rejected with `InactiveVariantProjection`, just as when `absent_enum` is active.
    let u = ShapesUnion::new();
    let decls = vec![u.ty.clone(), raw(Ty::Never, Mutability::Not)];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    state.slots[0] = LocalSlotState::Init(u.with_val(7));
    let absent_proj = proj(
        0,
        vec![
            u.f(ABSENT_ENUM),
            ProjectionElem::Downcast(1),
            field(0, Ty::Never),
        ],
    );
    assert_eq!(
        run(assign(local(1), raw_const(absent_proj)), &mut state),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0,
        })
    );

    // 2. `union W2 { z: (), a: MaybeUninit<u8>, b: u32 }` with `b` (4 bytes) active: copying an
    // uninitialized `MaybeUninit<u8>` (1 byte) into `w2.a` fails with `UNINIT_UNION_COPY` because
    // 3 bytes of `b` remain initialized.
    let mu_u8 = MaybeUninitTy::new(u8_ty());
    let (w2_def, w2_ty) = adt(AdtDef::new_union(
        "W2",
        vec![unit(), mu_u8.ty.clone(), u32_ty()],
    ));
    let decls = vec![
        w2_ty.clone(),
        mu_u8.ty.clone(),
        raw(mu_u8.ty.clone(), Mutability::Not),
        raw(mu_u8.ty.clone(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    let before = MirValue::union_value(&w2_def, 2, u32v(0x1122_3344));
    state.slots[0] = LocalSlotState::Init(before.clone());
    run(assign(local(2), raw_const(local(1))), &mut state).unwrap();
    run(
        assign(local(3), raw_mut(proj(0, vec![field(1, mu_u8.ty.clone())]))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        run(copy_nonoverlapping(2, 3, 1), &mut state),
        Err(RvalueEvalError::UnsupportedMemoryAccess(UNINIT_UNION_COPY))
    );
    assert_eq!(state.get_init(Local(0)), Some(&before));

    // 3. `union V { z: (), a: u32, b: (u32,) }`:
    // - when `v` is `Uninit`, reading `*(&raw const v as *const u32)` resolves to `v.a` and
    //   faults with `UninitializedLocal`;
    // - when `V` is wrapped in `MaybeUninit<V>`, writing `*(mu_v.as_mut_ptr() as *mut u32) = 5`
    //   prefers the innermost union's leaf field `a` over `b.0`.
    let one = Ty::Tuple(vec![u32_ty()]);
    let (v_def, v_ty) = adt(AdtDef::new_union("V", vec![unit(), u32_ty(), one]));
    let mu_v = MaybeUninitTy::new(v_ty.clone());
    let decls = vec![
        v_ty.clone(),
        raw(v_ty.clone(), Mutability::Not),
        raw(u32_ty(), Mutability::Not),
        mu_v.ty.clone(),
        raw(mu_v.ty.clone(), Mutability::Mut),
        raw(u32_ty(), Mutability::Mut),
    ];
    let mut state = StatementEvalState::from_local_decls(decls, PW);
    run(assign(local(1), raw_const(local(0))), &mut state).unwrap();
    run(
        assign(local(2), ptr_cast(1, raw(u32_ty(), Mutability::Not))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.read_place(&deref(2)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );

    state.slots[3] = LocalSlotState::Init(mu_v.uninit());
    run(assign(local(4), raw_mut(local(3))), &mut state).unwrap();
    run(
        assign(local(5), ptr_cast(4, raw(u32_ty(), Mutability::Mut))),
        &mut state,
    )
    .unwrap();
    run(assign(deref(5), int(5, u32_ty())), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&mu_v.init(MirValue::union_value(&v_def, 1, u32v(5))))
    );
}

// ---------------------------------------------------------------------------------------------
// Adversarial round ep1-A2 regression tests: `kani#5159` uninhabited zero-sized union fields
// ---------------------------------------------------------------------------------------------

/// `core::convert::Infallible` (`enum Infallible {}`).
fn infallible() -> Ty {
    adt(AdtDef::new_enum("core::convert::Infallible", None, vec![])).1
}

/// `union K5159 { val: u32, inf: Infallible, pair: (Infallible, ()), arr1: [Infallible; 1],
/// md: ManuallyDrop<Infallible>, phantom: PhantomData<Infallible>, arr0: [Infallible; 0],
/// zarr: [(); 3], v: V, mu: MaybeUninit<Infallible>, pair_u32: (Infallible, u32),
/// void_arr0: [CustomVoid; 0], void_arr1: [CustomVoid; 1], void_pair: (CustomVoid, ()),
/// arr2_v: [V; 2], v4: V4 }` with `union V { p: (Infallible, ()), y: () }` and
/// `union V4 { p: (Infallible, u32), x: u32 }`, mirroring `UnionZst.lean`'s
/// `kani5159_witness_reads`: `Trusted.MirSemantics`' `readProjectedValueUnionAware` faults with
/// `.ub` on every read of an uninhabited leaf, fails closed with `.unsupported` (never `.ub`,
/// matching `InactiveUnionField` here) on inhabited-leaf reads through an uninhabited container
/// (`subProjTouchesUninhabited`, whether the leaf is 0-byte as in `(Infallible, ()).1` or
/// positive-sized as in `(Infallible, u32).1`), and decodes every inhabited 0-byte field or
/// sub-place not passing through an uninhabited container from zero bytes.
#[test]
fn a2_kani_5159_uninhabited_zero_sized_union_fields_and_subplaces_fault() {
    let inf = infallible();
    let custom_void = adt(AdtDef::new_enum("CustomVoid", None, vec![])).1;
    let pair = Ty::Tuple(vec![inf.clone(), unit()]);
    let pair_u32 = Ty::Tuple(vec![inf.clone(), u32_ty()]);
    let void_pair = Ty::Tuple(vec![custom_void.clone(), unit()]);
    let (_, md_ty) = manually_drop(inf.clone());
    let (phantom_def, phantom_ty) = adt(AdtDef::new_struct("core::marker::PhantomData", vec![]));
    let (v_def, v_ty) = adt(AdtDef::new_union("V", vec![pair.clone(), unit()]));
    let (_, v4_ty) = adt(AdtDef::new_union("V4", vec![pair_u32.clone(), u32_ty()]));
    let mu = MaybeUninitTy::new(inf.clone());
    let fields = vec![
        u32_ty(),
        inf.clone(),
        pair.clone(),
        arr(inf.clone(), 1),
        md_ty,
        phantom_ty,
        arr(inf.clone(), 0),
        arr(unit(), 3),
        v_ty.clone(),
        mu.ty.clone(),
        pair_u32.clone(),
        arr(custom_void.clone(), 0),
        arr(custom_void.clone(), 1),
        void_pair.clone(),
        arr(v_ty.clone(), 2),
        v4_ty,
    ];
    let (u_def, u_ty) = adt(AdtDef::new_union("K5159", fields.clone()));
    let f = |idx: usize| field(idx, fields[idx].clone());
    for pw in PWS {
        let decls = vec![u_ty.clone(), Ty::Uint(UintTy::Usize)];
        let mut state = StatementEvalState::from_local_decls(decls, pw);
        let init = MirValue::union_value(&u_def, 0, MirValue::unsigned(42, UintTy::U32, pw));
        state.slots[0] = LocalSlotState::Init(init.clone());
        state.slots[1] = LocalSlotState::Init(MirValue::unsigned(0, UintTy::Usize, pw));
        let inactive = |requested_field: usize| {
            Err(RvalueEvalError::InactiveUnionField {
                active_field: 0,
                requested_field,
            })
        };
        // Inhabited zero-sized fields read their unique value, also when built from
        // `Infallible` or `CustomVoid` (`PhantomData<Infallible>`, `[Infallible; 0]`,
        // `[CustomVoid; 0]`) and inside the inhabited zero-sized union `V` (whose unique value
        // has `y` active).
        assert_eq!(
            state.read_place(&proj(0, vec![f(5)])),
            Ok(MirValue::adt(&phantom_def, 0, vec![]))
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(6)])),
            Ok(MirValue::Array {
                elements: vec![],
                elem_ty: inf.clone(),
            })
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(11)])),
            Ok(MirValue::Array {
                elements: vec![],
                elem_ty: custom_void.clone(),
            })
        );
        assert_eq!(state.read_place(&proj(0, vec![f(7)])), Ok(units(3)));
        assert_eq!(
            state.read_place(&proj(0, vec![f(7), cidx(2, 3)])),
            Ok(MirValue::Unit)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(8)])),
            Ok(MirValue::union_value(&v_def, 1, MirValue::Unit))
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(8), field(1, unit())])),
            Ok(MirValue::Unit)
        );
        assert_eq!(
            state.read_place(&proj(
                0,
                vec![
                    f(14),
                    ProjectionElem::Subslice {
                        from: 0,
                        to: 1,
                        from_end: true,
                    },
                    cidx(0, 1),
                    field(1, unit()),
                ]
            )),
            Ok(MirValue::Unit)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(9), mu.uninit_field()])),
            Ok(MirValue::Unit)
        );
        // Uninhabited fields have no value: reading one is undefined behavior.
        for idx in [1, 2, 3, 4, 10, 12, 13] {
            assert_eq!(
                state.read_place(&proj(0, vec![f(idx)])),
                inactive(idx),
                "field {idx} on {pw:?}"
            );
        }
        // Uninhabited leaf reads through an uninhabited field (`(Infallible, ()).0`,
        // `[Infallible; 1][0]` with constant or dynamic index, `ManuallyDrop<Infallible>.value`,
        // `(Infallible, u32).0`, `[CustomVoid; 1][0]`) are UB in `Trusted.MirSemantics`, while
        // inhabited-leaf reads through an uninhabited container (`(Infallible, ()).1`,
        // `(Infallible, u32).1`, `(CustomVoid, ()).1`) fail closed as `.unsupported` there;
        // both fail closed with `InactiveUnionField` in this value-tree evaluator.
        assert_eq!(
            state.read_place(&proj(0, vec![f(2), field(1, unit())])),
            inactive(2)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(2), field(0, inf.clone())])),
            inactive(2)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(3), cidx(0, 1)])),
            inactive(3)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(3), ProjectionElem::Index(Local(1))])),
            inactive(3)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(4), field(0, inf.clone())])),
            inactive(4)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(10), field(0, inf.clone())])),
            inactive(10)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(10), field(1, u32_ty())])),
            inactive(10)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(12), cidx(0, 1)])),
            inactive(12)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(13), field(1, unit())])),
            inactive(13)
        );
        // Inside `V` (and `[V; 2][0..-1][0]`), the uninhabited field `p` (and
        // `MaybeUninit<Infallible>`'s `value` field) is an uninhabited leaf load (`.ub` in
        // `Trusted.MirSemantics`), while `p.1` and `V4.p.1` have inhabited leaves through an
        // uninhabited container (fail-closed `.unsupported` in `Trusted.MirSemantics`); all
        // fail closed with `InactiveUnionField` here.
        let v_inactive = Err(RvalueEvalError::InactiveUnionField {
            active_field: 1,
            requested_field: 0,
        });
        assert_eq!(
            state.read_place(&proj(0, vec![f(8), field(0, pair.clone())])),
            v_inactive
        );
        assert_eq!(
            state.read_place(&proj(
                0,
                vec![f(8), field(0, pair.clone()), field(1, unit())]
            )),
            v_inactive
        );
        assert_eq!(
            state.read_place(&proj(
                0,
                vec![
                    f(14),
                    ProjectionElem::Subslice {
                        from: 0,
                        to: 1,
                        from_end: true,
                    },
                    cidx(0, 1),
                    field(0, pair.clone()),
                    field(1, unit()),
                ]
            )),
            v_inactive
        );
        assert_eq!(
            state.read_place(&proj(
                0,
                vec![f(15), field(0, pair_u32.clone()), field(1, u32_ty())]
            )),
            inactive(15)
        );
        assert_eq!(
            state.read_place(&proj(0, vec![f(9), field(1, mu.md_ty.clone())])),
            Err(RvalueEvalError::InactiveUnionField {
                active_field: 0,
                requested_field: 1,
            })
        );
        // None of these reads modifies the union.
        assert_eq!(state.get_init(Local(0)), Some(&init));
    }
}

// ---------------------------------------------------------------------------------------------
// Adversarial round ep1-A3 regression tests
// ---------------------------------------------------------------------------------------------

/// `kani#5159` through `copy` / `move` operands and non-static enum `Downcast` sub-projections,
/// mirroring `UnionZst.lean`'s `kani5159_witness_evalPlaceRead` (reads through
/// `Trusted.MirSemantics`' `evalPlaceRead`, the read behind both operands) and
/// `kani5159_witness_fieldRoot_downcast` (an instance of `readUnion_zeroByte_fieldRoot`): assigning
/// from an uninhabited union field, from a place (0-byte or positive-sized) through an uninhabited
/// container, or from an uninhabited variant of an inhabited 0-byte enum union field fails and
/// leaves the destination and the union untouched, while inhabited 0-byte fields, sub-places, and
/// present enum variants assign their unique value.
#[test]
fn a3_kani_5159_operand_reads_of_uninhabited_zero_sized_union_fields_fail() {
    let inf = infallible();
    let pair = Ty::Tuple(vec![inf.clone(), unit()]);
    let pair_u32 = Ty::Tuple(vec![inf.clone(), u32_ty()]);
    let (phantom_def, phantom_ty) = adt(AdtDef::new_struct("core::marker::PhantomData", vec![]));
    let (e_def, e_ty) = adt(AdtDef::new_enum(
        "E",
        None,
        vec![
            VariantDef::new("A", vec![unit()]),
            VariantDef::new("B", vec![inf.clone()]),
        ],
    ));
    // `union K { val: u32, inf: Infallible, pair: (Infallible, ()), phantom:
    // PhantomData<Infallible>, zarr: [(); 3], pair_u32: (Infallible, u32), e: E }`.
    let fields = vec![
        u32_ty(),
        inf.clone(),
        pair.clone(),
        phantom_ty.clone(),
        arr(unit(), 3),
        pair_u32.clone(),
        e_ty.clone(),
    ];
    let (u_def, u_ty) = adt(AdtDef::new_union("K", fields.clone()));
    let f = |idx: usize| field(idx, fields[idx].clone());
    for pw in PWS {
        let decls = vec![
            u_ty.clone(),
            inf.clone(),
            unit(),
            phantom_ty.clone(),
            arr(unit(), 3),
            u32_ty(),
            e_ty.clone(),
        ];
        let mut state = StatementEvalState::from_local_decls(decls, pw);
        let init = MirValue::union_value(&u_def, 0, MirValue::unsigned(42, UintTy::U32, pw));
        state.slots[0] = LocalSlotState::Init(init.clone());
        let inactive = |requested_field: usize| {
            Err(RvalueEvalError::InactiveUnionField {
                active_field: 0,
                requested_field,
            })
        };
        let before = |state: &StatementEvalState, l: usize| state.get_local(Local(l)).cloned();
        let (dst1, dst2, dst5) = (before(&state, 1), before(&state, 2), before(&state, 5));
        // `_1 = copy _0.inf` is undefined behavior (`Infallible` has no value), while
        // `_2 = copy _0.pair.1`, `_2 = move _0.pair.1`, `_5 = copy _0.pair_u32.1`, and
        // `_5 = move _0.pair_u32.1` read inhabited leaves through uninhabited tuples and
        // fail closed as `InactiveUnionField` (`.unsupported` in `readProjectedValueUnionAware`).
        assert_eq!(
            run(assign(local(1), copy_of(proj(0, vec![f(1)]))), &mut state),
            inactive(1),
            "{pw:?}"
        );
        assert_eq!(
            run(
                assign(local(2), copy_of(proj(0, vec![f(2), field(1, unit())]))),
                &mut state
            ),
            inactive(2),
            "{pw:?}"
        );
        assert_eq!(
            run(
                assign(
                    local(2),
                    Rvalue::Use(Operand::Move(proj(0, vec![f(2), field(1, unit())])))
                ),
                &mut state
            ),
            inactive(2),
            "{pw:?}"
        );
        assert_eq!(
            run(
                assign(local(5), copy_of(proj(0, vec![f(5), field(1, u32_ty())]))),
                &mut state
            ),
            inactive(5),
            "{pw:?}"
        );
        assert_eq!(
            run(
                assign(
                    local(5),
                    Rvalue::Use(Operand::Move(proj(0, vec![f(5), field(1, u32_ty())])))
                ),
                &mut state
            ),
            inactive(5),
            "{pw:?}"
        );
        // `(_0.e as B).0` downcasts the inhabited 0-byte enum `E` to its uninhabited variant `B`.
        assert_eq!(
            run(
                assign(
                    local(1),
                    copy_of(proj(
                        0,
                        vec![f(6), ProjectionElem::Downcast(1), field(0, inf.clone())]
                    ))
                ),
                &mut state
            ),
            Err(RvalueEvalError::InactiveVariantProjection {
                expected: 1,
                actual: 0,
            }),
            "{pw:?}"
        );
        assert_eq!(before(&state, 1), dst1, "{pw:?}");
        assert_eq!(before(&state, 2), dst2, "{pw:?}");
        assert_eq!(before(&state, 5), dst5, "{pw:?}");
        // `_3 = copy _0.phantom`, `_4 = copy _0.zarr`, `_2 = copy _0.zarr[2]`, `_6 = copy _0.e`,
        // and `_2 = copy (_0.e as A).0` assign the unique values of the inhabited zero-sized
        // fields and sub-places.
        run(assign(local(3), copy_of(proj(0, vec![f(3)]))), &mut state).unwrap();
        assert_eq!(
            state.get_init(Local(3)),
            Some(&MirValue::adt(&phantom_def, 0, vec![]))
        );
        run(assign(local(4), copy_of(proj(0, vec![f(4)]))), &mut state).unwrap();
        assert_eq!(state.get_init(Local(4)), Some(&units(3)));
        run(
            assign(local(2), copy_of(proj(0, vec![f(4), cidx(2, 3)]))),
            &mut state,
        )
        .unwrap();
        assert_eq!(state.get_init(Local(2)), Some(&MirValue::Unit));
        run(assign(local(6), copy_of(proj(0, vec![f(6)]))), &mut state).unwrap();
        assert_eq!(
            state.get_init(Local(6)),
            Some(&MirValue::adt(&e_def, 0, vec![MirValue::Unit]))
        );
        run(
            assign(
                local(2),
                copy_of(proj(
                    0,
                    vec![f(6), ProjectionElem::Downcast(0), field(0, unit())],
                )),
            ),
            &mut state,
        )
        .unwrap();
        assert_eq!(state.get_init(Local(2)), Some(&MirValue::Unit));
        assert_eq!(state.get_init(Local(0)), Some(&init));
    }
}
