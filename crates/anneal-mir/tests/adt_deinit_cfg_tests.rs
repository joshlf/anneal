//! Episode 1 (`ws-mir-lower-adt-deinit-retag-terminators`) tests: first-class `Ty::Adt` layouts,
//! `ScalarValidRange` niches, `OffsetOf`, `Discriminant`, transmutes, `Statement::{Deinit,
//! Retag, CopyNonOverlapping}`, `Rvalue::{ShallowInitBox, WrapUnsafeBinder}`,
//! `CastKind::{Subtype, PointerCoercion}`, and the `Terminator` CFG evaluator.
//!
//! Layout expectations marked "rustc" were observed with `size_of`/`align_of`/`offset_of!` on the
//! workspace toolchain (`rustc 1.98.0-nightly`, `x86_64-unknown-linux-gnu`).

use std::sync::Arc;

use anneal_mir::ir::{
    AdtDef, AdtKind, AdtRepr, AdtReprKind, AggregateKind, AssertMessage, BasicBlockData, BinOp,
    Body, CastKind, Constant, IntTy, LayoutError, Local, Mutability, NullOp, Operand, Place,
    PointerCoercionKind, PointerValue, ProjectionElem, PtrWidth, RetagKind, Rvalue, ScalarTy,
    ScalarValidRange, Statement, SwitchTargets, Terminator, Ty, TyLayout, UintTy, UnwindAction,
    VariantDef, width_mask,
};
use anneal_mir::lower::{
    CallOutcome, CastEvalError, CastLowerError, CastOp, CfgEvalError, CfgEvalOutcome, CfgStep,
    ExposedProvenanceTracker, LocalSlotState, LoweredBasicBlock, LoweredBody, LoweredCast,
    LoweredRvalue, LoweredStatement, LoweredTerminator, MirValue, PanicMessage, PartialAggregate,
    RvalueEvalError, RvalueLowerError, StatementEvalState, TerminatorLowerError, TransmutePolicy,
    TransmuteValue, UnwindState, eval_cfg_in_state, eval_lowered_body_cfg,
    eval_lowered_body_cfg_with_calls, eval_lowered_rvalue, eval_lowered_rvalue_in_state,
    eval_lowered_statement, eval_lowered_terminator, eval_place_read, eval_place_write,
    eval_transmute, lower_body, lower_rvalue, lower_statement, lower_terminator,
    resolve_offset_of, resolve_place_ty,
};

const PW: PtrWidth = PtrWidth::Bits64;

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
fn u64_ty() -> Ty {
    Ty::Uint(UintTy::U64)
}
fn usize_ty() -> Ty {
    Ty::Uint(UintTy::Usize)
}
fn i8_ty() -> Ty {
    Ty::Int(IntTy::I8)
}
fn i16_ty() -> Ty {
    Ty::Int(IntTy::I16)
}
fn uint(v: u128, ty: Ty) -> MirValue {
    MirValue::Int { bits: v, ty }
}
fn u8v(v: u128) -> MirValue {
    uint(v, u8_ty())
}
fn u16v(v: u128) -> MirValue {
    uint(v, u16_ty())
}
fn u32v(v: u128) -> MirValue {
    uint(v, u32_ty())
}
fn usizev(v: u128) -> MirValue {
    uint(v, usize_ty())
}
fn cint(v: u128, ty: Ty) -> Operand {
    Operand::Constant(Constant::Int(v, ty))
}
fn field(idx: usize, ty: Ty) -> ProjectionElem {
    ProjectionElem::Field(idx, ty)
}
fn place(local: usize, projection: Vec<ProjectionElem>) -> Place {
    Place::with_projection(local, projection)
}
fn local(l: usize) -> Place {
    Place::from_local(l)
}
fn unit() -> Ty {
    Ty::unit()
}
fn ref_ty(pointee: Ty) -> Ty {
    Ty::Ref(Box::new(pointee), Mutability::Not)
}
fn raw(pointee: Ty, m: Mutability) -> Ty {
    Ty::RawPtr(Box::new(pointee), m)
}
fn adt(def: AdtDef) -> (Arc<AdtDef>, Ty) {
    let arc = Arc::new(def);
    (arc.clone(), Ty::Adt(arc))
}
fn layout(ty: &Ty, pw: PtrWidth) -> TyLayout {
    ty.layout_for(pw)
        .unwrap_or_else(|e| panic!("layout of {ty:?}: {e:?}"))
}
fn offset(ty: &Ty, path: &[(usize, usize)]) -> Result<usize, RvalueLowerError> {
    resolve_offset_of(ty, path, PW)
}
fn run(stmt: Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = lower_statement(&stmt, &state.local_decls, state.ptr_width)
        .unwrap_or_else(|e| panic!("lowering {stmt:?}: {e:?}"));
    eval_lowered_statement(&lowered, state)
}
fn assign(p: Place, rv: Rvalue) -> Statement {
    Statement::Assign(p, rv)
}
fn read(state: &StatementEvalState, p: &Place) -> Result<MirValue, RvalueEvalError> {
    state.read_place(p)
}
fn discriminant(state: &mut StatementEvalState, p: Place) -> Result<MirValue, RvalueEvalError> {
    let rv = lower_rvalue(
        &Rvalue::Discriminant(p),
        &state.local_decls,
        state.ptr_width,
    )
    .unwrap();
    eval_lowered_rvalue_in_state(&rv, state)
}
fn state_with(decls: Vec<Ty>, pw: PtrWidth) -> StatementEvalState {
    StatementEvalState::from_local_decls(decls, pw)
}

/// `NonZeroU32` (`#[rustc_layout_scalar_valid_range_start(1)] struct(u32)`).
fn non_zero_u32() -> (Arc<AdtDef>, Ty) {
    adt(AdtDef::new_struct("NonZeroU32", vec![u32_ty()])
        .with_repr(AdtRepr::transparent())
        .with_scalar_valid_range(ScalarValidRange::non_zero(32)))
}

/// `#[repr(u8)] enum E { A(u8, u32), B(u16) }`.
fn repr_u8_enum() -> (Arc<AdtDef>, Ty) {
    adt(AdtDef::new_enum(
        "ReprU8",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u8_ty(), u32_ty()]),
            VariantDef::new("B", vec![u16_ty()]),
        ],
    ))
}

/// `enum Opt { None, Some(u32) }` (tagless, multi-variant: unspecified layout).
fn rust_option_u32() -> (Arc<AdtDef>, Ty) {
    adt(AdtDef::new_enum(
        "Opt",
        None,
        vec![
            VariantDef::new("None", vec![]),
            VariantDef::new("Some", vec![u32_ty()]),
        ],
    ))
}

// ---------------------------------------------------------------------------------------------
// ScalarValidRange
// ---------------------------------------------------------------------------------------------

/// Brute-force model of `ScalarValidRange` membership.
fn model_contains(start: u128, end: u128, bits: u128, width: u32) -> bool {
    let mask = width_mask(width);
    bits <= mask
        && if start <= end {
            start <= bits && bits <= end
        } else {
            bits >= start || bits <= end
        }
}

#[test]
fn test_scalar_valid_range_matches_brute_force_model_for_small_widths() {
    let mut seed = 0x1234_5678_9abc_def0u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for width in 1..=10u32 {
        let mask = width_mask(width);
        for _ in 0..60 {
            // Bounds sometimes exceed the width to exercise clipping.
            let start = u128::from(next()) % (mask + 4);
            let end = u128::from(next()) % (mask + 4);
            let range = ScalarValidRange::new(start, end);
            let members: Vec<u128> = (0..=mask + 2)
                .filter(|&b| model_contains(start, end, b, width))
                .collect();
            for bits in 0..=mask + 2 {
                assert_eq!(
                    range.contains(bits, width),
                    model_contains(start, end, bits, width),
                    "{range:?} contains {bits} at width {width}"
                );
            }
            assert_eq!(
                range.is_empty(width),
                members.is_empty(),
                "{range:?} empty @{width}"
            );
            assert_eq!(
                range.is_full(width),
                members.len() as u128 == mask + 1,
                "{range:?} full @{width}"
            );
            let from_intervals: Vec<u128> = range
                .intervals(width)
                .iter()
                .flat_map(|&(a, b)| a..=b)
                .collect();
            assert_eq!(from_intervals, members, "{range:?} intervals @{width}");
            assert_eq!(range.is_wrapping(), start > end);
        }
    }
}

#[test]
fn test_scalar_valid_range_full_width_128_and_non_zero_niches() {
    // Width 128 must not evaluate `1u128 << 128`.
    assert_eq!(width_mask(128), u128::MAX);
    assert_eq!(width_mask(0), 0);
    let full = ScalarValidRange::full(128);
    assert!(full.contains(0, 128) && full.contains(u128::MAX, 128));
    assert!(full.is_full(128) && !full.is_empty(128));
    let nz128 = ScalarValidRange::non_zero(128);
    assert!(!nz128.contains(0, 128));
    assert!(nz128.contains(1, 128) && nz128.contains(u128::MAX, 128));
    assert!(!nz128.is_full(128));
    assert_eq!(nz128.intervals(128), vec![(1, u128::MAX)]);
    let nz8 = ScalarValidRange::non_zero(8);
    assert!(!nz8.contains(0, 8) && nz8.contains(255, 8) && !nz8.contains(256, 8));
    // A wrapping range `250..=5` at width 8 holds 250..=255 and 0..=5, and always contains 0.
    let wrap = ScalarValidRange::new(250, 5);
    assert!(wrap.is_wrapping());
    assert!(wrap.contains(0, 8) && wrap.contains(5, 8) && wrap.contains(250, 8));
    assert!(!wrap.contains(6, 8) && !wrap.contains(249, 8));
    assert_eq!(wrap.intervals(8), vec![(0, 5), (250, 255)]);
    assert!(!wrap.is_empty(1));
    // Wrapping `u128::MAX..=0` at width 128 contains exactly {0, MAX}.
    let edge = ScalarValidRange::new(u128::MAX, 0);
    assert!(edge.contains(0, 128) && edge.contains(u128::MAX, 128) && !edge.contains(1, 128));
    // Non-wrapping ranges entirely above the width are empty; wrapping ones never are.
    assert!(ScalarValidRange::new(300, 400).is_empty(8));
    assert!(!ScalarValidRange::new(300, 5).is_empty(8));
    // `start == end + 1` wraps around every value.
    assert!(ScalarValidRange::new(100, 99).is_full(8));
}

// ---------------------------------------------------------------------------------------------
// Ty::Adt layouts (checked against rustc)
// ---------------------------------------------------------------------------------------------

#[test]
fn test_adt_layouts_match_rustc_repr_int_repr_c_int_transparent_unions() {
    // #[repr(u8)] enum ReprU8 { A(u8, u32), B(u16) }: size 8, align 4, A.0=1, A.1=4, B.0=2.
    let (_, repr_u8) = repr_u8_enum();
    assert_eq!(layout(&repr_u8, PW), TyLayout { size: 8, align: 4 });
    assert_eq!(offset(&repr_u8, &[(0, 0)]), Ok(1));
    assert_eq!(offset(&repr_u8, &[(0, 1)]), Ok(4));
    assert_eq!(offset(&repr_u8, &[(1, 0)]), Ok(2));

    // #[repr(C, u8)] enum ReprCU8 { A(u8, u32), B(u16) }: size 12, align 4, A.0=4, A.1=8, B.0=4.
    let (_, repr_c_u8) = adt(AdtDef::new_enum(
        "ReprCU8",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u8_ty(), u32_ty()]),
            VariantDef::new("B", vec![u16_ty()]),
        ],
    )
    .with_repr(AdtRepr::c()));
    assert_eq!(layout(&repr_c_u8, PW), TyLayout { size: 12, align: 4 });
    assert_eq!(offset(&repr_c_u8, &[(0, 0)]), Ok(4));
    assert_eq!(offset(&repr_c_u8, &[(0, 1)]), Ok(8));
    assert_eq!(offset(&repr_c_u8, &[(1, 0)]), Ok(4));

    // #[repr(u16)] enum { A = 1, B = 7 }: size 2, align 2.
    let (_, fieldless) = adt(AdtDef::new_enum(
        "ReprU16Fieldless",
        Some(ScalarTy::Uint(UintTy::U16)),
        vec![
            VariantDef::new("A", vec![]).with_discriminant(1),
            VariantDef::new("B", vec![]).with_discriminant(7),
        ],
    ));
    assert_eq!(layout(&fieldless, PW), TyLayout { size: 2, align: 2 });

    // #[repr(transparent)] struct W2(u32, PhantomData<u8>): size 4, offsets 0 and 4.
    let (_, w2) =
        adt(AdtDef::new_struct("W2", vec![u32_ty(), unit()]).with_repr(AdtRepr::transparent()));
    assert_eq!(layout(&w2, PW), TyLayout { size: 4, align: 4 });
    assert_eq!(offset(&w2, &[(0, 0)]), Ok(0));
    assert_eq!(offset(&w2, &[(0, 1)]), Ok(4));
    // #[repr(transparent)] struct W(PhantomData<u8>, u32): the u32 is at 0, but rustc moves
    // the leading 1-ZST to offset 4, so its offset fails closed instead of guessing.
    let (_, w) =
        adt(AdtDef::new_struct("W", vec![unit(), u32_ty()]).with_repr(AdtRepr::transparent()));
    assert_eq!(offset(&w, &[(0, 1)]), Ok(0));
    assert_eq!(
        offset(&w, &[(0, 0)]),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(w.clone()))
    );
    // All-1-ZST transparent struct: size 0, every field at 0.
    let (_, zst) =
        adt(AdtDef::new_struct("Z", vec![unit(), unit()]).with_repr(AdtRepr::transparent()));
    assert_eq!(layout(&zst, PW), TyLayout { size: 0, align: 1 });
    assert_eq!(offset(&zst, &[(0, 1)]), Ok(0));

    // struct S(u32, ()) => offsets 0, 4; struct S2((), u32) => reordered (unspecified).
    let (_, s) = adt(AdtDef::new_struct("S", vec![u32_ty(), unit()]));
    assert_eq!(offset(&s, &[(0, 1)]), Ok(4));
    let (_, s2) = adt(AdtDef::new_struct("S2", vec![unit(), u32_ty()]));
    assert_eq!(layout(&s2, PW), TyLayout { size: 4, align: 4 });
    assert_eq!(
        offset(&s2, &[(0, 1)]),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(s2.clone()))
    );

    // #[repr(C)] struct C1 { a: u8, b: u32, c: u16 }: size 12, offsets 0, 4, 8 (with padding).
    let (_, c1) =
        adt(AdtDef::new_struct("C1", vec![u8_ty(), u32_ty(), u16_ty()]).with_repr(AdtRepr::c()));
    assert_eq!(layout(&c1, PW), TyLayout { size: 12, align: 4 });
    assert_eq!(
        (0..3)
            .map(|i| offset(&c1, &[(0, i)]).unwrap())
            .collect::<Vec<_>>(),
        vec![0, 4, 8]
    );
    // #[repr(C, align(16))] struct C2 { a: u8 }: size 16, align 16.
    let (_, c2) =
        adt(AdtDef::new_struct("C2", vec![u8_ty()]).with_repr(AdtRepr::c().with_align(16)));
    assert_eq!(
        layout(&c2, PW),
        TyLayout {
            size: 16,
            align: 16
        }
    );
    // #[repr(align(8))] struct RA(u8, u8): size 8, align 8.
    let (_, ra) =
        adt(AdtDef::new_struct("RA", vec![u8_ty(), u8_ty()])
            .with_repr(AdtRepr::rust().with_align(8)));
    assert_eq!(layout(&ra, PW), TyLayout { size: 8, align: 8 });
    assert_eq!(offset(&ra, &[(0, 1)]), Ok(1));

    // union U1 { a: u8, b: u32 }: size 4, align 4, every field at 0.
    let (_, u1) = adt(AdtDef::new_union("U1", vec![u8_ty(), u32_ty()]));
    assert_eq!(layout(&u1, PW), TyLayout { size: 4, align: 4 });
    assert_eq!(offset(&u1, &[(0, 1)]), Ok(0));
    // #[repr(C)] union U2 { a: [u8; 5], b: u32 }: size 8, align 4.
    let (_, u2) = adt(
        AdtDef::new_union("U2", vec![Ty::Array(Box::new(u8_ty()), 5), u32_ty()])
            .with_repr(AdtRepr::c()),
    );
    assert_eq!(layout(&u2, PW), TyLayout { size: 8, align: 4 });
    // #[repr(align(16))] union U3 { a: u8 }: size 16, align 16.
    let (_, u3) =
        adt(AdtDef::new_union("U3", vec![u8_ty()]).with_repr(AdtRepr::rust().with_align(16)));
    assert_eq!(
        layout(&u3, PW),
        TyLayout {
            size: 16,
            align: 16
        }
    );

    // enum Single { A = 5 }: size 0. enum SingleData { A(u32, u8) }: size 8 (offsets fail closed:
    // the field tuple has tail padding, so its order is not canonical).
    let (_, single) = adt(AdtDef::new_enum(
        "Single",
        None,
        vec![VariantDef::new("A", vec![]).with_discriminant(5)],
    ));
    assert_eq!(layout(&single, PW), TyLayout { size: 0, align: 1 });
    let (_, single_data) = adt(AdtDef::new_enum(
        "SingleData",
        None,
        vec![VariantDef::new("A", vec![u32_ty(), u8_ty()])],
    ));
    assert_eq!(layout(&single_data, PW), TyLayout { size: 8, align: 4 });
    assert_eq!(
        offset(&single_data, &[(0, 1)]),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(
            single_data.clone()
        ))
    );

    // #[repr(u8)] enum { A(!), B }: size 1. enum Void {}: size 0, align 1.
    let (_, uninhabited_variant) = adt(AdtDef::new_enum(
        "ReprU8Uninhabited",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![Ty::Never]),
            VariantDef::new("B", vec![]),
        ],
    ));
    assert_eq!(
        layout(&uninhabited_variant, PW),
        TyLayout { size: 1, align: 1 }
    );
    let (_, void) = adt(AdtDef::new_enum("Void", None, vec![]));
    assert_eq!(layout(&void, PW), TyLayout { size: 0, align: 1 });

    // #[repr(C, u16)] enum { A(u16), B(i16) }: size 4, A.0 = B.0 = 2.
    let (_, c_u16_same) = adt(AdtDef::new_enum(
        "ReprCU16Same",
        Some(ScalarTy::Uint(UintTy::U16)),
        vec![
            VariantDef::new("A", vec![u16_ty()]),
            VariantDef::new("B", vec![i16_ty()]),
        ],
    )
    .with_repr(AdtRepr::c()));
    assert_eq!(layout(&c_u16_same, PW), TyLayout { size: 4, align: 2 });
    assert_eq!(offset(&c_u16_same, &[(1, 0)]), Ok(2));
    // #[repr(u8)] enum { A(u8, u16) }: size 4, A.0 = 1, A.1 = 2.
    let (_, pad) = adt(AdtDef::new_enum(
        "ReprU8Pad",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![VariantDef::new("A", vec![u8_ty(), u16_ty()])],
    ));
    assert_eq!(layout(&pad, PW), TyLayout { size: 4, align: 2 });
    assert_eq!(offset(&pad, &[(0, 1)]), Ok(2));
    // #[repr(u32)] enum { A(u8), B(u64) }: size 16, align 8, A.0 = 4, B.0 = 8.
    let (_, big) = adt(AdtDef::new_enum(
        "ReprU32Big",
        Some(ScalarTy::Uint(UintTy::U32)),
        vec![
            VariantDef::new("A", vec![u8_ty()]),
            VariantDef::new("B", vec![u64_ty()]),
        ],
    ));
    assert_eq!(layout(&big, PW), TyLayout { size: 16, align: 8 });
    assert_eq!(offset(&big, &[(0, 0)]), Ok(4));
    assert_eq!(offset(&big, &[(1, 0)]), Ok(8));
    // #[repr(C, u8)] enum { A(u8), B(u64) }: size 16, align 8, A.0 = B.0 = 8.
    let (_, c_big) = adt(AdtDef::new_enum(
        "ReprCU8Big",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u8_ty()]),
            VariantDef::new("B", vec![u64_ty()]),
        ],
    )
    .with_repr(AdtRepr::c()));
    assert_eq!(layout(&c_big, PW), TyLayout { size: 16, align: 8 });
    assert_eq!(offset(&c_big, &[(0, 0)]), Ok(8));

    // Multi-variant tagless enums (repr(Rust) niche/tag optimization, repr(C)'s C `int`) have
    // unspecified layouts: representable, but `size_of`/`align_of`/`offset_of!` fail closed.
    let (_, opt) = rust_option_u32();
    assert_eq!(opt.layout_for(PW), Err(LayoutError::Unspecified));
    assert_eq!(opt.check_representable(PW), Ok(()));
    assert_eq!(opt.layout_size_for(PW), None);
    let (_, c_fieldless) = adt(AdtDef::new_enum(
        "ReprCFieldless",
        None,
        vec![VariantDef::new("A", vec![]), VariantDef::new("B", vec![])],
    )
    .with_repr(AdtRepr::c()));
    assert_eq!(c_fieldless.layout_for(PW), Err(LayoutError::Unspecified));
    for op in [NullOp::SizeOf, NullOp::AlignOf] {
        assert_eq!(
            lower_rvalue(&Rvalue::NullaryOp(op, opt.clone()), &[], PW),
            Err(RvalueLowerError::UnsupportedLayout(opt.clone()))
        );
    }
    assert_eq!(
        offset(&opt, &[(1, 0)]),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(opt.clone()))
    );
    // ... but locals of such types are fine, and alignment bounds bracket rustc's choice.
    assert_eq!(opt.align_bounds(PW), Ok((4, 4)));
}

#[test]
fn test_adt_layouts_depend_on_pointer_width() {
    // #[repr(C)] struct { a: u8, p: *const u8 } is 16 bytes on 64-bit and 8 on 32-bit.
    let (_, s) = adt(
        AdtDef::new_struct("P", vec![u8_ty(), raw(u8_ty(), Mutability::Not)])
            .with_repr(AdtRepr::c()),
    );
    assert_eq!(
        layout(&s, PtrWidth::Bits64),
        TyLayout { size: 16, align: 8 }
    );
    assert_eq!(layout(&s, PtrWidth::Bits32), TyLayout { size: 8, align: 4 });
    assert_eq!(resolve_offset_of(&s, &[(0, 1)], PtrWidth::Bits32), Ok(4));
    assert_eq!(resolve_offset_of(&s, &[(0, 1)], PtrWidth::Bits64), Ok(8));
    // #[repr(isize)] enum discriminants must fit the target's isize.
    let (_, wide) = adt(AdtDef::new_enum(
        "Wide",
        Some(ScalarTy::Int(IntTy::Isize)),
        vec![VariantDef::new("A", vec![]).with_discriminant(1 << 40)],
    ));
    assert_eq!(
        layout(&wide, PtrWidth::Bits64),
        TyLayout { size: 8, align: 8 }
    );
    assert!(matches!(
        wide.layout_for(PtrWidth::Bits32),
        Err(LayoutError::IllFormed(_))
    ));
    // Sizes above the target's isize::MAX are too large, also inside ADTs.
    let (_, huge) = adt(AdtDef::new_struct(
        "Huge",
        vec![Ty::Array(Box::new(u8_ty()), 0x8000_0000)],
    ));
    assert_eq!(
        huge.layout_for(PtrWidth::Bits32),
        Err(LayoutError::TooLarge)
    );
    assert_eq!(layout(&huge, PtrWidth::Bits64).size, 0x8000_0000);
    let (_, huge_union) = adt(AdtDef::new_union(
        "HugeU",
        vec![Ty::Array(Box::new(u8_ty()), usize::MAX / 2), u16_ty()],
    ));
    assert_eq!(huge_union.layout_for(PW), Err(LayoutError::TooLarge));
    assert_eq!(
        huge_union.check_representable(PW),
        Err(LayoutError::TooLarge)
    );
}

#[test]
fn test_ill_formed_adt_definitions_fail_closed() {
    let ill = |def: AdtDef| {
        let ty = Ty::adt(def);
        let err = ty.layout_for(PW);
        assert!(
            matches!(err, Err(LayoutError::IllFormed(_))),
            "{ty:?}: {err:?}"
        );
        // Lowering a body with such a local fails with InvalidAdtDef.
        let body = Body {
            local_decls: vec![ty.clone()],
            basic_blocks: vec![],
        };
        assert!(matches!(
            lower_body(&body, PW),
            Err(RvalueLowerError::InvalidAdtDef { .. })
        ));
    };
    // repr(align) must be a power of two.
    ill(AdtDef::new_struct("A3", vec![u8_ty()]).with_repr(AdtRepr::c().with_align(3)));
    ill(AdtDef::new_struct("A0", vec![u8_ty()]).with_repr(AdtRepr::c().with_align(0)));
    // repr(transparent): at most one field with non-trivial size or alignment (a zero-sized
    // field with alignment above 1, like `[u64; 0]`, counts), and no repr(align).
    ill(AdtDef::new_struct("T2", vec![u32_ty(), u32_ty()]).with_repr(AdtRepr::transparent()));
    ill(
        AdtDef::new_struct("TZ", vec![u32_ty(), Ty::Array(Box::new(u64_ty()), 0)])
            .with_repr(AdtRepr::transparent()),
    );
    ill(AdtDef::new_struct("TA", vec![u32_ty()]).with_repr(AdtRepr::transparent().with_align(8)));
    ill(AdtDef::new_enum(
        "TE",
        None,
        vec![VariantDef::new("A", vec![]), VariantDef::new("B", vec![])],
    )
    .with_repr(AdtRepr::transparent()));
    ill(AdtDef::new_union("TU", vec![u32_ty(), u16_ty()]).with_repr(AdtRepr::transparent()));
    // Enum tags must be integers; discriminants must fit, not overflow, and be distinct.
    ill(AdtDef::new_enum(
        "BoolTag",
        Some(ScalarTy::Bool),
        vec![VariantDef::new("A", vec![])],
    ));
    ill(AdtDef::new_enum(
        "Overflow",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![]).with_discriminant(255),
            VariantDef::new("B", vec![]),
        ],
    ));
    ill(AdtDef::new_enum(
        "SignedOverflow",
        Some(ScalarTy::Int(IntTy::I8)),
        vec![
            VariantDef::new("A", vec![]).with_discriminant(127),
            VariantDef::new("B", vec![]),
        ],
    ));
    ill(AdtDef::new_enum(
        "TooBig",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![VariantDef::new("A", vec![]).with_discriminant(256)],
    ));
    ill(AdtDef::new_enum(
        "TooNegative",
        Some(ScalarTy::Int(IntTy::I8)),
        vec![VariantDef::new("A", vec![]).with_discriminant((-129i128) as u128)],
    ));
    ill(AdtDef::new_enum(
        "Duplicate",
        None,
        vec![
            VariantDef::new("A", vec![]).with_discriminant(1),
            VariantDef::new("B", vec![]).with_discriminant(0),
            VariantDef::new("C", vec![]),
        ],
    ));
    // Unions need a field; scalar ranges need a single scalar field of a struct.
    ill(AdtDef::new_union("Empty", vec![]));
    ill(AdtDef::new_struct("Pair", vec![u8_ty(), u8_ty()])
        .with_scalar_valid_range(ScalarValidRange::non_zero(8)));
    ill(
        AdtDef::new_struct("Arr", vec![Ty::Array(Box::new(u8_ty()), 1)])
            .with_scalar_valid_range(ScalarValidRange::non_zero(8)),
    );
    ill(
        AdtDef::new_enum("E", None, vec![VariantDef::new("A", vec![u8_ty()])])
            .with_scalar_valid_range(ScalarValidRange::non_zero(8)),
    );

    // Signed discriminants given sign-extended are masked; sequential ones continue from them.
    let (def, _) = adt(AdtDef::new_enum(
        "ReprI8",
        Some(ScalarTy::Int(IntTy::I8)),
        vec![
            VariantDef::new("A", vec![]).with_discriminant(u128::MAX),
            VariantDef::new("B", vec![]),
            VariantDef::new("C", vec![]).with_discriminant(5),
        ],
    ));
    assert_eq!(def.discriminants(PW), Ok(vec![0xFF, 0x00, 0x05]));
    assert_eq!(def.discr_ty(), i8_ty());
    assert_eq!(def.variant_index_of_discriminant(0xFF, PW), Some(0));
    // ZST fields beside the scalar of a niche struct are fine (e.g. PhantomData).
    let (_, nz_phantom) = adt(AdtDef::new_struct("NzP", vec![unit(), u32_ty()])
        .with_repr(AdtRepr::transparent())
        .with_scalar_valid_range(ScalarValidRange::non_zero(32)));
    assert_eq!(layout(&nz_phantom, PW), TyLayout { size: 4, align: 4 });
}

/// Reference copy of the pre-ADT `Ty::layout_size_for` algorithm for non-ADT types.
fn legacy_layout_size(ty: &Ty, pw: PtrWidth) -> Option<usize> {
    let size = match ty {
        Ty::Array(elem, count) => {
            if (*count as u128) > pw.max_usize() {
                return None;
            }
            legacy_layout_size(elem, pw)?.checked_mul(*count)?
        }
        Ty::Tuple(fields) => {
            let mut unpadded = 0usize;
            for f in fields {
                unpadded = unpadded.checked_add(legacy_layout_size(f, pw)?)?;
            }
            unpadded.checked_next_multiple_of(ty.align_for(pw))?
        }
        _ => ty.byte_size_for(pw),
    };
    ((size as u128) <= pw.max_object_size()).then_some(size)
}

#[test]
fn test_layout_engine_agrees_with_legacy_layout_for_non_adt_types() {
    let mut seed = 0xfeed_beef_u64;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    fn gen_ty(depth: u32, next: &mut dyn FnMut() -> u64) -> Ty {
        let leaves = [
            Ty::Bool,
            Ty::Char,
            Ty::Uint(UintTy::U8),
            Ty::Int(IntTy::I16),
            Ty::Uint(UintTy::U64),
            Ty::Int(IntTy::Isize),
            Ty::Uint(UintTy::U128),
            Ty::Never,
            Ty::RawPtr(Box::new(Ty::Bool), Mutability::Mut),
        ];
        if depth == 0 || next().is_multiple_of(3) {
            return leaves[(next() % leaves.len() as u64) as usize].clone();
        }
        if next().is_multiple_of(2) {
            let counts = [0usize, 1, 3, 1 << 20, usize::MAX / 4, usize::MAX];
            Ty::Array(
                Box::new(gen_ty(depth - 1, next)),
                counts[(next() % 6) as usize],
            )
        } else {
            let n = (next() % 4) as usize;
            Ty::Tuple((0..n).map(|_| gen_ty(depth - 1, next)).collect())
        }
    }
    for _ in 0..3000 {
        let ty = gen_ty(4, &mut next);
        for pw in [PtrWidth::Bits32, PtrWidth::Bits64] {
            assert_eq!(
                ty.layout_size_for(pw),
                legacy_layout_size(&ty, pw),
                "{ty:?} @ {pw:?}"
            );
            if let Ok(l) = ty.layout_for(pw) {
                assert_eq!(l.align, ty.align_for(pw));
            }
        }
    }
}

/// Generates random small ADTs (and types containing them) for layout property checks.
struct AdtGen {
    seed: u64,
}

impl AdtGen {
    fn next(&mut self) -> u64 {
        self.seed ^= self.seed << 13;
        self.seed ^= self.seed >> 7;
        self.seed ^= self.seed << 17;
        self.seed
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn leaf(&mut self) -> Ty {
        let leaves = [
            u8_ty(),
            u16_ty(),
            u32_ty(),
            u64_ty(),
            Ty::Bool,
            Ty::Char,
            i8_ty(),
            usize_ty(),
            unit(),
            Ty::Array(Box::new(u8_ty()), 3),
            raw(u8_ty(), Mutability::Not),
        ];
        leaves[self.below(leaves.len() as u64) as usize].clone()
    }
    fn ty(&mut self, depth: u32) -> Ty {
        if depth == 0 || self.below(3) == 0 {
            return self.leaf();
        }
        match self.below(4) {
            0 => {
                let n = self.below(4) as usize;
                Ty::Tuple((0..n).map(|_| self.ty(depth - 1)).collect())
            }
            _ => Ty::adt(self.adt(depth - 1)),
        }
    }
    fn repr(&mut self) -> AdtRepr {
        let kind = [AdtReprKind::Rust, AdtReprKind::C][self.below(2) as usize];
        let align = [None, None, None, Some(2), Some(16)][self.below(5) as usize];
        AdtRepr { kind, align }
    }
    fn adt(&mut self, depth: u32) -> AdtDef {
        match self.below(3) {
            0 => {
                let n = self.below(4) as usize;
                let fields = (0..n).map(|_| self.ty(depth)).collect();
                AdtDef::new_struct("S", fields).with_repr(self.repr())
            }
            1 => {
                let n = 1 + self.below(3) as usize;
                let fields = (0..n).map(|_| self.ty(depth)).collect();
                AdtDef::new_union("U", fields).with_repr(self.repr())
            }
            _ => {
                let tags = [
                    Some(ScalarTy::Uint(UintTy::U8)),
                    Some(ScalarTy::Int(IntTy::I16)),
                    Some(ScalarTy::Uint(UintTy::U32)),
                    None,
                ];
                let tag = tags[self.below(4) as usize];
                let n = if tag.is_none() {
                    1
                } else {
                    1 + self.below(3) as usize
                };
                let variants = (0..n)
                    .map(|v| {
                        let m = self.below(3) as usize;
                        VariantDef::new(format!("V{v}"), (0..m).map(|_| self.ty(depth)).collect())
                    })
                    .collect();
                AdtDef::new_enum("E", tag, variants).with_repr(self.repr())
            }
        }
    }
}

#[test]
fn test_property_adt_field_offsets_are_in_bounds_aligned_and_non_overlapping() {
    let mut g = AdtGen { seed: 0x5eed_0001 };
    let mut checked = 0usize;
    for _ in 0..4000 {
        let def = Arc::new(g.adt(3));
        let ty = Ty::Adt(def.clone());
        for pw in [PtrWidth::Bits32, PtrWidth::Bits64] {
            let Ok(container) = ty.layout_for(pw) else {
                continue;
            };
            assert!(container.align.is_power_of_two());
            assert!(container.size.is_multiple_of(container.align), "{ty:?}");
            for v in 0..def.variant_count() {
                let fields = def.variant_fields(v).unwrap();
                let mut spans = Vec::new();
                for (i, field_ty) in fields.iter().enumerate() {
                    let Ok(off) = def.field_offset(v, i, pw) else {
                        continue;
                    };
                    let fl = field_ty.layout_for(pw).unwrap();
                    assert!(off + fl.size <= container.size, "{ty:?} v{v}.{i} @ {pw:?}");
                    assert!(off.is_multiple_of(fl.align), "{ty:?} v{v}.{i} @ {pw:?}");
                    if def.is_union() {
                        assert_eq!(off, 0);
                    }
                    if let AdtKind::Enum {
                        tag_ty: Some(tag), ..
                    } = &def.kind
                    {
                        assert!(off >= tag.size_bytes(pw), "{ty:?}: field overlaps the tag");
                    }
                    assert_eq!(resolve_offset_of(&ty, &[(v, i)], pw), Ok(off));
                    spans.push((off, off + fl.size));
                    checked += 1;
                }
                if !def.is_union() {
                    spans.sort();
                    for w in spans.windows(2) {
                        assert!(w[0].1 <= w[1].0, "{ty:?}: overlapping fields {spans:?}");
                    }
                }
            }
            // A canonical layout is exactly the declaration-order concatenation of its fields.
            if ty.has_canonical_byte_layout(pw)
                && let AdtKind::Struct { fields } = &def.kind
            {
                let total: usize = fields.iter().map(|f| f.layout_for(pw).unwrap().size).sum();
                assert_eq!(total, container.size, "{ty:?}");
            }
        }
    }
    assert!(checked > 2000, "only {checked} offsets checked");
}

// ---------------------------------------------------------------------------------------------
// Inhabitedness, niches, canonical layouts
// ---------------------------------------------------------------------------------------------

#[test]
fn test_adt_inhabitedness_niches_and_canonical_layouts() {
    let (_, void) = adt(AdtDef::new_enum("Void", None, vec![]));
    assert!(!void.is_inhabited());
    let (_, s_never) = adt(AdtDef::new_struct("SN", vec![u32_ty(), Ty::Never]));
    assert!(!s_never.is_inhabited());
    // A union with an inhabited field is inhabited even if another field is `!`.
    let (_, u_never) = adt(AdtDef::new_union("UN", vec![u32_ty(), Ty::Never]));
    assert!(u_never.is_inhabited());
    let (_, u_only_never) = adt(AdtDef::new_union("UON", vec![Ty::Never]));
    assert!(!u_only_never.is_inhabited());
    let (_, e_partial) = adt(AdtDef::new_enum(
        "EP",
        None,
        vec![
            VariantDef::new("A", vec![Ty::Never]),
            VariantDef::new("B", vec![]),
        ],
    ));
    assert!(e_partial.is_inhabited());
    let (_, e_none) = adt(AdtDef::new_enum(
        "EN",
        None,
        vec![VariantDef::new("A", vec![u8_ty(), Ty::Never])],
    ));
    assert!(!e_none.is_inhabited());
    // Scalar valid ranges excluding every valid scalar bit pattern are uninhabited.
    let niche = |field: Ty, range: ScalarValidRange| {
        Ty::adt(AdtDef::new_struct("N", vec![field]).with_scalar_valid_range(range))
    };
    assert!(!niche(Ty::Bool, ScalarValidRange::new(2, 3)).is_inhabited());
    assert!(niche(Ty::Bool, ScalarValidRange::new(1, 3)).is_inhabited());
    assert!(!niche(Ty::Char, ScalarValidRange::new(0xD800, 0xDFFF)).is_inhabited());
    assert!(!niche(ref_ty(u8_ty()), ScalarValidRange::new(0, 0)).is_inhabited());
    assert!(!niche(u8_ty(), ScalarValidRange::new(300, 400)).is_inhabited());
    assert!(niche(u8_ty(), ScalarValidRange::new(300, 4)).is_inhabited());
    let (_, nz) = non_zero_u32();
    assert!(nz.is_inhabited());
    // Pointer-sized ranges are evaluated for the requested pointer width.
    let high = niche(usize_ty(), ScalarValidRange::new(1 << 40, 1 << 41));
    assert!(high.is_inhabited_for(PtrWidth::Bits64));
    assert!(!high.is_inhabited_for(PtrWidth::Bits32));

    // Niches: non-full valid ranges, enum tags with invalid values; unions expose none.
    assert!(nz.contains_niche());
    assert!(!niche(u32_ty(), ScalarValidRange::full(32)).contains_niche());
    let (_, repr_u8) = repr_u8_enum();
    assert!(repr_u8.contains_niche());
    let (_, u1) = adt(AdtDef::new_union("U1", vec![Ty::Bool]));
    assert!(!u1.contains_niche());
    let (_, plain) = adt(AdtDef::new_struct("P", vec![u32_ty(), u16_ty()]));
    assert!(!plain.contains_niche());
    let (_, with_bool) = adt(AdtDef::new_struct("B", vec![u32_ty(), Ty::Bool]));
    assert!(with_bool.contains_niche());
    let full_u8_variants: Vec<VariantDef> = (0..256)
        .map(|i| VariantDef::new(format!("V{i}"), vec![]))
        .collect();
    let (_, all_tags) = adt(AdtDef::new_enum(
        "All",
        Some(ScalarTy::Uint(UintTy::U8)),
        full_u8_variants,
    ));
    assert!(
        !all_tags.contains_niche(),
        "a u8 tag with 256 variants has no invalid value"
    );

    // Canonical byte layouts.
    let canonical = |ty: &Ty| ty.has_canonical_byte_layout(PW);
    assert!(canonical(&nz));
    let (_, c_padded) =
        adt(AdtDef::new_struct("CP", vec![u8_ty(), u32_ty()]).with_repr(AdtRepr::c()));
    assert!(!canonical(&c_padded));
    let (_, c_tight) =
        adt(AdtDef::new_struct("CT", vec![u8_ty(), Ty::Bool, u16_ty()]).with_repr(AdtRepr::c()));
    assert!(
        canonical(&c_tight),
        "repr(C) field order is fixed, so niches do not matter"
    );
    let (_, r_padded) = adt(AdtDef::new_struct("RP", vec![u8_ty(), u32_ty()]));
    assert!(!canonical(&r_padded));
    let (_, r_aligned) =
        adt(AdtDef::new_struct("RA", vec![u32_ty()]).with_repr(AdtRepr::rust().with_align(8)));
    assert!(!canonical(&r_aligned), "repr(align) tail padding");
    let (_, transparent) = adt(AdtDef::new_struct(
        "T",
        vec![Ty::Tuple(vec![u16_ty(), u16_ty()]), unit()],
    )
    .with_repr(AdtRepr::transparent()));
    assert!(canonical(&transparent));
    let (_, u32_union) = adt(AdtDef::new_union("UU", vec![u32_ty()]));
    assert!(canonical(&u32_union));
    assert!(
        !canonical(&u1),
        "a union of bool has invalid-for-bool but valid-for-union bytes"
    );
    let (_, two_field_union) = adt(AdtDef::new_union(
        "U2",
        vec![u32_ty(), Ty::Array(Box::new(u8_ty()), 4)],
    ));
    assert!(!canonical(&two_field_union));
    let (_, fieldless) = adt(AdtDef::new_enum(
        "F",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![]).with_discriminant(1),
            VariantDef::new("B", vec![]).with_discriminant(7),
        ],
    ));
    assert!(canonical(&fieldless));
    assert!(!canonical(&repr_u8), "variant A has padding after its tag");
    let (_, c_u16_same) = adt(AdtDef::new_enum(
        "CS",
        Some(ScalarTy::Uint(UintTy::U16)),
        vec![
            VariantDef::new("A", vec![u16_ty()]),
            VariantDef::new("B", vec![i16_ty()]),
        ],
    )
    .with_repr(AdtRepr::c()));
    assert!(canonical(&c_u16_same));
    let (_, ptr_enum) = adt(AdtDef::new_enum(
        "PE",
        Some(ScalarTy::Uint(UintTy::Usize)),
        vec![
            VariantDef::new("A", vec![raw(u8_ty(), Mutability::Not)]),
            VariantDef::new("B", vec![usize_ty()]),
        ],
    )
    .with_repr(AdtRepr::c()));
    assert!(
        !canonical(&ptr_enum),
        "pointer positions would depend on the variant"
    );
    let (_, opt) = rust_option_u32();
    assert!(!canonical(&opt));
    // Tuples mixing niche ADTs with other fields are not canonical (rustc may move niches).
    assert!(!canonical(&Ty::Tuple(vec![nz.clone(), u32_ty()])));
    assert!(canonical(&Ty::Tuple(vec![nz.clone(), nz.clone()])));
    assert!(canonical(&Ty::Tuple(vec![plain.clone(), plain.clone()])) == canonical(&plain));
}

// ---------------------------------------------------------------------------------------------
// Typed ADT values, aggregates, Discriminant, SetDiscriminant
// ---------------------------------------------------------------------------------------------

fn adt_aggregate(
    def: &Arc<AdtDef>,
    variant_idx: usize,
    active_field: Option<usize>,
    ops: Vec<Operand>,
) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt {
            def_path: def.def_path.clone(),
            variant_idx,
            active_field,
            adt_def: Some(def.clone()),
        },
        ops,
    )
}

#[test]
fn test_typed_adt_values_report_ty_adt_and_aggregates_type_check_against_def() {
    let (pair_def, pair_ty) = adt(AdtDef::new_struct("Pair", vec![u32_ty(), u8_ty()]));
    let (repr_u8_def, repr_u8_ty) = repr_u8_enum();
    let (union_def, union_ty) = adt(AdtDef::new_union("U", vec![u32_ty(), u16_ty()]));
    let decls = vec![pair_ty.clone(), repr_u8_ty.clone(), union_ty.clone()];
    let mut state = state_with(decls.clone(), PW);

    run(
        assign(
            local(0),
            adt_aggregate(
                &pair_def,
                0,
                None,
                vec![cint(7, u32_ty()), cint(9, u8_ty())],
            ),
        ),
        &mut state,
    )
    .unwrap();
    let pair_val = state.get_init(Local(0)).unwrap().clone();
    assert_eq!(pair_val, MirValue::adt(&pair_def, 0, vec![u32v(7), u8v(9)]));
    assert_eq!(pair_val.ty(), pair_ty);
    run(
        assign(
            local(1),
            adt_aggregate(&repr_u8_def, 1, None, vec![cint(3, u16_ty())]),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(1)).unwrap().ty(), repr_u8_ty);
    run(
        assign(
            local(2),
            adt_aggregate(&union_def, 0, Some(1), vec![cint(5, u16_ty())]),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(2)),
        Some(&MirValue::union_value(&union_def, 1, u16v(5)))
    );
    // Legacy ADT values (no AdtDef) keep reporting the tuple of their fields.
    let legacy = MirValue::Adt {
        def_path: "L".into(),
        variant_idx: 0,
        active_field: None,
        fields: vec![u32v(1)],
        adt_def: None,
    };
    assert_eq!(legacy.ty(), Ty::Tuple(vec![u32_ty()]));

    // Field reads/writes through typed places.
    assert_eq!(read(&state, &place(0, vec![field(1, u8_ty())])), Ok(u8v(9)));
    run(
        assign(
            place(0, vec![field(0, u32_ty())]),
            Rvalue::Use(cint(11, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        read(&state, &local(0)),
        Ok(MirValue::adt(&pair_def, 0, vec![u32v(11), u8v(9)]))
    );
    let b0 = place(1, vec![ProjectionElem::Downcast(1), field(0, u16_ty())]);
    assert_eq!(read(&state, &b0), Ok(u16v(3)));
    let a0 = place(1, vec![ProjectionElem::Downcast(0), field(0, u8_ty())]);
    assert_eq!(
        read(&state, &a0),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 0,
            actual: 1
        })
    );
    // Union: reading the inactive field is UB; writing a whole field switches it.
    assert!(matches!(
        read(&state, &place(2, vec![field(0, u32_ty())])),
        Err(RvalueEvalError::InactiveUnionField { .. })
    ));
    run(
        assign(
            place(2, vec![field(0, u32_ty())]),
            Rvalue::Use(cint(42, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(2)),
        Some(&MirValue::union_value(&union_def, 0, u32v(42)))
    );

    // Static place checks: `Field` on an enum needs `Downcast`; `Downcast` needs an enum and an
    // in-range variant; struct field types must match.
    for bad in [
        place(1, vec![field(0, u8_ty())]),
        place(1, vec![ProjectionElem::Downcast(2), field(0, u8_ty())]),
        place(0, vec![ProjectionElem::Downcast(0), field(0, u32_ty())]),
        place(0, vec![field(1, u32_ty())]),
        place(2, vec![field(2, u32_ty())]),
    ] {
        assert!(
            matches!(
                resolve_place_ty(&bad, &decls),
                Err(RvalueLowerError::InvalidProjection { .. })
            ),
            "{bad:?}"
        );
    }
    assert_eq!(resolve_place_ty(&a0, &decls), Ok(u8_ty()));

    // Aggregate lowering checks operands against the definition.
    let bad_aggs = [
        adt_aggregate(&pair_def, 0, None, vec![cint(7, u32_ty())]),
        adt_aggregate(
            &pair_def,
            0,
            None,
            vec![cint(7, u32_ty()), cint(9, u16_ty())],
        ),
        adt_aggregate(&pair_def, 1, None, vec![]),
        adt_aggregate(&pair_def, 0, Some(0), vec![cint(7, u32_ty())]),
        adt_aggregate(&union_def, 0, None, vec![cint(7, u32_ty())]),
        adt_aggregate(&union_def, 0, Some(2), vec![cint(7, u32_ty())]),
        adt_aggregate(&union_def, 0, Some(0), vec![cint(7, u16_ty())]),
        adt_aggregate(&repr_u8_def, 2, None, vec![]),
        Rvalue::Aggregate(
            AggregateKind::Adt {
                def_path: "Other".into(),
                variant_idx: 0,
                active_field: None,
                adt_def: Some(pair_def.clone()),
            },
            vec![cint(7, u32_ty()), cint(9, u8_ty())],
        ),
    ];
    for bad in bad_aggs {
        assert!(
            lower_rvalue(&bad, &decls, PW).is_err(),
            "{bad:?} must not lower"
        );
    }
    // Typed values do not match legacy tuple places (and vice versa).
    let lowered = lower_statement(
        &assign(
            local(0),
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![cint(7, u32_ty()), cint(9, u8_ty())],
            ),
        ),
        &decls,
        PW,
    );
    assert!(matches!(
        lowered,
        Err(RvalueLowerError::AssignmentTypeMismatch { .. })
    ));
}

#[test]
fn test_discriminant_on_typed_enums_structs_unions_and_shells() {
    // #[repr(i8)] enum { A = -1, B, C = 5 }: discriminants are i8 bit patterns.
    let (i8_def, i8_enum) = adt(AdtDef::new_enum(
        "ReprI8",
        Some(ScalarTy::Int(IntTy::I8)),
        vec![
            VariantDef::new("A", vec![]).with_discriminant((-1i128) as u128),
            VariantDef::new("B", vec![u32_ty()]),
            VariantDef::new("C", vec![]).with_discriminant(5),
        ],
    ));
    // enum { A, B = 10, C } with the default isize discriminant type.
    let (isize_def, isize_enum) = adt(AdtDef::new_enum(
        "Isize",
        None,
        vec![
            VariantDef::new("A", vec![]),
            VariantDef::new("B", vec![u8_ty()]).with_discriminant(10),
            VariantDef::new("C", vec![]),
        ],
    ));
    let (pair_def, pair_ty) = adt(AdtDef::new_struct("Pair", vec![u32_ty()]));
    let (union_def, union_ty) = adt(AdtDef::new_union("U", vec![u32_ty()]));
    let (single_def, single) = adt(AdtDef::new_enum(
        "Single",
        None,
        vec![VariantDef::new("A", vec![u8_ty()]).with_discriminant(5)],
    ));
    let decls = vec![
        i8_enum.clone(),
        isize_enum.clone(),
        pair_ty.clone(),
        union_ty.clone(),
        single.clone(),
    ];
    let mut state = state_with(decls.clone(), PW);

    // Lowered result types follow `rustc`'s discriminant_ty.
    let lowered_ty = |p: Place| {
        lower_rvalue(&Rvalue::Discriminant(p), &decls, PW)
            .unwrap()
            .ty()
            .clone()
    };
    assert_eq!(lowered_ty(local(0)), i8_ty());
    assert_eq!(lowered_ty(local(1)), Ty::Int(IntTy::Isize));
    assert_eq!(lowered_ty(local(2)), u8_ty());
    assert_eq!(lowered_ty(local(3)), u8_ty());
    assert_eq!(lowered_ty(local(4)), Ty::Int(IntTy::Isize));

    for (variant, ops, bits) in [
        (0, vec![], 0xFF),
        (1, vec![cint(1, u32_ty())], 0x00),
        (2, vec![], 0x05),
    ] {
        run(
            assign(local(0), adt_aggregate(&i8_def, variant, None, ops)),
            &mut state,
        )
        .unwrap();
        assert_eq!(discriminant(&mut state, local(0)), Ok(uint(bits, i8_ty())));
    }
    for (variant, ops, value) in [
        (0usize, vec![], 0i128),
        (1, vec![cint(2, u8_ty())], 10),
        (2, vec![], 11),
    ] {
        run(
            assign(local(1), adt_aggregate(&isize_def, variant, None, ops)),
            &mut state,
        )
        .unwrap();
        assert_eq!(
            discriminant(&mut state, local(1)),
            Ok(MirValue::signed(value, IntTy::Isize, PW))
        );
    }
    // Structs, unions, and tagless single-variant enums store no tag: the discriminant is a
    // constant read without touching (possibly uninitialized) memory, but the local must be live.
    assert_eq!(discriminant(&mut state, local(2)), Ok(u8v(0)));
    assert_eq!(discriminant(&mut state, local(3)), Ok(u8v(0)));
    assert_eq!(
        discriminant(&mut state, local(4)),
        Ok(MirValue::signed(5, IntTy::Isize, PW))
    );
    state.slots[2] = LocalSlotState::Dead;
    assert_eq!(
        discriminant(&mut state, local(2)),
        Err(RvalueEvalError::DeadLocal(Local(2)))
    );
    // Initialized values report the same constants.
    state.slots[2] = LocalSlotState::Init(MirValue::adt(&pair_def, 0, vec![u32v(1)]));
    state.slots[3] = LocalSlotState::Init(MirValue::union_value(&union_def, 0, u32v(1)));
    state.slots[4] = LocalSlotState::Init(MirValue::adt(&single_def, 0, vec![u8v(1)]));
    assert_eq!(discriminant(&mut state, local(2)), Ok(u8v(0)));
    assert_eq!(discriminant(&mut state, local(3)), Ok(u8v(0)));
    assert_eq!(
        discriminant(&mut state, local(4)),
        Ok(MirValue::signed(5, IntTy::Isize, PW))
    );

    // A tagged enum shell answers Discriminant once its tag is written, not before.
    let mut fresh = state_with(decls.clone(), PW);
    let b0 = place(0, vec![ProjectionElem::Downcast(1), field(0, u32_ty())]);
    run(
        assign(b0.clone(), Rvalue::Use(cint(9, u32_ty()))),
        &mut fresh,
    )
    .unwrap();
    assert!(matches!(
        fresh.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        discriminant(&mut fresh, local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    run(
        Statement::SetDiscriminant {
            place: local(0),
            variant_index: 1,
        },
        &mut fresh,
    )
    .unwrap();
    assert_eq!(
        fresh.get_init(Local(0)),
        Some(&MirValue::adt(&i8_def, 1, vec![u32v(9)]))
    );
    assert_eq!(discriminant(&mut fresh, local(0)), Ok(uint(0, i8_ty())));
}

#[test]
fn test_set_discriminant_writes_typed_enum_tags_like_minirust() {
    let (def, enum_ty) = adt(AdtDef::new_enum(
        "E",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u32_ty(), u8_ty()]),
            VariantDef::new("B", vec![]),
            VariantDef::new("C", vec![Ty::Never]),
        ],
    ));
    let (outer_def, outer_ty) =
        adt(AdtDef::new_struct("Outer", vec![u16_ty(), enum_ty.clone()]).with_repr(AdtRepr::c()));
    let decls = vec![
        enum_ty.clone(),
        outer_ty.clone(),
        Ty::Tuple(vec![u16_ty(), enum_ty.clone()]),
    ];
    let mut state = state_with(decls.clone(), PW);
    let set = |p: Place, v: usize| Statement::SetDiscriminant {
        place: p,
        variant_index: v,
    };

    // On an uninitialized typed enum, SetDiscriminant writes the tag: a fieldless variant is
    // then fully initialized, a data variant becomes a tagged shell.
    run(set(local(0), 1), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&def, 1, vec![]))
    );
    state.slots[0] = LocalSlotState::Uninit;
    run(set(local(0), 0), &mut state).unwrap();
    let LocalSlotState::PartialShell(shell) = state.get_local(Local(0)).unwrap().clone() else {
        panic!("expected a shell");
    };
    assert!(shell.discriminant_set && shell.variant_idx == 0 && shell.adt_def.is_some());
    assert_eq!(discriminant(&mut state, local(0)), Ok(u8v(0)));
    run(
        assign(
            place(0, vec![ProjectionElem::Downcast(0), field(0, u32_ty())]),
            Rvalue::Use(cint(1, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            place(0, vec![ProjectionElem::Downcast(0), field(1, u8_ty())]),
            Rvalue::Use(cint(2, u8_ty())),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&def, 0, vec![u32v(1), u8v(2)]))
    );
    // Same-variant SetDiscriminant is a no-op; switching variants leaves the new variant's
    // fields uninitialized (the old variant's fields do not initialize them).
    run(set(local(0), 0), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&def, 0, vec![u32v(1), u8v(2)]))
    );
    run(set(local(0), 1), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&def, 1, vec![]))
    );
    run(set(local(0), 0), &mut state).unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        read(&state, &local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    // Writing the tag of an uninhabited variant is UB; out-of-range variants do not lower.
    assert_eq!(
        run(set(local(0), 2), &mut state),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 2 })
    );
    assert!(matches!(
        lower_statement(&set(local(0), 3), &decls, PW),
        Err(RvalueLowerError::InvalidVariantIndex {
            variant_index: 3,
            ..
        })
    ));

    // Through a typed struct: an uninitialized container materializes shells.
    let inner = place(1, vec![field(1, enum_ty.clone())]);
    run(set(inner.clone(), 1), &mut state).unwrap();
    run(
        assign(
            place(1, vec![field(0, u16_ty())]),
            Rvalue::Use(cint(3, u16_ty())),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::adt(
            &outer_def,
            0,
            vec![u16v(3), MirValue::adt(&def, 1, vec![])]
        ))
    );
    // A variant switch nested in an initialized struct demotes the path to shells.
    run(set(inner.clone(), 0), &mut state).unwrap();
    assert!(matches!(
        state.get_local(Local(1)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        read(&state, &place(1, vec![field(0, u16_ty())])),
        Ok(u16v(3))
    );
    assert_eq!(discriminant(&mut state, inner.clone()), Ok(u8v(0)));
    // A failed SetDiscriminant leaves the state unchanged.
    let before = state.clone();
    assert!(run(set(inner.clone(), 2), &mut state).is_err());
    assert_eq!(state, before);
    // Legacy tuple containers keep the conservative rule: no tag write through Uninit.
    assert_eq!(
        run(
            set(place(2, vec![field(1, enum_ty.clone())]), 1),
            &mut state
        ),
        Err(RvalueEvalError::UninitializedLocal(Local(2)))
    );
    // Structs only have variant 0 (a no-op).
    run(set(local(1), 0), &mut state).unwrap();
    assert!(lower_statement(&set(local(1), 1), &decls, PW).is_err());
}

// ---------------------------------------------------------------------------------------------
// OffsetOf through nested ADTs, Transmute with niches and tags
// ---------------------------------------------------------------------------------------------

#[test]
fn test_offset_of_nested_adt_paths_and_errors() {
    let (_, repr_u8) = repr_u8_enum();
    let (_, inner) =
        adt(AdtDef::new_struct("Inner", vec![u8_ty(), u64_ty()]).with_repr(AdtRepr::c()));
    let (_, outer) = adt(AdtDef::new_struct(
        "Outer",
        vec![u32_ty(), inner.clone(), repr_u8.clone()],
    )
    .with_repr(AdtRepr::c()));
    // Outer: u32 @0, Inner (align 8, size 16) @8, ReprU8 (align 4, size 8) @24; size 32.
    assert_eq!(layout(&outer, PW), TyLayout { size: 32, align: 8 });
    assert_eq!(offset(&outer, &[(0, 1), (0, 1)]), Ok(16));
    assert_eq!(offset(&outer, &[(0, 2), (0, 1)]), Ok(28));
    assert_eq!(offset(&outer, &[(0, 2), (1, 0)]), Ok(26));
    // Mixed tuple/ADT paths.
    let tup = Ty::Tuple(vec![inner.clone(), inner.clone()]);
    assert!(tup.has_canonical_byte_layout(PW) == inner.has_canonical_byte_layout(PW));
    // Errors: bad variant, bad field, struct with a non-zero variant, union field offsets.
    let invalid = |ty: &Ty, v: usize, f: usize| RvalueLowerError::InvalidOffsetOfField {
        container_ty: ty.clone(),
        variant_idx: v,
        field_idx: f,
    };
    assert_eq!(offset(&outer, &[(1, 0)]), Err(invalid(&outer, 1, 0)));
    assert_eq!(offset(&outer, &[(0, 3)]), Err(invalid(&outer, 0, 3)));
    assert_eq!(offset(&repr_u8, &[(2, 0)]), Err(invalid(&repr_u8, 2, 0)));
    assert_eq!(offset(&repr_u8, &[(1, 1)]), Err(invalid(&repr_u8, 1, 1)));
    assert_eq!(
        offset(&outer, &[(0, 0), (0, 0)]),
        Err(invalid(&u32_ty(), 0, 0))
    );
    // NullOp::OffsetOf lowers and evaluates to the same offsets.
    let mut state = state_with(vec![usize_ty()], PW);
    run(
        assign(
            local(0),
            Rvalue::NullaryOp(NullOp::OffsetOf(vec![(0, 2), (0, 1)]), outer.clone()),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&usizev(28)));
    run(
        assign(local(0), Rvalue::NullaryOp(NullOp::SizeOf, outer.clone())),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&usizev(32)));
    run(
        assign(
            local(0),
            Rvalue::NullaryOp(NullOp::AlignOf, repr_u8.clone()),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(0)), Some(&usizev(4)));
}

fn transmute(
    state: &mut StatementEvalState,
    dst: usize,
    src: Operand,
    target: Ty,
) -> Result<(), RvalueEvalError> {
    run(
        assign(local(dst), Rvalue::Cast(CastKind::Transmute, src, target)),
        state,
    )
}

#[test]
fn test_transmute_enforces_scalar_valid_ranges_and_enum_tags() {
    let (nz_def, nz) = non_zero_u32();
    let (nz128_def, nz128) = adt(
        AdtDef::new_struct("NonZeroU128", vec![Ty::Uint(UintTy::U128)])
            .with_scalar_valid_range(ScalarValidRange::non_zero(128)),
    );
    // A wrapping niche: u8 valid in 250..=255 or 0..=5.
    let (wrap_def, wrap) = adt(AdtDef::new_struct("Wrap", vec![u8_ty()])
        .with_scalar_valid_range(ScalarValidRange::new(250, 5)));
    let (fieldless_def, fieldless) = adt(AdtDef::new_enum(
        "F",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![]).with_discriminant(1),
            VariantDef::new("B", vec![]).with_discriminant(7),
        ],
    ));
    let (cs_def, cs) = adt(AdtDef::new_enum(
        "CS",
        Some(ScalarTy::Uint(UintTy::U16)),
        vec![
            VariantDef::new("A", vec![u16_ty()]),
            VariantDef::new("B", vec![i16_ty()]),
        ],
    )
    .with_repr(AdtRepr::c()));
    let (cpair_def, cpair) =
        adt(AdtDef::new_struct("CPair", vec![u16_ty(), u16_ty()]).with_repr(AdtRepr::c()));
    let (u32_union_def, u32_union) = adt(AdtDef::new_union("UU", vec![u32_ty()]));
    let (_, bool_union) = adt(AdtDef::new_union("UB", vec![Ty::Bool]));
    let (_, opt) = rust_option_u32();
    let decls = vec![
        nz.clone(),
        nz128.clone(),
        wrap.clone(),
        fieldless.clone(),
        cs.clone(),
        cpair.clone(),
        u32_union.clone(),
        u32_ty(),
        Ty::Uint(UintTy::U128),
        u8_ty(),
    ];
    let mut state = state_with(decls.clone(), PW);

    // `0u32 -> NonZeroU32` violates the niche: InvalidBitPattern naming the ADT.
    assert_eq!(
        transmute(&mut state, 0, cint(0, u32_ty()), nz.clone()),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: nz.clone(),
                bits: 0
            }
        ))
    );
    transmute(&mut state, 0, cint(5, u32_ty()), nz.clone()).unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&nz_def, 0, vec![u32v(5)]))
    );
    transmute(&mut state, 7, Operand::Copy(local(0)), u32_ty()).unwrap();
    assert_eq!(state.get_init(Local(7)), Some(&u32v(5)));
    // The public cast-level API agrees.
    assert_eq!(
        eval_transmute(
            TransmuteValue::Scalar(0),
            &u32_ty(),
            &nz,
            PW,
            TransmutePolicy::RejectPtrToInt,
            &ExposedProvenanceTracker::new()
        ),
        Err(CastEvalError::InvalidBitPattern {
            target_ty: nz.clone(),
            bits: 0
        })
    );
    // 128-bit niches.
    assert!(
        transmute(
            &mut state,
            1,
            cint(0, Ty::Uint(UintTy::U128)),
            nz128.clone()
        )
        .is_err()
    );
    transmute(
        &mut state,
        1,
        cint(u128::MAX, Ty::Uint(UintTy::U128)),
        nz128.clone(),
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::adt(
            &nz128_def,
            0,
            vec![uint(u128::MAX, Ty::Uint(UintTy::U128))]
        ))
    );
    // Wrapping niches.
    for (bits, ok) in [
        (0, true),
        (5, true),
        (6, false),
        (249, false),
        (250, true),
        (255, true),
    ] {
        let res = transmute(&mut state, 2, cint(bits, u8_ty()), wrap.clone());
        assert_eq!(res.is_ok(), ok, "wrap {bits}");
        if ok {
            assert_eq!(
                state.get_init(Local(2)),
                Some(&MirValue::adt(&wrap_def, 0, vec![u8v(bits)]))
            );
        }
    }
    // Fieldless repr(u8) enums decode the tag; unknown tags are invalid.
    transmute(&mut state, 3, cint(7, u8_ty()), fieldless.clone()).unwrap();
    assert_eq!(
        state.get_init(Local(3)),
        Some(&MirValue::adt(&fieldless_def, 1, vec![]))
    );
    assert_eq!(
        transmute(&mut state, 3, cint(2, u8_ty()), fieldless.clone()),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: fieldless.clone(),
                bits: 2
            }
        ))
    );
    transmute(&mut state, 9, Operand::Copy(local(3)), u8_ty()).unwrap();
    assert_eq!(state.get_init(Local(9)), Some(&u8v(7)));
    // #[repr(C, u16)] enum: tag then payload, little-endian.
    transmute(&mut state, 4, cint(0xBEEF_0001, u32_ty()), cs.clone()).unwrap();
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::adt(&cs_def, 1, vec![uint(0xBEEF, i16_ty())]))
    );
    assert!(transmute(&mut state, 4, cint(0x0000_0002, u32_ty()), cs.clone()).is_err());
    transmute(&mut state, 7, Operand::Copy(local(4)), u32_ty()).unwrap();
    assert_eq!(state.get_init(Local(7)), Some(&u32v(0xBEEF_0001)));
    // repr(C) structs without padding and niche-free single-field unions are canonical.
    transmute(&mut state, 5, cint(0x0002_0001, u32_ty()), cpair.clone()).unwrap();
    assert_eq!(
        state.get_init(Local(5)),
        Some(&MirValue::adt(&cpair_def, 0, vec![u16v(1), u16v(2)]))
    );
    transmute(&mut state, 6, cint(0xABCD, u32_ty()), u32_union.clone()).unwrap();
    assert_eq!(
        state.get_init(Local(6)),
        Some(&MirValue::union_value(&u32_union_def, 0, u32v(0xABCD)))
    );
    // Unspecified layouts and niche-bearing unions fail closed at lowering.
    let lower = |src: Ty, dst: Ty| {
        lower_rvalue(
            &Rvalue::Cast(
                CastKind::Transmute,
                Operand::Constant(Constant::Int(0, src)),
                dst,
            ),
            &[],
            PW,
        )
    };
    assert_eq!(
        lower(u32_ty(), opt.clone()),
        Err(RvalueLowerError::CastError(
            CastLowerError::UnsupportedLayout { ty: opt.clone() }
        ))
    );
    assert_eq!(
        lower(u8_ty(), bool_union.clone()),
        Err(RvalueLowerError::CastError(
            CastLowerError::UnsupportedLayout {
                ty: bool_union.clone()
            }
        ))
    );
    // Identity transmutes of typed values revalidate niches.
    state.slots[0] = LocalSlotState::Init(MirValue::adt(&nz_def, 0, vec![u32v(0)]));
    assert_eq!(
        transmute(&mut state, 0, Operand::Copy(local(0)), nz.clone()),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: nz.clone(),
                bits: 0
            }
        ))
    );
}

#[test]
fn test_scalar_valid_ranges_are_enforced_on_construction_and_typed_reads_only() {
    let (nz_def, nz) = non_zero_u32();
    let (pair_def, pair) = adt(AdtDef::new_struct("P", vec![nz.clone(), u8_ty()]));
    let decls = vec![nz.clone(), pair.clone(), u32_ty()];
    let mut state = state_with(decls.clone(), PW);
    // Constructing NonZeroU32(0) by aggregate is invalid.
    assert_eq!(
        run(
            assign(
                local(0),
                adt_aggregate(&nz_def, 0, None, vec![cint(0, u32_ty())])
            ),
            &mut state
        ),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: nz.clone(),
                bits: 0
            }
        ))
    );
    assert_eq!(state.get_local(Local(0)), Some(&LocalSlotState::Uninit));
    run(
        assign(
            local(0),
            adt_aggregate(&nz_def, 0, None, vec![cint(3, u32_ty())]),
        ),
        &mut state,
    )
    .unwrap();
    // A raw field write may store 0 (the bytes are just a u32); a typed read of the whole
    // NonZeroU32 (or of a value containing it) is then invalid, while the field stays readable.
    run(
        assign(
            place(0, vec![field(0, u32_ty())]),
            Rvalue::Use(cint(0, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        read(&state, &place(0, vec![field(0, u32_ty())])),
        Ok(u32v(0))
    );
    assert_eq!(
        read(&state, &local(0)),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: nz.clone(),
                bits: 0
            }
        ))
    );
    // Writing a valid value back makes it readable again.
    run(
        assign(
            place(0, vec![field(0, u32_ty())]),
            Rvalue::Use(cint(9, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        read(&state, &local(0)),
        Ok(MirValue::adt(&nz_def, 0, vec![u32v(9)]))
    );
    // Nested niches are checked when the containing value is read.
    run(
        assign(
            local(1),
            adt_aggregate(
                &pair_def,
                0,
                None,
                vec![Operand::Copy(local(0)), cint(1, u8_ty())],
            ),
        ),
        &mut state,
    )
    .unwrap();
    run(
        assign(
            place(1, vec![field(0, nz.clone()), field(0, u32_ty())]),
            Rvalue::Use(cint(0, u32_ty())),
        ),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        read(&state, &local(1)),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern { .. }
        ))
    ));
    assert_eq!(read(&state, &place(1, vec![field(1, u8_ty())])), Ok(u8v(1)));
    // Body arguments are validated too.
    let body = lower_body(
        &Body {
            local_decls: vec![unit(), nz.clone()],
            basic_blocks: vec![],
        },
        PW,
    )
    .unwrap();
    assert!(matches!(
        StatementEvalState::from_body(&body, &[MirValue::adt(&nz_def, 0, vec![u32v(0)])]),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern { .. }
        ))
    ));
}

// ---------------------------------------------------------------------------------------------
// Statement::Deinit
// ---------------------------------------------------------------------------------------------

fn deinit(p: Place) -> Statement {
    Statement::Deinit(p)
}

#[test]
fn test_deinit_root_and_projected_places_satisfy_lens_laws() {
    let pair = Ty::Tuple(vec![u32_ty(), u8_ty()]);
    let nested = Ty::Tuple(vec![u16_ty(), pair.clone()]);
    let decls = vec![
        unit(),
        nested.clone(),
        usize_ty(),
        Ty::Array(Box::new(u32_ty()), 3),
    ];
    let mut state = state_with(decls.clone(), PW);
    let full = MirValue::Tuple(vec![u16v(1), MirValue::Tuple(vec![u32v(2), u8v(3)])]);
    state.slots[1] = LocalSlotState::Init(full.clone());

    // Root deinit makes the local Uninit; a dead local is UB.
    run(deinit(local(1)), &mut state).unwrap();
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));
    state.slots[1] = LocalSlotState::Dead;
    assert_eq!(
        run(deinit(local(1)), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(1)))
    );
    assert_eq!(
        run(deinit(place(1, vec![field(0, u16_ty())])), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(1)))
    );

    // (_1.1).0: Get-Deinit on the place, its parents, and the root.
    state.slots[1] = LocalSlotState::Init(full.clone());
    let p10 = place(1, vec![field(1, pair.clone()), field(0, u32_ty())]);
    let p11 = place(1, vec![field(1, pair.clone()), field(1, u8_ty())]);
    let p1 = place(1, vec![field(1, pair.clone())]);
    let p0 = place(1, vec![field(0, u16_ty())]);
    run(deinit(p10.clone()), &mut state).unwrap();
    for uninit in [&p10, &p1, &local(1)] {
        assert_eq!(
            read(&state, uninit),
            Err(RvalueEvalError::UninitializedLocal(Local(1))),
            "{uninit:?}"
        );
    }
    // Disjoint-sibling frame: every other field keeps its exact value.
    assert_eq!(read(&state, &p11), Ok(u8v(3)));
    assert_eq!(read(&state, &p0), Ok(u16v(1)));
    // Re-initialization re-promotes the local to Init.
    run(
        assign(p10.clone(), Rvalue::Use(cint(2, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_local(Local(1)),
        Some(&LocalSlotState::Init(full.clone()))
    );

    // Deinitializing every field one by one leaves an Uninit local (not an empty shell).
    for p in [&p0, &p10, &p11] {
        run(deinit((*p).clone()), &mut state).unwrap();
    }
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));
    // Already-uninitialized base: no fault, stays Uninit.
    run(deinit(p10.clone()), &mut state).unwrap();
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));

    // Arrays have no element shells: an element of an initialized array is unsupported (after
    // the index local and bounds are checked); of an uninitialized array it is a no-op.
    let elem = place(3, vec![ProjectionElem::Index(Local(2))]);
    state.slots[3] = LocalSlotState::Init(MirValue::Array {
        elements: vec![u32v(1), u32v(2), u32v(3)],
        elem_ty: u32_ty(),
    });
    state.slots[2] = LocalSlotState::Dead;
    assert_eq!(
        run(deinit(elem.clone()), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(2)))
    );
    state.slots[2] = LocalSlotState::Uninit;
    assert_eq!(
        run(deinit(elem.clone()), &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(2)))
    );
    state.slots[2] = LocalSlotState::Init(usizev(3));
    assert_eq!(
        run(deinit(elem.clone()), &mut state),
        Err(RvalueEvalError::IndexOutOfBounds { index: 3, len: 3 })
    );
    state.slots[2] = LocalSlotState::Init(usizev(1));
    assert_eq!(
        run(deinit(elem.clone()), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(elem.clone()))
    );
    assert!(matches!(
        state.get_local(Local(3)),
        Some(LocalSlotState::Init(_))
    ));
    state.slots[3] = LocalSlotState::Uninit;
    run(deinit(elem.clone()), &mut state).unwrap();
    state.slots[2] = LocalSlotState::Init(usizev(9));
    assert_eq!(
        run(deinit(elem), &mut state),
        Err(RvalueEvalError::IndexOutOfBounds { index: 9, len: 3 })
    );

    // A failed deinit leaves the state unchanged (atomicity), and ill-typed places do not lower.
    state.slots[1] = LocalSlotState::Init(full.clone());
    let before = state.clone();
    let deref_decls = vec![unit(), raw(u32_ty(), Mutability::Mut)];
    let mut deref_state = state_with(deref_decls.clone(), PW);
    deref_state.slots[1] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(8),
        raw(u32_ty(), Mutability::Mut),
    ));
    let deref_place = place(1, vec![ProjectionElem::Deref]);
    assert_eq!(
        run(deinit(deref_place.clone()), &mut deref_state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(deref_place))
    );
    assert!(lower_statement(&deinit(place(1, vec![field(2, u8_ty())])), &decls, PW).is_err());
    assert!(lower_statement(&deinit(local(9)), &decls, PW).is_err());
    assert_eq!(state, before);

    // Zero-sized fields are tracked like any other field.
    let zst_pair = Ty::Tuple(vec![u8_ty(), unit()]);
    let mut zst_state = state_with(vec![unit(), zst_pair.clone()], PW);
    zst_state.slots[1] = LocalSlotState::Init(MirValue::Tuple(vec![u8v(1), MirValue::Unit]));
    run(deinit(place(1, vec![field(1, unit())])), &mut zst_state).unwrap();
    assert_eq!(
        read(&zst_state, &local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(
        read(&zst_state, &place(1, vec![field(0, u8_ty())])),
        Ok(u8v(1))
    );
}

#[test]
fn test_deinit_enum_variant_fields_keeps_separate_tags_and_drops_niche_tags() {
    // Explicit tag: deinitializing a variant field keeps the tag (stored apart).
    let (def, enum_ty) = repr_u8_enum();
    let (opt_def, opt) = rust_option_u32();
    let (union_def, union_ty) = adt(AdtDef::new_union(
        "U",
        vec![u32_ty(), Ty::Tuple(vec![u16_ty(), u16_ty()])],
    ));
    let decls = vec![
        unit(),
        enum_ty.clone(),
        opt.clone(),
        union_ty.clone(),
        Ty::Tuple(vec![u32_ty(), u8_ty()]),
    ];
    let mut state = state_with(decls.clone(), PW);
    let a0 = place(1, vec![ProjectionElem::Downcast(0), field(0, u8_ty())]);
    let a1 = place(1, vec![ProjectionElem::Downcast(0), field(1, u32_ty())]);
    let b0 = place(1, vec![ProjectionElem::Downcast(1), field(0, u16_ty())]);
    let value = MirValue::adt(&def, 0, vec![u8v(7), u32v(8)]);
    state.slots[1] = LocalSlotState::Init(value.clone());
    run(deinit(a0.clone()), &mut state).unwrap();
    assert_eq!(
        read(&state, &a0),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(read(&state, &a1), Ok(u32v(8)));
    assert_eq!(
        read(&state, &local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(discriminant(&mut state, local(1)), Ok(u8v(0)));
    // Other variants stay inactive; a deinit through them is like a write (UB here).
    let before = state.clone();
    assert_eq!(
        run(deinit(b0.clone()), &mut state),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0
        })
    );
    assert_eq!(state, before);
    run(
        assign(a0.clone(), Rvalue::Use(cint(7, u8_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_local(Local(1)),
        Some(&LocalSlotState::Init(value.clone()))
    );
    // Deinit through `Downcast` on an uninitialized enum is a no-op.
    state.slots[1] = LocalSlotState::Uninit;
    run(deinit(b0.clone()), &mut state).unwrap();
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));

    // Unspecified layout (tagless, multi-variant): the tag may live in the field's niche, so it
    // is lost; rewriting the field does not re-promote until SetDiscriminant.
    let some0 = place(2, vec![ProjectionElem::Downcast(1), field(0, u32_ty())]);
    let some = MirValue::adt(&opt_def, 1, vec![u32v(5)]);
    state.slots[2] = LocalSlotState::Init(some.clone());
    run(deinit(some0.clone()), &mut state).unwrap();
    assert_eq!(
        discriminant(&mut state, local(2)),
        Err(RvalueEvalError::UninitializedLocal(Local(2)))
    );
    run(
        assign(some0.clone(), Rvalue::Use(cint(5, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(2)),
        Some(LocalSlotState::PartialShell(_))
    ));
    run(
        Statement::SetDiscriminant {
            place: local(2),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_local(Local(2)), Some(&LocalSlotState::Init(some)));

    // Union fields of an initialized union have no shells (fail closed); uninit: no-op.
    let u_a = place(3, vec![field(0, u32_ty())]);
    state.slots[3] = LocalSlotState::Init(MirValue::union_value(&union_def, 0, u32v(1)));
    assert_eq!(
        run(deinit(u_a.clone()), &mut state),
        Err(RvalueEvalError::UnsupportedPlaceProjection(u_a.clone()))
    );
    state.slots[3] = LocalSlotState::Uninit;
    run(deinit(u_a), &mut state).unwrap();
    assert_eq!(state.get_local(Local(3)), Some(&LocalSlotState::Uninit));

    // Legacy tuple-modeled enums: the tag is conservatively lost as well.
    let legacy = place(4, vec![ProjectionElem::Downcast(1), field(0, u32_ty())]);
    state.slots[4] = LocalSlotState::Init(MirValue::Adt {
        def_path: "L".into(),
        variant_idx: 1,
        active_field: None,
        fields: vec![u32v(1), u8v(2)],
        adt_def: None,
    });
    run(deinit(legacy.clone()), &mut state).unwrap();
    assert_eq!(
        discriminant(&mut state, local(4)),
        Err(RvalueEvalError::UninitializedLocal(Local(4)))
    );
    assert_eq!(
        read(
            &state,
            &place(4, vec![ProjectionElem::Downcast(1), field(1, u8_ty())])
        ),
        Ok(u8v(2))
    );
}

/// Leaf places of the differential test's local `_1: S` (see [`differential_types`]).
#[derive(Clone, Copy, Debug, PartialEq)]
enum Leaf {
    A,
    B0,
    B1,
    EA0,
    EA1,
    EB0,
}

const LEAVES: [Leaf; 6] = [Leaf::A, Leaf::B0, Leaf::B1, Leaf::EA0, Leaf::EA1, Leaf::EB0];
const TAG_BYTE: usize = 8;

/// `#[repr(u8)] enum E { A(u8, u16), B(u32) }` (tag @0, A.0 @1, A.1 @2, B.0 @4; size 8) and
/// `#[repr(C)] struct S { a: u32, b: (u16, u16), e: E }` (a @0, b @4, e @8; size 16).
fn differential_types() -> (Arc<AdtDef>, Ty, Arc<AdtDef>, Ty) {
    let (e_def, e_ty) = adt(AdtDef::new_enum(
        "E",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![u8_ty(), u16_ty()]),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    ));
    let (s_def, s_ty) = adt(AdtDef::new_struct(
        "S",
        vec![u32_ty(), Ty::Tuple(vec![u16_ty(), u16_ty()]), e_ty.clone()],
    )
    .with_repr(AdtRepr::c()));
    (e_def, e_ty, s_def, s_ty)
}

impl Leaf {
    fn range(self) -> (usize, usize) {
        match self {
            Leaf::A => (0, 4),
            Leaf::B0 => (4, 6),
            Leaf::B1 => (6, 8),
            Leaf::EA0 => (9, 10),
            Leaf::EA1 => (10, 12),
            Leaf::EB0 => (12, 16),
        }
    }
    fn variant(self) -> Option<usize> {
        match self {
            Leaf::EA0 | Leaf::EA1 => Some(0),
            Leaf::EB0 => Some(1),
            _ => None,
        }
    }
    fn ty(self) -> Ty {
        match self {
            Leaf::A | Leaf::EB0 => u32_ty(),
            Leaf::B0 | Leaf::B1 | Leaf::EA1 => u16_ty(),
            Leaf::EA0 => u8_ty(),
        }
    }
    fn place(self, e_ty: &Ty) -> Place {
        let b = Ty::Tuple(vec![u16_ty(), u16_ty()]);
        let e = |v: usize, i: usize, ty: Ty| {
            place(
                1,
                vec![
                    field(2, e_ty.clone()),
                    ProjectionElem::Downcast(v),
                    field(i, ty),
                ],
            )
        };
        match self {
            Leaf::A => place(1, vec![field(0, u32_ty())]),
            Leaf::B0 => place(1, vec![field(1, b), field(0, u16_ty())]),
            Leaf::B1 => place(1, vec![field(1, b), field(1, u16_ty())]),
            Leaf::EA0 => e(0, 0, u8_ty()),
            Leaf::EA1 => e(0, 1, u16_ty()),
            Leaf::EB0 => e(1, 0, u32_ty()),
        }
    }
}

/// Byte-level reference memory for `_1: S`: one `Option<u8>` per byte (`None` = uninitialized)
/// plus the variant the enum field was narrowed to by `Downcast` writes before its tag byte was
/// written (the only state a byte image cannot express).
#[derive(Clone, Debug)]
struct ByteModel {
    live: bool,
    bytes: [Option<u8>; 16],
    narrow: Option<usize>,
}

impl ByteModel {
    fn variant_leaves(v: usize) -> &'static [Leaf] {
        if v == 0 {
            &[Leaf::EA0, Leaf::EA1]
        } else {
            &[Leaf::EB0]
        }
    }
    fn effective_variant(&self) -> Option<usize> {
        self.bytes[TAG_BYTE].map(usize::from).or(self.narrow)
    }
    fn normalize(&mut self) {
        if self.bytes[TAG_BYTE].is_none() && self.bytes[9..16].iter().all(Option::is_none) {
            self.narrow = None;
        }
    }
    fn get(&self, leaf: Leaf) -> Option<u128> {
        let (lo, hi) = leaf.range();
        let mut v = 0u128;
        for (i, b) in self.bytes[lo..hi].iter().enumerate() {
            v |= u128::from((*b)?) << (8 * i);
        }
        Some(v)
    }
    fn set(&mut self, leaf: Leaf, val: Option<u128>) {
        let (lo, hi) = leaf.range();
        for (i, b) in self.bytes[lo..hi].iter_mut().enumerate() {
            *b = val.map(|v| (v >> (8 * i)) as u8);
        }
    }
    fn check_variant(&self, leaf: Leaf) -> Result<(), RvalueEvalError> {
        match (leaf.variant(), self.effective_variant()) {
            (Some(v), Some(w)) if v != w => Err(RvalueEvalError::InactiveVariantProjection {
                expected: v,
                actual: w,
            }),
            _ => Ok(()),
        }
    }
    fn live(&self) -> Result<(), RvalueEvalError> {
        if self.live {
            Ok(())
        } else {
            Err(RvalueEvalError::DeadLocal(Local(1)))
        }
    }
    fn write_leaf(&mut self, leaf: Leaf, val: u128) -> Result<(), RvalueEvalError> {
        self.live()?;
        self.check_variant(leaf)?;
        if let Some(v) = leaf.variant() {
            self.narrow = Some(v);
        }
        self.set(leaf, Some(val));
        Ok(())
    }
    fn write_enum(&mut self, variant: usize, vals: &[u128]) -> Result<(), RvalueEvalError> {
        self.live()?;
        for l in [Leaf::EA0, Leaf::EA1, Leaf::EB0] {
            self.set(l, None);
        }
        self.bytes[TAG_BYTE] = Some(variant as u8);
        for (l, v) in Self::variant_leaves(variant).iter().zip(vals) {
            self.set(*l, Some(*v));
        }
        self.narrow = Some(variant);
        Ok(())
    }
    fn deinit(&mut self, target: DeinitTarget) -> Result<(), RvalueEvalError> {
        self.live()?;
        match target {
            DeinitTarget::Root => self.bytes = [None; 16],
            DeinitTarget::B => {
                self.set(Leaf::B0, None);
                self.set(Leaf::B1, None);
            }
            DeinitTarget::E => {
                self.bytes[8..16].fill(None);
            }
            DeinitTarget::Leaf(leaf) => {
                self.check_variant(leaf)?;
                self.set(leaf, None);
            }
        }
        self.normalize();
        Ok(())
    }
    fn set_discriminant(&mut self, variant: usize) -> Result<(), RvalueEvalError> {
        self.live()?;
        if let Some(w) = self.effective_variant()
            && w != variant
        {
            for l in Self::variant_leaves(w) {
                self.set(*l, None);
            }
        }
        self.bytes[TAG_BYTE] = Some(variant as u8);
        self.narrow = Some(variant);
        Ok(())
    }
    fn read_leaf(&self, leaf: Leaf) -> Result<u128, RvalueEvalError> {
        self.live()?;
        self.check_variant(leaf)?;
        self.get(leaf)
            .ok_or(RvalueEvalError::UninitializedLocal(Local(1)))
    }
    fn read_enum(&self) -> Result<(usize, Vec<u128>), RvalueEvalError> {
        self.live()?;
        let tag = self.bytes[TAG_BYTE].ok_or(RvalueEvalError::UninitializedLocal(Local(1)))?;
        let v = usize::from(tag);
        let vals = Self::variant_leaves(v)
            .iter()
            .map(|l| self.get(*l))
            .collect::<Option<Vec<_>>>()
            .ok_or(RvalueEvalError::UninitializedLocal(Local(1)))?;
        Ok((v, vals))
    }
}

#[derive(Clone, Copy, Debug)]
enum DeinitTarget {
    Root,
    B,
    E,
    Leaf(Leaf),
}

#[test]
fn test_property_deinit_set_discriminant_and_writes_match_byte_level_reference_memory() {
    let (e_def, e_ty, s_def, s_ty) = differential_types();
    let b_ty = Ty::Tuple(vec![u16_ty(), u16_ty()]);
    let decls = vec![unit(), s_ty.clone()];
    let mut seed = 0x0dd_ba11_u64;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut steps = 0usize;
    let mut partial_states = 0usize;
    for _round in 0..300 {
        let mut state = state_with(decls.clone(), PW);
        let mut model = ByteModel {
            live: true,
            bytes: [None; 16],
            narrow: None,
        };
        for _ in 0..40 {
            let choice = next() % 100;
            let rand_val = |next: &mut dyn FnMut() -> u64, ty: &Ty| -> u128 {
                u128::from(next()) & ty.scalar_mask(PW)
            };
            let (impl_res, model_res) = match choice {
                0..=2 => (run(Statement::StorageLive(Local(1)), &mut state), {
                    model = ByteModel {
                        live: true,
                        bytes: [None; 16],
                        narrow: None,
                    };
                    Ok(())
                }),
                3..=4 => (run(Statement::StorageDead(Local(1)), &mut state), {
                    model.live = false;
                    Ok(())
                }),
                5..=34 => {
                    let leaf = LEAVES[(next() % 6) as usize];
                    let val = rand_val(&mut next, &leaf.ty());
                    (
                        run(
                            assign(leaf.place(&e_ty), Rvalue::Use(cint(val, leaf.ty()))),
                            &mut state,
                        ),
                        model.write_leaf(leaf, val),
                    )
                }
                35..=39 => {
                    let (x, y) = (
                        rand_val(&mut next, &u16_ty()),
                        rand_val(&mut next, &u16_ty()),
                    );
                    let rv = Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![cint(x, u16_ty()), cint(y, u16_ty())],
                    );
                    let res = model.live().map(|()| {
                        model.set(Leaf::B0, Some(x));
                        model.set(Leaf::B1, Some(y));
                    });
                    (
                        run(
                            assign(place(1, vec![field(1, b_ty.clone())]), rv),
                            &mut state,
                        ),
                        res,
                    )
                }
                40..=46 => {
                    let variant = (next() % 2) as usize;
                    let vals: Vec<u128> = if variant == 0 {
                        vec![
                            rand_val(&mut next, &u8_ty()),
                            rand_val(&mut next, &u16_ty()),
                        ]
                    } else {
                        vec![rand_val(&mut next, &u32_ty())]
                    };
                    let ops = vals
                        .iter()
                        .zip(e_def.variant_fields(variant).unwrap())
                        .map(|(v, ty)| cint(*v, ty.clone()))
                        .collect();
                    (
                        run(
                            assign(
                                place(1, vec![field(2, e_ty.clone())]),
                                adt_aggregate(&e_def, variant, None, ops),
                            ),
                            &mut state,
                        ),
                        model.write_enum(variant, &vals),
                    )
                }
                47..=74 => {
                    let target = match next() % 9 {
                        0 => DeinitTarget::Root,
                        1 => DeinitTarget::B,
                        2 => DeinitTarget::E,
                        k => DeinitTarget::Leaf(LEAVES[(k - 3) as usize]),
                    };
                    let p = match target {
                        DeinitTarget::Root => local(1),
                        DeinitTarget::B => place(1, vec![field(1, b_ty.clone())]),
                        DeinitTarget::E => place(1, vec![field(2, e_ty.clone())]),
                        DeinitTarget::Leaf(leaf) => leaf.place(&e_ty),
                    };
                    (run(deinit(p), &mut state), model.deinit(target))
                }
                _ => {
                    let variant = (next() % 2) as usize;
                    (
                        run(
                            Statement::SetDiscriminant {
                                place: place(1, vec![field(2, e_ty.clone())]),
                                variant_index: variant,
                            },
                            &mut state,
                        ),
                        model.set_discriminant(variant),
                    )
                }
            };
            assert_eq!(
                impl_res, model_res,
                "op {choice} diverged; model {model:?}\nstate {:?}",
                state.slots[1]
            );
            steps += 1;

            // Observations: every leaf, the composite fields, the whole local, the discriminant.
            for leaf in LEAVES {
                let expected = model.read_leaf(leaf).map(|v| uint(v, leaf.ty()));
                assert_eq!(
                    read(&state, &leaf.place(&e_ty)),
                    expected,
                    "{leaf:?}; model {model:?}\nstate {:?}",
                    state.slots[1]
                );
            }
            let expected_b = model.live().and_then(|()| {
                let b0 = model
                    .get(Leaf::B0)
                    .ok_or(RvalueEvalError::UninitializedLocal(Local(1)))?;
                let b1 = model
                    .get(Leaf::B1)
                    .ok_or(RvalueEvalError::UninitializedLocal(Local(1)))?;
                Ok(MirValue::Tuple(vec![u16v(b0), u16v(b1)]))
            });
            assert_eq!(
                read(&state, &place(1, vec![field(1, b_ty.clone())])),
                expected_b
            );
            let expected_e = model.read_enum().map(|(v, vals)| {
                let fields = vals
                    .iter()
                    .zip(e_def.variant_fields(v).unwrap())
                    .map(|(x, ty)| uint(*x, ty.clone()))
                    .collect();
                MirValue::adt(&e_def, v, fields)
            });
            assert_eq!(
                read(&state, &place(1, vec![field(2, e_ty.clone())])),
                expected_e,
                "model {model:?}"
            );
            let expected_root = model.live().and_then(|()| {
                let a = model
                    .get(Leaf::A)
                    .ok_or(RvalueEvalError::UninitializedLocal(Local(1)))?;
                let b = expected_b.clone()?;
                let e = expected_e.clone()?;
                Ok(MirValue::adt(&s_def, 0, vec![u32v(a), b, e]))
            });
            assert_eq!(read(&state, &local(1)), expected_root);
            let expected_discr = model.live().and_then(|()| {
                model.bytes[TAG_BYTE]
                    .map(|t| u8v(u128::from(t)))
                    .ok_or(RvalueEvalError::UninitializedLocal(Local(1)))
            });
            assert_eq!(
                discriminant(&mut state, place(1, vec![field(2, e_ty.clone())])),
                expected_discr
            );
            // Canonical slot representation: an all-uninitialized local is `Uninit`, a fully
            // readable one is `Init`.
            if model.live && model.bytes.iter().all(Option::is_none) {
                assert_eq!(state.slots[1], LocalSlotState::Uninit);
            }
            if expected_root.is_ok() {
                assert!(matches!(state.slots[1], LocalSlotState::Init(_)));
            }
            if matches!(state.slots[1], LocalSlotState::PartialShell(_)) {
                partial_states += 1;
            }
        }
    }
    assert!(
        steps >= 12_000 && partial_states > 2_000,
        "steps {steps}, partial {partial_states}"
    );
}

// ---------------------------------------------------------------------------------------------
// Statement::Retag
// ---------------------------------------------------------------------------------------------

fn retag(kind: RetagKind, p: Place) -> Statement {
    Statement::Retag(kind, p)
}

#[test]
fn test_retag_validates_every_reachable_reference() {
    let r32 = ref_ty(u32_ty());
    let (holder_def, holder) = adt(AdtDef::new_struct("H", vec![u8_ty(), r32.clone()]));
    let (union_def, union_ty) = adt(AdtDef::new_union("U", vec![r32.clone(), usize_ty()]));
    let (_, opt) = rust_option_u32();
    let decls = vec![
        unit(),
        r32.clone(),
        Ty::Tuple(vec![u64_ty(), r32.clone()]),
        holder.clone(),
        union_ty.clone(),
        ref_ty(Ty::Never),
        raw(u32_ty(), Mutability::Mut),
        u64_ty(),
        Ty::Array(Box::new(r32.clone()), 2),
        ref_ty(opt.clone()),
        ref_ty(u64_ty()),
    ];
    let mut state = state_with(decls.clone(), PW);
    let rptr =
        |addr: u64, ty: &Ty| MirValue::ptr(PointerValue::with_provenance(addr, 1, 1), ty.clone());
    for kind in [RetagKind::Default, RetagKind::FnEntry, RetagKind::TwoPhase] {
        // Direct references: initialized, non-null, aligned, inhabited pointee.
        assert_eq!(
            run(retag(kind, local(1)), &mut state),
            Err(RvalueEvalError::UninitializedLocal(Local(1)))
        );
        state.slots[1] = LocalSlotState::Init(rptr(0x1000, &r32));
        run(retag(kind, local(1)), &mut state).unwrap();
        state.slots[1] = LocalSlotState::Init(rptr(0x1002, &r32));
        assert_eq!(
            run(retag(kind, local(1)), &mut state),
            Err(RvalueEvalError::MisalignedPointer {
                addr: 0x1002,
                required_align: 4
            })
        );
        state.slots[1] = LocalSlotState::Init(rptr(0, &r32));
        assert_eq!(
            run(retag(kind, local(1)), &mut state),
            Err(RvalueEvalError::CastEval(
                CastEvalError::InvalidBitPattern {
                    target_ty: r32.clone(),
                    bits: 0
                }
            ))
        );
        state.slots[5] = LocalSlotState::Init(rptr(0x1000, &ref_ty(Ty::Never)));
        assert_eq!(
            run(retag(kind, local(5)), &mut state),
            Err(RvalueEvalError::UninhabitedPointee(Ty::Never))
        );
        state.slots[1] = LocalSlotState::Dead;
        assert_eq!(
            run(retag(kind, local(1)), &mut state),
            Err(RvalueEvalError::DeadLocal(Local(1)))
        );
        state.slots[1] = LocalSlotState::Uninit;
        // 64-bit alignment of `&u64`.
        state.slots[10] = LocalSlotState::Init(rptr(0x1004, &ref_ty(u64_ty())));
        assert_eq!(
            run(retag(kind, local(10)), &mut state),
            Err(RvalueEvalError::MisalignedPointer {
                addr: 0x1004,
                required_align: 8
            })
        );

        // References inside aggregates; uninitialized non-reference fields are fine, an
        // uninitialized reference field is UB.
        run(
            assign(
                place(2, vec![field(1, r32.clone())]),
                Rvalue::Use(Operand::Constant(Constant::Ptr(
                    PointerValue::without_provenance(0x2000),
                    r32.clone(),
                ))),
            ),
            &mut state,
        )
        .unwrap();
        run(retag(kind, local(2)), &mut state).unwrap();
        state.slots[2] = LocalSlotState::Uninit;
        run(
            assign(
                place(2, vec![field(0, u64_ty())]),
                Rvalue::Use(cint(1, u64_ty())),
            ),
            &mut state,
        )
        .unwrap();
        assert_eq!(
            run(retag(kind, local(2)), &mut state),
            Err(RvalueEvalError::UninitializedLocal(Local(2)))
        );
        state.slots[2] = LocalSlotState::Uninit;
        state.slots[3] = LocalSlotState::Init(MirValue::adt(
            &holder_def,
            0,
            vec![u8v(1), rptr(0x3001, &r32)],
        ));
        assert!(matches!(
            run(retag(kind, local(3)), &mut state),
            Err(RvalueEvalError::MisalignedPointer { .. })
        ));
        state.slots[3] = LocalSlotState::Init(MirValue::adt(
            &holder_def,
            0,
            vec![u8v(1), rptr(0x3000, &r32)],
        ));
        run(retag(kind, local(3)), &mut state).unwrap();
        run(retag(kind, place(3, vec![field(0, u8_ty())])), &mut state).unwrap();
        state.slots[8] = LocalSlotState::Init(MirValue::Array {
            elements: vec![rptr(0x4000, &r32), rptr(0, &r32)],
            elem_ty: r32.clone(),
        });
        assert!(matches!(
            run(retag(kind, local(8)), &mut state),
            Err(RvalueEvalError::CastEval(
                CastEvalError::InvalidBitPattern { .. }
            ))
        ));
        state.slots[8] = LocalSlotState::Uninit;
        // Union contents are never retagged.
        state.slots[4] = LocalSlotState::Init(MirValue::union_value(&union_def, 1, usizev(3)));
        run(retag(kind, local(4)), &mut state).unwrap();
        state.slots[4] = LocalSlotState::Uninit;
        run(retag(kind, local(4)), &mut state).unwrap();
        // Places without references only need to be live (uninitialized is fine).
        run(retag(kind, local(7)), &mut state).unwrap();
        run(retag(kind, local(6)), &mut state).unwrap();
        // An alignment the layout model cannot determine fails closed unless provably wrong.
        state.slots[9] = LocalSlotState::Init(rptr(0x5000, &ref_ty(opt.clone())));
        run(retag(kind, local(9)), &mut state).unwrap();
        state.slots[9] = LocalSlotState::Init(rptr(0x5002, &ref_ty(opt.clone())));
        assert!(matches!(
            run(retag(kind, local(9)), &mut state),
            Err(RvalueEvalError::MisalignedPointer { .. })
        ));
    }

    // Raw retags read the (initialized) pointer, which may be null, unaligned, or dangling.
    let raw_mut = raw(u32_ty(), Mutability::Mut);
    assert_eq!(
        run(retag(RetagKind::Raw(Mutability::Mut), local(6)), &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(6)))
    );
    state.slots[6] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(1),
        raw_mut.clone(),
    ));
    run(retag(RetagKind::Raw(Mutability::Mut), local(6)), &mut state).unwrap();
    state.slots[6] =
        LocalSlotState::Init(MirValue::ptr(PointerValue::without_provenance(0), raw_mut));
    run(retag(RetagKind::Raw(Mutability::Mut), local(6)), &mut state).unwrap();
    // Raw retags need a raw pointer place of the same mutability.
    for (kind, l) in [
        (RetagKind::Raw(Mutability::Not), 6),
        (RetagKind::Raw(Mutability::Mut), 1),
        (RetagKind::Raw(Mutability::Mut), 7),
    ] {
        assert!(matches!(
            lower_statement(&retag(kind, local(l)), &decls, PW),
            Err(RvalueLowerError::InvalidRetagTarget { .. })
        ));
    }
}

// ---------------------------------------------------------------------------------------------
// Statement::CopyNonOverlapping
// ---------------------------------------------------------------------------------------------

fn copy_nonoverlapping(src: Operand, dst: Operand, count: Operand) -> Statement {
    Statement::CopyNonOverlapping { src, dst, count }
}

fn ptr_const(addr: u64, alloc: Option<u64>, ty: Ty) -> Operand {
    let ptr = match alloc {
        Some(a) => PointerValue::with_provenance(addr, a, 1),
        None => PointerValue::without_provenance(addr),
    };
    Operand::Constant(Constant::Ptr(ptr, ty))
}

#[test]
fn test_copy_nonoverlapping_checks_ub_even_for_empty_copies_and_copies_whole_locals() {
    let src_ty = raw(u32_ty(), Mutability::Not);
    let dst_ty = raw(u32_ty(), Mutability::Mut);
    let decls = vec![
        unit(),
        u32_ty(),
        u32_ty(),
        src_ty.clone(),
        dst_ty.clone(),
        usize_ty(),
        Ty::Tuple(vec![u32_ty(), u8_ty()]),
    ];
    let mut state = state_with(decls.clone(), PW);
    let cnt = |n: u128| cint(n, usize_ty());
    let src = |addr: u64| ptr_const(addr, Some(10), src_ty.clone());
    let dst = |addr: u64| ptr_const(addr, Some(20), dst_ty.clone());
    // Null and misaligned pointers are UB even when nothing is copied.
    assert_eq!(
        run(copy_nonoverlapping(src(0), dst(0x100), cnt(0)), &mut state),
        Err(RvalueEvalError::NullPointerAccess)
    );
    assert_eq!(
        run(copy_nonoverlapping(src(0x100), dst(0), cnt(0)), &mut state),
        Err(RvalueEvalError::NullPointerAccess)
    );
    assert_eq!(
        run(
            copy_nonoverlapping(src(0x101), dst(0x100), cnt(0)),
            &mut state
        ),
        Err(RvalueEvalError::MisalignedPointer {
            addr: 0x101,
            required_align: 4
        })
    );
    assert_eq!(
        run(
            copy_nonoverlapping(src(0x100), dst(0x102), cnt(0)),
            &mut state
        ),
        Err(RvalueEvalError::MisalignedPointer {
            addr: 0x102,
            required_align: 4
        })
    );
    // `count * size_of::<T>()` must fit in isize::MAX, and ranges must not wrap.
    let huge = (u128::from(u64::MAX) >> 1) / 4 + 1;
    assert_eq!(
        run(
            copy_nonoverlapping(src(0x100), dst(0x200), cnt(huge)),
            &mut state
        ),
        Err(RvalueEvalError::CopyLengthOverflow {
            count: huge,
            elem_size: 4
        })
    );
    assert_eq!(
        run(
            copy_nonoverlapping(src(0xFFFF_FFFF_FFFF_FFF0), dst(0x200), cnt(8)),
            &mut state
        ),
        Err(RvalueEvalError::PointerRangeOverflow {
            addr: 0xFFFF_FFFF_FFFF_FFF0,
            byte_len: 32
        })
    );
    // Empty copies are no-ops after the checks.
    run(
        copy_nonoverlapping(src(0x100), dst(0x100), cnt(0)),
        &mut state,
    )
    .unwrap();
    // Overlap is checked within one allocation (or between pointers without provenance).
    let same = |addr: u64, ty: &Ty| ptr_const(addr, Some(7), ty.clone());
    assert_eq!(
        run(
            copy_nonoverlapping(same(0x100, &src_ty), same(0x104, &dst_ty), cnt(2)),
            &mut state
        ),
        Err(RvalueEvalError::CopyNonOverlappingOverlap {
            src_addr: 0x100,
            dst_addr: 0x104,
            byte_len: 8
        })
    );
    assert_eq!(
        run(
            copy_nonoverlapping(
                ptr_const(0x104, None, src_ty.clone()),
                ptr_const(0x100, None, dst_ty.clone()),
                cnt(2)
            ),
            &mut state
        ),
        Err(RvalueEvalError::CopyNonOverlappingOverlap {
            src_addr: 0x104,
            dst_addr: 0x100,
            byte_len: 8
        })
    );
    // Adjacent ranges do not overlap; the copy itself then needs a byte-level memory model.
    assert_eq!(
        run(
            copy_nonoverlapping(same(0x100, &src_ty), same(0x108, &dst_ty), cnt(2)),
            &mut state
        ),
        Err(RvalueEvalError::UnsupportedMemoryAccess(
            "copy_nonoverlapping outside of whole-local copies"
        ))
    );
    // On 32-bit targets the length limit is i32::MAX.
    let mut state32 = state_with(decls.clone(), PtrWidth::Bits32);
    assert!(matches!(
        run(
            copy_nonoverlapping(src(0x100), dst(0x200), cnt(0x2000_0000)),
            &mut state32
        ),
        Err(RvalueEvalError::CopyLengthOverflow { .. })
    ));

    // Whole-local copies through `&raw` pointers copy the source's state, even uninitialized.
    run(
        assign(local(3), Rvalue::RawPtr(Mutability::Not, local(1))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(4), Rvalue::RawPtr(Mutability::Mut, local(2))),
        &mut state,
    )
    .unwrap();
    state.slots[1] = LocalSlotState::Init(u32v(0xC0FFEE));
    state.slots[5] = LocalSlotState::Init(usizev(1));
    let copy_locals = copy_nonoverlapping(
        Operand::Copy(local(3)),
        Operand::Copy(local(4)),
        Operand::Copy(local(5)),
    );
    run(copy_locals.clone(), &mut state).unwrap();
    assert_eq!(state.get_init(Local(2)), Some(&u32v(0xC0FFEE)));
    state.slots[1] = LocalSlotState::Uninit;
    run(copy_locals.clone(), &mut state).unwrap();
    assert_eq!(state.get_local(Local(2)), Some(&LocalSlotState::Uninit));
    state.slots[1] = LocalSlotState::Dead;
    assert_eq!(
        run(copy_locals.clone(), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(1)))
    );
    // Copying a local onto itself overlaps.
    state.slots[1] = LocalSlotState::Init(u32v(1));
    run(
        assign(local(4), Rvalue::RawPtr(Mutability::Mut, local(1))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        run(copy_locals, &mut state),
        Err(RvalueEvalError::CopyNonOverlappingOverlap { .. })
    ));
    // `Move` operands deinitialize their locals.
    state.slots[5] = LocalSlotState::Init(usizev(0));
    run(
        copy_nonoverlapping(
            Operand::Copy(local(3)),
            Operand::Copy(local(4)),
            Operand::Move(local(5)),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_local(Local(5)), Some(&LocalSlotState::Uninit));

    // Lowering: `(*const T | &T, *mut T | &mut T, usize)` with equal `T` of exact layout.
    let (_, opt) = rust_option_u32();
    let lower = |s: Operand, d: Operand, c: Operand| {
        lower_statement(&copy_nonoverlapping(s, d, c), &decls, PW)
    };
    assert!(matches!(
        lower(src(4), ptr_const(4, None, src_ty.clone()), cnt(1)),
        Err(RvalueLowerError::InvalidCopyNonOverlapping { .. })
    ));
    assert!(matches!(
        lower(src(4), dst(4), cint(1, u32_ty())),
        Err(RvalueLowerError::InvalidCopyNonOverlapping { .. })
    ));
    assert!(matches!(
        lower(
            src(4),
            ptr_const(4, None, raw(u8_ty(), Mutability::Mut)),
            cnt(1)
        ),
        Err(RvalueLowerError::InvalidCopyNonOverlapping { .. })
    ));
    assert_eq!(
        lower(
            ptr_const(4, None, raw(opt.clone(), Mutability::Not)),
            ptr_const(8, None, raw(opt.clone(), Mutability::Mut)),
            cnt(1)
        ),
        Err(RvalueLowerError::UnsupportedLayout(opt.clone()))
    );
    let ok = lower(
        ptr_const(4, None, ref_ty(u32_ty())),
        ptr_const(8, None, Ty::Ref(Box::new(u32_ty()), Mutability::Mut)),
        cnt(1),
    )
    .unwrap();
    assert!(matches!(
        ok,
        LoweredStatement::CopyNonOverlapping {
            elem_size: 4,
            elem_align: 4,
            ..
        }
    ));
    // A ZST copy of any count is a no-op once the pointers are non-null and aligned.
    let zst_src = raw(unit(), Mutability::Not);
    let zst_dst = raw(unit(), Mutability::Mut);
    run(
        copy_nonoverlapping(
            ptr_const(1, None, zst_src),
            ptr_const(1, None, zst_dst),
            cnt(u128::from(u64::MAX)),
        ),
        &mut state,
    )
    .unwrap();
}

// ---------------------------------------------------------------------------------------------
// Rvalue::{ShallowInitBox, WrapUnsafeBinder}, CastKind::{Subtype, PointerCoercion}
// ---------------------------------------------------------------------------------------------

#[test]
fn test_shallow_init_box_and_wrap_unsafe_binder() {
    let (nz_def, nz) = non_zero_u32();
    let (wrapper_def, wrapper) = adt(AdtDef::new_struct("Wrapper", vec![u32_ty()]));
    let (_, two) = adt(AdtDef::new_struct("Two", vec![u32_ty(), u32_ty()]));
    let decls = vec![
        unit(),
        raw(u64_ty(), Mutability::Mut),
        wrapper.clone(),
        u32_ty(),
        nz.clone(),
    ];
    let mut state = state_with(decls.clone(), PW);
    let heap = PointerValue::with_provenance(0x9000, 77, 3);
    run(
        assign(
            local(1),
            Rvalue::ShallowInitBox(
                Operand::Constant(Constant::Ptr(heap, raw(u8_ty(), Mutability::Mut))),
                u64_ty(),
            ),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::ptr(heap, raw(u64_ty(), Mutability::Mut)))
    );
    assert!(matches!(
        lower_rvalue(
            &Rvalue::ShallowInitBox(cint(1, usize_ty()), u64_ty()),
            &decls,
            PW
        ),
        Err(RvalueLowerError::InvalidShallowInitBox { .. })
    ));

    run(
        assign(
            local(2),
            Rvalue::WrapUnsafeBinder(cint(5, u32_ty()), wrapper.clone()),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(2)),
        Some(&MirValue::adt(&wrapper_def, 0, vec![u32v(5)]))
    );
    run(
        assign(
            local(3),
            Rvalue::WrapUnsafeBinder(cint(6, u32_ty()), u32_ty()),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(3)), Some(&u32v(6)));
    assert_eq!(
        run(
            assign(
                local(4),
                Rvalue::WrapUnsafeBinder(cint(0, u32_ty()), nz.clone())
            ),
            &mut state
        ),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: nz.clone(),
                bits: 0
            }
        ))
    );
    run(
        assign(
            local(4),
            Rvalue::WrapUnsafeBinder(cint(1, u32_ty()), nz.clone()),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::adt(&nz_def, 0, vec![u32v(1)]))
    );
    for bad in [two.clone(), u64_ty()] {
        assert!(matches!(
            lower_rvalue(
                &Rvalue::WrapUnsafeBinder(cint(1, u32_ty()), bad),
                &decls,
                PW
            ),
            Err(RvalueLowerError::InvalidWrapUnsafeBinder { .. })
        ));
    }
}

#[test]
fn test_subtype_and_pointer_coercion_casts() {
    let mut_u8 = raw(u8_ty(), Mutability::Mut);
    let const_u8 = raw(u8_ty(), Mutability::Not);
    let arr_const = raw(Ty::Array(Box::new(u16_ty()), 4), Mutability::Not);
    let arr_mut = raw(Ty::Array(Box::new(u16_ty()), 4), Mutability::Mut);
    let decls = vec![
        unit(),
        const_u8.clone(),
        raw(u16_ty(), Mutability::Not),
        raw(u16_ty(), Mutability::Mut),
        u32_ty(),
        mut_u8.clone(),
    ];
    let mut state = state_with(decls.clone(), PW);
    let p = PointerValue::with_provenance(0x1_0000_0010, 3, 9);
    let cast = |kind: CastKind, src: Ty, target: Ty| {
        Rvalue::Cast(kind, Operand::Constant(Constant::Ptr(p, src)), target)
    };
    let m2c = CastKind::PointerCoercion(PointerCoercionKind::MutToConstPointer);
    let a2p = CastKind::PointerCoercion(PointerCoercionKind::ArrayToPointer);

    run(
        assign(local(1), cast(m2c, mut_u8.clone(), const_u8.clone())),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::ptr(p, const_u8.clone()))
    );
    run(
        assign(
            local(2),
            cast(a2p, arr_const.clone(), raw(u16_ty(), Mutability::Not)),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(2)),
        Some(&MirValue::ptr(p, raw(u16_ty(), Mutability::Not)))
    );
    run(
        assign(
            local(3),
            cast(a2p, arr_mut.clone(), raw(u16_ty(), Mutability::Mut)),
        ),
        &mut state,
    )
    .unwrap();
    // 32-bit targets mask the address (and reject over-wide pointer constants).
    let mut state32 = state_with(decls.clone(), PtrWidth::Bits32);
    assert!(matches!(
        lower_rvalue(
            &cast(m2c, mut_u8.clone(), const_u8.clone()),
            &decls,
            PtrWidth::Bits32
        ),
        Err(RvalueLowerError::InvalidConstant { .. })
    ));
    state32.slots[5] = LocalSlotState::Init(MirValue::ptr(p, mut_u8.clone()));
    run(
        assign(
            local(1),
            Rvalue::Cast(m2c, Operand::Copy(local(5)), const_u8.clone()),
        ),
        &mut state32,
    )
    .unwrap();
    assert_eq!(
        state32.get_init(Local(1)),
        Some(&MirValue::ptr(
            PointerValue::with_provenance(0x10, 3, 9),
            const_u8.clone()
        ))
    );

    let rejects = [
        (m2c, const_u8.clone(), const_u8.clone()),
        (m2c, mut_u8.clone(), mut_u8.clone()),
        (m2c, mut_u8.clone(), raw(u16_ty(), Mutability::Not)),
        (m2c, ref_ty(u8_ty()), const_u8.clone()),
        (a2p, arr_const.clone(), raw(u16_ty(), Mutability::Mut)),
        (a2p, arr_mut.clone(), raw(u16_ty(), Mutability::Not)),
        (a2p, arr_const.clone(), raw(u8_ty(), Mutability::Not)),
        (a2p, const_u8.clone(), const_u8.clone()),
    ];
    for (kind, src, target) in rejects {
        assert!(
            matches!(
                lower_rvalue(&cast(kind, src.clone(), target.clone()), &decls, PW),
                Err(RvalueLowerError::CastError(_))
            ),
            "{kind:?} {src:?} -> {target:?}"
        );
    }

    // Subtype casts preserve values of equal types and reject anything else.
    run(
        assign(
            local(4),
            Rvalue::Cast(CastKind::Subtype, cint(42, u32_ty()), u32_ty()),
        ),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(4)), Some(&u32v(42)));
    assert!(matches!(
        lower_rvalue(
            &Rvalue::Cast(CastKind::Subtype, cint(42, u32_ty()), u64_ty()),
            &decls,
            PW
        ),
        Err(RvalueLowerError::CastError(
            CastLowerError::UnsupportedCast { .. }
        ))
    ));
    assert!(matches!(
        lower_rvalue(
            &cast(CastKind::Subtype, mut_u8.clone(), const_u8.clone()),
            &decls,
            PW
        ),
        Err(RvalueLowerError::CastError(
            CastLowerError::UnsupportedCast { .. }
        ))
    ));
}

// ---------------------------------------------------------------------------------------------
// Terminators and the fuel-bounded CFG evaluator
// ---------------------------------------------------------------------------------------------

fn blk(stmts: Vec<Statement>, term: Terminator) -> BasicBlockData {
    BasicBlockData::with_terminator(stmts, term, false)
}
fn cleanup_blk(stmts: Vec<Statement>, term: Terminator) -> BasicBlockData {
    BasicBlockData::with_terminator(stmts, term, true)
}
fn mk_body(local_decls: Vec<Ty>, basic_blocks: Vec<BasicBlockData>) -> Body {
    Body {
        local_decls,
        basic_blocks,
    }
}
fn lower_ok(body: &Body, pw: PtrWidth) -> LoweredBody {
    lower_body(body, pw).unwrap_or_else(|e| panic!("lowering {body:?}: {e:?}"))
}
fn lower_term_err(body: &Body, pw: PtrWidth) -> (usize, TerminatorLowerError) {
    match lower_body(body, pw) {
        Err(RvalueLowerError::InvalidTerminator { bb, error }) => (bb, error),
        other => panic!("expected InvalidTerminator for {body:?}, got {other:?}"),
    }
}
fn goto_t(target: usize) -> Terminator {
    Terminator::Goto { target }
}
fn assert_t(
    cond: Operand,
    expected: bool,
    msg: AssertMessage,
    target: usize,
    unwind: UnwindAction,
) -> Terminator {
    Terminator::Assert {
        cond,
        expected,
        msg,
        target,
        unwind,
    }
}
fn drop_t(p: Place, target: usize, unwind: UnwindAction) -> Terminator {
    Terminator::Drop {
        place: p,
        target,
        unwind,
    }
}
fn custom(text: &str) -> AssertMessage {
    AssertMessage::Custom(text.to_string())
}
fn custom_msg(text: &str) -> PanicMessage {
    PanicMessage::Custom(text.to_string())
}
fn cp(l: usize) -> Operand {
    Operand::Copy(local(l))
}
fn mv(l: usize) -> Operand {
    Operand::Move(local(l))
}
fn cbool(b: bool) -> Operand {
    Operand::Constant(Constant::Bool(b))
}
fn returned(outcome: Result<CfgEvalOutcome, CfgEvalError>) -> MirValue {
    match outcome {
        Ok(CfgEvalOutcome::Returned(val)) => val,
        other => panic!("expected Returned, got {other:?}"),
    }
}

/// `fn(x: T) -> u32 { match x { values[0] => 10, values[1] => 20, .., _ => 10 * (n + 1) } }`:
/// `bb0` switches to the arm blocks `bb1..=bb(n+1)` (the last one is `otherwise`), which
/// write `_0` and jump to the return block `bb(n+2)`.
fn switch_body(discr_ty: Ty, values: &[u128]) -> Body {
    let n = values.len();
    let mut blocks = vec![blk(
        vec![],
        Terminator::SwitchInt {
            discr: cp(1),
            targets: SwitchTargets::new(values.iter().copied().zip(1..), n + 1),
        },
    )];
    for arm in 0..=n {
        blocks.push(blk(
            vec![assign(
                local(0),
                Rvalue::Use(cint(10 * (arm as u128 + 1), u32_ty())),
            )],
            goto_t(n + 2),
        ));
    }
    blocks.push(blk(vec![], Terminator::Return));
    mk_body(vec![u32_ty(), discr_ty], blocks)
}

#[test]
fn test_cfg_switch_int_matches_bool_char_and_masked_integer_bits() {
    let run_switch = |discr_ty: Ty, values: &[u128], arg: MirValue, pw: PtrWidth| -> MirValue {
        let body = lower_ok(&switch_body(discr_ty, values), pw);
        returned(eval_lowered_body_cfg(&body, &[arg], 16))
    };
    // Signed discriminants switch on their two's-complement bits masked to their width.
    let i8_values = [0xFF, 5];
    assert_eq!(
        run_switch(i8_ty(), &i8_values, MirValue::signed(-1, IntTy::I8, PW), PW),
        u32v(10)
    );
    assert_eq!(
        run_switch(i8_ty(), &i8_values, uint(5, i8_ty()), PW),
        u32v(20)
    );
    for other in [0, 0x7F, 0x80, 0xFE] {
        assert_eq!(
            run_switch(i8_ty(), &i8_values, uint(other, i8_ty()), PW),
            u32v(30)
        );
    }
    // `bool` switches on `0`/`1` (`switchInt(_1) -> [0: bb1, otherwise: bb2]`).
    assert_eq!(
        run_switch(Ty::Bool, &[0], MirValue::Bool(false), PW),
        u32v(10)
    );
    assert_eq!(
        run_switch(Ty::Bool, &[0], MirValue::Bool(true), PW),
        u32v(20)
    );
    // `char` switches on its code point.
    let char_values = ['a' as u128, '\u{10FFFF}' as u128];
    assert_eq!(
        run_switch(Ty::Char, &char_values, MirValue::Char('a'), PW),
        u32v(10)
    );
    assert_eq!(
        run_switch(Ty::Char, &char_values, MirValue::Char('\u{10FFFF}'), PW),
        u32v(20)
    );
    assert_eq!(
        run_switch(Ty::Char, &char_values, MirValue::Char('b'), PW),
        u32v(30)
    );
    // Full-width 128-bit values (`u128::MAX` is `-1i128`); the first matching value wins.
    let u128_ty = Ty::Uint(UintTy::U128);
    let i128_ty = Ty::Int(IntTy::I128);
    let wide = [u128::MAX, 0];
    assert_eq!(
        run_switch(u128_ty.clone(), &wide, uint(u128::MAX, u128_ty.clone()), PW),
        u32v(10)
    );
    assert_eq!(
        run_switch(u128_ty.clone(), &wide, uint(0, u128_ty.clone()), PW),
        u32v(20)
    );
    assert_eq!(
        run_switch(u128_ty.clone(), &wide, uint(7, u128_ty.clone()), PW),
        u32v(30)
    );
    assert_eq!(
        run_switch(
            i128_ty.clone(),
            &wide,
            MirValue::signed(-1, IntTy::I128, PW),
            PW
        ),
        u32v(10)
    );
    // `usize` values are checked against the target's pointer width.
    let b32 = PtrWidth::Bits32;
    assert_eq!(
        run_switch(usize_ty(), &[0xFFFF_FFFF], usizev(0xFFFF_FFFF), b32),
        u32v(10)
    );
    assert_eq!(
        run_switch(usize_ty(), &[0xFFFF_FFFF], usizev(0), b32),
        u32v(20)
    );
    assert_eq!(
        run_switch(usize_ty(), &[1 << 32], usizev(1 << 32), PW),
        u32v(10)
    );

    // Values that are not valid bit patterns of the discriminant type are rejected statically.
    for (discr_ty, value, pw) in [
        (i8_ty(), u128::MAX, PW),
        (i8_ty(), 0x100, PW),
        (u16_ty(), 0x1_0000, PW),
        (Ty::Bool, 2, PW),
        (Ty::Char, 0xD800, PW),
        (Ty::Char, 0xDFFF, PW),
        (Ty::Char, 0x11_0000, PW),
        (usize_ty(), 1 << 32, b32),
    ] {
        assert_eq!(
            lower_term_err(&switch_body(discr_ty.clone(), &[value]), pw),
            (
                0,
                TerminatorLowerError::SwitchValueOutOfRange { value, discr_ty }
            ),
        );
    }
    assert_eq!(
        lower_term_err(&switch_body(u8_ty(), &[3, 4, 3]), PW),
        (0, TerminatorLowerError::DuplicateSwitchValue(3)),
    );
    let mut mismatched = switch_body(u8_ty(), &[1, 2]);
    if let Some(Terminator::SwitchInt { targets, .. }) = &mut mismatched.basic_blocks[0].terminator
    {
        targets.targets.pop();
    }
    assert_eq!(
        lower_term_err(&mismatched, PW),
        (
            0,
            TerminatorLowerError::SwitchTargetsLengthMismatch {
                values: 2,
                targets: 1
            }
        ),
    );
    for discr_ty in [
        unit(),
        raw(u8_ty(), Mutability::Not),
        ref_ty(u8_ty()),
        Ty::Array(Box::new(u8_ty()), 1),
        non_zero_u32().1,
        repr_u8_enum().1,
    ] {
        assert_eq!(
            lower_term_err(&switch_body(discr_ty.clone(), &[]), PW),
            (0, TerminatorLowerError::InvalidSwitchDiscrType(discr_ty)),
        );
    }
    // A switch on a dead local faults at runtime in the terminator.
    let body = lower_ok(&switch_body(u8_ty(), &[1]), PW);
    assert_eq!(
        eval_lowered_body_cfg(&body, &[], 16),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::DeadLocal(Local(1)),
        }),
    );
}

/// `fn(n: u32) -> u32 { let mut acc = 0; while n != 0 { acc += n; n -= 1; } acc }`.
fn countdown_body() -> Body {
    mk_body(
        vec![u32_ty(), u32_ty(), Ty::Bool],
        vec![
            blk(
                vec![
                    Statement::StorageLive(Local(2)),
                    assign(local(0), Rvalue::Use(cint(0, u32_ty()))),
                ],
                goto_t(1),
            ),
            blk(
                vec![assign(
                    local(2),
                    Rvalue::BinaryOp(BinOp::Ne, cp(1), cint(0, u32_ty())),
                )],
                Terminator::SwitchInt {
                    discr: cp(2),
                    targets: SwitchTargets::static_if(0, 3, 2),
                },
            ),
            blk(
                vec![
                    assign(local(0), Rvalue::BinaryOp(BinOp::Add, cp(0), cp(1))),
                    assign(
                        local(1),
                        Rvalue::BinaryOp(BinOp::Sub, cp(1), cint(1, u32_ty())),
                    ),
                ],
                goto_t(1),
            ),
            blk(vec![Statement::StorageDead(Local(2))], Terminator::Return),
        ],
    )
}

#[test]
fn test_cfg_loops_consume_one_unit_of_fuel_per_executed_block() {
    let body = lower_ok(&countdown_body(), PW);
    // `n = 10` executes bb0, 11 x bb1, 10 x bb2, and bb3: 23 blocks.
    assert_eq!(
        returned(eval_lowered_body_cfg(&body, &[u32v(10)], 23)),
        u32v(55)
    );
    assert_eq!(
        returned(eval_lowered_body_cfg(&body, &[u32v(10)], 10_000)),
        u32v(55)
    );
    assert_eq!(
        returned(eval_lowered_body_cfg(&body, &[u32v(0)], 3)),
        u32v(0)
    );
    match eval_lowered_body_cfg(&body, &[u32v(10)], 22) {
        Ok(CfgEvalOutcome::OutOfFuel { bb: 3, state }) => {
            assert_eq!(state.slots[0], LocalSlotState::Init(u32v(55)));
            assert_eq!(state.slots[1], LocalSlotState::Init(u32v(0)));
            assert_eq!(state.slots[2], LocalSlotState::Init(MirValue::Bool(false)));
        }
        other => panic!("expected OutOfFuel at bb3, got {other:?}"),
    }
    // Fuel 0 runs no block at all: the state is the entry state.
    let entry = StatementEvalState::from_body(&body, &[u32v(10)]).unwrap();
    assert_eq!(
        eval_lowered_body_cfg(&body, &[u32v(10)], 0),
        Ok(CfgEvalOutcome::OutOfFuel {
            bb: 0,
            state: entry.clone()
        }),
    );
    // Resuming an out-of-fuel evaluation with `eval_cfg_in_state` finishes the loop.
    let Ok(CfgEvalOutcome::OutOfFuel { bb, state }) = eval_lowered_body_cfg(&body, &[u32v(10)], 7)
    else {
        panic!("expected OutOfFuel");
    };
    assert_eq!(
        eval_cfg_in_state(&body, state, bb, 16, None),
        Ok(CfgEvalOutcome::Returned(u32v(55)))
    );
    assert_eq!(
        eval_cfg_in_state(&body, entry.clone(), 4, 16, None),
        Err(CfgEvalError::InvalidBlock { bb: 4 })
    );
    // An infinite loop terminates cleanly.
    let spin = lower_ok(&mk_body(vec![unit()], vec![blk(vec![], goto_t(0))]), PW);
    for fuel in [0, 1, 7] {
        match eval_lowered_body_cfg(&spin, &[], fuel) {
            Ok(CfgEvalOutcome::OutOfFuel { bb: 0, state }) => {
                assert_eq!(state.slots, vec![LocalSlotState::Uninit]);
            }
            other => panic!("expected OutOfFuel, got {other:?}"),
        }
    }
    // Fuel 0 wins even over a block that would be undefined behavior.
    let ub = lower_ok(
        &mk_body(vec![unit()], vec![blk(vec![], Terminator::Unreachable)]),
        PW,
    );
    assert!(matches!(
        eval_lowered_body_cfg(&ub, &[], 0),
        Ok(CfgEvalOutcome::OutOfFuel { bb: 0, .. })
    ));
    assert_eq!(
        eval_lowered_body_cfg(&ub, &[], 1),
        Err(CfgEvalError::UnreachableReached { bb: 0 })
    );
}

/// `fn(n: u64) -> u32 { let mut steps = 0; while n != 1 { n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 }; steps += 1; } steps }`.
fn collatz_body() -> Body {
    let bump = || {
        assign(
            local(0),
            Rvalue::BinaryOp(BinOp::Add, cp(0), cint(1, u32_ty())),
        )
    };
    mk_body(
        vec![u32_ty(), u64_ty(), Ty::Bool, u64_ty()],
        vec![
            blk(
                vec![
                    Statement::StorageLive(Local(2)),
                    Statement::StorageLive(Local(3)),
                    assign(local(0), Rvalue::Use(cint(0, u32_ty()))),
                ],
                goto_t(1),
            ),
            blk(
                vec![assign(
                    local(2),
                    Rvalue::BinaryOp(BinOp::Ne, cp(1), cint(1, u64_ty())),
                )],
                Terminator::SwitchInt {
                    discr: cp(2),
                    targets: SwitchTargets::static_if(0, 5, 2),
                },
            ),
            blk(
                vec![assign(
                    local(3),
                    Rvalue::BinaryOp(BinOp::Rem, cp(1), cint(2, u64_ty())),
                )],
                Terminator::SwitchInt {
                    discr: cp(3),
                    targets: SwitchTargets::static_if(0, 3, 4),
                },
            ),
            blk(
                vec![
                    assign(
                        local(1),
                        Rvalue::BinaryOp(BinOp::Div, cp(1), cint(2, u64_ty())),
                    ),
                    bump(),
                ],
                goto_t(1),
            ),
            blk(
                vec![
                    assign(
                        local(1),
                        Rvalue::BinaryOp(BinOp::Mul, cp(1), cint(3, u64_ty())),
                    ),
                    assign(
                        local(1),
                        Rvalue::BinaryOp(BinOp::Add, cp(1), cint(1, u64_ty())),
                    ),
                    bump(),
                ],
                goto_t(1),
            ),
            blk(vec![], Terminator::Return),
        ],
    )
}

/// `fn(n: u32) -> u64 { let (mut a, mut b) = (0, 1); while n != 0 { let t = a + b; a = b; b = t; n -= 1; } a }`.
fn fibonacci_body() -> Body {
    mk_body(
        vec![u64_ty(), u32_ty(), u64_ty(), u64_ty(), Ty::Bool],
        vec![
            blk(
                vec![
                    Statement::StorageLive(Local(2)),
                    Statement::StorageLive(Local(3)),
                    Statement::StorageLive(Local(4)),
                    assign(local(0), Rvalue::Use(cint(0, u64_ty()))),
                    assign(local(2), Rvalue::Use(cint(1, u64_ty()))),
                ],
                goto_t(1),
            ),
            blk(
                vec![assign(
                    local(4),
                    Rvalue::BinaryOp(BinOp::Ne, cp(1), cint(0, u32_ty())),
                )],
                Terminator::SwitchInt {
                    discr: cp(4),
                    targets: SwitchTargets::static_if(0, 3, 2),
                },
            ),
            blk(
                vec![
                    assign(local(3), Rvalue::BinaryOp(BinOp::Add, cp(0), cp(2))),
                    assign(local(0), Rvalue::Use(cp(2))),
                    assign(local(2), Rvalue::Use(mv(3))),
                    assign(
                        local(1),
                        Rvalue::BinaryOp(BinOp::Sub, cp(1), cint(1, u32_ty())),
                    ),
                ],
                goto_t(1),
            ),
            blk(vec![], Terminator::Return),
        ],
    )
}

#[test]
fn test_cfg_collatz_and_fibonacci_loops_match_direct_computation() {
    let collatz = lower_ok(&collatz_body(), PW);
    let steps = |mut n: u64| {
        let mut steps = 0u32;
        while n != 1 {
            n = if n.is_multiple_of(2) {
                n / 2
            } else {
                3 * n + 1
            };
            steps += 1;
        }
        steps
    };
    for n in 1..=300u64 {
        let expected = steps(n);
        // bb0, then bb1 + bb2 + (bb3 | bb4) per step, then the final bb1 and bb5.
        let needed = 3 * expected as usize + 3;
        assert_eq!(
            returned(eval_lowered_body_cfg(
                &collatz,
                &[uint(u128::from(n), u64_ty())],
                needed
            )),
            u32v(u128::from(expected)),
            "collatz({n})"
        );
        assert!(matches!(
            eval_lowered_body_cfg(&collatz, &[uint(u128::from(n), u64_ty())], needed - 1),
            Ok(CfgEvalOutcome::OutOfFuel { bb: 5, .. })
        ));
    }
    assert_eq!(steps(27), 111);

    let fibonacci = lower_ok(&fibonacci_body(), PW);
    let (mut a, mut b) = (0u64, 1u64);
    for n in 0..=93u32 {
        assert_eq!(
            returned(eval_lowered_body_cfg(
                &fibonacci,
                &[u32v(u128::from(n))],
                2 * n as usize + 3
            )),
            uint(u128::from(a), u64_ty()),
            "fib({n})"
        );
        (a, b) = (b, a.wrapping_add(b));
    }
    assert_eq!(
        returned(eval_lowered_body_cfg(&fibonacci, &[u32v(50)], 1_000)),
        uint(12_586_269_025, u64_ty())
    );
}

/// `fn(a: [u32; 4], limit: usize) -> u32 { let (mut i, mut s) = (0, 0); while i < limit { s += a[i]; i += 1; } s }`
/// with `rustc`'s bounds-check and overflow-check `Assert`s.
fn array_sum_body() -> Body {
    let a_i = || Operand::Copy(place(1, vec![ProjectionElem::Index(Local(3))]));
    let checked = |ty: Ty| Ty::Tuple(vec![ty, Ty::Bool]);
    mk_body(
        vec![
            u32_ty(),
            Ty::Array(Box::new(u32_ty()), 4),
            usize_ty(),
            usize_ty(),
            Ty::Bool,
            checked(u32_ty()),
            checked(usize_ty()),
            Ty::Bool,
        ],
        vec![
            blk(
                vec![
                    Statement::StorageLive(Local(3)),
                    Statement::StorageLive(Local(4)),
                    Statement::StorageLive(Local(5)),
                    Statement::StorageLive(Local(6)),
                    Statement::StorageLive(Local(7)),
                    assign(local(0), Rvalue::Use(cint(0, u32_ty()))),
                    assign(local(3), Rvalue::Use(cint(0, usize_ty()))),
                ],
                goto_t(1),
            ),
            blk(
                vec![assign(local(4), Rvalue::BinaryOp(BinOp::Lt, cp(3), cp(2)))],
                Terminator::SwitchInt {
                    discr: cp(4),
                    targets: SwitchTargets::static_if(0, 5, 2),
                },
            ),
            blk(
                vec![assign(
                    local(7),
                    Rvalue::BinaryOp(BinOp::Lt, cp(3), cint(4, usize_ty())),
                )],
                assert_t(
                    cp(7),
                    true,
                    AssertMessage::BoundsCheck {
                        len: cint(4, usize_ty()),
                        index: cp(3),
                    },
                    3,
                    UnwindAction::Continue,
                ),
            ),
            blk(
                vec![assign(
                    local(5),
                    Rvalue::BinaryOp(BinOp::AddWithOverflow, cp(0), a_i()),
                )],
                assert_t(
                    Operand::Copy(place(5, vec![field(1, Ty::Bool)])),
                    false,
                    AssertMessage::Overflow(BinOp::Add, cp(0), a_i()),
                    4,
                    UnwindAction::Continue,
                ),
            ),
            blk(
                vec![
                    assign(
                        local(0),
                        Rvalue::Use(Operand::Copy(place(5, vec![field(0, u32_ty())]))),
                    ),
                    assign(
                        local(6),
                        Rvalue::BinaryOp(BinOp::AddWithOverflow, cp(3), cint(1, usize_ty())),
                    ),
                    assign(
                        local(3),
                        Rvalue::Use(Operand::Copy(place(6, vec![field(0, usize_ty())]))),
                    ),
                ],
                goto_t(1),
            ),
            blk(vec![], Terminator::Return),
        ],
    )
}

#[test]
fn test_cfg_bounds_and_overflow_asserts_panic_with_evaluated_messages() {
    let body = lower_ok(&array_sum_body(), PW);
    let arr = |vals: [u128; 4]| MirValue::Array {
        elements: vals.iter().map(|v| u32v(*v)).collect(),
        elem_ty: u32_ty(),
    };
    let sum = |vals: [u128; 4], limit: u128| {
        eval_lowered_body_cfg(&body, &[arr(vals), usizev(limit)], 1_000)
    };
    assert_eq!(returned(sum([1, 2, 3, 4], 4)), u32v(10));
    assert_eq!(returned(sum([1, 2, 3, 4], 2)), u32v(3));
    assert_eq!(returned(sum([1, 2, 3, 4], 0)), u32v(0));
    assert_eq!(
        sum([1, 2, 3, 4], 5),
        Ok(CfgEvalOutcome::Panicked {
            bb: 2,
            msg: PanicMessage::BoundsCheck {
                len: usizev(4),
                index: usizev(4),
            },
        }),
    );
    assert_eq!(
        sum([u32::MAX as u128, 1, 0, 0], 4),
        Ok(CfgEvalOutcome::Panicked {
            bb: 3,
            msg: PanicMessage::Overflow(BinOp::Add, u32v(u32::MAX as u128), u32v(1)),
        }),
    );

    // Every message kind evaluates its operands when (and only when) the assertion fails.
    // `fn(i: usize, x: i8) -> ()`; `_3: usize` is a dead temporary.
    let msg_body = |cond: bool, msg: AssertMessage| {
        mk_body(
            vec![unit(), usize_ty(), i8_ty(), usize_ty()],
            vec![
                blk(
                    vec![],
                    assert_t(cbool(cond), true, msg, 1, UnwindAction::Continue),
                ),
                blk(
                    vec![assign(
                        local(0),
                        Rvalue::Use(Operand::Constant(Constant::Unit)),
                    )],
                    Terminator::Return,
                ),
            ],
        )
    };
    let args = [usizev(9), uint(0x7F, i8_ty())];
    let cases = vec![
        (
            AssertMessage::BoundsCheck {
                len: cint(4, usize_ty()),
                index: cp(1),
            },
            PanicMessage::BoundsCheck {
                len: usizev(4),
                index: usizev(9),
            },
        ),
        (
            AssertMessage::Overflow(BinOp::Add, cp(2), cint(1, i8_ty())),
            PanicMessage::Overflow(BinOp::Add, uint(0x7F, i8_ty()), uint(1, i8_ty())),
        ),
        (
            AssertMessage::Overflow(BinOp::Shl, cp(2), cint(9, u32_ty())),
            PanicMessage::Overflow(BinOp::Shl, uint(0x7F, i8_ty()), u32v(9)),
        ),
        (
            AssertMessage::OverflowNeg(cint(0x80, i8_ty())),
            PanicMessage::OverflowNeg(uint(0x80, i8_ty())),
        ),
        (
            AssertMessage::DivisionByZero(cp(2)),
            PanicMessage::DivisionByZero(uint(0x7F, i8_ty())),
        ),
        (
            AssertMessage::RemainderByZero(cp(1)),
            PanicMessage::RemainderByZero(usizev(9)),
        ),
        (
            AssertMessage::MisalignedPointerDereference {
                required: cint(4, usize_ty()),
                found: cp(1),
            },
            PanicMessage::MisalignedPointerDereference {
                required: usizev(4),
                found: usizev(9),
            },
        ),
        (
            AssertMessage::NullPointerDereference,
            PanicMessage::NullPointerDereference,
        ),
        (
            AssertMessage::InvalidEnumConstruction(cint(3, u8_ty())),
            PanicMessage::InvalidEnumConstruction(u8v(3)),
        ),
        (custom("custom"), custom_msg("custom")),
    ];
    for (msg, expected) in cases {
        let failing = lower_ok(&msg_body(false, msg.clone()), PW);
        assert_eq!(
            eval_lowered_body_cfg(&failing, &args, 10),
            Ok(CfgEvalOutcome::Panicked {
                bb: 0,
                msg: expected
            }),
            "{msg:?}"
        );
        let passing = lower_ok(&msg_body(true, msg.clone()), PW);
        assert_eq!(
            returned(eval_lowered_body_cfg(&passing, &args, 10)),
            MirValue::Unit,
            "{msg:?}"
        );
    }
    // A message operand reading a dead local only faults when the assertion fails.
    for msg in [
        AssertMessage::BoundsCheck {
            len: cint(4, usize_ty()),
            index: cp(3),
        },
        AssertMessage::InvalidEnumConstruction(cp(3)),
    ] {
        let passing = lower_ok(&msg_body(true, msg.clone()), PW);
        assert_eq!(
            returned(eval_lowered_body_cfg(&passing, &args, 10)),
            MirValue::Unit
        );
        let failing = lower_ok(&msg_body(false, msg), PW);
        assert_eq!(
            eval_lowered_body_cfg(&failing, &args, 10),
            Err(CfgEvalError::Terminator {
                bb: 0,
                error: RvalueEvalError::DeadLocal(Local(3)),
            }),
        );
    }
    // Message operands and the condition are type-checked statically.
    let bad_operand =
        |msg: AssertMessage, got: Ty| match lower_term_err(&msg_body(false, msg.clone()), PW) {
            (0, TerminatorLowerError::InvalidAssertMessageOperand { got: actual, .. }) => {
                assert_eq!(actual, got, "{msg:?}")
            }
            other => panic!("{msg:?}: {other:?}"),
        };
    bad_operand(
        AssertMessage::BoundsCheck {
            len: cint(4, u32_ty()),
            index: cp(1),
        },
        u32_ty(),
    );
    bad_operand(
        AssertMessage::BoundsCheck {
            len: cint(4, usize_ty()),
            index: cp(2),
        },
        i8_ty(),
    );
    bad_operand(
        AssertMessage::Overflow(BinOp::Add, cp(2), cint(1, u8_ty())),
        u8_ty(),
    );
    bad_operand(
        AssertMessage::Overflow(BinOp::Add, cbool(true), cbool(true)),
        Ty::Bool,
    );
    bad_operand(AssertMessage::OverflowNeg(cint(1, u8_ty())), u8_ty());
    bad_operand(AssertMessage::DivisionByZero(cbool(false)), Ty::Bool);
    bad_operand(
        AssertMessage::RemainderByZero(Operand::Constant(Constant::Char('x'))),
        Ty::Char,
    );
    bad_operand(
        AssertMessage::MisalignedPointerDereference {
            required: cint(4, usize_ty()),
            found: cint(2, u64_ty()),
        },
        u64_ty(),
    );
    bad_operand(
        AssertMessage::InvalidEnumConstruction(Operand::Constant(Constant::Unit)),
        unit(),
    );
    lower_ok(
        &msg_body(
            false,
            AssertMessage::Overflow(BinOp::Shr, cint(1, u64_ty()), cint(1, i8_ty())),
        ),
        PW,
    );
    let mut not_bool = msg_body(false, custom("c"));
    not_bool.basic_blocks[0].terminator = Some(assert_t(
        cp(2),
        true,
        custom("c"),
        1,
        UnwindAction::Continue,
    ));
    assert_eq!(
        lower_term_err(&not_bool, PW),
        (0, TerminatorLowerError::InvalidAssertCondType(i8_ty()))
    );
}

/// `fn(c: bool) -> u8`: `bb0: _0 = 7; assert(c, "boom") -> [success: bb1, unwind: <unwind>]`,
/// `bb1: return`, followed by `cleanup` blocks from `bb2` on (`_2: u8` is a dead temporary).
fn assert_body(unwind: UnwindAction, cleanup: Vec<BasicBlockData>) -> Body {
    let mut blocks = vec![
        blk(
            vec![assign(local(0), Rvalue::Use(cint(7, u8_ty())))],
            assert_t(cp(1), true, custom("boom"), 1, unwind),
        ),
        blk(vec![], Terminator::Return),
    ];
    blocks.extend(cleanup);
    mk_body(vec![u8_ty(), Ty::Bool, u8_ty()], blocks)
}

#[test]
fn test_cfg_panics_follow_unwind_actions_through_cleanup_blocks() {
    let eval = |body: &Body, c: bool, fuel: usize| {
        eval_lowered_body_cfg(&lower_ok(body, PW), &[MirValue::Bool(c)], fuel)
    };
    let resume = || cleanup_blk(vec![], Terminator::UnwindResume);
    let terminate = || cleanup_blk(vec![], Terminator::UnwindTerminate);
    let panicked = |bb: usize, text: &str| {
        Ok(CfgEvalOutcome::Panicked {
            bb,
            msg: custom_msg(text),
        })
    };
    let terminated = |bb: usize, text: &str| {
        Ok(CfgEvalOutcome::Terminated {
            bb,
            msg: custom_msg(text),
        })
    };

    for unwind in [
        UnwindAction::Continue,
        UnwindAction::Terminate,
        UnwindAction::Unreachable,
        UnwindAction::Cleanup(2),
    ] {
        assert_eq!(
            returned(eval(&assert_body(unwind, vec![resume()]), true, 10)),
            u8v(7)
        );
    }
    assert_eq!(
        eval(&assert_body(UnwindAction::Continue, vec![]), false, 10),
        panicked(0, "boom")
    );
    assert_eq!(
        eval(&assert_body(UnwindAction::Terminate, vec![]), false, 10),
        terminated(0, "boom")
    );
    assert_eq!(
        eval(&assert_body(UnwindAction::Unreachable, vec![]), false, 10),
        Err(CfgEvalError::UnwindIntoUnreachable {
            bb: 0,
            msg: Box::new(custom_msg("boom")),
        })
    );
    assert_eq!(
        eval(
            &assert_body(UnwindAction::Cleanup(2), vec![resume()]),
            false,
            10
        ),
        panicked(0, "boom")
    );
    assert_eq!(
        eval(
            &assert_body(UnwindAction::Cleanup(2), vec![terminate()]),
            false,
            10
        ),
        terminated(0, "boom")
    );

    // A cleanup chain runs every block's statements and terminators, consuming fuel.
    let chain = assert_body(
        UnwindAction::Cleanup(2),
        vec![
            cleanup_blk(
                vec![
                    Statement::StorageLive(Local(2)),
                    assign(local(2), Rvalue::Use(cint(1, u8_ty()))),
                ],
                goto_t(3),
            ),
            cleanup_blk(
                vec![Statement::StorageDead(Local(2))],
                drop_t(local(0), 4, UnwindAction::Terminate),
            ),
            resume(),
        ],
    );
    assert_eq!(eval(&chain, false, 4), panicked(0, "boom"));
    match eval(&chain, false, 2) {
        Ok(CfgEvalOutcome::OutOfFuel { bb: 3, state }) => {
            assert_eq!(state.slots[0], LocalSlotState::Init(u8v(7)));
            assert_eq!(state.slots[2], LocalSlotState::Init(u8v(1)));
        }
        other => panic!("expected OutOfFuel at bb3, got {other:?}"),
    }
    match eval(&chain, false, 3) {
        Ok(CfgEvalOutcome::OutOfFuel { bb: 4, state }) => {
            assert_eq!(state.slots[2], LocalSlotState::Dead)
        }
        other => panic!("expected OutOfFuel at bb4, got {other:?}"),
    }
    // An endless cleanup loop runs out of fuel.
    let spin = assert_body(
        UnwindAction::Cleanup(2),
        vec![cleanup_blk(vec![], goto_t(2))],
    );
    assert!(matches!(
        eval(&spin, false, 50),
        Ok(CfgEvalOutcome::OutOfFuel { bb: 2, .. })
    ));
    // Undefined behavior inside a cleanup block is reported with its location.
    let ub = assert_body(
        UnwindAction::Cleanup(2),
        vec![cleanup_blk(
            vec![assign(local(0), Rvalue::Use(cp(2)))],
            Terminator::UnwindResume,
        )],
    );
    assert_eq!(
        eval(&ub, false, 10),
        Err(CfgEvalError::Statement {
            bb: 2,
            index: 0,
            error: RvalueEvalError::DeadLocal(Local(2)),
        })
    );
    let unreachable = assert_body(
        UnwindAction::Cleanup(2),
        vec![cleanup_blk(vec![], Terminator::Unreachable)],
    );
    assert_eq!(
        eval(&unreachable, false, 10),
        Err(CfgEvalError::UnreachableReached { bb: 2 })
    );
    // A second panic inside a cleanup block aborts (`Terminate`) or is UB (`Unreachable`); a
    // passing cleanup assertion keeps unwinding the original panic.
    let nested = |cond: bool, unwind: UnwindAction| {
        assert_body(
            UnwindAction::Cleanup(2),
            vec![
                cleanup_blk(
                    vec![],
                    assert_t(cbool(cond), true, custom("double"), 3, unwind),
                ),
                resume(),
            ],
        )
    };
    assert_eq!(
        eval(&nested(false, UnwindAction::Terminate), false, 10),
        terminated(2, "double")
    );
    assert_eq!(
        eval(&nested(false, UnwindAction::Unreachable), false, 10),
        Err(CfgEvalError::UnwindIntoUnreachable {
            bb: 2,
            msg: Box::new(custom_msg("double")),
        })
    );
    assert_eq!(
        eval(&nested(true, UnwindAction::Terminate), false, 10),
        panicked(0, "boom")
    );
}

#[test]
fn test_cfg_return_requires_a_fully_initialized_inhabited_return_place() {
    let eval = |body: &Body| eval_lowered_body_cfg(&lower_ok(body, PW), &[], 10);
    // `_0` never written (also for a zero-sized `_0`: initialization is tracked per local).
    for ret_ty in [u32_ty(), unit()] {
        assert_eq!(
            eval(&mk_body(
                vec![ret_ty],
                vec![blk(vec![], Terminator::Return)]
            )),
            Err(CfgEvalError::Terminator {
                bb: 0,
                error: RvalueEvalError::UninitializedLocal(Local(0)),
            })
        );
    }
    // A partially initialized typed struct cannot be returned; a complete one can.
    let (pair_def, pair_ty) = adt(AdtDef::new_struct("Pair", vec![u8_ty(), u32_ty()]));
    let write0 = assign(
        place(0, vec![field(0, u8_ty())]),
        Rvalue::Use(cint(1, u8_ty())),
    );
    let write1 = assign(
        place(0, vec![field(1, u32_ty())]),
        Rvalue::Use(cint(2, u32_ty())),
    );
    assert_eq!(
        eval(&mk_body(
            vec![pair_ty.clone()],
            vec![blk(vec![write0.clone()], Terminator::Return)]
        )),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::UninitializedLocal(Local(0)),
        })
    );
    assert_eq!(
        returned(eval(&mk_body(
            vec![pair_ty.clone()],
            vec![blk(
                vec![write0.clone(), write1.clone()],
                Terminator::Return
            )]
        ))),
        MirValue::adt(&pair_def, 0, vec![u8v(1), u32v(2)])
    );
    // An enum built field-by-field plus `SetDiscriminant` across blocks.
    let (enum_def, enum_ty) = repr_u8_enum();
    let body = mk_body(
        vec![enum_ty.clone()],
        vec![
            blk(
                vec![assign(
                    place(0, vec![ProjectionElem::Downcast(1), field(0, u16_ty())]),
                    Rvalue::Use(cint(5, u16_ty())),
                )],
                goto_t(1),
            ),
            blk(
                vec![Statement::SetDiscriminant {
                    place: local(0),
                    variant_index: 1,
                }],
                Terminator::Return,
            ),
        ],
    );
    assert_eq!(
        returned(eval(&body)),
        MirValue::adt(&enum_def, 1, vec![u16v(5)])
    );
    // Returning reads `_0` as a typed value, which enforces scalar valid ranges.
    let (_, nz_ty) = non_zero_u32();
    let zero = assign(
        place(0, vec![field(0, u32_ty())]),
        Rvalue::Use(cint(0, u32_ty())),
    );
    assert_eq!(
        eval(&mk_body(
            vec![nz_ty.clone()],
            vec![blk(vec![zero], Terminator::Return)]
        )),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: nz_ty.clone(),
                bits: 0,
            }),
        })
    );
    // Statically: no return place, an uninhabited return type, or a `Return` in a cleanup block.
    assert_eq!(
        lower_term_err(&mk_body(vec![], vec![blk(vec![], Terminator::Return)]), PW),
        (0, TerminatorLowerError::MissingReturnPlace)
    );
    let (_, void_ty) = adt(AdtDef::new_enum("Void", None, vec![]));
    for ret_ty in [Ty::Never, void_ty, Ty::Tuple(vec![u8_ty(), Ty::Never])] {
        assert_eq!(
            lower_term_err(
                &mk_body(vec![ret_ty.clone()], vec![blk(vec![], Terminator::Return)]),
                PW
            ),
            (0, TerminatorLowerError::UninhabitedReturnPlace(ret_ty))
        );
    }
    let cleanup_return = mk_body(
        vec![u8_ty()],
        vec![
            blk(
                vec![],
                assert_t(cbool(true), true, custom("x"), 0, UnwindAction::Cleanup(1)),
            ),
            cleanup_blk(vec![], Terminator::Return),
        ],
    );
    assert_eq!(
        lower_term_err(&cleanup_return, PW),
        (1, TerminatorLowerError::ReturnInCleanupBlock)
    );
    // `-> !` functions may still diverge without returning.
    let diverge = lower_ok(&mk_body(vec![Ty::Never], vec![blk(vec![], goto_t(0))]), PW);
    assert!(matches!(
        eval_lowered_body_cfg(&diverge, &[], 3),
        Ok(CfgEvalOutcome::OutOfFuel { bb: 0, .. })
    ));
}

#[test]
fn test_cfg_drop_is_a_no_op_on_live_places() {
    let eval = |body: &Body, args: &[MirValue], fuel: usize| {
        eval_lowered_body_cfg(&lower_ok(body, PW), args, fuel)
    };
    // `fn(x: u32) -> u32 { drop(x); x }`: the dropped value is unchanged.
    let body = mk_body(
        vec![u32_ty(), u32_ty()],
        vec![
            blk(vec![], drop_t(local(1), 1, UnwindAction::Continue)),
            blk(
                vec![assign(local(0), Rvalue::Use(cp(1)))],
                Terminator::Return,
            ),
        ],
    );
    assert_eq!(returned(eval(&body, &[u32v(42)], 10)), u32v(42));
    // Dropping an uninitialized field of a partially initialized struct leaves the shell as is.
    let (pair_def, pair_ty) = adt(AdtDef::new_struct("Pair", vec![u8_ty(), u32_ty()]));
    let write0 = assign(
        place(0, vec![field(0, u8_ty())]),
        Rvalue::Use(cint(1, u8_ty())),
    );
    let body = mk_body(
        vec![pair_ty.clone()],
        vec![
            blk(
                vec![write0.clone()],
                drop_t(
                    place(0, vec![field(1, u32_ty())]),
                    1,
                    UnwindAction::Continue,
                ),
            ),
            blk(
                vec![assign(
                    place(0, vec![field(1, u32_ty())]),
                    Rvalue::Use(cint(2, u32_ty())),
                )],
                Terminator::Return,
            ),
        ],
    );
    let lowered = lower_ok(&body, PW);
    let mut expected = StatementEvalState::from_body(&lowered, &[]).unwrap();
    run(write0, &mut expected).unwrap();
    assert!(matches!(expected.slots[0], LocalSlotState::PartialShell(_)));
    assert_eq!(
        eval_lowered_body_cfg(&lowered, &[], 1),
        Ok(CfgEvalOutcome::OutOfFuel {
            bb: 1,
            state: expected
        })
    );
    assert_eq!(
        returned(eval_lowered_body_cfg(&lowered, &[], 2)),
        MirValue::adt(&pair_def, 0, vec![u8v(1), u32v(2)])
    );
    // Dropping a dead local, or a place indexed by an uninitialized local, is UB.
    let arr = Ty::Array(Box::new(u32_ty()), 2);
    let dead = mk_body(
        vec![u32_ty(), u32_ty()],
        vec![
            blk(vec![], drop_t(local(1), 1, UnwindAction::Continue)),
            blk(vec![], Terminator::Return),
        ],
    );
    assert_eq!(
        eval(&dead, &[], 10),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::DeadLocal(Local(1)),
        })
    );
    let uninit_index = mk_body(
        vec![u32_ty(), arr, usize_ty()],
        vec![
            blk(
                vec![
                    Statement::StorageLive(Local(1)),
                    Statement::StorageLive(Local(2)),
                ],
                drop_t(
                    place(1, vec![ProjectionElem::Index(Local(2))]),
                    1,
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    assert_eq!(
        eval(&uninit_index, &[], 10),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::UninitializedLocal(Local(2)),
        })
    );
    // Statically: the unwind edge must lead to a cleanup block, and cleanup blocks may not
    // `Continue` unwinding.
    let bad_unwind = mk_body(
        vec![u32_ty()],
        vec![
            blk(vec![], drop_t(local(0), 1, UnwindAction::Cleanup(1))),
            blk(vec![], Terminator::Return),
        ],
    );
    assert!(matches!(
        lower_term_err(&bad_unwind, PW),
        (0, TerminatorLowerError::InvalidEdge { target: 1, .. })
    ));
    let continue_in_cleanup = mk_body(
        vec![u32_ty()],
        vec![
            blk(vec![], drop_t(local(0), 0, UnwindAction::Cleanup(1))),
            cleanup_blk(vec![], drop_t(local(0), 2, UnwindAction::Continue)),
            cleanup_blk(vec![], Terminator::UnwindResume),
        ],
    );
    assert_eq!(
        lower_term_err(&continue_in_cleanup, PW),
        (
            1,
            TerminatorLowerError::InvalidUnwindAction {
                unwind: UnwindAction::Continue,
                reason: "UnwindAction::Continue in a cleanup block",
            }
        )
    );
}

const FN_ADD: u128 = 0xADD;

/// `fn(a: u32, b: u32) -> u32`: `bb0: _0 = add(move _1, copy _2) -> [return: <target>, unwind:
/// <unwind>]`, `bb1: return`, followed by `extra` blocks from `bb2` on.
fn call_body(target: Option<usize>, unwind: UnwindAction, extra: Vec<BasicBlockData>) -> Body {
    let mut blocks = vec![
        blk(
            vec![],
            Terminator::Call {
                func: cint(FN_ADD, usize_ty()),
                args: vec![mv(1), cp(2)],
                destination: local(0),
                target,
                unwind,
            },
        ),
        blk(vec![], Terminator::Return),
    ];
    blocks.extend(extra);
    mk_body(vec![u32_ty(), u32_ty(), u32_ty()], blocks)
}

/// Call handler adding two `u32` arguments of `FN_ADD`.
fn add_handler(
    _bb: usize,
    func: &MirValue,
    args: &[MirValue],
) -> Result<CallOutcome, RvalueEvalError> {
    assert_eq!(func, &usizev(FN_ADD));
    match args {
        [MirValue::Int { bits: a, .. }, MirValue::Int { bits: b, .. }] => {
            Ok(CallOutcome::Return(u32v((a + b) & 0xFFFF_FFFF)))
        }
        _ => panic!("unexpected arguments {args:?}"),
    }
}

#[test]
fn test_cfg_calls_go_through_the_call_handler() {
    let args = [u32v(40), u32v(2)];
    let body = lower_ok(&call_body(Some(1), UnwindAction::Continue, vec![]), PW);
    assert_eq!(
        eval_lowered_body_cfg(&body, &args, 10),
        Err(CfgEvalError::UnsupportedCall { bb: 0 })
    );
    let mut log = Vec::new();
    let outcome = eval_lowered_body_cfg_with_calls(&body, &args, 10, |bb, func, call_args| {
        log.push((bb, func.clone(), call_args.to_vec()));
        add_handler(bb, func, call_args)
    });
    assert_eq!(returned(outcome), u32v(42));
    assert_eq!(log, vec![(0, usizev(FN_ADD), args.to_vec())]);

    // A moved argument local is deinitialized by the call; a copied one is not.
    let reread = |l: usize| {
        call_body(
            Some(2),
            UnwindAction::Continue,
            vec![blk(
                vec![assign(local(0), Rvalue::BinaryOp(BinOp::Add, cp(0), cp(l)))],
                goto_t(1),
            )],
        )
    };
    assert_eq!(
        returned(eval_lowered_body_cfg_with_calls(
            &lower_ok(&reread(2), PW),
            &args,
            10,
            add_handler
        )),
        u32v(44)
    );
    assert_eq!(
        eval_lowered_body_cfg_with_calls(&lower_ok(&reread(1), PW), &args, 10, add_handler),
        Err(CfgEvalError::Statement {
            bb: 2,
            index: 0,
            error: RvalueEvalError::UninitializedLocal(Local(1)),
        })
    );
    // Chained calls: the second call consumes the first call's result.
    let chained = mk_body(
        vec![u32_ty(), u32_ty(), u32_ty()],
        vec![
            blk(
                vec![],
                Terminator::Call {
                    func: cint(FN_ADD, usize_ty()),
                    args: vec![cp(1), cp(2)],
                    destination: local(2),
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
            ),
            blk(
                vec![],
                Terminator::Call {
                    func: cint(FN_ADD, usize_ty()),
                    args: vec![cp(2), cp(2)],
                    destination: local(0),
                    target: Some(2),
                    unwind: UnwindAction::Terminate,
                },
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    let mut blocks_called = Vec::new();
    let outcome = eval_lowered_body_cfg_with_calls(
        &lower_ok(&chained, PW),
        &args,
        10,
        |bb, func, call_args| {
            blocks_called.push(bb);
            add_handler(bb, func, call_args)
        },
    );
    assert_eq!(returned(outcome), u32v(84));
    assert_eq!(blocks_called, vec![0, 1]);

    // Panicking callees unwind like a failed assertion; the destination is left unchanged.
    let panicking =
        |_: usize, _: &MirValue, _: &[MirValue]| Ok(CallOutcome::Panic("callee".into()));
    let unwound = |unwind: UnwindAction, extra: Vec<BasicBlockData>| {
        eval_lowered_body_cfg_with_calls(
            &lower_ok(&call_body(Some(1), unwind, extra), PW),
            &args,
            10,
            panicking,
        )
    };
    let callee = || custom_msg("callee");
    assert_eq!(
        unwound(UnwindAction::Continue, vec![]),
        Ok(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: callee()
        })
    );
    assert_eq!(
        unwound(UnwindAction::Terminate, vec![]),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: callee()
        })
    );
    assert_eq!(
        unwound(UnwindAction::Unreachable, vec![]),
        Err(CfgEvalError::UnwindIntoUnreachable {
            bb: 0,
            msg: Box::new(callee()),
        })
    );
    assert_eq!(
        unwound(
            UnwindAction::Cleanup(2),
            vec![cleanup_blk(vec![], Terminator::UnwindResume)]
        ),
        Ok(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: callee()
        })
    );
    let mut pre_init = call_body(
        Some(1),
        UnwindAction::Cleanup(2),
        vec![cleanup_blk(vec![], goto_t(2))],
    );
    pre_init.basic_blocks[0].statements = vec![assign(local(0), Rvalue::Use(cint(5, u32_ty())))];
    match eval_lowered_body_cfg_with_calls(&lower_ok(&pre_init, PW), &args, 3, panicking) {
        Ok(CfgEvalOutcome::OutOfFuel { bb: 2, state }) => {
            assert_eq!(state.slots[0], LocalSlotState::Init(u32v(5)));
            assert_eq!(state.slots[1], LocalSlotState::Uninit);
            assert_eq!(state.slots[2], LocalSlotState::Init(u32v(2)));
        }
        other => panic!("expected OutOfFuel in the cleanup loop, got {other:?}"),
    }

    // Undefined behavior reported by the handler, or ill-typed / ill-formed return values.
    let with = |handler: &dyn Fn() -> Result<CallOutcome, RvalueEvalError>| {
        eval_lowered_body_cfg_with_calls(&body, &args, 10, |_, _, _| handler())
    };
    assert_eq!(
        with(&|| Err(RvalueEvalError::AssumeFalse)),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::AssumeFalse,
        })
    );
    assert!(matches!(
        with(&|| Ok(CallOutcome::Return(u8v(1)))),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::TypeMismatch(_),
        })
    ));
    assert_eq!(
        with(&|| Ok(CallOutcome::Return(uint(1 << 32, u32_ty())))),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: u32_ty(),
                bits: 1 << 32,
            }),
        })
    );
    let (nz_def, nz_ty) = non_zero_u32();
    let nz_call = mk_body(
        vec![nz_ty.clone()],
        vec![
            blk(
                vec![],
                Terminator::Call {
                    func: Operand::Constant(Constant::Unit),
                    args: vec![],
                    destination: local(0),
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    let nz_call = lower_ok(&nz_call, PW);
    assert_eq!(
        returned(eval_lowered_body_cfg_with_calls(
            &nz_call,
            &[],
            10,
            |_, func, _| {
                assert_eq!(func, &MirValue::Unit);
                Ok(CallOutcome::Return(MirValue::adt(
                    &nz_def,
                    0,
                    vec![u32v(9)],
                )))
            }
        )),
        MirValue::adt(&nz_def, 0, vec![u32v(9)])
    );
    assert_eq!(
        eval_lowered_body_cfg_with_calls(&nz_call, &[], 10, |_, _, _| {
            Ok(CallOutcome::Return(MirValue::adt(
                &nz_def,
                0,
                vec![u32v(0)],
            )))
        }),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: nz_ty.clone(),
                bits: 0,
            }),
        })
    );
    // A call without a return target must not return.
    let diverging = lower_ok(&call_body(None, UnwindAction::Continue, vec![]), PW);
    assert_eq!(
        eval_lowered_body_cfg_with_calls(&diverging, &args, 10, add_handler),
        Err(CfgEvalError::UnreachableReached { bb: 0 })
    );
    assert_eq!(
        eval_lowered_body_cfg_with_calls(&diverging, &args, 10, panicking),
        Ok(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: callee()
        })
    );
    // Faulting arguments or destinations are reported before the callee runs.
    let mut called = false;
    let mut dead_dest = call_body(Some(1), UnwindAction::Continue, vec![]);
    dead_dest.local_decls.push(u32_ty());
    if let Some(Terminator::Call { destination, .. }) = &mut dead_dest.basic_blocks[0].terminator {
        *destination = local(3);
    }
    assert_eq!(
        eval_lowered_body_cfg_with_calls(
            &lower_ok(&dead_dest, PW),
            &args,
            10,
            |bb, func, call_args| {
                called = true;
                add_handler(bb, func, call_args)
            }
        ),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::DeadLocal(Local(3)),
        })
    );
    let mut dead_arg = call_body(Some(1), UnwindAction::Continue, vec![]);
    dead_arg.local_decls.push(u32_ty());
    if let Some(Terminator::Call { args, .. }) = &mut dead_arg.basic_blocks[0].terminator {
        args[1] = cp(3);
    }
    assert_eq!(
        eval_lowered_body_cfg_with_calls(
            &lower_ok(&dead_arg, PW),
            &args,
            10,
            |bb, func, call_args| {
                called = true;
                add_handler(bb, func, call_args)
            }
        ),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::DeadLocal(Local(3)),
        })
    );
    assert!(!called);
    // Statically: a call into an uninhabited destination must not have a return target.
    let never_dest = |target: Option<usize>| {
        mk_body(
            vec![unit(), Ty::Never],
            vec![
                blk(
                    vec![Statement::StorageLive(Local(1))],
                    Terminator::Call {
                        func: Operand::Constant(Constant::Unit),
                        args: vec![],
                        destination: local(1),
                        target,
                        unwind: UnwindAction::Continue,
                    },
                ),
                blk(
                    vec![assign(
                        local(0),
                        Rvalue::Use(Operand::Constant(Constant::Unit)),
                    )],
                    Terminator::Return,
                ),
            ],
        )
    };
    assert_eq!(
        lower_term_err(&never_dest(Some(1)), PW),
        (
            0,
            TerminatorLowerError::CallToUninhabitedDestinationWithTarget(Ty::Never)
        )
    );
    assert_eq!(
        eval_lowered_body_cfg_with_calls(&lower_ok(&never_dest(None), PW), &[], 10, |_, _, _| {
            Ok(CallOutcome::Return(MirValue::Unit))
        }),
        Err(CfgEvalError::UnreachableReached { bb: 0 })
    );
}

#[test]
fn test_cfg_lowering_rejects_bad_targets_and_cleanup_edges() {
    let decls = || vec![u8_ty(), Ty::Bool];
    let err = |blocks: Vec<BasicBlockData>| lower_term_err(&mk_body(decls(), blocks), PW);
    let ret = || blk(vec![], Terminator::Return);
    let resume = || cleanup_blk(vec![], Terminator::UnwindResume);
    let call = |target: Option<usize>, unwind: UnwindAction| Terminator::Call {
        func: Operand::Constant(Constant::Unit),
        args: vec![],
        destination: local(0),
        target,
        unwind,
    };
    let invalid_target = |target: usize, num_blocks: usize| TerminatorLowerError::InvalidTarget {
        target,
        num_blocks,
    };

    // Out-of-range targets on every kind of edge.
    assert_eq!(err(vec![blk(vec![], goto_t(3))]), (0, invalid_target(3, 1)));
    assert_eq!(
        err(vec![blk(
            vec![],
            Terminator::SwitchInt {
                discr: cp(1),
                targets: SwitchTargets::static_if(0, 0, 9),
            }
        )]),
        (0, invalid_target(9, 1))
    );
    assert_eq!(
        err(vec![blk(
            vec![],
            assert_t(cp(1), true, custom("a"), 5, UnwindAction::Continue)
        )]),
        (0, invalid_target(5, 1))
    );
    assert_eq!(
        err(vec![blk(
            vec![],
            drop_t(local(0), 0, UnwindAction::Cleanup(7))
        )]),
        (0, invalid_target(7, 1))
    );
    assert_eq!(
        err(vec![blk(vec![], call(Some(2), UnwindAction::Continue))]),
        (0, invalid_target(2, 1))
    );
    // Unreachable blocks are validated too.
    assert_eq!(
        err(vec![ret(), blk(vec![], goto_t(4))]),
        (1, invalid_target(4, 2))
    );

    // Normal edges stay on one side of the cleanup boundary; unwind edges enter cleanup blocks.
    assert!(matches!(
        err(vec![blk(vec![], goto_t(1)), resume()]),
        (0, TerminatorLowerError::InvalidEdge { target: 1, .. })
    ));
    assert!(matches!(
        err(vec![
            blk(
                vec![],
                assert_t(cp(1), true, custom("a"), 0, UnwindAction::Cleanup(1))
            ),
            cleanup_blk(vec![], goto_t(0)),
        ]),
        (1, TerminatorLowerError::InvalidEdge { target: 0, .. })
    ));
    assert!(matches!(
        err(vec![
            blk(
                vec![],
                Terminator::SwitchInt {
                    discr: cp(1),
                    targets: SwitchTargets::static_if(0, 2, 1),
                }
            ),
            resume(),
            ret(),
        ]),
        (0, TerminatorLowerError::InvalidEdge { target: 1, .. })
    ));
    assert!(matches!(
        err(vec![
            blk(vec![], call(Some(1), UnwindAction::Continue)),
            resume()
        ]),
        (0, TerminatorLowerError::InvalidEdge { target: 1, .. })
    ));
    assert!(matches!(
        err(vec![blk(vec![], call(Some(0), UnwindAction::Cleanup(0)))]),
        (0, TerminatorLowerError::InvalidEdge { target: 0, .. })
    ));
    // Inside cleanup blocks: no further `Cleanup` or `Continue` unwinding, no `Return`.
    let in_cleanup = |term: Terminator| {
        err(vec![
            blk(vec![], call(Some(0), UnwindAction::Cleanup(1))),
            cleanup_blk(vec![], term),
            resume(),
        ])
    };
    assert!(matches!(
        in_cleanup(call(Some(2), UnwindAction::Cleanup(2))),
        (
            1,
            TerminatorLowerError::InvalidUnwindAction {
                unwind: UnwindAction::Cleanup(2),
                ..
            }
        )
    ));
    assert!(matches!(
        in_cleanup(assert_t(
            cp(1),
            true,
            custom("a"),
            2,
            UnwindAction::Continue
        )),
        (
            1,
            TerminatorLowerError::InvalidUnwindAction {
                unwind: UnwindAction::Continue,
                ..
            }
        )
    ));
    assert_eq!(
        in_cleanup(Terminator::Return),
        (1, TerminatorLowerError::ReturnInCleanupBlock)
    );
    for ok in [
        call(Some(2), UnwindAction::Terminate),
        call(None, UnwindAction::Unreachable),
        drop_t(local(0), 2, UnwindAction::Terminate),
        Terminator::UnwindTerminate,
        Terminator::Unreachable,
    ] {
        let body = mk_body(
            decls(),
            vec![
                blk(vec![], call(Some(0), UnwindAction::Cleanup(1))),
                cleanup_blk(vec![], ok.clone()),
                resume(),
            ],
        );
        assert!(lower_body(&body, PW).is_ok(), "{ok:?}");
    }
    // Unwinding terminators only inside cleanup blocks; the entry block is not a cleanup block.
    for term in [Terminator::UnwindResume, Terminator::UnwindTerminate] {
        assert_eq!(
            err(vec![blk(vec![], term)]),
            (0, TerminatorLowerError::UnwindTerminatorOutsideCleanup)
        );
    }
    assert_eq!(
        err(vec![resume()]),
        (0, TerminatorLowerError::CleanupEntryBlock)
    );
    // Operand lowering errors are reported as such (not as terminator errors).
    let bad_local = mk_body(
        decls(),
        vec![blk(
            vec![],
            Terminator::SwitchInt {
                discr: cp(9),
                targets: SwitchTargets::static_if(0, 0, 0),
            },
        )],
    );
    assert!(matches!(
        lower_body(&bad_local, PW),
        Err(e) if !matches!(e, RvalueLowerError::InvalidTerminator { .. })
    ));
    // `lower_terminator` itself rejects a block index outside the body.
    assert_eq!(
        lower_terminator(&Terminator::Return, 3, &mk_body(decls(), vec![ret()]), PW),
        Err(RvalueLowerError::InvalidTerminator {
            bb: 3,
            error: invalid_target(3, 1),
        })
    );
}

#[test]
fn test_cfg_evaluator_rejects_hand_built_bodies_that_break_the_discipline() {
    let lb = |terminator: Option<LoweredTerminator>, is_cleanup: bool| LoweredBasicBlock {
        statements: vec![],
        terminator,
        is_cleanup,
    };
    let body = |basic_blocks: Vec<LoweredBasicBlock>| LoweredBody {
        local_decls: vec![u8_ty()],
        basic_blocks,
        ptr_width: PW,
    };
    let eval = |blocks: Vec<LoweredBasicBlock>| eval_lowered_body_cfg(&body(blocks), &[], 10);
    let panic_to = |unwind: UnwindAction| LoweredTerminator::Assert {
        cond: cbool(false),
        expected: true,
        msg: custom("p"),
        target: 0,
        unwind,
    };
    assert_eq!(eval(vec![]), Err(CfgEvalError::InvalidBlock { bb: 0 }));
    assert_eq!(
        eval(vec![lb(Some(LoweredTerminator::Goto { target: 9 }), false)]),
        Err(CfgEvalError::InvalidBlock { bb: 9 })
    );
    assert_eq!(
        eval(vec![lb(None, false)]),
        Err(CfgEvalError::MissingTerminator { bb: 0 })
    );
    // Entering a cleanup block without unwinding (or starting in one), and vice versa.
    assert_eq!(
        eval(vec![
            lb(Some(LoweredTerminator::Goto { target: 1 }), false),
            lb(Some(LoweredTerminator::UnwindResume), true),
        ]),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 1 })
    );
    assert_eq!(
        eval(vec![lb(Some(LoweredTerminator::UnwindResume), true)]),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 0 })
    );
    assert_eq!(
        eval(vec![lb(Some(panic_to(UnwindAction::Cleanup(0))), false)]),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 0 })
    );
    assert_eq!(
        eval(vec![
            lb(Some(panic_to(UnwindAction::Cleanup(1))), false),
            lb(Some(LoweredTerminator::Goto { target: 0 }), true),
        ]),
        Err(CfgEvalError::InvalidEdge { from: 1, to: 0 })
    );
    // Unwinding terminators while not unwinding; returning or re-unwinding while unwinding.
    for term in [
        LoweredTerminator::UnwindResume,
        LoweredTerminator::UnwindTerminate,
    ] {
        assert_eq!(
            eval(vec![lb(Some(term), false)]),
            Err(CfgEvalError::InvalidUnwind { bb: 0 })
        );
    }
    for in_cleanup in [
        LoweredTerminator::Return { ret_ty: u8_ty() },
        panic_to(UnwindAction::Continue),
        panic_to(UnwindAction::Cleanup(1)),
    ] {
        assert_eq!(
            eval(vec![
                lb(Some(panic_to(UnwindAction::Cleanup(1))), false),
                lb(Some(in_cleanup), true)
            ]),
            Err(CfgEvalError::InvalidUnwind { bb: 1 })
        );
    }
    // Lowered types that disagree with the body are runtime type errors.
    let type_errors = [
        LoweredTerminator::SwitchInt {
            discr: cint(1, u16_ty()),
            discr_ty: u8_ty(),
            targets: SwitchTargets::static_if(1, 0, 0),
        },
        LoweredTerminator::SwitchInt {
            discr: Operand::Constant(Constant::Unit),
            discr_ty: unit(),
            targets: SwitchTargets::static_if(1, 0, 0),
        },
        LoweredTerminator::Return { ret_ty: u16_ty() },
        LoweredTerminator::Assert {
            cond: cint(1, u8_ty()),
            expected: true,
            msg: custom("x"),
            target: 0,
            unwind: UnwindAction::Continue,
        },
        LoweredTerminator::Call {
            func: Operand::Constant(Constant::Unit),
            func_ty: u8_ty(),
            args: vec![],
            arg_tys: vec![],
            destination: local(0),
            dest_ty: u8_ty(),
            target: Some(0),
            unwind: UnwindAction::Continue,
        },
        LoweredTerminator::Call {
            func: Operand::Constant(Constant::Unit),
            func_ty: unit(),
            args: vec![cint(1, u8_ty())],
            arg_tys: vec![],
            destination: local(0),
            dest_ty: u8_ty(),
            target: Some(0),
            unwind: UnwindAction::Continue,
        },
        LoweredTerminator::Call {
            func: Operand::Constant(Constant::Unit),
            func_ty: unit(),
            args: vec![cint(1, u8_ty())],
            arg_tys: vec![u16_ty()],
            destination: local(0),
            dest_ty: u8_ty(),
            target: Some(0),
            unwind: UnwindAction::Continue,
        },
        LoweredTerminator::Drop {
            place: local(0),
            place_ty: u16_ty(),
            target: 0,
            unwind: UnwindAction::Continue,
        },
    ];
    for term in type_errors {
        let result = eval_lowered_body_cfg_with_calls(
            &body(vec![lb(Some(term.clone()), false)]),
            &[],
            10,
            |_, _, _| Ok(CallOutcome::Return(u8v(0))),
        );
        assert!(
            matches!(
                result,
                Err(CfgEvalError::Terminator {
                    bb: 0,
                    error: RvalueEvalError::TypeMismatch(_)
                })
            ),
            "{term:?}: {result:?}"
        );
    }
    let never = LoweredBody {
        local_decls: vec![Ty::Never],
        basic_blocks: vec![lb(
            Some(LoweredTerminator::Return { ret_ty: Ty::Never }),
            false,
        )],
        ptr_width: PW,
    };
    assert!(matches!(
        eval_lowered_body_cfg(&never, &[], 10),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::TypeMismatch(_)
        })
    ));
}

#[test]
fn test_cfg_arguments_must_be_well_formed_values_of_the_parameter_types() {
    let body = lower_ok(&countdown_body(), PW);
    let invalid = |args: &[MirValue]| match eval_lowered_body_cfg(&body, args, 5) {
        Err(CfgEvalError::InvalidArguments(err)) => err,
        other => panic!("expected InvalidArguments for {args:?}, got {other:?}"),
    };
    assert!(matches!(
        invalid(&[u8v(1)]),
        RvalueEvalError::TypeMismatch(_)
    ));
    assert!(matches!(
        invalid(&[u32v(1), u32v(2)]),
        RvalueEvalError::TypeMismatch(_)
    ));
    assert!(matches!(
        invalid(&[u32v(1), MirValue::Bool(true), u32v(3)]),
        RvalueEvalError::TypeMismatch(_)
    ));
    assert_eq!(
        invalid(&[uint(1 << 32, u32_ty())]),
        RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: u32_ty(),
            bits: 1 << 32,
        })
    );
    // Null references, over-wide pointers, and scalar-range violations nested in aggregates.
    let r = ref_ty(u8_ty());
    let p = raw(u8_ty(), Mutability::Not);
    let (nz_def, nz_ty) = non_zero_u32();
    let decls = vec![
        unit(),
        r.clone(),
        p.clone(),
        Ty::Tuple(vec![u8_ty(), nz_ty.clone()]),
    ];
    let body = lower_ok(
        &mk_body(decls.clone(), vec![blk(vec![], Terminator::Unreachable)]),
        PtrWidth::Bits32,
    );
    let good = [
        MirValue::ptr(PointerValue::with_provenance(0x10, 1, 0), r.clone()),
        MirValue::ptr(PointerValue::without_provenance(0), p.clone()),
        MirValue::Tuple(vec![u8v(1), MirValue::adt(&nz_def, 0, vec![u32v(1)])]),
    ];
    assert_eq!(
        eval_lowered_body_cfg(&body, &good, 5),
        Err(CfgEvalError::UnreachableReached { bb: 0 })
    );
    let with = |idx: usize, val: MirValue| {
        let mut args = good.to_vec();
        args[idx] = val;
        match eval_lowered_body_cfg(&body, &args, 5) {
            Err(CfgEvalError::InvalidArguments(err)) => err,
            other => panic!("expected InvalidArguments, got {other:?}"),
        }
    };
    let bit_pattern = |target_ty: Ty, bits: u128| {
        RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern { target_ty, bits })
    };
    assert_eq!(
        with(
            0,
            MirValue::ptr(PointerValue::without_provenance(0), r.clone())
        ),
        bit_pattern(r.clone(), 0)
    );
    assert_eq!(
        with(
            1,
            MirValue::ptr(PointerValue::without_provenance(1 << 32), p.clone())
        ),
        bit_pattern(p.clone(), 1 << 32)
    );
    assert_eq!(
        with(
            2,
            MirValue::Tuple(vec![u8v(1), MirValue::adt(&nz_def, 0, vec![u32v(0)])])
        ),
        bit_pattern(nz_ty, 0)
    );
    assert_eq!(
        with(
            2,
            MirValue::Tuple(vec![u8v(0x100), MirValue::adt(&nz_def, 0, vec![u32v(1)])])
        ),
        bit_pattern(u8_ty(), 0x100)
    );
}

#[test]
fn test_cfg_matches_on_typed_enum_discriminants() {
    // `#[repr(i8)] enum S { Neg(u8) = -1, Pos(u16, u8) = 5, Zero = 0 }`
    let (def, enum_ty) = adt(AdtDef::new_enum(
        "S",
        Some(ScalarTy::Int(IntTy::I8)),
        vec![
            VariantDef::new("Neg", vec![u8_ty()]).with_discriminant(u128::MAX),
            VariantDef::new("Pos", vec![u16_ty(), u8_ty()]).with_discriminant(5),
            VariantDef::new("Zero", vec![]).with_discriminant(0),
        ],
    ));
    let downcast = |variant: usize, idx: usize, ty: Ty| {
        Operand::Copy(place(
            1,
            vec![ProjectionElem::Downcast(variant), field(idx, ty)],
        ))
    };
    let widen = |op: Operand| Rvalue::Cast(CastKind::IntToInt, op, u32_ty());
    // fn(s: S) -> u32 { match s { Neg(x) => x as u32, Pos(y, z) => y as u32 + z as u32, Zero => 100 } }
    let body = mk_body(
        vec![u32_ty(), enum_ty.clone(), i8_ty(), u32_ty()],
        vec![
            blk(
                vec![
                    Statement::StorageLive(Local(2)),
                    assign(local(2), Rvalue::Discriminant(local(1))),
                ],
                Terminator::SwitchInt {
                    discr: cp(2),
                    targets: SwitchTargets::new([(0xFF, 1), (5, 2), (0, 3)], 4),
                },
            ),
            blk(
                vec![assign(local(0), widen(downcast(0, 0, u8_ty())))],
                goto_t(5),
            ),
            blk(
                vec![
                    Statement::StorageLive(Local(3)),
                    assign(local(3), widen(downcast(1, 1, u8_ty()))),
                    assign(local(0), widen(downcast(1, 0, u16_ty()))),
                    assign(local(0), Rvalue::BinaryOp(BinOp::Add, cp(0), cp(3))),
                ],
                goto_t(5),
            ),
            blk(
                vec![assign(local(0), Rvalue::Use(cint(100, u32_ty())))],
                goto_t(5),
            ),
            blk(vec![], Terminator::Unreachable),
            blk(vec![], Terminator::Return),
        ],
    );
    let lowered = lower_ok(&body, PW);
    let eval = |val: MirValue| eval_lowered_body_cfg(&lowered, &[val], 10);
    assert_eq!(
        returned(eval(MirValue::adt(&def, 0, vec![u8v(7)]))),
        u32v(7)
    );
    assert_eq!(
        returned(eval(MirValue::adt(&def, 1, vec![u16v(300), u8v(12)]))),
        u32v(312)
    );
    assert_eq!(returned(eval(MirValue::adt(&def, 2, vec![]))), u32v(100));
    // Projecting through the wrong variant is UB.
    let mut wrong_arm = body.clone();
    wrong_arm.basic_blocks[1].statements = vec![assign(local(0), widen(downcast(1, 1, u8_ty())))];
    assert!(matches!(
        eval_lowered_body_cfg(
            &lower_ok(&wrong_arm, PW),
            &[MirValue::adt(&def, 0, vec![u8v(7)])],
            10
        ),
        Err(CfgEvalError::Statement {
            bb: 1,
            index: 0,
            error: RvalueEvalError::InactiveVariantProjection { .. },
        })
    ));
}

/// Terminator shapes of the random CFGs in
/// `test_property_cfg_evaluator_matches_a_reference_interpreter`.
#[derive(Clone, Debug)]
enum RefTerm {
    Goto(usize),
    /// Switch on `acc & 7`.
    Switch(Vec<(u128, usize)>, usize),
    Return,
    /// `assert(acc & 7 < 6)`, unwinding with `Continue` or `Terminate`.
    Assert(usize, bool),
}

/// Outcome of the reference interpreter.
#[derive(Debug, PartialEq)]
enum RefOutcome {
    Returned(u32),
    Panicked(usize),
    Terminated(usize),
    OutOfFuel(usize, u32),
}

#[test]
fn test_property_cfg_evaluator_matches_a_reference_interpreter() {
    let mut g = AdtGen { seed: 0xcf9_0001 };
    let multipliers = [1u32, 3, 5, 0x9E37_79B9];
    // Outcome counts: returned, panicked, terminated, out of fuel.
    let mut seen = [0usize; 4];
    for _ in 0..300 {
        let n = 1 + g.below(6) as usize;
        let blocks: Vec<(u32, u32, RefTerm)> = (0..n)
            .map(|_| {
                let m = multipliers[g.below(4) as usize];
                let k = g.next() as u32;
                let term = match g.below(8) {
                    0 | 1 => RefTerm::Goto(g.below(n as u64) as usize),
                    2..=4 => {
                        let mut values: Vec<u128> = (0..8).filter(|_| g.below(2) == 0).collect();
                        if g.below(2) == 0 {
                            values.reverse();
                        }
                        let branches = values
                            .into_iter()
                            .map(|v| (v, g.below(n as u64) as usize))
                            .collect();
                        RefTerm::Switch(branches, g.below(n as u64) as usize)
                    }
                    5 => RefTerm::Return,
                    _ => RefTerm::Assert(g.below(n as u64) as usize, g.below(2) == 0),
                };
                (m, k, term)
            })
            .collect();
        // Lower to MIR: `_0: u32` (return), `_1: u32` (acc), `_2: u32` (acc & 7), `_3: bool`.
        let mir_blocks = blocks
            .iter()
            .map(|(m, k, term)| {
                let mut stmts = vec![
                    assign(
                        local(1),
                        Rvalue::BinaryOp(BinOp::Mul, cp(1), cint(u128::from(*m), u32_ty())),
                    ),
                    assign(
                        local(1),
                        Rvalue::BinaryOp(BinOp::Add, cp(1), cint(u128::from(*k), u32_ty())),
                    ),
                    assign(
                        local(2),
                        Rvalue::BinaryOp(BinOp::BitAnd, cp(1), cint(7, u32_ty())),
                    ),
                ];
                let term = match term {
                    RefTerm::Goto(t) => goto_t(*t),
                    RefTerm::Switch(branches, otherwise) => Terminator::SwitchInt {
                        discr: cp(2),
                        targets: SwitchTargets::new(branches.iter().copied(), *otherwise),
                    },
                    RefTerm::Return => {
                        stmts.push(assign(local(0), Rvalue::Use(cp(1))));
                        Terminator::Return
                    }
                    RefTerm::Assert(t, terminate) => {
                        stmts.push(assign(
                            local(3),
                            Rvalue::BinaryOp(BinOp::Lt, cp(2), cint(6, u32_ty())),
                        ));
                        let unwind = if *terminate {
                            UnwindAction::Terminate
                        } else {
                            UnwindAction::Continue
                        };
                        assert_t(cp(3), true, custom("high"), *t, unwind)
                    }
                };
                blk(stmts, term)
            })
            .collect();
        let body = lower_ok(
            &mk_body(vec![u32_ty(), u32_ty(), u32_ty(), Ty::Bool], mir_blocks),
            PW,
        );
        for _ in 0..4 {
            let start = g.next() as u32;
            let fuel = g.below(40) as usize;
            // Reference interpreter.
            let (mut acc, mut bb, mut left) = (start, 0usize, fuel);
            let expected = loop {
                if left == 0 {
                    break RefOutcome::OutOfFuel(bb, acc);
                }
                left -= 1;
                let (m, k, term) = &blocks[bb];
                acc = acc.wrapping_mul(*m).wrapping_add(*k);
                let low = u128::from(acc & 7);
                match term {
                    RefTerm::Goto(t) => bb = *t,
                    RefTerm::Switch(branches, otherwise) => {
                        bb = branches
                            .iter()
                            .find(|(v, _)| *v == low)
                            .map_or(*otherwise, |(_, t)| *t);
                    }
                    RefTerm::Return => break RefOutcome::Returned(acc),
                    RefTerm::Assert(t, terminate) => {
                        if low < 6 {
                            bb = *t;
                        } else if *terminate {
                            break RefOutcome::Terminated(bb);
                        } else {
                            break RefOutcome::Panicked(bb);
                        }
                    }
                }
            };
            let args = [u32v(u128::from(start)), u32v(0), MirValue::Bool(false)];
            let actual = match eval_lowered_body_cfg(&body, &args, fuel) {
                Ok(CfgEvalOutcome::Returned(MirValue::Int { bits, .. })) => {
                    RefOutcome::Returned(bits as u32)
                }
                Ok(CfgEvalOutcome::Panicked { bb, msg }) => {
                    assert_eq!(msg, custom_msg("high"));
                    RefOutcome::Panicked(bb)
                }
                Ok(CfgEvalOutcome::Terminated { bb, msg }) => {
                    assert_eq!(msg, custom_msg("high"));
                    RefOutcome::Terminated(bb)
                }
                Ok(CfgEvalOutcome::OutOfFuel { bb, state }) => match &state.slots[1] {
                    LocalSlotState::Init(MirValue::Int { bits, .. }) => {
                        RefOutcome::OutOfFuel(bb, *bits as u32)
                    }
                    other => panic!("acc slot {other:?}"),
                },
                other => panic!("unexpected outcome {other:?}"),
            };
            assert_eq!(
                actual, expected,
                "blocks {blocks:?}, start {start:#x}, fuel {fuel}"
            );
            seen[match expected {
                RefOutcome::Returned(_) => 0,
                RefOutcome::Panicked(_) => 1,
                RefOutcome::Terminated(_) => 2,
                RefOutcome::OutOfFuel(..) => 3,
            }] += 1;
        }
    }
    assert!(
        seen.iter().all(|count| *count >= 50),
        "outcome distribution {seen:?}"
    );
}

// ---------------------------------------------------------------------------------------------
// [ep1-adv B1] Regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_b1_adt_transparent_unspecified_fields_field_offset_and_enum_niche_with_uninhabited_variants()
 {
    let (_, opt) = rust_option_u32();
    // 1. `#[repr(transparent)]` structs and unions with a second non-1-ZST field whose layout is
    // `Unspecified` (`Option<u32>`) must be rejected as ill-formed (`E0690`), not treated as a
    // valid 1-field wrapper with an inexact layout.
    let bad_trans_struct = Ty::adt(
        AdtDef::new_struct("BadTS", vec![u32_ty(), opt.clone()]).with_repr(AdtRepr::transparent()),
    );
    assert!(matches!(
        bad_trans_struct.layout_for(PW),
        Err(LayoutError::IllFormed(_))
    ));
    assert!(matches!(
        bad_trans_struct.check_representable(PW),
        Err(LayoutError::IllFormed(_))
    ));
    let bad_trans_union = Ty::adt(
        AdtDef::new_union("BadTU", vec![u32_ty(), opt.clone()]).with_repr(AdtRepr::transparent()),
    );
    assert!(matches!(
        bad_trans_union.layout_for(PW),
        Err(LayoutError::IllFormed(_))
    ));
    assert!(matches!(
        bad_trans_union.check_representable(PW),
        Err(LayoutError::IllFormed(_))
    ));

    // 2. `AdtDef::field_offset` and `resolve_offset_of` (including an empty path `&[]`) must
    // reject containers whose overall layout is `Unspecified`, even when querying an earlier
    // field whose offset would otherwise be known.
    let (s_opt_def, s_opt_ty) =
        adt(AdtDef::new_struct("SOpt", vec![u32_ty(), opt.clone()]).with_repr(AdtRepr::c()));
    assert_eq!(s_opt_ty.layout_for(PW), Err(LayoutError::Unspecified));
    assert_eq!(
        s_opt_def.field_offset(0, 0, PW),
        Err(LayoutError::Unspecified)
    );
    assert_eq!(
        resolve_offset_of(&s_opt_ty, &[(0, 0)], PW),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(
            s_opt_ty.clone()
        ))
    );
    assert_eq!(
        resolve_offset_of(&opt, &[], PW),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(opt.clone()))
    );
    let (u_opt_def, u_opt_ty) =
        adt(AdtDef::new_union("UOpt", vec![u32_ty(), opt.clone()]).with_repr(AdtRepr::c()));
    assert_eq!(
        u_opt_def.field_offset(0, 0, PW),
        Err(LayoutError::Unspecified)
    );
    assert_eq!(
        resolve_offset_of(&u_opt_ty, &[], PW),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(u_opt_ty))
    );

    // 3. `#[repr(u8)]` enums with uninhabited variants or niche-carrying payload fields:
    // - 256 variants where variant 0 holds `!` has only 255 inhabited tags, so it still has a
    //   niche;
    // - 256 inhabited variants where variant 0 holds `bool` has a payload niche (`contains_niche`),
    //   so a union containing it is not canonical for transmutation.
    let mut vars_with_never: Vec<VariantDef> = vec![VariantDef::new("V0", vec![Ty::Never])];
    for i in 1..256 {
        vars_with_never.push(VariantDef::new(format!("V{i}"), vec![]));
    }
    let (_, e256_never) = adt(AdtDef::new_enum(
        "E256Never",
        Some(ScalarTy::Uint(UintTy::U8)),
        vars_with_never,
    ));
    assert!(e256_never.contains_niche_for(PW));

    let mut vars_with_bool: Vec<VariantDef> =
        vec![VariantDef::new("V0", vec![Ty::Bool]).with_discriminant(0)];
    for i in 1..256 {
        vars_with_bool
            .push(VariantDef::new(format!("V{i}"), vec![u8_ty()]).with_discriminant(i as u128));
    }
    let (_, e256_bool) =
        adt(
            AdtDef::new_enum("E256Bool", Some(ScalarTy::Uint(UintTy::U8)), vars_with_bool)
                .with_repr(AdtRepr::c()),
        );
    assert!(e256_bool.contains_niche_for(PW));
    let (_, union_e256_bool) =
        adt(AdtDef::new_union("UE256Bool", vec![e256_bool]).with_repr(AdtRepr::c()));
    assert!(!union_e256_bool.has_canonical_byte_layout(PW));

    // 4. Transmuting bytes whose tag selects an uninhabited variant (`Dead(u8, !) = 0`) of an
    // inhabited `#[repr(C, u8)]` enum must fail with `InvalidBitPattern` for the enum type, not
    // `UninhabitedTarget { target_ty: Ty::Never }`.
    let (_, e_dead_live) = adt(AdtDef::new_enum(
        "EDeadLive",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("Dead", vec![u8_ty(), Ty::Never]).with_discriminant(0),
            VariantDef::new("Live", vec![u8_ty()]).with_discriminant(1),
        ],
    )
    .with_repr(AdtRepr::c()));
    let mut state = state_with(vec![e_dead_live.clone(), u16_ty()], PW);
    assert_eq!(
        transmute(&mut state, 0, cint(0x0000, u16_ty()), e_dead_live.clone()),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: e_dead_live.clone(),
                bits: 0,
            }
        ))
    );
    transmute(&mut state, 0, cint(0x2A01, u16_ty()), e_dead_live).unwrap();
}

#[test]
fn test_b1_place_access_checks_dynamic_index_bounds_and_active_variants_across_drop_call_retag_and_discriminant()
 {
    let (enum_def, enum_ty) = repr_u8_enum(); // V0(u8, u32), V1(u16)
    let (single_def, single_ty) = adt(AdtDef::new_struct("Single", vec![u8_ty()]));
    let (enum_single_def, enum_single_ty) = adt(AdtDef::new_enum(
        "ESingle",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![single_ty.clone()]),
            VariantDef::new("B", vec![single_ty.clone()]),
        ],
    ));
    let arr_ty = Ty::Array(Box::new(single_ty.clone()), 2);
    let decls = vec![
        unit(),                 // _0
        arr_ty.clone(),         // _1: [Single; 2]
        usize_ty(),             // _2: usize index
        enum_ty.clone(),        // _3: ReprU8
        enum_single_ty.clone(), // _4: ESingle
        u8_ty(),                // _5: discriminant scratch
    ];
    let mut state = state_with(decls.clone(), PW);
    state.slots[1] = LocalSlotState::Init(MirValue::Array {
        elements: vec![
            MirValue::adt(&single_def, 0, vec![u8v(1)]),
            MirValue::adt(&single_def, 0, vec![u8v(2)]),
        ],
        elem_ty: single_ty.clone(),
    });
    state.slots[2] = LocalSlotState::Init(usizev(5)); // out of bounds for len 2
    state.slots[3] = LocalSlotState::Init(MirValue::adt(&enum_def, 0, vec![u8v(1), u32v(2)]));
    state.slots[4] = LocalSlotState::Init(MirValue::adt(
        &enum_single_def,
        0,
        vec![MirValue::adt(&single_def, 0, vec![u8v(9)])],
    ));

    let oob_elem = place(1, vec![ProjectionElem::Index(Local(2))]);
    let inactive_v1 = place(3, vec![ProjectionElem::Downcast(1), field(0, u16_ty())]);
    let inactive_single = place(
        4,
        vec![ProjectionElem::Downcast(1), field(0, single_ty.clone())],
    );

    // 1. `Statement::Retag` on a place without references still validates dynamic array bounds
    // and active variants on `Downcast`.
    assert_eq!(
        run(retag(RetagKind::Default, oob_elem.clone()), &mut state),
        Err(RvalueEvalError::IndexOutOfBounds { index: 5, len: 2 })
    );
    assert_eq!(
        run(retag(RetagKind::Default, inactive_v1.clone()), &mut state),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0,
        })
    );
    // Even when `_1` is `Uninit`, static array length catches out-of-bounds `Index(_2)`.
    state.slots[1] = LocalSlotState::Uninit;
    assert_eq!(
        run(retag(RetagKind::Default, oob_elem.clone()), &mut state),
        Err(RvalueEvalError::IndexOutOfBounds { index: 5, len: 2 })
    );

    // 2. `Rvalue::Discriminant` on a single-variant ADT (`!def.requires_tag_write()`) still
    // validates `Index` bounds and outer `Downcast` active variants in both stateful and pure
    // evaluation.
    assert_eq!(
        run(
            assign(local(5), Rvalue::Discriminant(oob_elem.clone())),
            &mut state
        ),
        Err(RvalueEvalError::IndexOutOfBounds { index: 5, len: 2 })
    );
    assert_eq!(
        run(
            assign(local(5), Rvalue::Discriminant(inactive_single.clone())),
            &mut state
        ),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0,
        })
    );
    let lowered_discr =
        lower_rvalue(&Rvalue::Discriminant(inactive_single.clone()), &decls, PW).unwrap();
    let pure_locals = vec![
        MirValue::Unit,
        MirValue::Array {
            elements: vec![
                MirValue::adt(&single_def, 0, vec![u8v(1)]),
                MirValue::adt(&single_def, 0, vec![u8v(2)]),
            ],
            elem_ty: single_ty,
        },
        usizev(5),
        MirValue::adt(&enum_def, 0, vec![u8v(1), u32v(2)]),
        MirValue::adt(
            &enum_single_def,
            0,
            vec![MirValue::adt(&single_def, 0, vec![u8v(9)])],
        ),
        u8v(0),
    ];
    assert_eq!(
        eval_lowered_rvalue(
            &lowered_discr,
            &pure_locals,
            PW,
            TransmutePolicy::RejectPtrToInt,
            &mut ExposedProvenanceTracker::new(),
        ),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0,
        })
    );

    // 3. `Terminator::Drop` and `Terminator::Call` (even when panicking) reject out-of-bounds
    // `Index` and inactive `Downcast` places.
    let drop_oob_body = lower_ok(
        &mk_body(
            decls.clone(),
            vec![
                blk(vec![], drop_t(oob_elem.clone(), 1, UnwindAction::Continue)),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
    assert_eq!(
        eval_cfg_in_state(&drop_oob_body, state.clone(), 0, 4, None),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::IndexOutOfBounds { index: 5, len: 2 },
        })
    );

    let drop_inactive_body = lower_ok(
        &mk_body(
            decls.clone(),
            vec![
                blk(
                    vec![],
                    drop_t(inactive_v1.clone(), 1, UnwindAction::Continue),
                ),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
    assert_eq!(
        eval_cfg_in_state(&drop_inactive_body, state.clone(), 0, 4, None),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::InactiveVariantProjection {
                expected: 1,
                actual: 0,
            },
        })
    );

    let call_inactive_body = lower_ok(
        &mk_body(
            decls,
            vec![
                blk(
                    vec![],
                    Terminator::Call {
                        func: cint(1, u32_ty()),
                        args: vec![],
                        destination: inactive_v1,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
    let mut panic_handler =
        |_: usize, _: &MirValue, _: &[MirValue]| Ok(CallOutcome::Panic("boom".into()));
    assert_eq!(
        eval_cfg_in_state(&call_inactive_body, state, 0, 4, Some(&mut panic_handler),),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::InactiveVariantProjection {
                expected: 1,
                actual: 0,
            },
        })
    );
}

#[test]
fn test_b1_set_discriminant_and_discriminant_variant_ordering_and_fieldless_array_switches() {
    let (e_def, e_ty) = adt(AdtDef::new_enum(
        "E",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("Data", vec![u32_ty()]),
            VariantDef::new("Unit", vec![]),
            VariantDef::new("Dead", vec![Ty::Never]),
        ],
    ));
    let (outer_def, outer_ty) = adt(AdtDef::new_enum(
        "Outer",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("Left", vec![e_ty.clone()]),
            VariantDef::new("Right", vec![e_ty.clone()]),
        ],
    ));
    let arr_e_ty = Ty::Array(Box::new(e_ty.clone()), 2);
    let decls = vec![
        u8_ty(),          // _0
        e_ty.clone(),     // _1: E
        arr_e_ty.clone(), // _2: [E; 2]
        usize_ty(),       // _3: index
        outer_ty.clone(), // _4: Outer
    ];
    let mut state = state_with(decls, PW);

    // 1. `SetDiscriminant` checks `DeadLocal`, index operands, and outer `InactiveVariantProjection`
    // before checking `UninhabitedEnumVariant`, and reports `TypeMismatch` on out-of-range
    // variant indices in hand-built `LoweredStatement::SetDiscriminant`.
    state.slots[1] = LocalSlotState::Dead;
    assert_eq!(
        run(
            Statement::SetDiscriminant {
                place: local(1),
                variant_index: 2,
            },
            &mut state
        ),
        Err(RvalueEvalError::DeadLocal(Local(1)))
    );
    state.slots[1] = LocalSlotState::Uninit;
    assert!(matches!(
        eval_lowered_statement(
            &LoweredStatement::SetDiscriminant {
                place: local(1),
                place_ty: e_ty.clone(),
                variant_index: 99,
            },
            &mut state,
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    state.slots[4] = LocalSlotState::Init(MirValue::adt(
        &outer_def,
        0,
        vec![MirValue::adt(&e_def, 1, vec![])],
    ));
    let inactive_inner = place(4, vec![ProjectionElem::Downcast(1), field(0, e_ty.clone())]);
    assert_eq!(
        run(
            Statement::SetDiscriminant {
                place: inactive_inner,
                variant_index: 2,
            },
            &mut state
        ),
        Err(RvalueEvalError::InactiveVariantProjection {
            expected: 1,
            actual: 0,
        })
    );

    // 2. Switching a typed enum element inside an initialized array (`_2[_3]`) from a data
    // variant `Data(42)` to a fieldless variant `Unit` succeeds in place without needing an
    // array shell; switching from `Unit` to `Data(u32)` fails closed with `UnsupportedPlaceProjection`.
    state.slots[2] = LocalSlotState::Init(MirValue::Array {
        elements: vec![
            MirValue::adt(&e_def, 0, vec![u32v(42)]),
            MirValue::adt(&e_def, 1, vec![]),
        ],
        elem_ty: e_ty.clone(),
    });
    state.slots[3] = LocalSlotState::Init(usizev(0));
    let elem0 = place(2, vec![ProjectionElem::Index(Local(3))]);
    run(
        Statement::SetDiscriminant {
            place: elem0.clone(),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(read(&state, &elem0), Ok(MirValue::adt(&e_def, 1, vec![])));
    assert_eq!(
        run(
            Statement::SetDiscriminant {
                place: elem0.clone(),
                variant_index: 0,
            },
            &mut state
        ),
        Err(RvalueEvalError::UnsupportedPlaceProjection(elem0))
    );

    // 3. `Rvalue::Discriminant` on a shell whose tag selects an uninhabited variant (`Dead(!)`)
    // fails closed with `UninhabitedEnumVariant`.
    let mut dead_shell = PartialAggregate::new_uninit_adt(&e_def, 2).unwrap();
    dead_shell.discriminant_set = true;
    state.slots[1] = LocalSlotState::PartialShell(dead_shell);
    assert_eq!(
        run(assign(local(0), Rvalue::Discriminant(local(1))), &mut state),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 2 })
    );
}

#[test]
fn test_b1_copy_nonoverlapping_whole_local_zst_dead_provenance_and_layout_guards() {
    let zst_src_ty = raw(unit(), Mutability::Not);
    let zst_dst_ty = raw(unit(), Mutability::Mut);
    let u32_src_ty = raw(u32_ty(), Mutability::Not);
    let u32_dst_ty = raw(u32_ty(), Mutability::Mut);
    let decls = vec![
        unit(),             // _0: ()
        unit(),             // _1: ()
        zst_src_ty.clone(), // _2: *const ()
        zst_dst_ty.clone(), // _3: *mut ()
        u32_ty(),           // _4: u32
        u32_src_ty.clone(), // _5: *const u32
    ];
    let mut state = state_with(decls, PW);
    run(
        assign(local(2), Rvalue::RawPtr(Mutability::Not, local(0))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(3), Rvalue::RawPtr(Mutability::Mut, local(1))),
        &mut state,
    )
    .unwrap();
    run(
        assign(local(5), Rvalue::RawPtr(Mutability::Not, local(4))),
        &mut state,
    )
    .unwrap();

    // 1. Whole-local `copy_nonoverlapping::<()>(src, dst, 1)` copies `_0`'s initialization state
    // (`Init(Unit)` or `Uninit`) into `_1`, and faults with `DeadLocal` when `_0` or `_1` is `Dead`.
    state.slots[0] = LocalSlotState::Init(MirValue::Unit);
    state.slots[1] = LocalSlotState::Uninit;
    run(
        copy_nonoverlapping(cp(2), cp(3), cint(1, usize_ty())),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&MirValue::Unit));

    state.slots[0] = LocalSlotState::Uninit;
    run(
        copy_nonoverlapping(cp(2), cp(3), cint(1, usize_ty())),
        &mut state,
    )
    .unwrap();
    assert_eq!(state.get_local(Local(1)), Some(&LocalSlotState::Uninit));

    state.slots[0] = LocalSlotState::Dead;
    assert_eq!(
        run(
            copy_nonoverlapping(cp(2), cp(3), cint(1, usize_ty())),
            &mut state
        ),
        Err(RvalueEvalError::DeadLocal(Local(0)))
    );
    // `count == 0` is a no-op even when `_0` is `Dead`.
    run(
        copy_nonoverlapping(cp(2), cp(3), cint(0, usize_ty())),
        &mut state,
    )
    .unwrap();

    // 2. When `byte_len > 0` and a pointer carries the provenance of a `Dead` local (`_4`),
    // `copy_nonoverlapping` reports `DeadLocal(Local(4))` even when `count > 1` or the peer
    // pointer is not a whole-local pointer.
    state.slots[4] = LocalSlotState::Dead;
    assert_eq!(
        run(
            copy_nonoverlapping(
                cp(5),
                ptr_const(0x9000, Some(99), u32_dst_ty.clone()),
                cint(2, usize_ty()),
            ),
            &mut state
        ),
        Err(RvalueEvalError::DeadLocal(Local(4)))
    );

    // 3. Hand-built `LoweredStatement::CopyNonOverlapping` with wrong `elem_size` / `elem_align`
    // fails closed with `TypeMismatch`.
    state.slots[4] = LocalSlotState::Init(u32v(7));
    assert!(matches!(
        eval_lowered_statement(
            &LoweredStatement::CopyNonOverlapping {
                src: cp(5),
                dst: ptr_const(0x9000, Some(99), u32_dst_ty),
                count: cint(0, usize_ty()),
                elem_ty: u32_ty(),
                elem_size: 8, // wrong size for u32
                elem_align: 4,
            },
            &mut state,
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
}

#[test]
fn test_b1_hand_built_lowered_casts_rvalues_shells_and_cfg_terminators_fail_closed() {
    let (nz_def, nz_ty) = non_zero_u32();
    let (s1_def, s1_ty) = adt(AdtDef::new_struct("S1", vec![u32_ty(), u32_ty()]));
    let (s2_def, _) = adt(AdtDef::new_struct("S2", vec![u32_ty(), u32_ty()]));
    let bad_adt = Ty::adt(
        AdtDef::new_struct("BadAlign", vec![u8_ty()]).with_repr(AdtRepr::c().with_align(3)),
    );

    // 1. `Subtype` lowering rejects ill-formed ADTs.
    assert!(matches!(
        lower_rvalue(
            &Rvalue::Cast(CastKind::Subtype, cp(0), bad_adt.clone()),
            &[bad_adt],
            PW,
        ),
        Err(RvalueLowerError::CastError(
            CastLowerError::IllFormedType { .. }
        ))
    ));

    // 2. Hand-built `LoweredCast::Subtype` and `LoweredRvalue::WrapUnsafeBinder` validate
    // `scalar_valid_range`, and hand-built `LoweredCast::PointerCoercion` validates coercion
    // types.
    let decls = vec![nz_ty.clone(), s1_ty.clone(), u32_ty()];
    let mut state = state_with(decls.clone(), PW);
    state.slots[0] = LocalSlotState::Init(MirValue::adt(&nz_def, 0, vec![u32v(0)]));
    let hand_subtype = LoweredRvalue::Cast {
        cast: anneal_mir::lower::LoweredCast::Subtype {
            operand: cp(0),
            src_ty: nz_ty.clone(),
            target_ty: nz_ty.clone(),
        },
        ty: nz_ty.clone(),
    };
    assert_eq!(
        anneal_mir::lower::eval_lowered_rvalue_in_state(&hand_subtype, &mut state),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: nz_ty.clone(),
                bits: 0,
            }
        ))
    );
    let hand_binder = LoweredRvalue::WrapUnsafeBinder {
        operand: cp(0),
        operand_ty: nz_ty.clone(),
        ty: nz_ty.clone(),
    };
    assert_eq!(
        anneal_mir::lower::eval_lowered_rvalue_in_state(&hand_binder, &mut state),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: nz_ty,
                bits: 0,
            }
        ))
    );
    let const_u8 = raw(u8_ty(), Mutability::Not);
    let mut_u8 = raw(u8_ty(), Mutability::Mut);
    let hand_coercion = LoweredRvalue::Cast {
        cast: anneal_mir::lower::LoweredCast::PointerCoercion {
            coercion: PointerCoercionKind::MutToConstPointer,
            operand: Operand::Constant(Constant::Ptr(
                PointerValue::without_provenance(8),
                const_u8.clone(),
            )),
            src_ty: const_u8,
            target_ty: mut_u8.clone(),
        },
        ty: mut_u8,
    };
    assert!(matches!(
        anneal_mir::lower::eval_lowered_rvalue_in_state(&hand_coercion, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    // 3. A `PartialShell` whose `adt_def` (`S2`) does not match the local's declared `Ty::Adt(S1)`
    // is rejected with `TypeMismatch` across read, write, deinit, retag, and SetDiscriminant.
    let mut wrong_shell = PartialAggregate::new_uninit_adt(&s2_def, 0).unwrap();
    wrong_shell.fields[0] = anneal_mir::lower::FieldSlot::Init(u32v(1));
    state.slots[1] = LocalSlotState::PartialShell(wrong_shell);
    let f0 = place(1, vec![field(0, u32_ty())]);
    let f1 = place(1, vec![field(1, u32_ty())]);
    assert!(matches!(
        state.read_place(&f0),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.write_place(&f1, &u32_ty(), u32v(2)),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.deinit_place(&f0, &u32_ty()),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        state.retag_place(RetagKind::Default, &local(1), &s1_ty),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        eval_lowered_statement(
            &LoweredStatement::SetDiscriminant {
                place: local(1),
                place_ty: s1_ty,
                variant_index: 0,
            },
            &mut state,
        ),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    let _ = s1_def;

    // 4. Hand-built CFG terminators: `SwitchInt` with mismatched values/targets lengths, `Call`
    // with `target: Some(_)` on an uninhabited destination, and `Assert` with mistyped message
    // operands fail closed with `TypeMismatch`.
    let run_hand_term = |decls: Vec<Ty>, term: LoweredTerminator| {
        let state = state_with(decls.clone(), PW);
        let body = LoweredBody {
            local_decls: decls,
            basic_blocks: vec![
                LoweredBasicBlock {
                    statements: vec![],
                    terminator: Some(term),
                    is_cleanup: false,
                },
                LoweredBasicBlock {
                    statements: vec![],
                    terminator: Some(LoweredTerminator::Return { ret_ty: unit() }),
                    is_cleanup: false,
                },
            ],
            ptr_width: PW,
        };
        let mut handler =
            |_: usize, _: &MirValue, _: &[MirValue]| Ok(CallOutcome::Panic("p".into()));
        eval_cfg_in_state(&body, state, 0, 4, Some(&mut handler))
    };
    assert!(matches!(
        run_hand_term(
            vec![unit()],
            LoweredTerminator::SwitchInt {
                discr: cint(0, u32_ty()),
                discr_ty: u32_ty(),
                targets: SwitchTargets {
                    values: vec![0, 1],
                    targets: vec![1],
                    otherwise: 1,
                },
            },
        ),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::TypeMismatch(_),
        })
    ));
    assert!(matches!(
        run_hand_term(
            vec![unit(), Ty::Never],
            LoweredTerminator::Call {
                func: cint(1, u32_ty()),
                func_ty: u32_ty(),
                args: vec![],
                arg_tys: vec![],
                destination: local(1),
                dest_ty: Ty::Never,
                target: Some(1),
                unwind: UnwindAction::Continue,
            },
        ),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::TypeMismatch(_),
        })
    ));
    assert!(matches!(
        run_hand_term(
            vec![unit()],
            LoweredTerminator::Assert {
                cond: cbool(false),
                expected: true,
                msg: AssertMessage::BoundsCheck {
                    len: cint(2, u32_ty()), // not usize!
                    index: cint(0, usize_ty()),
                },
                target: 1,
                unwind: UnwindAction::Continue,
            },
        ),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::TypeMismatch(_),
        })
    ));
}

// ---------------------------------------------------------------------------------------------
// A1 regressions: tagless `#[repr(C)]` enums, `E0084`, and `rustc`'s univariant enum layouts
// ---------------------------------------------------------------------------------------------

/// `core::convert::Infallible` (`enum Infallible {}`).
fn infallible() -> Ty {
    Ty::adt(AdtDef::new_enum("Infallible", None, vec![]))
}

#[test]
fn test_a1_tagless_repr_c_enums_store_a_c_int_tag_even_with_one_variant() {
    // rustc: `#[repr(C)] enum C1 { A(u32) }` is 8 bytes with `A.0` at offset 4 (a C `int` tag
    // precedes the payload), and `#[repr(C)] enum C1u { A }` is 4 bytes. The tag size is the
    // target's C `int` (not determined by the pointer width), so the layout is unspecified
    // rather than the 4-byte struct layout A0 reported.
    let (c1_def, c1) =
        adt(
            AdtDef::new_enum("C1", None, vec![VariantDef::new("A", vec![u32_ty()])])
                .with_repr(AdtRepr::c()),
        );
    let (_, c1u) = adt(
        AdtDef::new_enum("C1u", None, vec![VariantDef::new("A", vec![])]).with_repr(AdtRepr::c()),
    );
    for pw in [PtrWidth::Bits32, PtrWidth::Bits64] {
        assert_eq!(c1.layout_for(pw), Err(LayoutError::Unspecified));
        assert_eq!(c1u.layout_for(pw), Err(LayoutError::Unspecified));
        assert_eq!(c1.check_representable(pw), Ok(()));
        assert_eq!(c1_def.field_offset(0, 0, pw), Err(LayoutError::Unspecified));
        assert!(!c1.has_canonical_byte_layout(pw));
    }
    assert_eq!(
        resolve_offset_of(&c1, &[(0, 0)], PW),
        Err(RvalueLowerError::UnsupportedOffsetOfLayout(c1.clone()))
    );
    // The C `int` tag is stored (and has invalid values), apart from the payload.
    assert!(c1_def.requires_tag_write());
    assert!(c1_def.tag_survives_field_deinit());
    assert!(c1.contains_niche());
    assert_eq!(c1_def.univariant_index(), None);

    // `Discriminant` reads the tag: an uninitialized `C1` is UB (A0 returned `0` unread).
    let mut state = state_with(vec![c1.clone(), u32_ty()], PW);
    assert_eq!(
        discriminant(&mut state, local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    // Writing the field alone leaves the tag uninitialized; `SetDiscriminant` completes it.
    let a0 = place(0, vec![ProjectionElem::Downcast(0), field(0, u32_ty())]);
    run(
        assign(a0.clone(), Rvalue::Use(cint(7, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(state.slots[0], LocalSlotState::PartialShell(_)));
    assert_eq!(
        read(&state, &local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    assert_eq!(
        discriminant(&mut state, local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    run(
        Statement::SetDiscriminant {
            place: local(0),
            variant_index: 0,
        },
        &mut state,
    )
    .unwrap();
    assert_eq!(
        read(&state, &local(0)),
        Ok(MirValue::adt(&c1_def, 0, vec![u32v(7)]))
    );
    assert_eq!(
        discriminant(&mut state, local(0)),
        Ok(uint(0, Ty::Int(IntTy::Isize)))
    );
    // Deinitializing the payload keeps the separately stored tag.
    run(deinit(a0.clone()), &mut state).unwrap();
    assert_eq!(
        discriminant(&mut state, local(0)),
        Ok(uint(0, Ty::Int(IntTy::Isize)))
    );
    assert_eq!(
        read(&state, &a0),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    // Multi-variant tagless `repr(C)` enums keep their tag across payload `Deinit` too.
    let (c2_def, _) = adt(AdtDef::new_enum(
        "C2",
        None,
        vec![
            VariantDef::new("A", vec![u8_ty()]),
            VariantDef::new("B", vec![u16_ty()]),
        ],
    )
    .with_repr(AdtRepr::c()));
    assert!(c2_def.requires_tag_write());
    assert!(c2_def.tag_survives_field_deinit());
}

#[test]
fn test_a1_zero_variant_enums_reject_non_rust_reprs_e0084() {
    // rustc: `#[repr(u8)]`, `#[repr(C)]`, and `#[repr(align(8))]` on `enum E {}` are E0084.
    let bad = [
        AdtDef::new_enum("E", Some(ScalarTy::Uint(UintTy::U8)), vec![]),
        AdtDef::new_enum("E", None, vec![]).with_repr(AdtRepr::c()),
        AdtDef::new_enum("E", None, vec![]).with_repr(AdtRepr::rust().with_align(8)),
    ];
    for def in bad {
        assert!(
            matches!(def.validate(PW), Err(LayoutError::IllFormed(_))),
            "{def:?}"
        );
        let ty = Ty::adt(def);
        assert!(matches!(
            lower_body(
                &Body {
                    local_decls: vec![ty],
                    basic_blocks: vec![]
                },
                PW
            ),
            Err(RvalueLowerError::InvalidAdtDef { .. })
        ));
    }
    // `enum Void {}` itself is fine: size 0, alignment 1, uninhabited.
    let void = infallible();
    assert_eq!(layout(&void, PW), TyLayout { size: 0, align: 1 });
    assert!(!void.is_inhabited());
}

#[test]
fn test_a1_tagless_enums_with_one_present_variant_use_rustc_univariant_layouts() {
    let never = || Ty::Never;
    let enum_of = |variants: Vec<VariantDef>| AdtDef::new_enum("E", None, variants);
    // Expected layouts observed with rustc 1.98.0-nightly (x86_64-unknown-linux-gnu).
    // `#[repr(align(8))] enum E1 { A(!) }`: laid out like `!`, ignoring `repr(align)`.
    let (e1_def, e1) =
        adt(enum_of(vec![VariantDef::new("A", vec![never()])])
            .with_repr(AdtRepr::rust().with_align(8)));
    // `#[repr(align(8))] enum E2 { A(u8), B(!) }`: the struct of `A`, aligned to 8.
    let (e2_def, e2) = adt(enum_of(vec![
        VariantDef::new("A", vec![u8_ty()]),
        VariantDef::new("B", vec![never()]),
    ])
    .with_repr(AdtRepr::rust().with_align(8)));
    // `#[repr(align(8))] enum E3 { A(!), B(!) }`: no present variant.
    let (_, e3) = adt(enum_of(vec![
        VariantDef::new("A", vec![never()]),
        VariantDef::new("B", vec![never()]),
    ])
    .with_repr(AdtRepr::rust().with_align(8)));
    // `enum E4 { A(!), B(u16, u8) }`: the struct of `B` (size 4, alignment 2).
    let (e4_def, e4) = adt(enum_of(vec![
        VariantDef::new("A", vec![never()]),
        VariantDef::new("B", vec![u16_ty(), u8_ty()]),
    ]));
    // `enum E5 { A(u16, u8), B(Infallible) }`.
    let (_, e5) = adt(enum_of(vec![
        VariantDef::new("A", vec![u16_ty(), u8_ty()]),
        VariantDef::new("B", vec![infallible()]),
    ]));
    // `enum E8 { A((), Infallible), B(u32) }`: `B.0` and the absent `A`'s fields at offset 0.
    let (e8_def, e8) = adt(enum_of(vec![
        VariantDef::new("A", vec![unit(), infallible()]),
        VariantDef::new("B", vec![u32_ty()]),
    ]));
    // `enum E10 { A(!), B(bool) }`: 1 byte, exposing `bool`'s niche (`Option<E10>` is 1 byte).
    let (_, e10) = adt(enum_of(vec![
        VariantDef::new("A", vec![never()]),
        VariantDef::new("B", vec![Ty::Bool]),
    ]));
    for pw in [PtrWidth::Bits32, PtrWidth::Bits64] {
        assert_eq!(layout(&e1, pw), TyLayout { size: 0, align: 1 });
        assert_eq!(layout(&e2, pw), TyLayout { size: 8, align: 8 });
        assert_eq!(e2_def.field_offset(0, 0, pw), Ok(0));
        assert_eq!(layout(&e3, pw), TyLayout { size: 0, align: 1 });
        assert_eq!(layout(&e4, pw), TyLayout { size: 4, align: 2 });
        assert_eq!(layout(&e5, pw), TyLayout { size: 4, align: 2 });
        assert_eq!(layout(&e8, pw), TyLayout { size: 4, align: 4 });
        assert_eq!(e8_def.field_offset(1, 0, pw), Ok(0));
        assert_eq!(e8_def.field_offset(0, 0, pw), Ok(0));
        assert_eq!(e8_def.field_offset(0, 1, pw), Ok(0));
        assert_eq!(layout(&e10, pw), TyLayout { size: 1, align: 1 });
    }
    assert_eq!(e1_def.univariant_index(), None);
    assert_eq!(e2_def.univariant_index(), Some(0));
    assert_eq!(e4_def.univariant_index(), Some(1));
    assert!(e10.contains_niche());
    assert!(!e4.contains_niche());
    assert!(e8.has_canonical_byte_layout(PW));
    // Variants with a non-1-ZST field stay present even when uninhabited, so these keep a
    // tag and an unspecified layout: `enum E6 { A([u32; 0], Infallible), B }` (4 bytes) and
    // `enum E7 { A(u8, Infallible), B }` (2 bytes).
    let (e6_def, e6) = adt(enum_of(vec![
        VariantDef::new("A", vec![Ty::Array(Box::new(u32_ty()), 0), infallible()]),
        VariantDef::new("B", vec![]),
    ]));
    let (e7_def, e7) = adt(enum_of(vec![
        VariantDef::new("A", vec![u8_ty(), infallible()]),
        VariantDef::new("B", vec![]),
    ]));
    for (def, ty) in [(&e6_def, &e6), (&e7_def, &e7)] {
        assert_eq!(ty.layout_for(PW), Err(LayoutError::Unspecified));
        assert_eq!(def.univariant_index(), None);
        assert!(def.requires_tag_write());
    }
    // An explicit `tag_ty` inhibits the optimization: `#[repr(u8)] enum E11 { A(!), B(u32) }`
    // is 8 bytes.
    let (_, e11) = adt(AdtDef::new_enum(
        "E11",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![never()]),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    ));
    assert_eq!(layout(&e11, PW), TyLayout { size: 8, align: 4 });
    // `#[repr(transparent)] struct TW(u32, AbsZ)` with `enum AbsZ { A, B(Infallible) }` is a
    // valid 4-byte wrapper (AbsZ is a 1-ZST), not an E0690 error.
    let absz = Ty::adt(enum_of(vec![
        VariantDef::new("A", vec![]),
        VariantDef::new("B", vec![infallible()]),
    ]));
    assert_eq!(layout(&absz, PW), TyLayout { size: 0, align: 1 });
    let tw =
        Ty::adt(AdtDef::new_struct("TW", vec![u32_ty(), absz]).with_repr(AdtRepr::transparent()));
    assert_eq!(layout(&tw, PW), TyLayout { size: 4, align: 4 });

    // Values: every `E4` is `B`, built without a tag write and with a constant discriminant
    // (Miri reads no memory for `Variants::Single`).
    assert!(!e4_def.requires_tag_write());
    assert!(e4_def.tag_survives_field_deinit());
    let mut state = state_with(vec![e4.clone(), u32_ty(), e8.clone()], PW);
    assert_eq!(
        discriminant(&mut state, local(0)),
        Ok(uint(1, Ty::Int(IntTy::Isize)))
    );
    let b = |i: usize, ty: Ty| place(0, vec![ProjectionElem::Downcast(1), field(i, ty)]);
    run(
        assign(b(0, u16_ty()), Rvalue::Use(cint(300, u16_ty()))),
        &mut state,
    )
    .unwrap();
    run(
        assign(b(1, u8_ty()), Rvalue::Use(cint(9, u8_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(&e4_def, 1, vec![u16v(300), u8v(9)]))
    );
    assert_eq!(
        discriminant(&mut state, local(0)),
        Ok(uint(1, Ty::Int(IntTy::Isize)))
    );
    // The absent variant cannot be selected.
    assert_eq!(
        run(
            Statement::SetDiscriminant {
                place: local(0),
                variant_index: 0,
            },
            &mut state,
        ),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 0 })
    );
    // Transmutes decode into (and encode from) the present variant.
    transmute(&mut state, 2, cint(0xDEAD_BEEF, u32_ty()), e8.clone()).unwrap();
    assert_eq!(
        state.get_init(Local(2)),
        Some(&MirValue::adt(&e8_def, 1, vec![u32v(0xDEAD_BEEF)]))
    );
    transmute(&mut state, 1, Operand::Copy(local(2)), u32_ty()).unwrap();
    assert_eq!(state.get_init(Local(1)), Some(&u32v(0xDEAD_BEEF)));
}

// ---------------------------------------------------------------------------------------------
// Adversarial Round B2 Regression Tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_b2_univariant_enum_absent_variant_shell_discriminant_and_retag() {
    let (inf_def, inf_ty) = adt(AdtDef::new_enum("Infallible", None, vec![]));
    // `enum E8 { A((), Infallible), B(u32) }`: `A` is absent (`univariant_index() == Some(1)`,
    // `!requires_tag_write()`).
    let (e8_def, e8_ty) = adt(AdtDef::new_enum(
        "E8",
        None,
        vec![
            VariantDef::new("A", vec![unit(), inf_ty.clone()]),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    ));
    assert_eq!(e8_def.univariant_index(), Some(1));
    assert!(!e8_def.requires_tag_write());

    // 1. If a program writes to the inhabited field of the absent variant `(_0 as A).0 = ()`,
    // `_0` is a `PartialShell` narrowed to absent variant `0`. `Discriminant(_0)` must inspect
    // the runtime shell variant and fail with `UninhabitedEnumVariant { variant_index: 0 }`
    // rather than returning variant `B`'s constant discriminant `1`.
    let mut state = state_with(vec![e8_ty.clone()], PW);
    run(
        assign(
            place(0, vec![ProjectionElem::Downcast(0), field(0, unit())]),
            Rvalue::Use(Operand::Constant(Constant::Unit)),
        ),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(0)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        discriminant(&mut state, local(0)),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 0 })
    );

    // Hand-built `MirValue::Adt` with `variant_idx = 0` must also fail in both stateful and
    // stateless `eval_lowered_rvalue`.
    let bad_e8_val = MirValue::adt(
        &e8_def,
        0,
        vec![MirValue::Unit, MirValue::adt(&inf_def, 0, vec![])],
    );
    state.slots[0] = LocalSlotState::Init(bad_e8_val.clone());
    assert_eq!(
        discriminant(&mut state, local(0)),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 0 })
    );
    let lowered_discr = lower_rvalue(
        &Rvalue::Discriminant(local(0)),
        std::slice::from_ref(&e8_ty),
        PW,
    )
    .unwrap();
    assert_eq!(
        eval_lowered_rvalue(
            &lowered_discr,
            &[bad_e8_val],
            PW,
            TransmutePolicy::RejectPtrToInt,
            &mut ExposedProvenanceTracker::new(),
        ),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 0 })
    );

    // 2. `enum ERef<'a> { A((), Infallible), B(&'a u32) }`: narrowing `_0` to absent variant `A`
    // via `(_0 as A).0 = ()` must not allow `Statement::Retag` to succeed by skipping variant
    // `B`'s uninitialized `&'a u32`.
    let (eref_def, eref_ty) = adt(AdtDef::new_enum(
        "ERef",
        None,
        vec![
            VariantDef::new("A", vec![unit(), inf_ty.clone()]),
            VariantDef::new("B", vec![ref_ty(u32_ty())]),
        ],
    ));
    assert_eq!(eref_def.univariant_index(), Some(1));
    assert!(!eref_def.requires_tag_write());
    assert!(eref_ty.contains_ref());

    let mut ref_state = state_with(vec![eref_ty.clone()], PW);
    run(
        assign(
            place(0, vec![ProjectionElem::Downcast(0), field(0, unit())]),
            Rvalue::Use(Operand::Constant(Constant::Unit)),
        ),
        &mut ref_state,
    )
    .unwrap();
    assert_eq!(
        run(retag(RetagKind::Default, local(0)), &mut ref_state),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    if let LocalSlotState::PartialShell(shell) = &mut ref_state.slots[0] {
        shell.discriminant_set = true;
    }
    assert_eq!(
        run(retag(RetagKind::Default, local(0)), &mut ref_state),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 0 })
    );
    ref_state.slots[0] = LocalSlotState::Init(MirValue::adt(
        &eref_def,
        0,
        vec![MirValue::Unit, MirValue::adt(&inf_def, 0, vec![])],
    ));
    assert_eq!(
        run(retag(RetagKind::Default, local(0)), &mut ref_state),
        Err(RvalueEvalError::UninhabitedEnumVariant { variant_index: 0 })
    );
}

#[test]
fn test_b2_absent_variant_layout_validation_and_transmute_uninhabited_errors() {
    // 1. `#[repr(transparent)]` single-variant enums whose single variant is absent must still
    // enforce E0690 (more than one field with non-trivial size or alignment). A zero-sized
    // field with alignment above 1 is allowed as the one non-trivial field (A2: rustc reports
    // `#[repr(transparent)] enum ETransAlign { A([u64; 0], !) }` as size 0, alignment 8).
    let (_, bad_align_zst) = adt(AdtDef::new_enum(
        "ETransAlign",
        None,
        vec![VariantDef::new(
            "A",
            vec![Ty::Array(Box::new(u64_ty()), 0), Ty::Never],
        )],
    )
    .with_repr(AdtRepr::transparent()));
    assert_eq!(
        bad_align_zst.layout_for(PW),
        Ok(TyLayout { size: 0, align: 8 })
    );

    let (_, bad_two_non_zst) = adt(AdtDef::new_enum(
        "ETransTwo",
        None,
        vec![VariantDef::new("A", vec![u32_ty(), u32_ty(), Ty::Never])],
    )
    .with_repr(AdtRepr::transparent()));
    assert!(matches!(
        bad_two_non_zst.layout_for(PW),
        Err(LayoutError::IllFormed(_))
    ));

    // 2. `enum EBigAbsent { A(!, [(); 1 << 40]), B(u32) }`:
    // On `Bits64`, `[(); 1 << 40]` is a valid 1-ZST so `A` is absent and `EBigAbsent` has the
    // 4-byte layout of `B(u32)`. On `Bits32`, `[(); 1 << 40]` exceeds `u32::MAX` (`TooLarge`).
    let (_, e_big_absent) = adt(AdtDef::new_enum(
        "EBigAbsent",
        None,
        vec![
            VariantDef::new(
                "A",
                vec![Ty::Never, Ty::Array(Box::new(unit()), 1usize << 40)],
            ),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    ));
    assert_eq!(
        e_big_absent.layout_for(PtrWidth::Bits64),
        Ok(TyLayout { size: 4, align: 4 })
    );
    assert_eq!(
        e_big_absent.layout_for(PtrWidth::Bits32),
        Err(LayoutError::TooLarge)
    );
    assert_eq!(
        e_big_absent.check_representable(PtrWidth::Bits32),
        Err(LayoutError::TooLarge)
    );

    // 3. Transmuting into an uninhabited enum whose variants are all absent (`enum E1 { A(!) }`)
    // or whose single variant has a payload and `!` (`enum E2 { A(u32, !) }`) must fail with
    // `UninhabitedTarget` naming the target enum `Ty::Adt`, not `UnsupportedLayout` or `Ty::Never`.
    let (_, e1) = adt(AdtDef::new_enum(
        "E1",
        None,
        vec![VariantDef::new("A", vec![Ty::Never])],
    ));
    let (_, e2) = adt(AdtDef::new_enum(
        "E2",
        None,
        vec![VariantDef::new("A", vec![u32_ty(), Ty::Never])],
    ));
    let mut state = state_with(vec![e1.clone(), e2.clone()], PW);
    let hand_transmute =
        |src_ty: Ty, target_ty: Ty, operand: Operand, op: CastOp, size_bytes: usize| {
            LoweredRvalue::Cast {
                cast: LoweredCast::Transmute {
                    src_ty,
                    target_ty: target_ty.clone(),
                    operand,
                    op,
                    size_bytes,
                    exposes_provenance: false,
                },
                ty: target_ty,
            }
        };
    assert_eq!(
        eval_lowered_rvalue_in_state(
            &hand_transmute(
                unit(),
                e1.clone(),
                Operand::Constant(Constant::Unit),
                CastOp::AggregateTransmute { size_bytes: 0 },
                0,
            ),
            &mut state,
        ),
        Err(RvalueEvalError::CastEval(
            CastEvalError::UninhabitedTarget {
                target_ty: e1.clone()
            }
        ))
    );
    assert_eq!(
        eval_transmute(
            TransmuteValue::Bytes(vec![]),
            &unit(),
            &e1,
            PW,
            TransmutePolicy::RejectPtrToInt,
            &ExposedProvenanceTracker::new(),
        ),
        Err(CastEvalError::UninhabitedTarget { target_ty: e1 })
    );
    assert_eq!(
        eval_lowered_rvalue_in_state(
            &hand_transmute(
                u32_ty(),
                e2.clone(),
                cint(0, u32_ty()),
                CastOp::AggregateTransmute { size_bytes: 4 },
                4,
            ),
            &mut state,
        ),
        Err(RvalueEvalError::CastEval(
            CastEvalError::UninhabitedTarget {
                target_ty: e2.clone()
            }
        ))
    );
    assert_eq!(
        eval_transmute(
            TransmuteValue::Scalar(0),
            &u32_ty(),
            &e2,
            PW,
            TransmutePolicy::RejectPtrToInt,
            &ExposedProvenanceTracker::new(),
        ),
        Err(CastEvalError::UninhabitedTarget { target_ty: e2 })
    );
}

#[test]
fn test_b2_scalar_range_contains_validates_underlying_scalar_and_hand_built_aggregate_validates_adt_def()
 {
    // 1. `AdtDef::scalar_range_contains` must reject bit patterns that are invalid for the
    // underlying scalar field even when they fall within `scalar_valid_range`.
    let (niche_ref_def, niche_ref_ty) = adt(AdtDef::new_struct("NicheRef", vec![ref_ty(u8_ty())])
        .with_scalar_valid_range(ScalarValidRange::new(0, 0xFFFF)));
    assert!(!niche_ref_def.scalar_range_contains(0, PW));
    assert!(niche_ref_def.scalar_range_contains(1, PW));

    let (niche_bool_def, _) = adt(AdtDef::new_struct("NicheBool", vec![Ty::Bool])
        .with_scalar_valid_range(ScalarValidRange::new(1, 3)));
    assert!(!niche_bool_def.scalar_range_contains(0, PW));
    assert!(niche_bool_def.scalar_range_contains(1, PW));
    assert!(!niche_bool_def.scalar_range_contains(2, PW));

    let (niche_char_def, _) = adt(AdtDef::new_struct("NicheChar", vec![Ty::Char])
        .with_scalar_valid_range(ScalarValidRange::new(0, 0xFFFF)));
    assert!(!niche_char_def.scalar_range_contains(0xD800, PW));
    assert!(niche_char_def.scalar_range_contains(0x41, PW));

    let mut state = state_with(vec![niche_ref_ty.clone()], PW);
    state.slots[0] = LocalSlotState::Init(MirValue::adt(
        &niche_ref_def,
        0,
        vec![MirValue::ptr(
            PointerValue::without_provenance(0),
            ref_ty(u8_ty()),
        )],
    ));
    assert_eq!(
        read(&state, &local(0)),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: niche_ref_ty.clone(),
                bits: 0,
            }
        ))
    );

    // 2. `struct SBigRange(u32, [(); 1 << 40])` with `scalar_valid_range`:
    // Valid 4-byte struct on `Bits64`, and `TooLarge` (not `IllFormed`) on `Bits32`.
    let (_, s_big_range) = adt(AdtDef::new_struct(
        "SBigRange",
        vec![u32_ty(), Ty::Array(Box::new(unit()), 1usize << 40)],
    )
    .with_scalar_valid_range(ScalarValidRange::non_zero(32)));
    assert_eq!(
        s_big_range.layout_for(PtrWidth::Bits64),
        Ok(TyLayout { size: 4, align: 4 })
    );
    assert_eq!(
        s_big_range.layout_for(PtrWidth::Bits32),
        Err(LayoutError::TooLarge)
    );

    // 3. Hand-built `LoweredRvalue::Aggregate` with an ill-formed `AdtDef` must fail closed at
    // evaluation time.
    let (bad_align_def, bad_align_ty) =
        adt(AdtDef::new_struct("BadAlign", vec![u32_ty()]).with_repr(AdtRepr::c().with_align(3)));
    let hand_agg = LoweredRvalue::Aggregate {
        kind: AggregateKind::Adt {
            def_path: "BadAlign".to_string(),
            variant_idx: 0,
            active_field: None,
            adt_def: Some(bad_align_def),
        },
        operands: vec![cint(1, u32_ty())],
        operand_tys: vec![u32_ty()],
        ty: bad_align_ty.clone(),
    };
    let mut bad_state = state_with(vec![bad_align_ty.clone()], PW);
    assert!(matches!(
        eval_lowered_rvalue_in_state(&hand_agg, &mut bad_state),
        Err(RvalueEvalError::CastEval(CastEvalError::IllFormedType {
            ty,
            ..
        })) if ty == bad_align_ty
    ));
}

// ---------------------------------------------------------------------------------------------
// A2 regressions: `repr(transparent)` over-aligned ZSTs, and a rustc-pinned layout table
// ---------------------------------------------------------------------------------------------

#[test]
fn test_a2_transparent_allows_one_over_aligned_zero_sized_field() {
    // rustc 1.98.0-nightly: the one field with non-trivial size *or alignment* may be a ZST
    // (A0/B1/B2 rejected these as `E0691`):
    // `#[repr(transparent)] struct S1([u64; 0], ());` is size 0, alignment 8;
    // `#[repr(transparent)] struct S3([u32; 0]);` is size 0, alignment 4;
    // `#[repr(transparent)] union U1 { a: [u64; 0], b: () }` is size 0, alignment 8.
    let zst = |elem: Ty| Ty::Array(Box::new(elem), 0);
    let (s1_def, s1) = adt(
        AdtDef::new_struct("S1", vec![zst(u64_ty()), unit()]).with_repr(AdtRepr::transparent())
    );
    let (_, s3) =
        adt(AdtDef::new_struct("S3", vec![zst(u32_ty())]).with_repr(AdtRepr::transparent()));
    let (_, u1) =
        adt(AdtDef::new_union("U1", vec![zst(u64_ty()), unit()]).with_repr(AdtRepr::transparent()));
    for pw in [PtrWidth::Bits32, PtrWidth::Bits64] {
        assert_eq!(layout(&s1, pw), TyLayout { size: 0, align: 8 });
        assert_eq!(layout(&s3, pw), TyLayout { size: 0, align: 4 });
        assert_eq!(layout(&u1, pw), TyLayout { size: 0, align: 8 });
        assert_eq!(s1_def.field_offset(0, 0, pw), Ok(0));
    }
    // rustc: `struct S2(u32, [u64; 0])` has two such fields (`E0690`), as do unions.
    for def in [
        AdtDef::new_struct("S2", vec![u32_ty(), zst(u64_ty())]).with_repr(AdtRepr::transparent()),
        AdtDef::new_struct("S4", vec![zst(u16_ty()), zst(u32_ty())])
            .with_repr(AdtRepr::transparent()),
        AdtDef::new_union("U2", vec![zst(u64_ty()), u8_ty()]).with_repr(AdtRepr::transparent()),
    ] {
        assert!(
            matches!(def.validate(PW), Err(LayoutError::IllFormed(_))),
            "{def:?}"
        );
    }
}

/// Layouts observed with rustc 1.98.0-nightly (`x86_64-unknown-linux-gnu`) for 30 randomly
/// generated ADTs (repr(C)/repr(Int)/repr(C, Int) enums with explicit discriminants and
/// `repr(align)`, repr(C)/repr(Rust)/transparent structs and unions, univariant enums, and
/// nesting), produced by an out-of-tree rustc-vs-Anneal differential generator (seed 31; 5600+
/// generated types agreed). Pins the sizes, alignments, and every field offset Anneal
/// determines (the others are fail-closed `Unspecified`).
#[test]
fn test_a2_layouts_agree_with_rustc_on_random_adts() {
    let check = |ty: &Ty, size: usize, align: usize, offsets: &[(usize, usize, usize)]| {
        assert_eq!(layout(ty, PW), TyLayout { size, align }, "{ty:?}");
        let Ty::Adt(def) = ty else { unreachable!() };
        for &(v, i, off) in offsets {
            assert_eq!(def.field_offset(v, i, PW), Ok(off), "{ty:?} v{v}.{i}");
            assert_eq!(
                resolve_offset_of(ty, &[(v, i)], PW),
                Ok(off),
                "{ty:?} v{v}.{i}"
            );
        }
    };
    // #[repr(C)] struct T0(u128, u16, u128);
    let t0 = Ty::Adt(Arc::new(
        AdtDef::new_struct(
            "T0",
            vec![
                Ty::Uint(UintTy::U128),
                Ty::Uint(UintTy::U16),
                Ty::Uint(UintTy::U128),
            ],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(&t0, 48, 16, &[(0, 0, 0), (0, 1, 16), (0, 2, 32)]);
    // #[repr(C)] union T1 { f0: u128, f1: u16, f2: u128 }
    let t1 = Ty::Adt(Arc::new(
        AdtDef::new_union(
            "T1",
            vec![
                Ty::Uint(UintTy::U128),
                Ty::Uint(UintTy::U16),
                Ty::Uint(UintTy::U128),
            ],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(&t1, 16, 16, &[(0, 0, 0), (0, 1, 0), (0, 2, 0)]);
    // #[repr(C, i32)] enum T2 { V0(u32) = 294, V1(i32, [u32; 0], bool) = 11, V2(u16, i8, i32) = 92, V3 = 171 }
    let t2 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T2",
            Some(ScalarTy::Int(IntTy::I32)),
            vec![
                VariantDef::new("V0", vec![Ty::Uint(UintTy::U32)]).with_discriminant(294),
                VariantDef::new(
                    "V1",
                    vec![
                        Ty::Int(IntTy::I32),
                        Ty::Array(Box::new(Ty::Uint(UintTy::U32)), 0),
                        Ty::Bool,
                    ],
                )
                .with_discriminant(11),
                VariantDef::new(
                    "V2",
                    vec![
                        Ty::Uint(UintTy::U16),
                        Ty::Int(IntTy::I8),
                        Ty::Int(IntTy::I32),
                    ],
                )
                .with_discriminant(92),
                VariantDef::new("V3", vec![]).with_discriminant(171),
            ],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(
        &t2,
        12,
        4,
        &[
            (0, 0, 4),
            (1, 0, 4),
            (1, 1, 8),
            (1, 2, 8),
            (2, 0, 4),
            (2, 1, 6),
            (2, 2, 8),
        ],
    );
    //  enum T3 { V0(i32, bool, char) }
    let t3 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T3",
            None,
            vec![VariantDef::new(
                "V0",
                vec![Ty::Int(IntTy::I32), Ty::Bool, Ty::Char],
            )],
        )
        .with_repr(AdtRepr::rust()),
    ));
    check(&t3, 12, 4, &[]);
    //  struct T4([u16; 3], u64, ());
    let t4 = Ty::Adt(Arc::new(
        AdtDef::new_struct(
            "T4",
            vec![
                Ty::Array(Box::new(Ty::Uint(UintTy::U16)), 3),
                Ty::Uint(UintTy::U64),
                Ty::unit(),
            ],
        )
        .with_repr(AdtRepr::rust()),
    ));
    check(&t4, 16, 8, &[]);
    // #[repr(u64)] enum T5 { V0 = 14, V1(u64, ()), V2(T1) }
    let t5 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T5",
            Some(ScalarTy::Uint(UintTy::U64)),
            vec![
                VariantDef::new("V0", vec![]).with_discriminant(14),
                VariantDef::new("V1", vec![Ty::Uint(UintTy::U64), Ty::unit()]),
                VariantDef::new("V2", vec![t1.clone()]),
            ],
        )
        .with_repr(AdtRepr::rust()),
    ));
    check(&t5, 32, 16, &[(1, 0, 8), (1, 1, 16), (2, 0, 16)]);
    // #[repr(i8)] enum T7 { V0, V1((u8, u32), u16), V2(T5, (u8, u32), u8) = 95, V3(u8, T4, i8) }
    let t7 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T7",
            Some(ScalarTy::Int(IntTy::I8)),
            vec![
                VariantDef::new("V0", vec![]),
                VariantDef::new(
                    "V1",
                    vec![
                        Ty::Tuple(vec![Ty::Uint(UintTy::U8), Ty::Uint(UintTy::U32)]),
                        Ty::Uint(UintTy::U16),
                    ],
                ),
                VariantDef::new(
                    "V2",
                    vec![
                        t5.clone(),
                        Ty::Tuple(vec![Ty::Uint(UintTy::U8), Ty::Uint(UintTy::U32)]),
                        Ty::Uint(UintTy::U8),
                    ],
                )
                .with_discriminant(95),
                VariantDef::new(
                    "V3",
                    vec![Ty::Uint(UintTy::U8), t4.clone(), Ty::Int(IntTy::I8)],
                ),
            ],
        )
        .with_repr(AdtRepr::rust()),
    ));
    check(
        &t7,
        64,
        16,
        &[
            (1, 0, 4),
            (1, 1, 12),
            (2, 0, 16),
            (2, 1, 48),
            (2, 2, 56),
            (3, 0, 1),
            (3, 1, 8),
            (3, 2, 24),
        ],
    );
    // #[repr(u64, align(2))] enum T8 { V0(()), V1([u8; 0], T3, *const u8) }
    let t8 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T8",
            Some(ScalarTy::Uint(UintTy::U64)),
            vec![
                VariantDef::new("V0", vec![Ty::unit()]),
                VariantDef::new(
                    "V1",
                    vec![
                        Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0),
                        t3.clone(),
                        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not),
                    ],
                ),
            ],
        )
        .with_repr(AdtRepr::rust().with_align(2)),
    ));
    check(&t8, 32, 8, &[(0, 0, 8), (1, 0, 8), (1, 1, 8), (1, 2, 24)]);
    // #[repr(u16)] enum T10 { V0((), bool, char), V1 = 140 }
    let t10 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T10",
            Some(ScalarTy::Uint(UintTy::U16)),
            vec![
                VariantDef::new("V0", vec![Ty::unit(), Ty::Bool, Ty::Char]),
                VariantDef::new("V1", vec![]).with_discriminant(140),
            ],
        )
        .with_repr(AdtRepr::rust()),
    ));
    check(&t10, 8, 4, &[(0, 0, 2), (0, 1, 2), (0, 2, 4)]);
    // #[repr(transparent)] struct T11([u32; 0]);
    let t11 = Ty::Adt(Arc::new(
        AdtDef::new_struct("T11", vec![Ty::Array(Box::new(Ty::Uint(UintTy::U32)), 0)])
            .with_repr(AdtRepr::transparent()),
    ));
    check(&t11, 0, 4, &[(0, 0, 0)]);
    // #[repr(C, i8)] enum T16 { V0, V1(bool) = 5, V2(u64, u16), V3(usize, T1, u16) }
    let t16 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T16",
            Some(ScalarTy::Int(IntTy::I8)),
            vec![
                VariantDef::new("V0", vec![]),
                VariantDef::new("V1", vec![Ty::Bool]).with_discriminant(5),
                VariantDef::new("V2", vec![Ty::Uint(UintTy::U64), Ty::Uint(UintTy::U16)]),
                VariantDef::new(
                    "V3",
                    vec![Ty::Uint(UintTy::Usize), t1.clone(), Ty::Uint(UintTy::U16)],
                ),
            ],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(
        &t16,
        64,
        16,
        &[
            (1, 0, 16),
            (2, 0, 16),
            (2, 1, 24),
            (3, 0, 16),
            (3, 1, 32),
            (3, 2, 48),
        ],
    );
    //  enum T18 { V0(i32, u16) }
    let t18 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T18",
            None,
            vec![VariantDef::new(
                "V0",
                vec![Ty::Int(IntTy::I32), Ty::Uint(UintTy::U16)],
            )],
        )
        .with_repr(AdtRepr::rust()),
    ));
    // #[repr(align(16))] enum T19 { V0([u8; 0], !), V1(*const u8, T18) }
    let t19 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T19",
            None,
            vec![
                VariantDef::new(
                    "V0",
                    vec![Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0), Ty::Never],
                ),
                VariantDef::new(
                    "V1",
                    vec![
                        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not),
                        t18.clone(),
                    ],
                ),
            ],
        )
        .with_repr(AdtRepr::rust().with_align(16)),
    ));
    check(&t19, 16, 16, &[(0, 0, 0), (0, 1, 0)]);
    // #[repr(C, i32, align(16))] enum T20 { V0(usize, char), V1(i8, char, i8) = -45 }
    let t20 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T20",
            Some(ScalarTy::Int(IntTy::I32)),
            vec![
                VariantDef::new("V0", vec![Ty::Uint(UintTy::Usize), Ty::Char]),
                VariantDef::new("V1", vec![Ty::Int(IntTy::I8), Ty::Char, Ty::Int(IntTy::I8)])
                    .with_discriminant(340282366920938463463374607431768211411),
            ],
        )
        .with_repr(AdtRepr::c().with_align(16)),
    ));
    check(
        &t20,
        32,
        16,
        &[(0, 0, 8), (0, 1, 16), (1, 0, 8), (1, 1, 12), (1, 2, 16)],
    );
    // #[repr(transparent)] union T24 { f0: i8, f1: () }
    let t24 = Ty::Adt(Arc::new(
        AdtDef::new_union("T24", vec![Ty::Int(IntTy::I8), Ty::unit()])
            .with_repr(AdtRepr::transparent()),
    ));
    check(&t24, 1, 1, &[(0, 0, 0), (0, 1, 0)]);
    //  enum T29 { V0(u32, T5, i8) }
    let t29 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T29",
            None,
            vec![VariantDef::new(
                "V0",
                vec![Ty::Uint(UintTy::U32), t5.clone(), Ty::Int(IntTy::I8)],
            )],
        )
        .with_repr(AdtRepr::rust()),
    ));
    // #[repr(align(4))] struct T30(u64, bool, (u8, u32));
    let t30 = Ty::Adt(Arc::new(
        AdtDef::new_struct(
            "T30",
            vec![
                Ty::Uint(UintTy::U64),
                Ty::Bool,
                Ty::Tuple(vec![Ty::Uint(UintTy::U8), Ty::Uint(UintTy::U32)]),
            ],
        )
        .with_repr(AdtRepr::rust().with_align(4)),
    ));
    check(&t30, 24, 8, &[]);
    //  enum T36 { V0, V1(!, [u8; 0]), V2(std::convert::Infallible) }
    let t36 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T36",
            None,
            vec![
                VariantDef::new("V0", vec![]),
                VariantDef::new(
                    "V1",
                    vec![Ty::Never, Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0)],
                ),
                VariantDef::new(
                    "V2",
                    vec![Ty::adt(AdtDef::new_enum("Infallible", None, vec![]))],
                ),
            ],
        )
        .with_repr(AdtRepr::rust()),
    ));
    // #[repr(transparent)] struct T40(u64);
    let t40 = Ty::Adt(Arc::new(
        AdtDef::new_struct("T40", vec![Ty::Uint(UintTy::U64)]).with_repr(AdtRepr::transparent()),
    ));
    // #[repr(C, u8)] enum T43 { V0 = 38, V1(()), V2(u16, usize), V3(T30, bool, u8) }
    let t43 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T43",
            Some(ScalarTy::Uint(UintTy::U8)),
            vec![
                VariantDef::new("V0", vec![]).with_discriminant(38),
                VariantDef::new("V1", vec![Ty::unit()]),
                VariantDef::new("V2", vec![Ty::Uint(UintTy::U16), Ty::Uint(UintTy::Usize)]),
                VariantDef::new("V3", vec![t30.clone(), Ty::Bool, Ty::Uint(UintTy::U8)]),
            ],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(
        &t43,
        40,
        8,
        &[
            (1, 0, 8),
            (2, 0, 8),
            (2, 1, 16),
            (3, 0, 8),
            (3, 1, 32),
            (3, 2, 33),
        ],
    );
    // #[repr(align(8))] struct T45((), [u8; 0], u64);
    let t45 = Ty::Adt(Arc::new(
        AdtDef::new_struct(
            "T45",
            vec![
                Ty::unit(),
                Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0),
                Ty::Uint(UintTy::U64),
            ],
        )
        .with_repr(AdtRepr::rust().with_align(8)),
    ));
    check(&t45, 8, 8, &[]);
    //  enum T46 { V0 }
    let t46 = Ty::Adt(Arc::new(
        AdtDef::new_enum("T46", None, vec![VariantDef::new("V0", vec![])])
            .with_repr(AdtRepr::rust()),
    ));
    // #[repr(C, i8, align(4))] enum T47 { V0([u16; 3]) = 125, V1([u8; 0], [u32; 0]) = -19, V2(T40) }
    let t47 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T47",
            Some(ScalarTy::Int(IntTy::I8)),
            vec![
                VariantDef::new("V0", vec![Ty::Array(Box::new(Ty::Uint(UintTy::U16)), 3)])
                    .with_discriminant(125),
                VariantDef::new(
                    "V1",
                    vec![
                        Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0),
                        Ty::Array(Box::new(Ty::Uint(UintTy::U32)), 0),
                    ],
                )
                .with_discriminant(340282366920938463463374607431768211437),
                VariantDef::new("V2", vec![t40.clone()]),
            ],
        )
        .with_repr(AdtRepr::c().with_align(4)),
    ));
    check(&t47, 16, 8, &[(0, 0, 8), (1, 0, 8), (1, 1, 8), (2, 0, 8)]);
    // #[repr(C)] struct T49([u16; 3], char);
    let t49 = Ty::Adt(Arc::new(
        AdtDef::new_struct(
            "T49",
            vec![Ty::Array(Box::new(Ty::Uint(UintTy::U16)), 3), Ty::Char],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(&t49, 12, 4, &[(0, 0, 0), (0, 1, 8)]);
    // #[repr(transparent)] struct T50(u8, (), [u8; 0]);
    let t50 = Ty::Adt(Arc::new(
        AdtDef::new_struct(
            "T50",
            vec![
                Ty::Uint(UintTy::U8),
                Ty::unit(),
                Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0),
            ],
        )
        .with_repr(AdtRepr::transparent()),
    ));
    // #[repr(i8, align(2))] enum T54 { V0(usize) }
    let t54 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T54",
            Some(ScalarTy::Int(IntTy::I8)),
            vec![VariantDef::new("V0", vec![Ty::Uint(UintTy::Usize)])],
        )
        .with_repr(AdtRepr::rust().with_align(2)),
    ));
    check(&t54, 16, 8, &[(0, 0, 8)]);
    // #[repr(transparent)] struct T58(usize);
    let t58 = Ty::Adt(Arc::new(
        AdtDef::new_struct("T58", vec![Ty::Uint(UintTy::Usize)]).with_repr(AdtRepr::transparent()),
    ));
    // #[repr(C, u16)] enum T60 { V0((), u128, (u8, u32)), V1(T45) = 291, V2(char, char) }
    let t60 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T60",
            Some(ScalarTy::Uint(UintTy::U16)),
            vec![
                VariantDef::new(
                    "V0",
                    vec![
                        Ty::unit(),
                        Ty::Uint(UintTy::U128),
                        Ty::Tuple(vec![Ty::Uint(UintTy::U8), Ty::Uint(UintTy::U32)]),
                    ],
                ),
                VariantDef::new("V1", vec![t45.clone()]).with_discriminant(291),
                VariantDef::new("V2", vec![Ty::Char, Ty::Char]),
            ],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(
        &t60,
        48,
        16,
        &[
            (0, 0, 16),
            (0, 1, 16),
            (0, 2, 32),
            (1, 0, 16),
            (2, 0, 16),
            (2, 1, 20),
        ],
    );
    // #[repr(C, u64)] enum T62 { V0, V1 = 106, V2, V3(u16, [u8; 0], T29) }
    let t62 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T62",
            Some(ScalarTy::Uint(UintTy::U64)),
            vec![
                VariantDef::new("V0", vec![]),
                VariantDef::new("V1", vec![]).with_discriminant(106),
                VariantDef::new("V2", vec![]),
                VariantDef::new(
                    "V3",
                    vec![
                        Ty::Uint(UintTy::U16),
                        Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0),
                        t29.clone(),
                    ],
                ),
            ],
        )
        .with_repr(AdtRepr::c()),
    ));
    check(&t62, 80, 16, &[(3, 0, 16), (3, 1, 18), (3, 2, 32)]);
    // #[repr(C, u64)] enum T80 { V0([u8; 0]) }
    let t80 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T80",
            Some(ScalarTy::Uint(UintTy::U64)),
            vec![VariantDef::new(
                "V0",
                vec![Ty::Array(Box::new(Ty::Uint(UintTy::U8)), 0)],
            )],
        )
        .with_repr(AdtRepr::c()),
    ));
    // #[repr(transparent)] union T84 { f0: (), f1: bool, f2: () }
    let t84 = Ty::Adt(Arc::new(
        AdtDef::new_union("T84", vec![Ty::unit(), Ty::Bool, Ty::unit()])
            .with_repr(AdtRepr::transparent()),
    ));
    // #[repr(i8, align(16))] enum T91 { V0(()) = -39 }
    let t91 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T91",
            Some(ScalarTy::Int(IntTy::I8)),
            vec![
                VariantDef::new("V0", vec![Ty::unit()])
                    .with_discriminant(340282366920938463463374607431768211417),
            ],
        )
        .with_repr(AdtRepr::rust().with_align(16)),
    ));
    check(&t91, 16, 16, &[(0, 0, 1)]);
    // #[repr(i32)] enum T92 { V0(u16, *const u8) = -86, V1(i32, u128) = -93 }
    let t92 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T92",
            Some(ScalarTy::Int(IntTy::I32)),
            vec![
                VariantDef::new(
                    "V0",
                    vec![
                        Ty::Uint(UintTy::U16),
                        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not),
                    ],
                )
                .with_discriminant(340282366920938463463374607431768211370),
                VariantDef::new("V1", vec![Ty::Int(IntTy::I32), Ty::Uint(UintTy::U128)])
                    .with_discriminant(340282366920938463463374607431768211363),
            ],
        )
        .with_repr(AdtRepr::rust()),
    ));
    check(&t92, 32, 16, &[(0, 0, 4), (0, 1, 8), (1, 0, 4), (1, 1, 16)]);
    // #[repr(C, align(8))] struct T95(T84, bool, u32);
    let t95 = Ty::Adt(Arc::new(
        AdtDef::new_struct("T95", vec![t84.clone(), Ty::Bool, Ty::Uint(UintTy::U32)])
            .with_repr(AdtRepr::c().with_align(8)),
    ));
    check(&t95, 8, 8, &[(0, 0, 0), (0, 1, 1), (0, 2, 4)]);
    // #[repr(C, i32, align(2))] enum T114 { V0(()) = -70 }
    let t114 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T114",
            Some(ScalarTy::Int(IntTy::I32)),
            vec![
                VariantDef::new("V0", vec![Ty::unit()])
                    .with_discriminant(340282366920938463463374607431768211386),
            ],
        )
        .with_repr(AdtRepr::c().with_align(2)),
    ));
    check(&t114, 4, 4, &[(0, 0, 4)]);
    // #[repr(i32, align(16))] enum T118 { V0(char) = 128, V1(bool, u128) = 120, V2, V3 }
    let t118 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T118",
            Some(ScalarTy::Int(IntTy::I32)),
            vec![
                VariantDef::new("V0", vec![Ty::Char]).with_discriminant(128),
                VariantDef::new("V1", vec![Ty::Bool, Ty::Uint(UintTy::U128)])
                    .with_discriminant(120),
                VariantDef::new("V2", vec![]),
                VariantDef::new("V3", vec![]),
            ],
        )
        .with_repr(AdtRepr::rust().with_align(16)),
    ));
    check(&t118, 32, 16, &[(0, 0, 4), (1, 0, 4), (1, 1, 16)]);
    // #[repr(C, align(2))] union T134 { f0: T58, f1: T50 }
    let t134 = Ty::Adt(Arc::new(
        AdtDef::new_union("T134", vec![t58.clone(), t50.clone()])
            .with_repr(AdtRepr::c().with_align(2)),
    ));
    check(&t134, 8, 8, &[(0, 0, 0), (0, 1, 0)]);
    // #[repr(C, align(8))] union T146 { f0: T36, f1: T46, f2: T80 }
    let t146 = Ty::Adt(Arc::new(
        AdtDef::new_union("T146", vec![t36.clone(), t46.clone(), t80.clone()])
            .with_repr(AdtRepr::c().with_align(8)),
    ));
    check(&t146, 8, 8, &[(0, 0, 0), (0, 1, 0), (0, 2, 0)]);
    // #[repr(u8)] enum T151 { V0((u8, u32)), V1(u128), V2(*const u8, bool) = 33 }
    let t151 = Ty::Adt(Arc::new(
        AdtDef::new_enum(
            "T151",
            Some(ScalarTy::Uint(UintTy::U8)),
            vec![
                VariantDef::new(
                    "V0",
                    vec![Ty::Tuple(vec![Ty::Uint(UintTy::U8), Ty::Uint(UintTy::U32)])],
                ),
                VariantDef::new("V1", vec![Ty::Uint(UintTy::U128)]),
                VariantDef::new(
                    "V2",
                    vec![
                        Ty::RawPtr(Box::new(Ty::Uint(UintTy::U8)), Mutability::Not),
                        Ty::Bool,
                    ],
                )
                .with_discriminant(33),
            ],
        )
        .with_repr(AdtRepr::rust()),
    ));
    check(
        &t151,
        32,
        16,
        &[(0, 0, 4), (1, 0, 16), (2, 0, 8), (2, 1, 16)],
    );
}

// ---------------------------------------------------------------------------------------------
// Adversarial Round B3 Regression Tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_b3_eval_place_read_and_write_enforce_typed_adt_union_enum_and_struct_invariants() {
    let (u_def, _) = adt(AdtDef::new_union("U2", vec![u32_ty(), u8_ty()]));
    let (e_def, _) = repr_u8_enum();
    let (s_def, _) = adt(AdtDef::new_struct("S2", vec![u32_ty(), u8_ty()]));

    // 1. Typed union `MirValue::union_value` in stateless `eval_place_read` / `eval_place_write`
    // (`declared_ty: None`) must enforce `AdtDef` field bounds and field types instead of
    // reporting `InactiveUnionField` on out-of-bounds reads or corrupting `active_field` on writes.
    let u_val = MirValue::union_value(&u_def, 0, u32v(10));
    let mut locals = vec![u_val.clone()];
    let oob_union_place = place(0, vec![field(5, Ty::Bool)]);
    assert_eq!(
        eval_place_read(&oob_union_place, &locals, PW),
        Err(RvalueEvalError::FieldOutOfBounds {
            field_idx: 5,
            field_count: 2,
        })
    );
    assert_eq!(
        eval_place_write(&oob_union_place, MirValue::Bool(true), &mut locals, PW),
        Err(RvalueEvalError::FieldOutOfBounds {
            field_idx: 5,
            field_count: 2,
        })
    );
    assert_eq!(locals[0], u_val);

    let bad_ty_union_place = place(0, vec![field(1, Ty::Bool)]);
    assert!(matches!(
        eval_place_write(&bad_ty_union_place, MirValue::Bool(true), &mut locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(locals[0], u_val);

    // 2. Typed enum `MirValue::adt` must require `Downcast` before `Field` even when
    // `variant_idx == 0`, and reject out-of-range `Downcast(99)` with `TypeMismatch`.
    let e_val = MirValue::adt(&e_def, 0, vec![u8v(1), u32v(2)]);
    let mut e_locals = vec![e_val.clone()];
    let no_downcast = place(0, vec![field(0, u8_ty())]);
    assert!(matches!(
        eval_place_read(&no_downcast, &e_locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        eval_place_write(&no_downcast, u8v(9), &mut e_locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    let oob_downcast = place(0, vec![ProjectionElem::Downcast(99), field(0, u8_ty())]);
    assert!(matches!(
        eval_place_read(&oob_downcast, &e_locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        eval_place_write(&oob_downcast, u8v(9), &mut e_locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(e_locals[0], e_val);

    // 3. Typed struct `MirValue::adt` must reject `Downcast(0)` with `TypeMismatch`.
    let s_val = MirValue::adt(&s_def, 0, vec![u32v(7), u8v(8)]);
    let mut s_locals = vec![s_val.clone()];
    let struct_downcast = place(0, vec![ProjectionElem::Downcast(0), field(0, u32_ty())]);
    assert!(matches!(
        eval_place_read(&struct_downcast, &s_locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert!(matches!(
        eval_place_write(&struct_downcast, u32v(9), &mut s_locals, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    assert_eq!(s_locals[0], s_val);
}

#[test]
fn test_b3_legacy_multi_field_union_identity_transmute_and_well_formedness() {
    let (nz_def, nz_ty) = non_zero_u32();
    let union_tuple_ty = Ty::Tuple(vec![u32_ty(), nz_ty.clone()]);
    // Legacy multi-field union `MirValue::Adt` with `active_field: Some(0)` (`u32` active) and
    // an invalid `NonZeroU32(0)` sitting in the inactive slot `fields[1]`.
    let legacy_union = MirValue::Adt {
        def_path: "LegacyU".to_string(),
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![u32v(42), MirValue::adt(&nz_def, 0, vec![u32v(0)])],
        adt_def: None,
    };

    // 1. Identity transmute on `union_tuple_ty` must accept the 2-element legacy union and
    // normalize the active field `0`.
    let mut state = state_with(vec![union_tuple_ty.clone()], PW);
    state.slots[0] = LocalSlotState::Init(legacy_union.clone());
    transmute(
        &mut state,
        0,
        Operand::Copy(local(0)),
        union_tuple_ty.clone(),
    )
    .unwrap();
    assert_eq!(
        state.read_place(&place(0, vec![field(0, u32_ty())])),
        Ok(u32v(42))
    );

    // 2. Passing `legacy_union` as a CFG body argument checks only the active field (`u32v(42)`),
    // not the inactive slot `fields[1]`.
    let body = lower_ok(
        &mk_body(
            vec![u32_ty(), union_tuple_ty],
            vec![blk(
                vec![assign(
                    local(0),
                    Rvalue::Use(Operand::Copy(place(1, vec![field(0, u32_ty())]))),
                )],
                Terminator::Return,
            )],
        ),
        PW,
    );
    assert_eq!(
        eval_lowered_body_cfg(&body, &[legacy_union], 4),
        Ok(CfgEvalOutcome::Returned(u32v(42)))
    );
}

#[test]
fn test_b3_shallow_init_box_wrap_unsafe_binder_and_canonical_layout_bounds() {
    // 1. Hand-built `LoweredRvalue::ShallowInitBox` must reject `*const T` (`Mutability::Not`)
    // and unrepresentable pointee types.
    let ptr_u8 = raw(u8_ty(), Mutability::Mut);
    let ptr_val = PointerValue::with_provenance(0x2000, 1, 1);
    let mut state = state_with(vec![raw(u32_ty(), Mutability::Not)], PW);
    let const_box = LoweredRvalue::ShallowInitBox {
        operand: Operand::Constant(Constant::Ptr(ptr_val, ptr_u8.clone())),
        operand_ty: ptr_u8.clone(),
        ty: raw(u32_ty(), Mutability::Not),
    };
    assert!(matches!(
        eval_lowered_rvalue_in_state(&const_box, &mut state),
        Err(RvalueEvalError::TypeMismatch(_))
    ));

    let too_large_inner = Ty::Array(Box::new(u8_ty()), usize::MAX);
    let too_large_box = LoweredRvalue::ShallowInitBox {
        operand: Operand::Constant(Constant::Ptr(ptr_val, ptr_u8)),
        operand_ty: raw(u8_ty(), Mutability::Mut),
        ty: raw(too_large_inner.clone(), Mutability::Mut),
    };
    assert_eq!(
        eval_lowered_rvalue_in_state(&too_large_box, &mut state),
        Err(RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge {
            ty: too_large_inner.clone(),
        }))
    );

    // 2. `Rvalue::WrapUnsafeBinder` must reject single-field structs with `repr(align)` overrides,
    // and hand-built `LoweredRvalue::WrapUnsafeBinder` must validate `ty` representability.
    let (_, over_aligned_wrapper) = adt(
        AdtDef::new_struct("OverAligned", vec![u32_ty()]).with_repr(AdtRepr::c().with_align(8)),
    );
    assert!(matches!(
        lower_rvalue(
            &Rvalue::WrapUnsafeBinder(cint(1, u32_ty()), over_aligned_wrapper),
            &[],
            PW,
        ),
        Err(RvalueLowerError::InvalidWrapUnsafeBinder { .. })
    ));

    let (_, ill_formed_wrapper) = adt(
        AdtDef::new_struct("BadAlignWrapper", vec![u32_ty()])
            .with_repr(AdtRepr::rust().with_align(3)),
    );
    let hand_binder = LoweredRvalue::WrapUnsafeBinder {
        operand: cint(1, u32_ty()),
        operand_ty: u32_ty(),
        ty: ill_formed_wrapper.clone(),
    };
    assert!(matches!(
        eval_lowered_rvalue_in_state(&hand_binder, &mut state),
        Err(RvalueEvalError::CastEval(CastEvalError::IllFormedType {
            ty,
            ..
        })) if ty == ill_formed_wrapper
    ));

    // 3. `Ty::has_canonical_byte_layout` must return `false` on unrepresentable arrays and tuples.
    assert!(!too_large_inner.has_canonical_byte_layout(PW));
    let half_max_arr = Ty::Array(Box::new(u8_ty()), (isize::MAX as usize / 2) + 1);
    let too_large_tuple = Ty::Tuple(vec![half_max_arr.clone(), half_max_arr]);
    assert_eq!(too_large_tuple.layout_for(PW), Err(LayoutError::TooLarge));
    assert!(!too_large_tuple.has_canonical_byte_layout(PW));
}

#[test]
fn test_b3_eval_cfg_in_state_validates_state_switch_int_targets_and_unwind_actions() {
    let lb = |terminator: Option<LoweredTerminator>, is_cleanup: bool| LoweredBasicBlock {
        statements: vec![],
        terminator,
        is_cleanup,
    };
    let mk_lowered = |basic_blocks: Vec<LoweredBasicBlock>| LoweredBody {
        local_decls: vec![u8_ty()],
        basic_blocks,
        ptr_width: PW,
    };

    // 1. `eval_cfg_in_state` rejects a `StatementEvalState` whose `ptr_width` or `local_decls`
    // disagree with `LoweredBody`.
    let simple_body = mk_lowered(vec![lb(
        Some(LoweredTerminator::Return { ret_ty: u8_ty() }),
        false,
    )]);
    let wrong_pw_state = state_with(vec![u8_ty()], PtrWidth::Bits32);
    assert!(matches!(
        eval_cfg_in_state(&simple_body, wrong_pw_state, 0, 4, None),
        Err(CfgEvalError::InvalidArguments(
            RvalueEvalError::TypeMismatch(_)
        ))
    ));
    let wrong_decls_state = state_with(vec![u32_ty()], PW);
    assert!(matches!(
        eval_cfg_in_state(&simple_body, wrong_decls_state, 0, 4, None),
        Err(CfgEvalError::InvalidArguments(
            RvalueEvalError::TypeMismatch(_)
        ))
    ));

    // 2. Hand-built `LoweredTerminator::SwitchInt` with duplicate or out-of-range target values
    // fails closed even when the discriminant takes `otherwise`.
    let oob_switch = mk_lowered(vec![lb(
        Some(LoweredTerminator::SwitchInt {
            discr: cbool(false),
            discr_ty: Ty::Bool,
            targets: SwitchTargets {
                values: vec![2],
                targets: vec![0],
                otherwise: 0,
            },
        }),
        false,
    )]);
    assert!(matches!(
        eval_lowered_body_cfg(&oob_switch, &[], 4),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::TypeMismatch(_),
        })
    ));

    let dup_switch = mk_lowered(vec![lb(
        Some(LoweredTerminator::SwitchInt {
            discr: cint(9, u8_ty()),
            discr_ty: u8_ty(),
            targets: SwitchTargets {
                values: vec![1, 1],
                targets: vec![0, 0],
                otherwise: 0,
            },
        }),
        false,
    )]);
    assert!(matches!(
        eval_lowered_body_cfg(&dup_switch, &[], 4),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::TypeMismatch(_),
        })
    ));

    // 3. Hand-built `Drop`, passing `Assert`, and returning `Call` validate their `unwind`
    // actions/edges even when no panic occurs.
    let mut init_state = state_with(vec![u8_ty()], PW);
    init_state.slots[0] = LocalSlotState::Init(u8v(1));

    let bad_drop = mk_lowered(vec![lb(
        Some(LoweredTerminator::Drop {
            place: local(0),
            place_ty: u8_ty(),
            target: 0,
            unwind: UnwindAction::Cleanup(0), // bb0 is not a cleanup block
        }),
        false,
    )]);
    assert_eq!(
        eval_cfg_in_state(&bad_drop, init_state.clone(), 0, 4, None),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 0 })
    );

    let bad_passing_assert = mk_lowered(vec![lb(
        Some(LoweredTerminator::Assert {
            cond: cbool(true),
            expected: true,
            msg: custom("ok"),
            target: 0,
            unwind: UnwindAction::Cleanup(99), // out-of-range block
        }),
        false,
    )]);
    assert_eq!(
        eval_cfg_in_state(&bad_passing_assert, init_state.clone(), 0, 4, None),
        Err(CfgEvalError::InvalidBlock { bb: 99 })
    );

    let bad_returning_call = mk_lowered(vec![lb(
        Some(LoweredTerminator::Call {
            func: Operand::Constant(Constant::Unit),
            func_ty: unit(),
            args: vec![],
            arg_tys: vec![],
            destination: local(0),
            dest_ty: u8_ty(),
            target: Some(0),
            unwind: UnwindAction::Cleanup(0), // bb0 is not a cleanup block
        }),
        false,
    )]);
    let mut ok_handler = |_: usize, _: &MirValue, _: &[MirValue]| Ok(CallOutcome::Return(u8v(2)));
    assert_eq!(
        eval_cfg_in_state(
            &bad_returning_call,
            init_state,
            0,
            4,
            Some(&mut ok_handler),
        ),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 0 })
    );
}

// ---------------------------------------------------------------------------------------------
// A3 regression tests
// ---------------------------------------------------------------------------------------------

/// `Option<T>` modeled as the tagless `repr(Rust)` enum `{ None, Some(T) }`.
fn option_of(name: &str, payload: Ty) -> (Arc<AdtDef>, Ty) {
    adt(AdtDef::new_enum(
        name,
        None,
        vec![
            VariantDef::new("None", vec![]),
            VariantDef::new("Some", vec![payload]),
        ],
    ))
}

#[test]
fn test_a3_niche_capable_enum_shells_have_no_readable_tag_until_complete() {
    // `Option<NonZeroU32>`: `rustc` niche-encodes `None` in the payload and leaves `Some`
    // untagged, so `SetDiscriminant(Some)` writes no bytes and the discriminant is decoded from
    // the payload. Before the payload is written, reading the discriminant is UB (MiniRust
    // decodes uninitialized niche bytes; Miri reports `InvalidNichedEnumVariantWritten`).
    let (nz_def, nz) = non_zero_u32();
    let (opt_def, opt) = option_of("OptNz", nz.clone());
    assert!(opt_def.requires_tag_write() && !opt_def.tag_survives_field_deinit());
    // `enum BoolRef { A(bool, &u32), B }`: the niche (and so `B`'s tag) lives in `A`'s `bool`.
    let (bool_ref_def, bool_ref) = adt(AdtDef::new_enum(
        "BoolRef",
        None,
        vec![
            VariantDef::new("A", vec![Ty::Bool, ref_ty(u32_ty())]),
            VariantDef::new("B", vec![]),
        ],
    ));
    let decls = vec![opt.clone(), bool_ref.clone(), u32_ty()];
    let mut state = state_with(decls.clone(), PW);
    let set = |l: usize, v: usize| Statement::SetDiscriminant {
        place: local(l),
        variant_index: v,
    };
    let isize_v = |v: i128| MirValue::signed(v, IntTy::Isize, PW);

    run(set(0, 1), &mut state).unwrap();
    let Some(LocalSlotState::PartialShell(shell)) = state.get_local(Local(0)).cloned() else {
        panic!("expected a shell");
    };
    assert!(shell.discriminant_set && !shell.tag_is_readable());
    assert_eq!(
        discriminant(&mut state, local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    // Writing the payload completes the value, whose discriminant is then readable.
    let some0 = place(0, vec![ProjectionElem::Downcast(1), field(0, nz.clone())]);
    run(
        assign(some0, adt_aggregate(&nz_def, 0, None, vec![cint(5, u32_ty())])),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(0)),
        Some(&MirValue::adt(
            &opt_def,
            1,
            vec![MirValue::adt(&nz_def, 0, vec![u32v(5)])]
        ))
    );
    assert_eq!(discriminant(&mut state, local(0)), Ok(isize_v(1)));
    // Switching an initialized `None` to `Some` without writing the payload: no readable tag.
    state.slots[0] = LocalSlotState::Init(MirValue::adt(&opt_def, 0, vec![]));
    run(set(0, 1), &mut state).unwrap();
    assert_eq!(
        discriminant(&mut state, local(0)),
        Err(RvalueEvalError::UninitializedLocal(Local(0)))
    );
    // A fieldless variant is complete (and its tag readable) right away.
    run(set(0, 0), &mut state).unwrap();
    assert_eq!(discriminant(&mut state, local(0)), Ok(isize_v(0)));

    // Retag reads the discriminant to find the variant holding references: with `A.1` written
    // but the niche-carrying `A.0` not, the variant is unreadable.
    run(set(1, 0), &mut state).unwrap();
    state.slots[2] = LocalSlotState::Init(u32v(7));
    let a1 = place(1, vec![ProjectionElem::Downcast(0), field(1, ref_ty(u32_ty()))]);
    run(assign(a1, Rvalue::Ref(Mutability::Not, local(2))), &mut state).unwrap();
    assert_eq!(
        run(retag(RetagKind::Default, local(1)), &mut state),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    assert_eq!(
        discriminant(&mut state, local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    let a0 = place(1, vec![ProjectionElem::Downcast(0), field(0, Ty::Bool)]);
    run(assign(a0, Rvalue::Use(cbool(true))), &mut state).unwrap();
    assert!(matches!(
        state.get_local(Local(1)),
        Some(LocalSlotState::Init(MirValue::Adt { adt_def: Some(def), variant_idx: 0, .. }))
            if *def == bool_ref_def
    ));
    run(retag(RetagKind::Default, local(1)), &mut state).unwrap();
    assert_eq!(discriminant(&mut state, local(1)), Ok(isize_v(0)));

    // Tags stored apart from the fields (explicit `repr(Int)`, tagless `repr(C)`) are written by
    // `SetDiscriminant` and stay readable on incomplete shells.
    let (_, repr_u8) = repr_u8_enum();
    let (c_def, c_opt) = adt(
        AdtDef::new_enum(
            "COptNz",
            None,
            vec![
                VariantDef::new("None", vec![]),
                VariantDef::new("Some", vec![nz.clone()]),
            ],
        )
        .with_repr(AdtRepr::c()),
    );
    assert!(c_def.tag_survives_field_deinit());
    let mut tagged = state_with(vec![repr_u8, c_opt], PW);
    run(set(0, 0), &mut tagged).unwrap();
    assert_eq!(discriminant(&mut tagged, local(0)), Ok(u8v(0)));
    run(set(1, 1), &mut tagged).unwrap();
    assert_eq!(discriminant(&mut tagged, local(1)), Ok(isize_v(1)));

    // Legacy tuple-modeled shells keep their rule (a written tag is readable), and tuple
    // shells have no tag.
    let mut legacy = PartialAggregate::new_uninit(1, 1, true);
    assert!(!legacy.tag_is_readable());
    legacy.discriminant_set = true;
    assert!(legacy.tag_is_readable());
    assert!(PartialAggregate::new_uninit(2, 0, false).tag_is_readable());
}

#[test]
fn test_a3_episode1_evaluators_reject_out_of_width_values_instead_of_truncating() {
    // On a 32-bit target, a `usize` or pointer value above `u32::MAX` is ill-formed. The
    // evaluators used to mask such values, turning them into valid ones.
    let pw = PtrWidth::Bits32;
    let const_u32 = raw(u32_ty(), Mutability::Not);
    let mut_u32 = raw(u32_ty(), Mutability::Mut);
    let decls = vec![
        unit(),
        u32_ty(),
        u32_ty(),
        usize_ty(),
        const_u32.clone(),
        ref_ty(u32_ty()),
    ];
    let mut state = state_with(decls.clone(), pw);
    state.slots[1] = LocalSlotState::Init(u32v(7));
    // `copy_nonoverlapping::<u32>(&raw _1, &raw mut _2, _3)`: synthetic bases `0x2000`/`0x3000`.
    let src = ptr_const(0x2000, Some(2), const_u32.clone());
    let dst = ptr_const(0x3000, Some(3), mut_u32.clone());
    let mut ok_state = state.clone();
    ok_state.slots[3] = LocalSlotState::Init(usizev(1));
    run(copy_nonoverlapping(src.clone(), dst.clone(), cp(3)), &mut ok_state).unwrap();
    assert_eq!(ok_state.get_init(Local(2)), Some(&u32v(7)));
    // An out-of-width count (`2^32 + 1`) used to be truncated to `1` and copied.
    let wide_count = (1u128 << 32) + 1;
    state.slots[3] = LocalSlotState::Init(usizev(wide_count));
    let before = state.clone();
    assert_eq!(
        run(copy_nonoverlapping(src.clone(), dst.clone(), cp(3)), &mut state),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: usize_ty(),
            bits: wide_count,
        }))
    );
    assert_eq!(state, before);
    // An out-of-width source address used to be truncated onto `_1`'s synthetic base.
    let wide_addr = (1u64 << 32) + 0x2000;
    state.slots[3] = LocalSlotState::Init(usizev(1));
    state.slots[4] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::with_provenance(wide_addr, 2, 1),
        const_u32.clone(),
    ));
    let before = state.clone();
    assert_eq!(
        run(copy_nonoverlapping(cp(4), dst.clone(), cp(3)), &mut state),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: const_u32.clone(),
            bits: u128::from(wide_addr),
        }))
    );
    assert_eq!(state, before);

    // Retag: an out-of-width (but aligned once truncated) reference used to pass.
    let wide_ref = (1u64 << 32) + 0x1000;
    state.slots[5] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(wide_ref),
        ref_ty(u32_ty()),
    ));
    assert_eq!(
        run(retag(RetagKind::Default, local(5)), &mut state),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ref_ty(u32_ty()),
            bits: u128::from(wide_ref),
        }))
    );
    state.slots[5] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(0x1000),
        ref_ty(u32_ty()),
    ));
    run(retag(RetagKind::Default, local(5)), &mut state).unwrap();

    // SwitchInt: a `u8` holding `0x101` used to be truncated to `1` and take that arm.
    let body = mk_body(
        vec![u32_ty(), u8_ty()],
        vec![
            blk(
                vec![],
                Terminator::SwitchInt {
                    discr: cp(1),
                    targets: SwitchTargets::static_if(1, 1, 2),
                },
            ),
            blk(
                vec![assign(local(0), Rvalue::Use(cint(1, u32_ty())))],
                Terminator::Return,
            ),
            blk(
                vec![assign(local(0), Rvalue::Use(cint(2, u32_ty())))],
                Terminator::Return,
            ),
        ],
    );
    let lowered = lower_ok(&body, pw);
    let mut switch_state = state_with(body.local_decls.clone(), pw);
    switch_state.slots[1] = LocalSlotState::Init(u8v(1));
    assert_eq!(
        returned(eval_cfg_in_state(&lowered, switch_state.clone(), 0, 4, None)),
        u32v(1)
    );
    switch_state.slots[1] = LocalSlotState::Init(u8v(0x101));
    assert_eq!(
        eval_cfg_in_state(&lowered, switch_state, 0, 4, None),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: u8_ty(),
                bits: 0x101,
            }),
        })
    );
}

#[test]
fn test_a3_retag_rejects_references_into_storage_dead_locals() {
    let decls = vec![
        unit(),
        u32_ty(),
        ref_ty(u32_ty()),
        unit(),
        ref_ty(unit()),
        Ty::Tuple(vec![ref_ty(u32_ty()), u8_ty()]),
    ];
    let mut state = state_with(decls.clone(), PW);
    state.slots[1] = LocalSlotState::Init(u32v(7));
    state.slots[3] = LocalSlotState::Init(MirValue::Unit);
    run(assign(local(2), Rvalue::Ref(Mutability::Not, local(1))), &mut state).unwrap();
    run(assign(local(4), Rvalue::Ref(Mutability::Not, local(3))), &mut state).unwrap();
    run(
        assign(
            local(5),
            Rvalue::Aggregate(AggregateKind::Tuple, vec![cp(2), cint(1, u8_ty())]),
        ),
        &mut state,
    )
    .unwrap();
    for p in [local(2), local(4), local(5)] {
        run(retag(RetagKind::Default, p), &mut state).unwrap();
    }
    run(Statement::StorageDead(Local(1)), &mut state).unwrap();
    run(Statement::StorageDead(Local(3)), &mut state).unwrap();
    // `&_1` now dangles: retagging it, directly or nested in an aggregate, is UB.
    assert_eq!(
        run(retag(RetagKind::Default, local(2)), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(1)))
    );
    assert_eq!(
        run(retag(RetagKind::FnEntry, local(5)), &mut state),
        Err(RvalueEvalError::DeadLocal(Local(1)))
    );
    // A zero-sized pointee needs no live allocation.
    run(retag(RetagKind::Default, local(4)), &mut state).unwrap();
    // `StorageLive` gives the local (and its synthetic allocation) live storage again.
    run(Statement::StorageLive(Local(1)), &mut state).unwrap();
    run(retag(RetagKind::TwoPhase, local(2)), &mut state).unwrap();
}

/// Runs `body` from `bb0` step by step with [`eval_lowered_terminator`], composing the steps
/// exactly as [`eval_cfg_in_state`] specifies: one unit of fuel, the block's statements, then
/// its terminator.
fn run_terminator_steps(
    body: &LoweredBody,
    args: &[MirValue],
    mut fuel: usize,
) -> Result<CfgEvalOutcome, CfgEvalError> {
    let mut state =
        StatementEvalState::from_body(body, args).map_err(CfgEvalError::InvalidArguments)?;
    let mut bb = 0;
    let mut unwinding: UnwindState = None;
    loop {
        if fuel == 0 {
            return Ok(CfgEvalOutcome::OutOfFuel { bb, state });
        }
        fuel -= 1;
        let block = &body.basic_blocks[bb];
        for (index, stmt) in block.statements.iter().enumerate() {
            eval_lowered_statement(stmt, &mut state)
                .map_err(|error| CfgEvalError::Statement { bb, index, error })?;
        }
        let term = block
            .terminator
            .as_ref()
            .ok_or(CfgEvalError::MissingTerminator { bb })?;
        match eval_lowered_terminator(body, bb, term, &mut state, &mut unwinding, None)? {
            CfgStep::Goto(next) => bb = next,
            CfgStep::Done(outcome) => return Ok(outcome),
        }
    }
}

#[test]
fn test_a3_eval_lowered_terminator_steps_compose_into_eval_cfg_in_state() {
    let countdown = lower_ok(&countdown_body(), PW);
    for n in [0u128, 1, 3] {
        for fuel in 0..12 {
            assert_eq!(
                run_terminator_steps(&countdown, &[u32v(n)], fuel),
                eval_lowered_body_cfg(&countdown, &[u32v(n)], fuel),
                "countdown({n}) with fuel {fuel}"
            );
        }
    }
    let resume = cleanup_blk(vec![], Terminator::UnwindResume);
    let unwinding_body = lower_ok(&assert_body(UnwindAction::Cleanup(2), vec![resume]), PW);
    for c in [true, false] {
        for fuel in 0..4 {
            assert_eq!(
                run_terminator_steps(&unwinding_body, &[MirValue::Bool(c)], fuel),
                eval_lowered_body_cfg(&unwinding_body, &[MirValue::Bool(c)], fuel),
                "assert({c}) with fuel {fuel}"
            );
        }
    }

    // One failing-assertion step enters unwinding mode at the cleanup block; `UnwindResume`
    // then ends the body with the original panic and leaves unwinding mode.
    let mut state =
        StatementEvalState::from_body(&unwinding_body, &[MirValue::Bool(false)]).unwrap();
    let mut unwinding: UnwindState = None;
    let term0 = unwinding_body.basic_blocks[0].terminator.clone().unwrap();
    let term2 = unwinding_body.basic_blocks[2].terminator.clone().unwrap();
    assert_eq!(
        eval_lowered_terminator(&unwinding_body, 0, &term0, &mut state, &mut unwinding, None),
        Ok(CfgStep::Goto(2))
    );
    assert_eq!(unwinding, Some((0, custom_msg("boom"))));
    assert_eq!(
        eval_lowered_terminator(&unwinding_body, 2, &term2, &mut state, &mut unwinding, None),
        Ok(CfgStep::Done(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: custom_msg("boom"),
        }))
    );
    assert_eq!(unwinding, None);
    // Unknown blocks and edges that break the cleanup discipline are rejected.
    assert_eq!(
        eval_lowered_terminator(&unwinding_body, 9, &term0, &mut state, &mut unwinding, None),
        Err(CfgEvalError::InvalidBlock { bb: 9 })
    );
    assert_eq!(
        eval_lowered_terminator(
            &unwinding_body,
            0,
            &LoweredTerminator::Goto { target: 2 },
            &mut state,
            &mut unwinding,
            None,
        ),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 2 })
    );
}

// ---------------------------------------------------------------------------------------------
// B4 regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_b4_niche_encoded_enum_init_values_reject_invalid_niche_payloads_in_discriminant_and_retag()
{
    let (nz_def, nz) = non_zero_u32();
    let (opt_def, opt) = option_of("OptNzB4", nz.clone());
    let (nz_ref_def, nz_ref) = adt(AdtDef::new_enum(
        "NzRefB4",
        None,
        vec![
            VariantDef::new("A", vec![nz.clone(), ref_ty(u32_ty())]),
            VariantDef::new("B", vec![]),
        ],
    ));
    let (_, wrapper) = adt(AdtDef::new_struct("WrapOptNzB4", vec![opt.clone(), u32_ty()]));

    let decls = vec![opt.clone(), nz_ref.clone(), u32_ty(), wrapper.clone(), Ty::Int(IntTy::Isize)];
    let mut state = state_with(decls.clone(), PW);

    // 1. Building `Option<NonZeroU32>` via `SetDiscriminant(_0, Some)` followed by writing `0u32`
    // into the inner `u32` field `((_0 as Some).0).0` promotes `_0` to `LocalSlotState::Init`
    // holding `Some(NonZeroU32(0))`. Because `0` is `None`'s niche bit pattern (and outside
    // `NonZeroU32`'s valid range), `Discriminant(_0)` must fail closed in both stateful and
    // stateless evaluators.
    run(
        Statement::SetDiscriminant {
            place: local(0),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    let some_inner_u32 = place(
        0,
        vec![
            ProjectionElem::Downcast(1),
            field(0, nz.clone()),
            field(0, u32_ty()),
        ],
    );
    run(
        assign(some_inner_u32.clone(), Rvalue::Use(cint(0, u32_ty()))),
        &mut state,
    )
    .unwrap();
    let invalid_some = MirValue::adt(&opt_def, 1, vec![MirValue::adt(&nz_def, 0, vec![u32v(0)])]);
    assert_eq!(state.get_init(Local(0)), Some(&invalid_some));
    assert_eq!(
        discriminant(&mut state, local(0)),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: nz.clone(),
            bits: 0,
        }))
    );
    let lowered_discr = lower_rvalue(&Rvalue::Discriminant(local(0)), &decls, PW).unwrap();
    let mut tracker = ExposedProvenanceTracker::new();
    assert_eq!(
        eval_lowered_rvalue(
            &lowered_discr,
            &[invalid_some],
            PW,
            TransmutePolicy::RejectPtrToInt,
            &mut tracker,
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: nz.clone(),
            bits: 0,
        }))
    );
    // Writing a valid non-zero payload (`5`) restores a readable `Some` discriminant.
    run(
        assign(some_inner_u32, Rvalue::Use(cint(5, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        discriminant(&mut state, local(0)),
        Ok(MirValue::signed(1, IntTy::Isize, PW))
    );

    // Same when `Option<NonZeroU32>` is an `Init` field inside an incomplete outer struct shell.
    let wrap_opt = place(3, vec![field(0, opt.clone())]);
    let wrap_opt_u32 = place(
        3,
        vec![
            field(0, opt.clone()),
            ProjectionElem::Downcast(1),
            field(0, nz.clone()),
            field(0, u32_ty()),
        ],
    );
    run(
        Statement::SetDiscriminant {
            place: wrap_opt.clone(),
            variant_index: 1,
        },
        &mut state,
    )
    .unwrap();
    run(
        assign(wrap_opt_u32, Rvalue::Use(cint(0, u32_ty()))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(3)),
        Some(LocalSlotState::PartialShell(_))
    ));
    assert_eq!(
        discriminant(&mut state, wrap_opt),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: nz.clone(),
            bits: 0,
        }))
    );

    // 2. `Statement::Retag` on `enum NzRef { A(NonZeroU32, &u32), B }` where `A.0` holds the
    // invalid niche value `0` (even though `NonZeroU32` contains no references) must fail closed.
    state.slots[2] = LocalSlotState::Init(u32v(9));
    run(
        Statement::SetDiscriminant {
            place: local(1),
            variant_index: 0,
        },
        &mut state,
    )
    .unwrap();
    let a0_u32 = place(
        1,
        vec![
            ProjectionElem::Downcast(0),
            field(0, nz.clone()),
            field(0, u32_ty()),
        ],
    );
    let a1_ref = place(
        1,
        vec![ProjectionElem::Downcast(0), field(1, ref_ty(u32_ty()))],
    );
    run(assign(a0_u32.clone(), Rvalue::Use(cint(0, u32_ty()))), &mut state).unwrap();
    run(
        assign(a1_ref, Rvalue::Ref(Mutability::Not, local(2))),
        &mut state,
    )
    .unwrap();
    assert!(matches!(
        state.get_local(Local(1)),
        Some(LocalSlotState::Init(MirValue::Adt { adt_def: Some(def), variant_idx: 0, .. }))
            if *def == nz_ref_def
    ));
    assert_eq!(
        run(retag(RetagKind::Default, local(1)), &mut state),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: nz.clone(),
            bits: 0,
        }))
    );
    run(assign(a0_u32, Rvalue::Use(cint(1, u32_ty()))), &mut state).unwrap();
    run(retag(RetagKind::Default, local(1)), &mut state).unwrap();

    // 3. On `Bits32`, `check_scalar_ranges` must not mask an out-of-width pointer field into a
    // valid `NonNull<u32>` bit pattern.
    let pw32 = PtrWidth::Bits32;
    let const_u32 = raw(u32_ty(), Mutability::Not);
    let (non_null_def, non_null) = adt(
        AdtDef::new_struct("NonNullU32B4", vec![const_u32.clone()])
            .with_scalar_valid_range(ScalarValidRange::non_zero(32)),
    );
    let wide_ptr = (1u64 << 32) + 4;
    let mut state32 = state_with(vec![non_null.clone(), const_u32.clone()], pw32);
    state32.slots[1] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::without_provenance(wide_ptr),
        const_u32,
    ));
    assert_eq!(
        run(
            assign(local(0), adt_aggregate(&non_null_def, 0, None, vec![cp(1)])),
            &mut state32,
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: non_null,
            bits: u128::from(wide_ptr),
        }))
    );
}

#[test]
fn test_b4_mir_value_matches_ty_subtype_and_wrap_unsafe_binder_enforce_scalar_and_leaf_validity() {
    let (wrapper_def, wrapper) = adt(AdtDef::new_struct("WrapRefB4", vec![ref_ty(u32_ty())]));
    let decls = vec![
        Ty::Bool,
        ref_ty(u32_ty()),
        u32_ty(),
        u8_ty(),
        wrapper.clone(),
    ];
    let mut state = state_with(decls.clone(), PW);

    // 1. `MirValue::Int` with a non-integral `Ty` and `MirValue::Ptr` with a non-pointer `Ty`
    // are rejected by `mir_value_matches_ty` (`write_place`, `from_body`, etc.).
    for (slot_idx, ty, bad_val) in [
        (
            0,
            Ty::Bool,
            MirValue::Int {
                bits: 1,
                ty: Ty::Bool,
            },
        ),
        (
            1,
            ref_ty(u32_ty()),
            MirValue::Int {
                bits: 0x1000,
                ty: ref_ty(u32_ty()),
            },
        ),
        (
            2,
            u32_ty(),
            MirValue::Ptr {
                ptr: PointerValue::without_provenance(7),
                ty: u32_ty(),
            },
        ),
    ] {
        assert_eq!(
            state.write_place(&local(slot_idx), &ty, bad_val.clone()),
            Err(RvalueEvalError::TypeMismatch(
                "assigned value runtime type does not match destination place type"
            ))
        );
        let body = lower_ok(
            &mk_body(
                vec![unit(), ty],
                vec![blk(
                    vec![assign(local(0), Rvalue::Use(Operand::Constant(Constant::Unit)))],
                    Terminator::Return,
                )],
            ),
            PW,
        );
        assert!(matches!(
            StatementEvalState::from_body(&body, &[bad_val]),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
    }

    // 2. `CastKind::Subtype` and `Rvalue::WrapUnsafeBinder` reject null references and
    // out-of-width integers/pointers instead of passing them through `check_scalar_ranges`.
    let null_ref = MirValue::ptr(PointerValue::without_provenance(0), ref_ty(u32_ty()));
    state.slots[1] = LocalSlotState::Init(null_ref);
    assert_eq!(
        run(
            assign(
                local(1),
                Rvalue::Cast(CastKind::Subtype, cp(1), ref_ty(u32_ty()))
            ),
            &mut state,
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ref_ty(u32_ty()),
            bits: 0,
        }))
    );
    assert_eq!(
        run(
            assign(local(4), Rvalue::WrapUnsafeBinder(cp(1), wrapper.clone())),
            &mut state,
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: ref_ty(u32_ty()),
            bits: 0,
        }))
    );

    state.slots[3] = LocalSlotState::Init(u8v(0x101));
    assert_eq!(
        run(
            assign(local(3), Rvalue::Cast(CastKind::Subtype, cp(3), u8_ty())),
            &mut state,
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: u8_ty(),
            bits: 0x101,
        }))
    );
    assert_eq!(
        run(
            assign(local(3), Rvalue::WrapUnsafeBinder(cp(3), u8_ty())),
            &mut state,
        ),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: u8_ty(),
            bits: 0x101,
        }))
    );

    // Valid reference passes both `Subtype` and `WrapUnsafeBinder`.
    let good_ptr = PointerValue::with_provenance(0x2000, 2, 1);
    state.slots[1] = LocalSlotState::Init(MirValue::ptr(good_ptr, ref_ty(u32_ty())));
    run(
        assign(local(4), Rvalue::WrapUnsafeBinder(cp(1), wrapper)),
        &mut state,
    )
    .unwrap();
    assert_eq!(
        state.get_init(Local(4)),
        Some(&MirValue::adt(
            &wrapper_def,
            0,
            vec![MirValue::ptr(good_ptr, ref_ty(u32_ty()))]
        ))
    );
}

#[test]
fn test_b4_eval_lowered_terminator_enforces_state_cleanup_mode_and_well_formed_boundary_values() {
    let resume = cleanup_blk(vec![], Terminator::UnwindResume);
    let unwinding_body = lower_ok(&assert_body(UnwindAction::Cleanup(2), vec![resume]), PW);
    let term0 = unwinding_body.basic_blocks[0].terminator.clone().unwrap();
    let term2 = unwinding_body.basic_blocks[2].terminator.clone().unwrap();

    // 1. Direct calls to `eval_lowered_terminator` validate `state` against `body` and require
    // `block.is_cleanup == unwinding.is_some()` on entry.
    let mut wrong_pw_state = state_with(unwinding_body.local_decls.clone(), PtrWidth::Bits32);
    let mut unwinding: UnwindState = None;
    assert!(matches!(
        eval_lowered_terminator(
            &unwinding_body,
            0,
            &term0,
            &mut wrong_pw_state,
            &mut unwinding,
            None,
        ),
        Err(CfgEvalError::InvalidArguments(
            RvalueEvalError::TypeMismatch(_)
        ))
    ));

    let mut state =
        StatementEvalState::from_body(&unwinding_body, &[MirValue::Bool(true)]).unwrap();
    // Cleanup block `bb2` cannot run while `unwinding` is `None` (even with `Goto { target: 0 }`).
    assert_eq!(
        eval_lowered_terminator(
            &unwinding_body,
            2,
            &LoweredTerminator::Goto { target: 0 },
            &mut state,
            &mut None,
            None,
        ),
        Err(CfgEvalError::InvalidUnwind { bb: 2 })
    );
    // Non-cleanup block `bb0` cannot run while `unwinding` is `Some(...)` (even with `UnwindResume`
    // or `Goto { target: 2 }`).
    let mut active_unwind: UnwindState = Some((0, custom_msg("boom")));
    assert_eq!(
        eval_lowered_terminator(
            &unwinding_body,
            0,
            &term2,
            &mut state,
            &mut active_unwind,
            None,
        ),
        Err(CfgEvalError::InvalidUnwind { bb: 0 })
    );
    assert_eq!(
        eval_lowered_terminator(
            &unwinding_body,
            0,
            &LoweredTerminator::Goto { target: 2 },
            &mut state,
            &mut active_unwind,
            None,
        ),
        Err(CfgEvalError::InvalidUnwind { bb: 0 })
    );

    // 2. `Return`, `Call`, and failing `Assert` message evaluation reject out-of-width integers
    // and null references.
    let ret_body = lower_ok(
        &mk_body(vec![u8_ty()], vec![blk(vec![], Terminator::Return)]),
        PW,
    );
    let mut bad_ret_state = state_with(vec![u8_ty()], PW);
    bad_ret_state.slots[0] = LocalSlotState::Init(u8v(0x101));
    assert_eq!(
        eval_cfg_in_state(&ret_body, bad_ret_state, 0, 2, None),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: u8_ty(),
                bits: 0x101,
            }),
        })
    );

    let call_body = lower_ok(
        &mk_body(
            vec![u8_ty(), u8_ty()],
            vec![
                blk(
                    vec![],
                    Terminator::Call {
                        func: Operand::Constant(Constant::Unit),
                        args: vec![cp(1)],
                        destination: local(0),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
    let mut bad_call_state = state_with(vec![u8_ty(), u8_ty()], PW);
    bad_call_state.slots[1] = LocalSlotState::Init(u8v(0x101));
    let mut handler = |_: usize, _: &MirValue, _: &[MirValue]| Ok(CallOutcome::Return(u8v(1)));
    assert_eq!(
        eval_cfg_in_state(&call_body, bad_call_state, 0, 2, Some(&mut handler)),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: u8_ty(),
                bits: 0x101,
            }),
        })
    );

    let bounds_assert_body = lower_ok(
        &mk_body(
            vec![unit(), usize_ty()],
            vec![blk(
                vec![],
                assert_t(
                    cbool(false),
                    true,
                    AssertMessage::BoundsCheck {
                        len: cp(1),
                        index: cint(0, usize_ty()),
                    },
                    0,
                    UnwindAction::Continue,
                ),
            )],
        ),
        PtrWidth::Bits32,
    );
    let mut bad_assert_state = state_with(vec![unit(), usize_ty()], PtrWidth::Bits32);
    let wide_len = 1u128 << 32;
    bad_assert_state.slots[1] = LocalSlotState::Init(usizev(wide_len));
    assert_eq!(
        eval_cfg_in_state(&bounds_assert_body, bad_assert_state, 0, 2, None),
        Err(CfgEvalError::Terminator {
            bb: 0,
            error: RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
                target_ty: usize_ty(),
                bits: wide_len,
            }),
        })
    );
}

// ---------------------------------------------------------------------------------------------
// A4 regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_a4_raw_retag_rejects_out_of_width_pointers_and_rustc_niche_construction_stays_defined() {
    // 1. `Retag([raw] _1)` accepts null, unaligned, and dangling raw pointers, but (like every
    // other Episode 1 validity check since A3/B4) not an address beyond the target's width,
    // which it used to accept on a 32-bit target.
    let pw32 = PtrWidth::Bits32;
    let const_u32 = raw(u32_ty(), Mutability::Not);
    let mut state32 = state_with(vec![unit(), const_u32.clone()], pw32);
    for addr in [0u64, 3, 0xFFFF_FFFC] {
        state32.slots[1] = LocalSlotState::Init(MirValue::ptr(
            PointerValue::without_provenance(addr),
            const_u32.clone(),
        ));
        run(retag(RetagKind::Raw(Mutability::Not), local(1)), &mut state32).unwrap();
    }
    let wide = (1u64 << 32) + 0x10;
    state32.slots[1] = LocalSlotState::Init(MirValue::ptr(
        PointerValue::with_provenance(wide, 2, 1),
        const_u32.clone(),
    ));
    assert_eq!(
        run(retag(RetagKind::Raw(Mutability::Not), local(1)), &mut state32),
        Err(RvalueEvalError::CastEval(CastEvalError::InvalidBitPattern {
            target_ty: const_u32,
            bits: u128::from(wide),
        }))
    );

    // 2. The conservative niche rules (A3: no readable tag on an incomplete niche-capable
    // shell; B4: a niche-capable value's discriminant needs a well-formed value) keep the order
    // in which `rustc` builds such enums in place fully defined: fields first, then
    // `SetDiscriminant`, then `Retag`/`Discriminant`.
    let (opt_def, opt_ref) = option_of("OptRefA4", ref_ty(u32_ty()));
    let decls = vec![unit(), opt_ref.clone(), u32_ty()];
    let mut state = state_with(decls.clone(), PW);
    state.slots[2] = LocalSlotState::Init(u32v(7));
    let some0 = place(1, vec![ProjectionElem::Downcast(1), field(0, ref_ty(u32_ty()))]);
    let set = |v: usize| Statement::SetDiscriminant {
        place: local(1),
        variant_index: v,
    };
    run(assign(some0, Rvalue::Ref(Mutability::Not, local(2))), &mut state).unwrap();
    assert_eq!(
        discriminant(&mut state, local(1)),
        Err(RvalueEvalError::UninitializedLocal(Local(1)))
    );
    run(set(1), &mut state).unwrap();
    let some = MirValue::adt(
        &opt_def,
        1,
        vec![MirValue::ptr(
            PointerValue::with_provenance(0x3000, 3, 1),
            ref_ty(u32_ty()),
        )],
    );
    assert_eq!(state.get_init(Local(1)), Some(&some));
    for kind in [RetagKind::FnEntry, RetagKind::Default, RetagKind::TwoPhase] {
        run(retag(kind, local(1)), &mut state).unwrap();
    }
    assert_eq!(
        discriminant(&mut state, local(1)),
        Ok(MirValue::signed(1, IntTy::Isize, PW))
    );
    // Writing the niche-tagged `None` completes the value right away.
    run(set(0), &mut state).unwrap();
    assert_eq!(
        state.get_init(Local(1)),
        Some(&MirValue::adt(&opt_def, 0, vec![]))
    );
    run(retag(RetagKind::Default, local(1)), &mut state).unwrap();
    assert_eq!(
        discriminant(&mut state, local(1)),
        Ok(MirValue::signed(0, IntTy::Isize, PW))
    );
}
