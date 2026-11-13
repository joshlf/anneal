//! Episode 1 (`ep1-rust-lower-wide-ptr-slice-unsize-and-fnptr`) tests: unsized slices and
//! `str`, wide pointers, array-to-slice `Unsize`, function pointers (reification, casts,
//! transmutes, and indirect calls), checked against
//! `Trusted.Rustc.V2026_06_01.MirSemantics.Places` (`unsizeArrayToSliceSpec?`,
//! `evalUnsizeCoercion`, `evalPlaceLen`, `evalWidePtrAggregateRelBinOp`,
//! `reifyCoercionSafetyCompatible`, `checkCalleeSig`, `evalFnPtrToPtr`) on both
//! `PtrWidth::Bits32` and `PtrWidth::Bits64`.

use std::collections::BTreeSet;
use std::sync::Arc;

use anneal_mir::*;

const PWS: [PtrWidth; 2] = [PtrWidth::Bits32, PtrWidth::Bits64];

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
fn unit() -> Ty {
    Ty::unit()
}
fn slice(elem: Ty) -> Ty {
    Ty::Slice(Box::new(elem))
}
fn arr(elem: Ty, n: usize) -> Ty {
    Ty::Array(Box::new(elem), n)
}
fn rf(pointee: Ty, m: Mutability) -> Ty {
    Ty::Ref(Box::new(pointee), m)
}
fn raw(pointee: Ty, m: Mutability) -> Ty {
    Ty::RawPtr(Box::new(pointee), m)
}
fn fn_ty(inputs: Vec<Ty>, output: Ty) -> Ty {
    Ty::fn_ptr(inputs, output, Safety::Safe)
}
fn unsafe_fn_ty(inputs: Vec<Ty>, output: Ty) -> Ty {
    Ty::fn_ptr(inputs, output, Safety::Unsafe)
}
fn adt(def: AdtDef) -> (Arc<AdtDef>, Ty) {
    let def = Arc::new(def);
    (def.clone(), Ty::Adt(def))
}
/// `enum Option<T> { None, Some(T) }` (tagless, `#[repr(Rust)]`).
fn option_of(payload: Ty) -> (Arc<AdtDef>, Ty) {
    adt(AdtDef::new_enum(
        "Option",
        None,
        vec![
            VariantDef::new("None", vec![]),
            VariantDef::new("Some", vec![payload]),
        ],
    ))
}

const NOT: Mutability = Mutability::Not;
const MUT: Mutability = Mutability::Mut;

fn local(i: usize) -> Place {
    Place::from_local(i)
}
fn proj(i: usize, projection: Vec<ProjectionElem>) -> Place {
    Place::with_projection(i, projection)
}
fn deref(i: usize) -> Place {
    proj(i, vec![ProjectionElem::Deref])
}
fn copy(i: usize) -> Operand {
    Operand::Copy(local(i))
}
fn cint(v: u128, ty: Ty) -> Operand {
    Operand::Constant(Constant::Int(v, ty))
}
fn cusize(v: u128) -> Operand {
    cint(v, usize_ty())
}
fn assign(i: usize, rv: Rvalue) -> Statement {
    Statement::Assign(local(i), rv)
}
fn uv(v: u128, ty: Ty) -> MirValue {
    MirValue::Int { bits: v, ty }
}
fn usizev(v: u128) -> MirValue {
    uv(v, usize_ty())
}
fn u32v(v: u128) -> MirValue {
    uv(v, u32_ty())
}
fn array_rv(elem: Ty, vals: &[u128]) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Array(elem.clone()),
        vals.iter().map(|v| cint(*v, elem.clone())).collect(),
    )
}
fn array_val(elem: Ty, vals: &[u128]) -> MirValue {
    MirValue::Array {
        elements: vals.iter().map(|v| uv(*v, elem.clone())).collect(),
        elem_ty: elem,
    }
}
fn cast(kind: CastKind, op: Operand, ty: Ty) -> Rvalue {
    Rvalue::Cast(kind, op, ty)
}
fn unsize(op: Operand, ty: Ty) -> Rvalue {
    cast(
        CastKind::PointerCoercion(PointerCoercionKind::Unsize),
        op,
        ty,
    )
}
fn reify(kind: PointerCoercionKind, op: Operand, ty: Ty) -> Rvalue {
    cast(CastKind::PointerCoercion(kind), op, ty)
}
/// Synthetic base address of local `i` in a frame whose preceding locals all fit a page.
fn base(i: usize) -> u64 {
    ((i + 1) * 0x1000) as u64
}
fn stack_ptr(i: usize, offset: u64) -> PointerValue {
    PointerValue::with_provenance(base(i) + offset, i as u64 + 1, 1)
}

/// Lowers and evaluates `stmts` in a frame whose locals `decls` all start live and
/// uninitialized, returning the state or the first evaluation error.
fn run(
    decls: &[Ty],
    stmts: &[Statement],
    pw: PtrWidth,
) -> Result<StatementEvalState, RvalueEvalError> {
    let mut state = StatementEvalState::from_local_decls(decls.to_vec(), pw);
    for stmt in stmts {
        let lowered = lower_statement(stmt, decls, pw)
            .unwrap_or_else(|err| panic!("lowering {stmt:?}: {err:?}"));
        eval_lowered_statement(&lowered, &mut state)?;
    }
    Ok(state)
}
fn value(state: &StatementEvalState, i: usize) -> MirValue {
    state
        .get_init(Local(i))
        .cloned()
        .unwrap_or_else(|| panic!("_{i} is not initialized"))
}

/// The common frame of the slice tests: `_1: [u32; 4] = [10, 11, 12, 13]`, `_2 = &mut _1`,
/// `_3 = _2 as &mut [u32]` (`Unsize`), plus `_4: usize`, `_5: u32`, `_6: &mut [u32]`,
/// `_7: &[u32]`, `_8: *const [u32]`.
fn slice_frame() -> (Vec<Ty>, Vec<Statement>) {
    let decls = vec![
        unit(),
        arr(u32_ty(), 4),
        rf(arr(u32_ty(), 4), MUT),
        rf(slice(u32_ty()), MUT),
        usize_ty(),
        u32_ty(),
        rf(slice(u32_ty()), MUT),
        rf(slice(u32_ty()), NOT),
        raw(slice(u32_ty()), NOT),
    ];
    let stmts = vec![
        assign(1, array_rv(u32_ty(), &[10, 11, 12, 13])),
        assign(2, Rvalue::Ref(MUT, local(1))),
        assign(3, unsize(copy(2), rf(slice(u32_ty()), MUT))),
    ];
    (decls, stmts)
}

// ---------------------------------------------------------------------------------------------
// A. Types, sizedness, layouts, and niches
// ---------------------------------------------------------------------------------------------

#[test]
fn wide_pointer_and_fn_pointer_layouts() {
    for pw in PWS {
        let ptr = pw.byte_size();
        for ty in [
            rf(slice(u8_ty()), NOT),
            rf(slice(u32_ty()), MUT),
            raw(slice(u16_ty()), NOT),
            raw(slice(u64_ty()), MUT),
            rf(Ty::Str, NOT),
            rf(Ty::Str, MUT),
            raw(Ty::Str, NOT),
            raw(Ty::Str, MUT),
        ] {
            assert!(
                ty.is_sized() && ty.is_wide_ptr() && !ty.is_thin_ptr(),
                "{ty:?}"
            );
            assert_eq!(
                ty.layout_for(pw),
                Ok(TyLayout {
                    size: 2 * ptr,
                    align: ptr
                }),
                "{ty:?} on {pw:?}"
            );
        }
        // Unsized types have no layout.
        for ty in [slice(u8_ty()), Ty::Str] {
            assert!(!ty.is_sized());
            assert_eq!(ty.layout_for(pw), Err(LayoutError::Unsized), "{ty:?}");
        }
        // Aggregates cannot hold unsized values; slices need sized elements.
        assert!(!arr(Ty::Str, 2).is_sized());
        assert!(arr(Ty::Str, 2).layout_for(pw).is_err());
        assert!(
            Ty::Tuple(vec![u8_ty(), slice(u8_ty())])
                .layout_for(pw)
                .is_err()
        );
        assert!(matches!(
            rf(slice(slice(u8_ty())), NOT).layout_for(pw),
            Err(LayoutError::IllFormed(_))
        ));
        assert!(matches!(
            rf(slice(Ty::Str), NOT).layout_for(pw),
            Err(LayoutError::IllFormed(_))
        ));
        // Function pointers: one non-null pointer.
        let f = fn_ty(vec![u32_ty(), rf(slice(u8_ty()), NOT)], u64_ty());
        assert!(f.is_sized() && f.is_fn_ptr() && f.has_null_niche());
        assert_eq!(
            f.layout_for(pw),
            Ok(TyLayout {
                size: ptr,
                align: ptr
            })
        );
        assert!(!f.is_valid_scalar_bits(0, pw));
        assert!(f.is_valid_scalar_bits(1, pw));
        assert!(f.is_valid_scalar_bits(pw.mask(), pw));
        assert!(matches!(
            fn_ty(vec![slice(u8_ty())], unit()).layout_for(pw),
            Err(LayoutError::IllFormed(_))
        ));
        assert!(matches!(
            fn_ty(vec![], Ty::Str).layout_for(pw),
            Err(LayoutError::IllFormed(_))
        ));
        // Function items are zero-sized; a closure is laid out as the tuple of its upvars.
        assert_eq!(
            Ty::FnDef(CallTarget::callee("f")).layout_for(pw),
            Ok(TyLayout { size: 0, align: 1 })
        );
        let closure = Ty::closure("c", vec![u32_ty(), u8_ty()]);
        assert_eq!(
            closure.layout_for(pw),
            Ty::Tuple(vec![u32_ty(), u8_ty()]).layout_for(pw)
        );
    }
    // `Constant::FnDef` keeps its unit type and value.
    assert_eq!(Constant::callee("f").ty(), Ty::unit());
    assert_eq!(
        eval_constant(&Constant::callee("f"), PtrWidth::Bits64),
        Ok(MirValue::Unit)
    );
}

#[test]
fn null_pointer_optimized_option_layouts() {
    for pw in PWS {
        let ptr = pw.byte_size();
        for (payload, size) in [
            (rf(slice(u8_ty()), NOT), 2 * ptr),
            (rf(Ty::Str, NOT), 2 * ptr),
            (rf(slice(u32_ty()), MUT), 2 * ptr),
            (fn_ty(vec![], unit()), ptr),
            (unsafe_fn_ty(vec![u32_ty()], u32_ty()), ptr),
            (rf(u32_ty(), NOT), ptr),
        ] {
            let (_, opt) = option_of(payload.clone());
            assert_eq!(
                opt.layout_for(pw),
                Ok(TyLayout { size, align: ptr }),
                "Option<{payload:?}> on {pw:?}"
            );
        }
        // Raw pointers and integers have no null niche.
        for payload in [raw(slice(u8_ty()), NOT), raw(u8_ty(), NOT), u32_ty()] {
            let (_, opt) = option_of(payload.clone());
            assert!(opt.layout_for(pw).is_err(), "Option<{payload:?}> on {pw:?}");
        }
    }
}

#[test]
fn unsized_places_are_rejected_by_value() {
    let pw = PtrWidth::Bits64;
    let decls = vec![unit(), rf(slice(u8_ty()), NOT), slice(u8_ty()).clone()];
    // Reading `*_1` by value.
    assert!(matches!(
        lower_rvalue(&Rvalue::Use(Operand::Copy(deref(1))), &decls, pw),
        Err(RvalueLowerError::UnsizedType(_))
    ));
    // `size_of::<[u8]>()`.
    assert!(
        lower_rvalue(
            &Rvalue::NullaryOp(NullOp::SizeOf, slice(u8_ty())),
            &decls,
            pw
        )
        .is_err()
    );
    // `Len` of a `str` place.
    let str_decls = vec![unit(), rf(Ty::Str, NOT)];
    assert!(matches!(
        lower_rvalue(&Rvalue::Len(deref(1)), &str_decls, pw),
        Err(RvalueLowerError::InvalidLenTarget(Ty::Str))
    ));
}

// ---------------------------------------------------------------------------------------------
// B. `Unsize`
// ---------------------------------------------------------------------------------------------

#[test]
fn unsize_lowering_follows_unsize_array_to_slice_spec() {
    for pw in PWS {
        let elem = u16_ty();
        let a = arr(elem.clone(), 3);
        let s = slice(elem.clone());
        let kinds = [
            ("&", rf(a.clone(), NOT), rf(s.clone(), NOT)),
            ("&mut", rf(a.clone(), MUT), rf(s.clone(), MUT)),
            ("*const", raw(a.clone(), NOT), raw(s.clone(), NOT)),
            ("*mut", raw(a.clone(), MUT), raw(s.clone(), MUT)),
        ];
        // (source kind, target kind) pairs accepted by `unsizeArrayToSliceSpec?`.
        let accepted: BTreeSet<(&str, &str)> = [
            ("&mut", "&"),
            ("&mut", "&mut"),
            ("&mut", "*const"),
            ("&mut", "*mut"),
            ("&", "&"),
            ("&", "*const"),
            ("*mut", "*const"),
            ("*mut", "*mut"),
            ("*const", "*const"),
        ]
        .into_iter()
        .collect();
        for (src_name, src_ty, _) in &kinds {
            for (dst_name, _, dst_ty) in &kinds {
                let decls = vec![unit(), src_ty.clone()];
                let lowered = lower_rvalue(&unsize(copy(1), dst_ty.clone()), &decls, pw);
                assert_eq!(
                    lowered.is_ok(),
                    accepted.contains(&(*src_name, *dst_name)),
                    "{src_name} [u16; 3] -> {dst_name} [u16] on {pw:?}: {lowered:?}"
                );
            }
        }
        // Element types must match, and only arrays unsize to slices.
        let decls = vec![unit(), rf(arr(u8_ty(), 3), NOT)];
        assert!(lower_rvalue(&unsize(copy(1), rf(slice(u16_ty()), NOT)), &decls, pw).is_err());
        assert!(lower_rvalue(&unsize(copy(1), rf(Ty::Str, NOT)), &decls, pw).is_err());
        let decls = vec![unit(), rf(u8_ty(), NOT)];
        assert!(lower_rvalue(&unsize(copy(1), rf(slice(u8_ty()), NOT)), &decls, pw).is_err());
        let decls = vec![unit(), rf(slice(u8_ty()), NOT)];
        assert!(lower_rvalue(&unsize(copy(1), rf(slice(u8_ty()), NOT)), &decls, pw).is_err());
    }
}

#[test]
fn unsize_array_length_must_fit_the_target() {
    // `[u8; 2^32]` is representable on 64-bit targets only.
    let big = arr(u8_ty(), 1usize << 32);
    let decls = vec![unit(), rf(big.clone(), NOT)];
    let rv = unsize(copy(1), rf(slice(u8_ty()), NOT));
    assert!(lower_rvalue(&rv, &decls, PtrWidth::Bits32).is_err());
    assert!(lower_rvalue(&rv, &decls, PtrWidth::Bits64).is_ok());
}

#[test]
fn wide_references_are_bounded_by_isize_max() {
    for pw in PWS {
        let max_isize = pw.max_isize() as u128;
        let pair = Ty::Tuple(vec![raw(u16_ty(), NOT), usize_ty()]);
        let decls = vec![
            unit(),
            pair.clone(),
            rf(slice(u16_ty()), NOT),
            raw(slice(u16_ty()), NOT),
        ];
        let make = |len: u128| {
            assign(
                1,
                Rvalue::Aggregate(
                    AggregateKind::Tuple,
                    vec![
                        Operand::Constant(Constant::Ptr(
                            PointerValue::without_provenance(0x40),
                            raw(u16_ty(), NOT),
                        )),
                        cusize(len),
                    ],
                ),
            )
        };
        // `isize::MAX / 2` `u16`s fit; one more does not (as a reference). A raw slice may
        // claim any length.
        let to_ref = assign(
            2,
            cast(CastKind::Transmute, copy(1), rf(slice(u16_ty()), NOT)),
        );
        let to_raw = assign(
            3,
            cast(CastKind::Transmute, copy(1), raw(slice(u16_ty()), NOT)),
        );
        let ok = run(&decls, &[make(max_isize / 2), to_ref.clone()], pw).unwrap();
        assert_eq!(
            value(&ok, 2).as_wide_ptr(),
            Some((
                PointerValue::without_provenance(0x40),
                (max_isize / 2) as usize
            ))
        );
        assert!(matches!(
            run(&decls, &[make(max_isize / 2 + 1), to_ref], pw).err(),
            Some(RvalueEvalError::CastEval(
                CastEvalError::InvalidBitPattern { .. }
            ))
        ));
        let raw_ok = run(&decls, &[make(pw.max_usize()), to_raw], pw).unwrap();
        assert_eq!(
            value(&raw_ok, 3).as_wide_ptr(),
            Some((
                PointerValue::without_provenance(0x40),
                pw.max_usize() as usize
            ))
        );
    }
}

#[test]
fn unsize_evaluates_to_wide_pointer_over_stack_array() {
    for pw in PWS {
        let (decls, stmts) = slice_frame();
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(
            value(&state, 3),
            MirValue::WidePtr {
                data: stack_ptr(1, 0),
                len: 4,
                ty: rf(slice(u32_ty()), MUT),
            }
        );
        // `&mut [u8; 3] -> *mut [u8]` and `*const [u8]` keep the data pointer.
        let decls = vec![
            unit(),
            arr(u8_ty(), 3),
            rf(arr(u8_ty(), 3), MUT),
            raw(slice(u8_ty()), MUT),
            raw(slice(u8_ty()), NOT),
        ];
        let state = run(
            &decls,
            &[
                assign(1, array_rv(u8_ty(), &[1, 2, 3])),
                assign(2, Rvalue::Ref(MUT, local(1))),
                assign(3, unsize(copy(2), raw(slice(u8_ty()), MUT))),
                assign(4, unsize(copy(2), raw(slice(u8_ty()), NOT))),
            ],
            pw,
        )
        .unwrap();
        assert_eq!(value(&state, 3).as_wide_ptr(), Some((stack_ptr(1, 0), 3)));
        assert_eq!(value(&state, 4).as_wide_ptr(), Some((stack_ptr(1, 0), 3)));
    }
}

#[test]
fn unsize_checks_backing_allocation() {
    for pw in PWS {
        let a4 = arr(u32_ty(), 4);
        let decls = vec![
            unit(),
            a4.clone(),
            rf(a4.clone(), NOT),
            rf(slice(u32_ty()), NOT),
        ];
        let init = assign(1, array_rv(u32_ty(), &[1, 2, 3, 4]));
        // A `&[u32; 4]` 8 bytes into the 16-byte `_1` designates bytes past its end.
        let past_end = Operand::Constant(Constant::Ptr(stack_ptr(1, 8), rf(a4.clone(), NOT)));
        assert_eq!(
            run(
                &decls,
                &[
                    init.clone(),
                    assign(3, unsize(past_end, rf(slice(u32_ty()), NOT)))
                ],
                pw
            )
            .err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: base(1) + 8,
                byte_len: 16
            })
        );
        // A storage-dead backing local.
        assert_eq!(
            run(
                &decls,
                &[
                    init.clone(),
                    assign(2, Rvalue::Ref(NOT, local(1))),
                    Statement::StorageDead(Local(1)),
                    assign(3, unsize(copy(2), rf(slice(u32_ty()), NOT))),
                ],
                pw
            )
            .err(),
            Some(RvalueEvalError::DeadLocal(Local(1)))
        );
        // A misaligned reference.
        let misaligned =
            Operand::Constant(Constant::Ptr(stack_ptr(1, 2), rf(arr(u32_ty(), 2), NOT)));
        let decls2 = vec![
            unit(),
            a4.clone(),
            rf(arr(u32_ty(), 2), NOT),
            rf(slice(u32_ty()), NOT),
        ];
        assert_eq!(
            run(
                &decls2,
                &[
                    init.clone(),
                    assign(3, unsize(misaligned, rf(slice(u32_ty()), NOT)))
                ],
                pw
            )
            .err(),
            Some(RvalueEvalError::MisalignedPointer {
                addr: base(1) + 2,
                required_align: 4
            })
        );
        // Without provenance a non-empty reference dangles, a raw pointer is fine, and an
        // empty reference is fine.
        let a3 = arr(u8_ty(), 3);
        let decls3 = vec![
            unit(),
            rf(slice(u8_ty()), NOT),
            raw(slice(u8_ty()), NOT),
            rf(slice(u8_ty()), NOT),
        ];
        let dangling = PointerValue::without_provenance(0x40);
        assert_eq!(
            run(
                &decls3,
                &[assign(
                    1,
                    unsize(
                        Operand::Constant(Constant::Ptr(dangling, rf(a3.clone(), NOT))),
                        rf(slice(u8_ty()), NOT)
                    )
                )],
                pw
            )
            .err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: 0x40,
                byte_len: 3
            })
        );
        let state = run(
            &decls3,
            &[
                assign(
                    2,
                    unsize(
                        Operand::Constant(Constant::Ptr(dangling, raw(a3.clone(), NOT))),
                        raw(slice(u8_ty()), NOT),
                    ),
                ),
                assign(
                    3,
                    unsize(
                        Operand::Constant(Constant::Ptr(dangling, rf(arr(u8_ty(), 0), NOT))),
                        rf(slice(u8_ty()), NOT),
                    ),
                ),
            ],
            pw,
        )
        .unwrap();
        assert_eq!(value(&state, 2).as_wide_ptr(), Some((dangling, 3)));
        assert_eq!(value(&state, 3).as_wide_ptr(), Some((dangling, 0)));
    }
}

// ---------------------------------------------------------------------------------------------
// C. Slice places: `Deref`, `Index`, `ConstantIndex`, `Subslice`, `Len`
// ---------------------------------------------------------------------------------------------

#[test]
fn slice_element_reads_and_writes() {
    for pw in PWS {
        let (decls, mut stmts) = slice_frame();
        stmts.extend([
            // `_5 = (*_3)[2]`
            assign(4, Rvalue::Use(cusize(2))),
            assign(
                5,
                Rvalue::Use(Operand::Copy(proj(
                    3,
                    vec![ProjectionElem::Deref, ProjectionElem::Index(Local(4))],
                ))),
            ),
            // `(*_3)[0] = 99`
            Statement::Assign(
                proj(
                    3,
                    vec![
                        ProjectionElem::Deref,
                        ProjectionElem::ConstantIndex {
                            offset: 0,
                            min_length: 1,
                            from_end: false,
                        },
                    ],
                ),
                Rvalue::Use(cint(99, u32_ty())),
            ),
            // `(*_3)[len - 1] = 77` (`from_end`)
            Statement::Assign(
                proj(
                    3,
                    vec![
                        ProjectionElem::Deref,
                        ProjectionElem::ConstantIndex {
                            offset: 1,
                            min_length: 1,
                            from_end: true,
                        },
                    ],
                ),
                Rvalue::Use(cint(77, u32_ty())),
            ),
        ]);
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 5), u32v(12));
        assert_eq!(value(&state, 1), array_val(u32_ty(), &[99, 11, 12, 77]));
    }
}

#[test]
fn slice_subslice_reborrow_and_len() {
    for pw in PWS {
        let (decls, mut stmts) = slice_frame();
        let sub = |from, to, from_end| ProjectionElem::Subslice { from, to, from_end };
        stmts.extend([
            // `_6 = &mut (*_3)[1..3]`
            assign(
                6,
                Rvalue::Ref(MUT, proj(3, vec![ProjectionElem::Deref, sub(1, 3, false)])),
            ),
            // `(*_6)[1] = 55` writes `_1[2]`.
            assign(4, Rvalue::Use(cusize(1))),
            Statement::Assign(
                proj(
                    6,
                    vec![ProjectionElem::Deref, ProjectionElem::Index(Local(4))],
                ),
                Rvalue::Use(cint(55, u32_ty())),
            ),
        ]);
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(
            value(&state, 6),
            MirValue::WidePtr {
                data: stack_ptr(1, 4),
                len: 2,
                ty: rf(slice(u32_ty()), MUT),
            }
        );
        assert_eq!(value(&state, 1), array_val(u32_ty(), &[10, 11, 55, 13]));

        // `Len(*_3)`, `Len((*_3)[1..])` (`from_end`), and `&(*_3)` keeps the length.
        let (decls, mut stmts) = slice_frame();
        stmts.extend([
            assign(4, Rvalue::Len(deref(3))),
            assign(7, Rvalue::Ref(NOT, deref(3))),
        ]);
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 4), usizev(4));
        assert_eq!(value(&state, 7).as_wide_ptr(), Some((stack_ptr(1, 0), 4)));
        let (decls, mut stmts) = slice_frame();
        stmts.push(assign(
            4,
            Rvalue::Len(proj(3, vec![ProjectionElem::Deref, sub(1, 1, true)])),
        ));
        assert_eq!(value(&run(&decls, &stmts, pw).unwrap(), 4), usizev(2));
        // `&raw const (*_3)[1..]` advances the raw data pointer.
        let (decls, mut stmts) = slice_frame();
        stmts.push(assign(
            8,
            Rvalue::RawPtr(NOT, proj(3, vec![ProjectionElem::Deref, sub(1, 0, true)])),
        ));
        assert_eq!(
            value(&run(&decls, &stmts, pw).unwrap(), 8).as_wide_ptr(),
            Some((stack_ptr(1, 4), 3))
        );
    }
}

#[test]
fn slice_projections_check_dynamic_bounds() {
    for pw in PWS {
        // `(*_3)[4]` on a 4-element slice.
        let (decls, mut stmts) = slice_frame();
        stmts.extend([
            assign(4, Rvalue::Use(cusize(4))),
            assign(
                5,
                Rvalue::Use(Operand::Copy(proj(
                    3,
                    vec![ProjectionElem::Deref, ProjectionElem::Index(Local(4))],
                ))),
            ),
        ]);
        assert_eq!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::IndexOutOfBounds { index: 4, len: 4 })
        );
        // `(*_3)[2..5]`.
        let (decls, mut stmts) = slice_frame();
        stmts.push(assign(
            7,
            Rvalue::Ref(
                NOT,
                proj(
                    3,
                    vec![
                        ProjectionElem::Deref,
                        ProjectionElem::Subslice {
                            from: 2,
                            to: 5,
                            from_end: false,
                        },
                    ],
                ),
            ),
        ));
        assert!(matches!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::IndexOutOfBounds { len: 4, .. })
        ));
        // `ConstantIndex` with `min_length` beyond the length.
        let (decls, mut stmts) = slice_frame();
        stmts.push(assign(
            5,
            Rvalue::Use(Operand::Copy(proj(
                3,
                vec![
                    ProjectionElem::Deref,
                    ProjectionElem::ConstantIndex {
                        offset: 0,
                        min_length: 5,
                        from_end: false,
                    },
                ],
            ))),
        ));
        assert!(matches!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::IndexOutOfBounds { len: 4, .. })
        ));
        // A storage-dead backing local.
        let (decls, mut stmts) = slice_frame();
        stmts.extend([
            Statement::StorageDead(Local(1)),
            assign(4, Rvalue::Len(deref(3))),
        ]);
        assert_eq!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::DeadLocal(Local(1)))
        );
    }
}

#[test]
fn str_places_reborrow_through_raw_aggregates() {
    for pw in PWS {
        // `_1: [u8; 5]`, `_2 = &raw const _1[0]`-like thin pointer, `_3 = *const str` from
        // `(_2, 5)`, `_4 = &*_3`.
        let decls = vec![
            unit(),
            arr(u8_ty(), 5),
            raw(u8_ty(), NOT),
            raw(Ty::Str, NOT),
            rf(Ty::Str, NOT),
            raw(arr(u8_ty(), 5), NOT),
            usize_ty(),
        ];
        let state = run(
            &decls,
            &[
                assign(1, array_rv(u8_ty(), &[104, 101, 108, 108, 111])),
                assign(5, Rvalue::RawPtr(NOT, local(1))),
                assign(
                    2,
                    cast(
                        CastKind::PointerCoercion(PointerCoercionKind::ArrayToPointer),
                        copy(5),
                        raw(u8_ty(), NOT),
                    ),
                ),
                assign(
                    3,
                    Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee: Ty::Str,
                            mutability: NOT,
                        },
                        vec![copy(2), cusize(5)],
                    ),
                ),
                assign(4, Rvalue::Ref(NOT, deref(3))),
                assign(6, Rvalue::UnaryOp(UnOp::PtrMetadata, copy(4))),
            ],
            pw,
        )
        .unwrap();
        assert_eq!(value(&state, 3).as_wide_ptr(), Some((stack_ptr(1, 0), 5)));
        assert_eq!(
            value(&state, 4),
            MirValue::WidePtr {
                data: stack_ptr(1, 0),
                len: 5,
                ty: rf(Ty::Str, NOT),
            }
        );
        assert_eq!(value(&state, 6), usizev(5));
    }
}

// ---------------------------------------------------------------------------------------------
// D. `AggregateKind::RawPtr`, `PtrMetadata`, `PtrToPtr`, `MutToConstPointer`
// ---------------------------------------------------------------------------------------------

#[test]
fn raw_ptr_aggregates_and_metadata() {
    for pw in PWS {
        let decls = vec![
            unit(),
            raw(u16_ty(), MUT),
            raw(slice(u16_ty()), MUT),
            usize_ty(),
            unit(),
            raw(slice(u16_ty()), NOT),
        ];
        let null = Operand::Constant(Constant::Ptr(
            PointerValue::without_provenance(0),
            raw(u16_ty(), MUT),
        ));
        let state = run(
            &decls,
            &[
                assign(1, Rvalue::Use(null)),
                assign(
                    2,
                    Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee: slice(u16_ty()),
                            mutability: MUT,
                        },
                        vec![copy(1), cusize(7)],
                    ),
                ),
                // `PtrMetadata` reads the length without dereferencing (even of a null slice).
                assign(3, Rvalue::UnaryOp(UnOp::PtrMetadata, copy(2))),
                // A thin pointer's metadata is `()`.
                assign(4, Rvalue::UnaryOp(UnOp::PtrMetadata, copy(1))),
                // `*mut [u16] -> *const [u16]`.
                assign(
                    5,
                    cast(
                        CastKind::PointerCoercion(PointerCoercionKind::MutToConstPointer),
                        copy(2),
                        raw(slice(u16_ty()), NOT),
                    ),
                ),
            ],
            pw,
        )
        .unwrap();
        assert_eq!(
            value(&state, 2),
            MirValue::WidePtr {
                data: PointerValue::without_provenance(0),
                len: 7,
                ty: raw(slice(u16_ty()), MUT),
            }
        );
        assert_eq!(value(&state, 3), usizev(7));
        assert_eq!(value(&state, 4), MirValue::Unit);
        assert_eq!(
            value(&state, 5).as_wide_ptr(),
            Some((PointerValue::without_provenance(0), 7))
        );
        // Unit metadata for a slice pointee and `usize` metadata for a sized pointee are
        // ill-typed, as is a non-pointer data operand.
        let decls = vec![unit(), raw(u16_ty(), MUT), usize_ty()];
        for (pointee, meta) in [
            (slice(u16_ty()), Operand::Constant(Constant::Unit)),
            (u16_ty(), cusize(1)),
        ] {
            assert!(
                lower_rvalue(
                    &Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee: pointee.clone(),
                            mutability: MUT,
                        },
                        vec![copy(1), meta],
                    ),
                    &decls,
                    pw
                )
                .is_err(),
                "{pointee:?}"
            );
        }
        assert!(
            lower_rvalue(
                &Rvalue::Aggregate(
                    AggregateKind::RawPtr {
                        pointee: slice(u16_ty()),
                        mutability: MUT,
                    },
                    vec![copy(2), cusize(1)],
                ),
                &decls,
                pw
            )
            .is_err()
        );
    }
}

#[test]
fn ptr_to_ptr_between_thin_and_wide_pointers() {
    for pw in PWS {
        let (mut decls, mut stmts) = slice_frame();
        // `_9 = _3 as *const [u32]`... via `&raw const *_3`, `_10 = _9 as *const u32`,
        // `_11 = _9 as *const [u8]`, `_12 = *_10`.
        decls.extend([
            raw(slice(u32_ty()), NOT),
            raw(u32_ty(), NOT),
            raw(slice(u8_ty()), NOT),
            u32_ty(),
        ]);
        stmts.extend([
            assign(9, Rvalue::RawPtr(NOT, deref(3))),
            assign(10, cast(CastKind::PtrToPtr, copy(9), raw(u32_ty(), NOT))),
            assign(
                11,
                cast(CastKind::PtrToPtr, copy(9), raw(slice(u8_ty()), NOT)),
            ),
            assign(12, Rvalue::Use(Operand::Copy(deref(10)))),
        ]);
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(
            value(&state, 10),
            MirValue::Ptr {
                ptr: stack_ptr(1, 0),
                ty: raw(u32_ty(), NOT),
            }
        );
        // The metadata is kept unchanged (4 elements, not 16 bytes).
        assert_eq!(value(&state, 11).as_wide_ptr(), Some((stack_ptr(1, 0), 4)));
        assert_eq!(value(&state, 12), u32v(10));
        // Thin to wide is rejected statically.
        let decls = vec![unit(), raw(u32_ty(), NOT)];
        assert!(
            lower_rvalue(
                &cast(CastKind::PtrToPtr, copy(1), raw(slice(u32_ty()), NOT)),
                &decls,
                pw
            )
            .is_err()
        );
        // ... and at runtime.
        let thin_to_wide = LoweredCast::PtrToPtr {
            src_ty: raw(u32_ty(), NOT),
            target_ty: raw(slice(u32_ty()), NOT),
            operand: copy(1),
        };
        let mut tracker = ExposedProvenanceTracker::new();
        assert!(
            eval_lowered_cast(
                &thin_to_wide,
                &MirValue::Ptr {
                    ptr: stack_ptr(1, 0),
                    ty: raw(u32_ty(), NOT),
                },
                pw,
                TransmutePolicy::RejectPtrToInt,
                &mut tracker
            )
            .is_err()
        );
    }
}

// ---------------------------------------------------------------------------------------------
// E. Relational operators
// ---------------------------------------------------------------------------------------------

#[test]
fn wide_and_fn_pointer_comparisons() {
    for pw in PWS {
        let ty = raw(slice(u8_ty()), NOT);
        let wide = |addr: u64, len: usize| MirValue::WidePtr {
            data: PointerValue::without_provenance(addr),
            len,
            ty: ty.clone(),
        };
        let b = |v: bool| MirValue::Bool(v);
        let cmp = |v: i128| MirValue::signed(v, IntTy::I8, pw);
        // Lexicographic on `(address, length)`.
        assert_eq!(
            eval_binop(BinOp::Eq, &wide(8, 2), &wide(8, 2), pw),
            Ok(b(true))
        );
        assert_eq!(
            eval_binop(BinOp::Eq, &wide(8, 2), &wide(8, 3), pw),
            Ok(b(false))
        );
        assert_eq!(
            eval_binop(BinOp::Ne, &wide(8, 2), &wide(8, 3), pw),
            Ok(b(true))
        );
        assert_eq!(
            eval_binop(BinOp::Lt, &wide(8, 9), &wide(16, 1), pw),
            Ok(b(true))
        );
        assert_eq!(
            eval_binop(BinOp::Lt, &wide(8, 2), &wide(8, 3), pw),
            Ok(b(true))
        );
        assert_eq!(
            eval_binop(BinOp::Ge, &wide(8, 3), &wide(8, 3), pw),
            Ok(b(true))
        );
        assert_eq!(
            eval_binop(BinOp::Gt, &wide(16, 0), &wide(8, 9), pw),
            Ok(b(true))
        );
        assert_eq!(
            eval_binop(BinOp::Le, &wide(16, 0), &wide(8, 9), pw),
            Ok(b(false))
        );
        assert_eq!(
            eval_binop(BinOp::Cmp, &wide(8, 2), &wide(8, 3), pw),
            Ok(cmp(-1))
        );
        assert_eq!(
            eval_binop(BinOp::Cmp, &wide(8, 3), &wide(8, 3), pw),
            Ok(cmp(0))
        );
        assert_eq!(
            eval_binop(BinOp::Cmp, &wide(9, 0), &wide(8, 3), pw),
            Ok(cmp(1))
        );
        // Function pointers compare by address.
        let f = MirValue::fn_ptr(CalleeSymbol::new("cmp_f"), fn_ty(vec![], unit()));
        let g = MirValue::fn_ptr(CalleeSymbol::new("cmp_g"), fn_ty(vec![], unit()));
        let (MirValue::FnPtr { addr: fa, .. }, MirValue::FnPtr { addr: ga, .. }) = (&f, &g) else {
            unreachable!()
        };
        assert_eq!(eval_binop(BinOp::Eq, &f, &f.clone(), pw), Ok(b(true)));
        assert_eq!(eval_binop(BinOp::Eq, &f, &g, pw), Ok(b(fa == ga)));
        assert_eq!(eval_binop(BinOp::Lt, &f, &g, pw), Ok(b(fa < ga)));
        let expected = match fa.cmp(ga) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        };
        assert_eq!(eval_binop(BinOp::Cmp, &f, &g, pw), Ok(cmp(expected)));
        // Statically, both operands need the same wide or function pointer type.
        let decls = vec![
            unit(),
            ty.clone(),
            raw(slice(u16_ty()), NOT),
            fn_ty(vec![], unit()),
        ];
        assert!(lower_rvalue(&Rvalue::BinaryOp(BinOp::Cmp, copy(1), copy(1)), &decls, pw).is_ok());
        assert!(lower_rvalue(&Rvalue::BinaryOp(BinOp::Eq, copy(1), copy(2)), &decls, pw).is_err());
        assert!(lower_rvalue(&Rvalue::BinaryOp(BinOp::Cmp, copy(3), copy(3)), &decls, pw).is_ok());
    }
}

// ---------------------------------------------------------------------------------------------
// F. Transmutes
// ---------------------------------------------------------------------------------------------

#[test]
fn wide_pointer_transmute_round_trips() {
    for pw in PWS {
        let (mut decls, mut stmts) = slice_frame();
        let pair = Ty::Tuple(vec![raw(u32_ty(), NOT), usize_ty()]);
        let (opt_def, opt) = option_of(rf(slice(u32_ty()), NOT));
        // `_9 = transmute::<&[u32], (*const u32, usize)>(_7)`, `_10 = transmute(_9)` back,
        // `_11: Option<&[u32]> = transmute(_9)`, `_12: Option<&[u32]>` from zero bytes.
        decls.extend([
            pair.clone(),
            rf(slice(u32_ty()), NOT),
            opt.clone(),
            opt.clone(),
        ]);
        stmts.extend([
            assign(7, Rvalue::Ref(NOT, deref(3))),
            assign(9, cast(CastKind::Transmute, copy(7), pair.clone())),
            assign(
                10,
                cast(CastKind::Transmute, copy(9), rf(slice(u32_ty()), NOT)),
            ),
            assign(11, cast(CastKind::Transmute, copy(9), opt.clone())),
            assign(
                12,
                cast(
                    CastKind::Transmute,
                    Operand::Constant(Constant::Int(
                        0,
                        if pw == PtrWidth::Bits32 {
                            u64_ty()
                        } else {
                            Ty::Uint(UintTy::U128)
                        },
                    )),
                    opt.clone(),
                ),
            ),
        ]);
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(
            value(&state, 9),
            MirValue::Tuple(vec![
                MirValue::Ptr {
                    ptr: stack_ptr(1, 0),
                    ty: raw(u32_ty(), NOT),
                },
                usizev(4),
            ])
        );
        assert_eq!(value(&state, 10), value(&state, 7));
        assert_eq!(
            value(&state, 11),
            MirValue::adt(&opt_def, 1, vec![value(&state, 7)])
        );
        assert_eq!(value(&state, 12), MirValue::adt(&opt_def, 0, vec![]));
        // A null `&[u32]` is an invalid value.
        let decls = vec![unit(), pair.clone(), rf(slice(u32_ty()), NOT)];
        let null_pair = Rvalue::Aggregate(
            AggregateKind::Tuple,
            vec![
                Operand::Constant(Constant::Ptr(
                    PointerValue::without_provenance(0),
                    raw(u32_ty(), NOT),
                )),
                cusize(1),
            ],
        );
        assert!(matches!(
            run(
                &decls,
                &[
                    assign(1, null_pair),
                    assign(
                        2,
                        cast(CastKind::Transmute, copy(1), rf(slice(u32_ty()), NOT))
                    ),
                ],
                pw
            )
            .err(),
            Some(RvalueEvalError::CastEval(
                CastEvalError::InvalidBitPattern { .. }
            ))
        ));
    }
}

// ---------------------------------------------------------------------------------------------
// G. Function pointers: reification, coercions, casts
// ---------------------------------------------------------------------------------------------

#[test]
fn reify_and_closure_coercions() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let closure_ty = Ty::closure("my_closure", vec![]);
        let decls = vec![
            unit(),
            f_ty.clone(),
            Ty::FnDef(CallTarget::callee("item")),
            f_ty.clone(),
            closure_ty.clone(),
            f_ty.clone(),
            unsafe_fn_ty(vec![u32_ty()], u32_ty()),
        ];
        let state = run(
            &decls,
            &[
                // `_1 = item as fn(u32) -> u32` (constant function item).
                assign(
                    1,
                    reify(
                        PointerCoercionKind::ReifyFnPointer,
                        Operand::callee("item"),
                        f_ty.clone(),
                    ),
                ),
                // `_2 = item` (a function item value), `_3 = _2 as fn(u32) -> u32`.
                assign(2, Rvalue::Use(Operand::callee("item"))),
                assign(
                    3,
                    reify(
                        PointerCoercionKind::ReifyFnPointerWithSafety(Safety::Safe),
                        copy(2),
                        f_ty.clone(),
                    ),
                ),
                // `_4 = || ..` (no captures), `_5 = _4 as fn(u32) -> u32`.
                assign(4, Rvalue::Aggregate(AggregateKind::Closure, vec![])),
                assign(
                    5,
                    reify(
                        PointerCoercionKind::ClosureFnPointer(Safety::Safe),
                        copy(4),
                        f_ty.clone(),
                    ),
                ),
                // `_6 = _1 as unsafe fn(u32) -> u32`.
                assign(
                    6,
                    reify(
                        PointerCoercionKind::UnsafeFnPointer,
                        copy(1),
                        unsafe_fn_ty(vec![u32_ty()], u32_ty()),
                    ),
                ),
            ],
            pw,
        )
        .unwrap();
        let item = CalleeSymbol::new("item");
        let expected = MirValue::FnPtr {
            target: item.clone(),
            addr: fn_ptr_addr(&item),
            ty: f_ty.clone(),
        };
        assert_eq!(value(&state, 1), expected);
        assert_eq!(value(&state, 3), expected);
        assert_eq!(
            value(&state, 5),
            MirValue::fn_ptr(CalleeSymbol::new("my_closure"), f_ty.clone())
        );
        assert_eq!(
            value(&state, 6),
            MirValue::FnPtr {
                target: item.clone(),
                addr: fn_ptr_addr(&item),
                ty: unsafe_fn_ty(vec![u32_ty()], u32_ty()),
            }
        );
        // Function-pointer addresses are non-null, in width, deterministic, and outside every
        // synthetic stack allocation.
        let addr = fn_ptr_addr(&item);
        assert!(addr != 0 && u128::from(addr) <= pw.mask() && addr < 0x1000);
        assert_eq!(fn_ptr_addr(&item), addr);

        // Static rejections: intrinsics, capturing closures, a closure through
        // `ReifyFnPointer`, safety mismatches, and `unsafe -> safe`.
        let capturing = Ty::closure("cap", vec![u32_ty()]);
        let decls = vec![
            unit(),
            capturing.clone(),
            closure_ty.clone(),
            unsafe_fn_ty(vec![u32_ty()], u32_ty()),
        ];
        let rejected = [
            reify(
                PointerCoercionKind::ReifyFnPointer,
                Operand::intrinsic(IntrinsicOp::Ctpop),
                f_ty.clone(),
            ),
            reify(
                PointerCoercionKind::ClosureFnPointerAnySafety,
                copy(1),
                f_ty.clone(),
            ),
            reify(PointerCoercionKind::ReifyFnPointer, copy(2), f_ty.clone()),
            reify(
                PointerCoercionKind::ReifyFnPointerWithSafety(Safety::Unsafe),
                Operand::callee("item"),
                f_ty.clone(),
            ),
            reify(
                PointerCoercionKind::ClosureFnPointer(Safety::Unsafe),
                copy(2),
                f_ty.clone(),
            ),
            reify(PointerCoercionKind::UnsafeFnPointer, copy(3), f_ty.clone()),
            reify(
                PointerCoercionKind::ReifyFnPointer,
                Operand::callee("item"),
                u32_ty(),
            ),
        ];
        for rv in rejected {
            assert!(lower_rvalue(&rv, &decls, pw).is_err(), "{rv:?}");
        }
        // An unparameterized `ReifyFnPointer` accepts either safety.
        assert!(
            lower_rvalue(
                &reify(
                    PointerCoercionKind::ReifyFnPointer,
                    Operand::callee("item"),
                    unsafe_fn_ty(vec![u32_ty()], u32_ty()),
                ),
                &decls,
                pw
            )
            .is_ok()
        );
    }
}

#[test]
fn fn_ptr_casts_expose_and_forbid_memory_access() {
    for pw in PWS {
        let f_ty = fn_ty(vec![], unit());
        let decls = vec![
            unit(),
            f_ty.clone(),
            raw(unit(), NOT),
            usize_ty(),
            raw(u8_ty(), NOT),
            u8_ty(),
        ];
        let prelude = vec![
            assign(
                1,
                reify(
                    PointerCoercionKind::ReifyFnPointer,
                    Operand::callee("cast_target"),
                    f_ty.clone(),
                ),
            ),
            assign(2, cast(CastKind::FnPtrToPtr, copy(1), raw(unit(), NOT))),
            assign(
                3,
                cast(CastKind::PointerExposeProvenance, copy(1), usize_ty()),
            ),
            assign(4, cast(CastKind::FnPtrToPtr, copy(1), raw(u8_ty(), NOT))),
        ];
        let state = run(&decls, &prelude, pw).unwrap();
        let sym = CalleeSymbol::new("cast_target");
        let addr = fn_ptr_addr(&sym);
        assert_eq!(
            value(&state, 2),
            MirValue::Ptr {
                ptr: PointerValue {
                    addr,
                    provenance: fn_ptr_provenance(&sym),
                },
                ty: raw(unit(), NOT),
            }
        );
        assert_eq!(value(&state, 3), usizev(u128::from(addr)));
        // Reading through a function's address is undefined behavior.
        let mut stmts = prelude.clone();
        stmts.push(assign(5, Rvalue::Use(Operand::Copy(deref(4)))));
        assert_eq!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::FnPtrMemoryAccess { addr })
        );
        // `FnPtrToPtr` targets thin raw pointers only.
        for target in [raw(slice(u8_ty()), NOT), rf(u8_ty(), NOT), usize_ty()] {
            assert!(
                lower_rvalue(
                    &cast(CastKind::FnPtrToPtr, copy(1), target.clone()),
                    &decls,
                    pw
                )
                .is_err(),
                "{target:?}"
            );
        }
        // A function pointer cannot be dereferenced.
        assert!(lower_rvalue(&Rvalue::Use(Operand::Copy(deref(1))), &decls, pw).is_err());
    }
}

#[test]
fn fn_ptr_transmute_round_trips() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let (opt_def, opt) = option_of(f_ty.clone());
        let decls = vec![
            unit(),
            f_ty.clone(),
            raw(unit(), NOT),
            f_ty.clone(),
            opt.clone(),
            opt.clone(),
            usize_ty(),
            f_ty.clone(),
        ];
        let state = run(
            &decls,
            &[
                assign(
                    1,
                    reify(
                        PointerCoercionKind::ReifyFnPointer,
                        Operand::callee("rt_target"),
                        f_ty.clone(),
                    ),
                ),
                // `fn -> *const () -> transmute -> fn`.
                assign(2, cast(CastKind::FnPtrToPtr, copy(1), raw(unit(), NOT))),
                assign(3, cast(CastKind::Transmute, copy(2), f_ty.clone())),
                // `fn -> Option<fn>` and a null `*const ()` -> `None`.
                assign(4, cast(CastKind::Transmute, copy(1), opt.clone())),
                assign(
                    5,
                    cast(
                        CastKind::Transmute,
                        Operand::Constant(Constant::Ptr(
                            PointerValue::without_provenance(0),
                            raw(unit(), NOT),
                        )),
                        opt.clone(),
                    ),
                ),
            ],
            pw,
        )
        .unwrap();
        assert_eq!(value(&state, 3), value(&state, 1));
        assert_eq!(
            value(&state, 4),
            MirValue::adt(&opt_def, 1, vec![value(&state, 1)])
        );
        assert_eq!(value(&state, 5), MirValue::adt(&opt_def, 0, vec![]));
        // A zero address is not a function pointer.
        let zero = Statement::Assign(
            local(7),
            cast(
                CastKind::Transmute,
                Operand::Constant(Constant::Ptr(
                    PointerValue::without_provenance(0),
                    raw(unit(), NOT),
                )),
                f_ty.clone(),
            ),
        );
        assert!(matches!(
            run(&decls, &[zero], pw).err(),
            Some(RvalueEvalError::CastEval(
                CastEvalError::InvalidBitPattern { bits: 0, .. }
            ))
        ));
    }
}

// ---------------------------------------------------------------------------------------------
// H. Indirect calls through function pointers
// ---------------------------------------------------------------------------------------------

fn block(stmts: Vec<Statement>, term: Terminator) -> BasicBlockData {
    BasicBlockData::with_terminator(stmts, term, false)
}

/// `fn double(x: u32) -> u32 { x + x }`.
fn double_body(pw: PtrWidth) -> LoweredBody {
    let body = Body {
        local_decls: vec![u32_ty(), u32_ty()],
        basic_blocks: vec![block(
            vec![assign(0, Rvalue::BinaryOp(BinOp::Add, copy(1), copy(1)))],
            Terminator::Return,
        )],
    };
    lower_body(&body, pw).unwrap()
}

/// `fn main(x: u32) -> u32 { let f: F = callee as F; let g: G = transmute(f); g(x) }` with
/// `F = fn(u32) -> u32` reified by `coercion` and `G = call_ty` (`F` itself when `None`).
fn indirect_main(
    callee: &str,
    coercion: PointerCoercionKind,
    reify_ty: Ty,
    call_ty: Option<Ty>,
    pw: PtrWidth,
) -> LoweredBody {
    let call_ty = call_ty.unwrap_or_else(|| reify_ty.clone());
    let mut stmts = vec![
        Statement::StorageLive(Local(2)),
        Statement::StorageLive(Local(3)),
        assign(
            2,
            reify(coercion, Operand::callee(callee), reify_ty.clone()),
        ),
    ];
    let func = if call_ty == reify_ty {
        copy(2)
    } else {
        stmts.push(assign(
            3,
            cast(CastKind::Transmute, copy(2), call_ty.clone()),
        ));
        copy(3)
    };
    let body = Body {
        local_decls: vec![u32_ty(), u32_ty(), reify_ty, call_ty],
        basic_blocks: vec![
            block(
                stmts,
                Terminator::Call {
                    func,
                    args: vec![copy(1)],
                    destination: local(0),
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
            ),
            block(vec![], Terminator::Return),
        ],
    };
    lower_body(&body, pw).unwrap()
}

#[test]
fn indirect_calls_run_linked_callees() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let table = CallTable::new().with_callee("double", 1, double_body(pw));
        let main = indirect_main(
            "double",
            PointerCoercionKind::ReifyFnPointer,
            f_ty.clone(),
            None,
            pw,
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&main, &[u32v(21)], 100, &table),
            Ok(CfgEvalOutcome::Returned(u32v(42)))
        );
        // An unsafe function pointer to a safe callee is fine, too.
        let unsafe_main = indirect_main(
            "double",
            PointerCoercionKind::ReifyFnPointer,
            unsafe_fn_ty(vec![u32_ty()], u32_ty()),
            None,
            pw,
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&unsafe_main, &[u32v(5)], 100, &table),
            Ok(CfgEvalOutcome::Returned(u32v(10)))
        );
    }
}

#[test]
fn indirect_calls_check_callee_signatures() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let g_ty = fn_ty(vec![u64_ty()], u32_ty());
        let table = CallTable::new().with_callee("double", 1, double_body(pw));
        // Reifying `double` at another signature is undefined behavior (even if the function
        // pointer is never called).
        let reify_only = |coercion: PointerCoercionKind, ty: Ty| {
            let body = Body {
                local_decls: vec![u32_ty(), ty.clone()],
                basic_blocks: vec![block(
                    vec![
                        Statement::StorageLive(Local(1)),
                        assign(1, reify(coercion, Operand::callee("double"), ty)),
                        assign(0, Rvalue::Use(cint(0, u32_ty()))),
                    ],
                    Terminator::Return,
                )],
            };
            lower_body(&body, pw).unwrap()
        };
        for bad_ty in [
            g_ty.clone(),
            fn_ty(vec![u32_ty()], u64_ty()),
            fn_ty(vec![u32_ty(), u32_ty()], u32_ty()),
        ] {
            assert!(
                matches!(
                    eval_lowered_body_cfg_with_call_table(
                        &reify_only(PointerCoercionKind::ReifyFnPointer, bad_ty.clone()),
                        &[],
                        100,
                        &table
                    ),
                    Err(CfgEvalError::Statement {
                        bb: 0,
                        index: 1,
                        error: RvalueEvalError::FnPtrSignatureMismatch { .. },
                    })
                ),
                "{bad_ty:?}"
            );
        }
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(
                &reify_only(PointerCoercionKind::ReifyFnPointer, f_ty.clone()),
                &[],
                100,
                &table
            ),
            Ok(CfgEvalOutcome::Returned(u32v(0)))
        );
        // A `u64` argument cannot be passed to `main(u32)`; use a u64-taking main instead:
        // call `double` through a transmuted `fn(u64) -> u32`.
        let body = Body {
            local_decls: vec![u32_ty(), u64_ty(), f_ty.clone(), g_ty.clone()],
            basic_blocks: vec![
                block(
                    vec![
                        Statement::StorageLive(Local(2)),
                        Statement::StorageLive(Local(3)),
                        assign(
                            2,
                            reify(
                                PointerCoercionKind::ReifyFnPointer,
                                Operand::callee("double"),
                                f_ty.clone(),
                            ),
                        ),
                        assign(3, cast(CastKind::Transmute, copy(2), g_ty.clone())),
                    ],
                    Terminator::Call {
                        func: copy(3),
                        args: vec![copy(1)],
                        destination: local(0),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                block(vec![], Terminator::Return),
            ],
        };
        let main = lower_body(&body, pw).unwrap();
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&main, &[uv(3, u64_ty())], 100, &table),
            Err(CfgEvalError::Terminator {
                bb: 0,
                error: RvalueEvalError::FnPtrSignatureMismatch {
                    callee: CalleeSymbol::new("double"),
                    reason: "the callee's parameter types differ from the function pointer's",
                },
            })
        );
        // An `unsafe fn` cannot be reified to a safe function pointer.
        let unsafe_table = CallTable::new().with_unsafe_callee("double", 1, double_body(pw));
        let main = indirect_main(
            "double",
            PointerCoercionKind::ReifyFnPointer,
            f_ty.clone(),
            None,
            pw,
        );
        assert!(matches!(
            eval_lowered_body_cfg_with_call_table(&main, &[u32v(1)], 100, &unsafe_table),
            Err(CfgEvalError::Statement {
                bb: 0,
                error: RvalueEvalError::FnPtrSignatureMismatch { .. },
                ..
            })
        ));
        // ... but to an unsafe one.
        let main = indirect_main(
            "double",
            PointerCoercionKind::ReifyFnPointer,
            unsafe_fn_ty(vec![u32_ty()], u32_ty()),
            None,
            pw,
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&main, &[u32v(4)], 100, &unsafe_table),
            Ok(CfgEvalOutcome::Returned(u32v(8)))
        );
    }
}

#[test]
fn indirect_calls_of_unlinked_targets_go_to_the_handler() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let table = CallTable::new().with_callee("double", 1, double_body(pw));
        let main = indirect_main(
            "ext",
            PointerCoercionKind::ReifyFnPointer,
            f_ty.clone(),
            None,
            pw,
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&main, &[u32v(1)], 100, &table),
            Err(CfgEvalError::UnknownCallee {
                bb: 0,
                callee: CalleeSymbol::new("ext"),
            })
        );
        let ext = CalleeSymbol::new("ext");
        let expected_func = MirValue::fn_ptr(ext.clone(), f_ty.clone());
        let outcome = eval_lowered_body_cfg_with_call_table_and_calls(
            &main,
            &[u32v(1)],
            100,
            &table,
            |call: &ExternalCall<'_>| {
                assert_eq!(call.callee, Some(&ext));
                assert_eq!(call.func, &expected_func);
                assert_eq!(call.args, &[u32v(1)]);
                Ok(CallOutcome::Return(u32v(7)))
            },
        );
        assert_eq!(outcome, Ok(CfgEvalOutcome::Returned(u32v(7))));
        // Without a table, the plain call handler sees the function pointer.
        let outcome = eval_lowered_body_cfg_with_calls(&main, &[u32v(2)], 100, |_, func, args| {
            assert!(matches!(func, MirValue::FnPtr { target, .. } if target.as_str() == "ext"));
            Ok(CallOutcome::Return(args[0].clone()))
        });
        assert_eq!(outcome, Ok(CfgEvalOutcome::Returned(u32v(2))));
    }
}

#[test]
fn indirect_calls_are_type_checked_statically() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let call = |args: Vec<Operand>, destination: Place| Body {
            local_decls: vec![u64_ty(), f_ty.clone(), u32_ty(), u64_ty()],
            basic_blocks: vec![
                block(
                    vec![],
                    Terminator::Call {
                        func: copy(1),
                        args,
                        destination,
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                block(vec![], Terminator::Return),
            ],
        };
        let invalid = |body: &Body| {
            matches!(
                lower_body(body, pw),
                Err(RvalueLowerError::InvalidTerminator {
                    bb: 0,
                    error: TerminatorLowerError::InvalidFnPtrCall { .. },
                })
            )
        };
        assert!(invalid(&call(vec![], local(2))));
        assert!(invalid(&call(vec![copy(3)], local(2))));
        assert!(invalid(&call(vec![copy(2)], local(3))));
        assert!(lower_body(&call(vec![copy(2)], local(2)), pw).is_ok());
    }
}

// ---------------------------------------------------------------------------------------------
// I. `size_of_val` / `align_of_val` and `Retag`
// ---------------------------------------------------------------------------------------------

#[test]
fn size_and_align_of_slices() {
    for pw in PWS {
        let wide = |ty: Ty, len: usize| MirValue::WidePtr {
            data: PointerValue::without_provenance(0x40),
            len,
            ty,
        };
        let size = |v: &MirValue| {
            eval_intrinsic(
                IntrinsicOp::SizeOfVal,
                std::slice::from_ref(v),
                &usize_ty(),
                pw,
            )
        };
        let align = |v: &MirValue| {
            eval_intrinsic(
                IntrinsicOp::AlignOfVal,
                std::slice::from_ref(v),
                &usize_ty(),
                pw,
            )
        };
        let words = wide(rf(slice(u32_ty()), NOT), 4);
        assert_eq!(size(&words), Ok(usizev(16)));
        assert_eq!(align(&words), Ok(usizev(4)));
        let text = wide(rf(Ty::Str, NOT), 5);
        assert_eq!(size(&text), Ok(usizev(5)));
        assert_eq!(align(&text), Ok(usizev(1)));
        // `isize::MAX` bounds the size (a raw slice may claim more).
        let max_isize = pw.max_isize() as u128;
        let big = wide(raw(slice(u16_ty()), NOT), (max_isize / 2) as usize);
        assert_eq!(size(&big), Ok(usizev(max_isize - 1)));
        let too_big = wide(raw(slice(u16_ty()), NOT), (max_isize / 2 + 1) as usize);
        assert!(matches!(
            size(&too_big),
            Err(RvalueEvalError::IntrinsicUb {
                op: IntrinsicOp::SizeOfVal,
                ..
            })
        ));
        assert_eq!(align(&too_big), Ok(usizev(2)));
        // Statically, a slice pointee needs a sized element type with a layout.
        assert!(
            check_intrinsic_call_types(
                IntrinsicOp::SizeOfVal,
                &[rf(slice(u32_ty()), NOT)],
                &usize_ty(),
                pw
            )
            .is_ok()
        );
    }
}

#[test]
fn retag_validates_wide_references() {
    for pw in PWS {
        let (decls, mut stmts) = slice_frame();
        stmts.extend([
            assign(7, Rvalue::Ref(NOT, deref(3))),
            Statement::Retag(RetagKind::Default, local(7)),
        ]);
        assert!(run(&decls, &stmts, pw).is_ok());
        let (decls, mut stmts) = slice_frame();
        stmts.extend([
            assign(7, Rvalue::Ref(NOT, deref(3))),
            Statement::StorageDead(Local(1)),
            Statement::Retag(RetagKind::Default, local(7)),
        ]);
        assert_eq!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::DeadLocal(Local(1)))
        );
    }
}

// ---------------------------------------------------------------------------------------------
// J. The `V2026_06_01` coercion spellings
// ---------------------------------------------------------------------------------------------

#[test]
fn pointer_coercion_spellings_match_trusted_places() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean"
    );
    let source = std::fs::read_to_string(path).expect("Places.lean is readable");
    let mut trusted: BTreeSet<String> = BTreeSet::new();
    for marker in ["stringEq coercionKind \"", "pointerCoercion \""] {
        let mut rest = source.as_str();
        while let Some(start) = rest.find(marker) {
            rest = &rest[start + marker.len()..];
            let end = rest.find('"').expect("closing quote");
            trusted.insert(rest[..end].to_string());
            rest = &rest[end..];
        }
    }
    let ours: BTreeSet<String> = POINTER_COERCION_SPELLINGS_V2026_06_01
        .iter()
        .map(|(tag, _)| tag.to_string())
        .collect();
    assert_eq!(ours.len(), 10);
    assert_eq!(
        trusted, ours,
        "Places.lean coercion tags drifted from POINTER_COERCION_SPELLINGS_V2026_06_01"
    );
    // The mapping is a bijection between the tags and the typed kinds.
    let kinds: BTreeSet<String> = POINTER_COERCION_SPELLINGS_V2026_06_01
        .iter()
        .map(|(_, kind)| format!("{kind:?}"))
        .collect();
    assert_eq!(kinds.len(), 10);
    for (tag, kind) in POINTER_COERCION_SPELLINGS_V2026_06_01 {
        assert_eq!(lower_pointer_coercion_kind_v2026_06_01(tag), Some(*kind));
        assert_eq!(pointer_coercion_spelling_v2026_06_01(*kind), *tag);
    }
    assert_eq!(
        lower_pointer_coercion_kind_v2026_06_01("Unsize(Safe)"),
        None
    );
    assert_eq!(lower_pointer_coercion_kind_v2026_06_01("unsize"), None);
    // `reifyCoercionSafetyCompatible`: the unparameterized tags accept either safety.
    use PointerCoercionKind as K;
    assert_eq!(K::ReifyFnPointer.required_fn_ptr_safety(), None);
    assert_eq!(K::ClosureFnPointerAnySafety.required_fn_ptr_safety(), None);
    assert_eq!(
        K::ReifyFnPointerWithSafety(Safety::Unsafe).required_fn_ptr_safety(),
        Some(Safety::Unsafe)
    );
    assert_eq!(
        K::ClosureFnPointer(Safety::Safe).required_fn_ptr_safety(),
        Some(Safety::Safe)
    );
}

// ---------------------------------------------------------------------------------------------
// K. Adversarial Round B1 regressions
// ---------------------------------------------------------------------------------------------

#[test]
fn b1_unsize_and_slice_len_enforce_zst_provenance_and_backing_array_bounds() {
    for pw in PWS {
        let dangling = PointerValue::without_provenance(0x40);
        // 1. Provenance-less ZST reference unsizing: `&[(); 3] -> &[()]` (`len = 3 > 0`,
        // `byte_len = 0`) faults with `PointerOutOfBounds`, while `&[(); 0] -> &[()]` succeeds.
        let decls_zst = vec![unit(), rf(slice(unit()), NOT), rf(slice(unit()), NOT)];
        assert_eq!(
            run(
                &decls_zst,
                &[assign(
                    1,
                    unsize(
                        Operand::Constant(Constant::Ptr(dangling, rf(arr(unit(), 3), NOT))),
                        rf(slice(unit()), NOT),
                    ),
                )],
                pw,
            )
            .err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: 0x40,
                byte_len: 0,
            })
        );
        let state_zst0 = run(
            &decls_zst,
            &[assign(
                2,
                unsize(
                    Operand::Constant(Constant::Ptr(dangling, rf(arr(unit(), 0), NOT))),
                    rf(slice(unit()), NOT),
                ),
            )],
            pw,
        )
        .unwrap();
        assert_eq!(value(&state_zst0, 2).as_wide_ptr(), Some((dangling, 0)));

        // 2. Provenance-less `Rvalue::Len(*s)` on non-empty `*const [u32]` (`len = 2 > 0`) or
        // `*const [()]` (`len = 3 > 0`) faults with `PointerOutOfBounds`, while `len == 0`
        // returns `0`.
        let decls_len = vec![
            unit(),
            raw(u32_ty(), NOT),
            raw(slice(u32_ty()), NOT),
            usize_ty(),
        ];
        let raw_ptr_const = Operand::Constant(Constant::Ptr(dangling, raw(u32_ty(), NOT)));
        assert_eq!(
            run(
                &decls_len,
                &[
                    assign(1, Rvalue::Use(raw_ptr_const.clone())),
                    assign(
                        2,
                        Rvalue::Aggregate(
                            AggregateKind::RawPtr {
                                pointee: slice(u32_ty()),
                                mutability: NOT,
                            },
                            vec![copy(1), cusize(2)],
                        ),
                    ),
                    assign(3, Rvalue::Len(deref(2))),
                ],
                pw,
            )
            .err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: 0x40,
                byte_len: 8,
            })
        );
        let state_len0 = run(
            &decls_len,
            &[
                assign(1, Rvalue::Use(raw_ptr_const)),
                assign(
                    2,
                    Rvalue::Aggregate(
                        AggregateKind::RawPtr {
                            pointee: slice(u32_ty()),
                            mutability: NOT,
                        },
                        vec![copy(1), cusize(0)],
                    ),
                ),
                assign(3, Rvalue::Len(deref(2))),
            ],
            pw,
        )
        .unwrap();
        assert_eq!(value(&state_len0, 3), usizev(0));

        // 3. Unsizing `&[u32; 2] -> *const [u32]` (reference source, raw target) still enforces
        // reference alignment and provenance!
        let decls_ref_to_raw = vec![unit(), arr(u32_ty(), 4), raw(slice(u32_ty()), NOT)];
        let misaligned_ref =
            Operand::Constant(Constant::Ptr(stack_ptr(1, 2), rf(arr(u32_ty(), 2), NOT)));
        assert_eq!(
            run(
                &decls_ref_to_raw,
                &[
                    assign(1, array_rv(u32_ty(), &[1, 2, 3, 4])),
                    assign(2, unsize(misaligned_ref, raw(slice(u32_ty()), NOT))),
                ],
                pw,
            )
            .err(),
            Some(RvalueEvalError::MisalignedPointer {
                addr: base(1) + 2,
                required_align: 4,
            })
        );
        let dangling_ref = Operand::Constant(Constant::Ptr(dangling, rf(arr(u32_ty(), 2), NOT)));
        assert_eq!(
            run(
                &decls_ref_to_raw,
                &[assign(2, unsize(dangling_ref, raw(slice(u32_ty()), NOT)))],
                pw,
            )
            .err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: 0x40,
                byte_len: 8,
            })
        );

        // 4. Cross-field unsizing inside `_1: ([u32; 2], [u32; 2])` (16 bytes total) or
        // over-length ZST unsizing `&[(); 5]` inside `_1: [(); 2]` faults with
        // `PointerOutOfBounds`.
        let pair_arr = Ty::Tuple(vec![arr(u32_ty(), 2), arr(u32_ty(), 2)]);
        let decls_pair = vec![unit(), pair_arr, rf(slice(u32_ty()), NOT)];
        let init_pair = assign(
            1,
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![
                    Operand::Constant(Constant::Int(0, u32_ty())), // dummy replaced below
                ],
            ),
        );
        let _ = init_pair;
        let mut state_pair = StatementEvalState::from_local_decls(decls_pair.clone(), pw);
        state_pair.slots[1] = LocalSlotState::Init(MirValue::Tuple(vec![
            array_val(u32_ty(), &[1, 2]),
            array_val(u32_ty(), &[3, 4]),
        ]));
        for (off, n) in [(0u64, 3usize), (4u64, 2usize)] {
            let bad_ptr =
                Operand::Constant(Constant::Ptr(stack_ptr(1, off), rf(arr(u32_ty(), n), NOT)));
            let stmt = lower_statement(
                &assign(2, unsize(bad_ptr, rf(slice(u32_ty()), NOT))),
                &decls_pair,
                pw,
            )
            .unwrap();
            assert_eq!(
                eval_lowered_statement(&stmt, &mut state_pair),
                Err(RvalueEvalError::PointerOutOfBounds {
                    addr: base(1) + off,
                    byte_len: (n as u128) * 4,
                })
            );
        }

        let decls_zst_arr = vec![unit(), arr(unit(), 2), rf(slice(unit()), NOT)];
        let over_zst = Operand::Constant(Constant::Ptr(stack_ptr(1, 0), rf(arr(unit(), 5), NOT)));
        assert_eq!(
            run(
                &decls_zst_arr,
                &[
                    assign(1, Rvalue::Repeat(Operand::Constant(Constant::Unit), 2),),
                    assign(2, unsize(over_zst, rf(slice(unit()), NOT))),
                ],
                pw,
            )
            .err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: base(1),
                byte_len: 0,
            })
        );

        // 5. `Rvalue::Len(*s)` on a slice whose backing local was deinitialized faults with
        // `UninitializedLocal`.
        let (decls_uninit, mut stmts_uninit) = slice_frame();
        stmts_uninit.extend([
            Statement::Deinit(local(1)),
            assign(4, Rvalue::Len(deref(3))),
        ]);
        assert_eq!(
            run(&decls_uninit, &stmts_uninit, pw).err(),
            Some(RvalueEvalError::UninitializedLocal(Local(1)))
        );
    }
}

#[test]
fn b1_slice_mutability_permissions_reject_mutable_reborrow_and_write_through_shared_or_const() {
    for pw in PWS {
        let (mut decls, mut stmts) = slice_frame();
        // `_7: &[u32] = &*_3`, `_8: *const [u32] = &raw const *_3`.
        stmts.extend([
            assign(7, Rvalue::Ref(NOT, deref(3))),
            assign(8, Rvalue::RawPtr(NOT, deref(3))),
        ]);
        let sub = ProjectionElem::Subslice {
            from: 0,
            to: 2,
            from_end: false,
        };
        let elem0 = ProjectionElem::ConstantIndex {
            offset: 0,
            min_length: 1,
            from_end: false,
        };
        for immut_local in [7usize, 8usize] {
            // Static rejections: `&mut (*s)`, `&mut (*s)[0..2]`, `&raw mut (*s)[0..2]`,
            // `&mut (*s)[0]`, `&raw mut (*s)[0]`, `(*s)[0] = 1`, `Deinit((*s)[0])`.
            assert!(lower_rvalue(&Rvalue::Ref(MUT, deref(immut_local)), &decls, pw).is_err());
            assert!(
                lower_rvalue(
                    &Rvalue::Ref(
                        MUT,
                        proj(immut_local, vec![ProjectionElem::Deref, sub.clone()])
                    ),
                    &decls,
                    pw,
                )
                .is_err()
            );
            assert!(
                lower_rvalue(
                    &Rvalue::RawPtr(
                        MUT,
                        proj(immut_local, vec![ProjectionElem::Deref, sub.clone()]),
                    ),
                    &decls,
                    pw,
                )
                .is_err()
            );
            assert!(
                lower_rvalue(
                    &Rvalue::Ref(
                        MUT,
                        proj(immut_local, vec![ProjectionElem::Deref, elem0.clone()]),
                    ),
                    &decls,
                    pw,
                )
                .is_err()
            );
            assert!(
                lower_rvalue(
                    &Rvalue::RawPtr(
                        MUT,
                        proj(immut_local, vec![ProjectionElem::Deref, elem0.clone()]),
                    ),
                    &decls,
                    pw,
                )
                .is_err()
            );
            assert!(
                lower_statement(
                    &Statement::Assign(
                        proj(immut_local, vec![ProjectionElem::Deref, elem0.clone()]),
                        Rvalue::Use(cint(1, u32_ty())),
                    ),
                    &decls,
                    pw,
                )
                .is_err()
            );
            assert!(
                lower_statement(
                    &Statement::Deinit(proj(
                        immut_local,
                        vec![ProjectionElem::Deref, elem0.clone()]
                    )),
                    &decls,
                    pw,
                )
                .is_err()
            );

            // Runtime rejections on hand-built `LoweredRvalue` / `write_place`:
            let mut state = run(&decls, &stmts, pw).unwrap();
            let hand_wide_mut = LoweredRvalue::Ref {
                mutability: MUT,
                place: proj(immut_local, vec![ProjectionElem::Deref, sub.clone()]),
                ty: rf(slice(u32_ty()), MUT),
            };
            assert!(matches!(
                eval_lowered_rvalue_in_state(&hand_wide_mut, &mut state),
                Err(RvalueEvalError::TypeMismatch(_))
            ));
            let hand_elem_mut = LoweredRvalue::Ref {
                mutability: MUT,
                place: proj(immut_local, vec![ProjectionElem::Deref, elem0.clone()]),
                ty: rf(u32_ty(), MUT),
            };
            assert!(matches!(
                eval_lowered_rvalue_in_state(&hand_elem_mut, &mut state),
                Err(RvalueEvalError::TypeMismatch(_))
            ));
            assert!(matches!(
                state.write_place(
                    &proj(immut_local, vec![ProjectionElem::Deref, elem0.clone()]),
                    &u32_ty(),
                    u32v(1),
                ),
                Err(RvalueEvalError::TypeMismatch(_))
            ));
        }

        // Double-deref `(**_9)[0] = 88` where `_9: &(&mut [u32])` writes through a `&mut`
        // reached through a shared reference, which `rustc` rejects (E0594: the place is behind
        // a `&` reference); `(**_10)[0] = 88` where `_10: &mut (&[u32])` is rejected because the
        // last `Deref` dereferences `&[u32]`. (See `a1_place_mutability_follows_borrowck` for
        // the accepted `*mut` / `&mut &mut` forms.)
        decls.push(rf(rf(slice(u32_ty()), MUT), NOT)); // _9
        decls.push(rf(rf(slice(u32_ty()), NOT), MUT)); // _10
        stmts.push(assign(9, Rvalue::Ref(NOT, local(3))));
        stmts.push(assign(10, Rvalue::Ref(MUT, local(7))));
        let write_via_9 = Statement::Assign(
            proj(
                9,
                vec![ProjectionElem::Deref, ProjectionElem::Deref, elem0.clone()],
            ),
            Rvalue::Use(cint(88, u32_ty())),
        );
        assert!(lower_statement(&write_via_9, &decls, pw).is_err());
        // The evaluator keeps its pre-existing leniency for hand-built writes whose last
        // `Deref` is through a `&mut` (`subplace_deref_copy_tests` writes `(**pp).0` with
        // `pp: &&mut (u32, u32)`): only lowering applies the full borrowck rule.
        let mut state = run(&decls, &stmts, pw).unwrap();
        state
            .write_place(
                &proj(
                    9,
                    vec![ProjectionElem::Deref, ProjectionElem::Deref, elem0.clone()],
                ),
                &u32_ty(),
                u32v(88),
            )
            .unwrap();
        assert_eq!(value(&state, 1), array_val(u32_ty(), &[88, 11, 12, 13]));

        let write_via_10 = Statement::Assign(
            proj(
                10,
                vec![ProjectionElem::Deref, ProjectionElem::Deref, elem0],
            ),
            Rvalue::Use(cint(99, u32_ty())),
        );
        assert!(lower_statement(&write_via_10, &decls, pw).is_err());
    }
}

#[test]
fn b1_empty_and_single_element_scalar_backed_slice_indexing_and_reborrows() {
    for pw in PWS {
        let dangling = PointerValue::without_provenance(0x40);
        // 1. Indexing or element-borrowing an empty provenance-less slice `&[u32] = &[]`
        // reports `IndexOutOfBounds { len: 0 }` (never `UnsupportedPlaceProjection`).
        let decls_empty = vec![
            unit(),
            rf(slice(u32_ty()), NOT),
            usize_ty(),
            u32_ty(),
            rf(u32_ty(), NOT),
        ];
        let empty_init = assign(
            1,
            unsize(
                Operand::Constant(Constant::Ptr(dangling, rf(arr(u32_ty(), 0), NOT))),
                rf(slice(u32_ty()), NOT),
            ),
        );
        let idx_place = proj(
            1,
            vec![ProjectionElem::Deref, ProjectionElem::Index(Local(2))],
        );
        assert_eq!(
            run(
                &decls_empty,
                &[
                    empty_init.clone(),
                    assign(2, Rvalue::Use(cusize(0))),
                    assign(3, Rvalue::Use(Operand::Copy(idx_place.clone()))),
                ],
                pw,
            )
            .err(),
            Some(RvalueEvalError::IndexOutOfBounds { index: 0, len: 0 })
        );
        assert_eq!(
            run(
                &decls_empty,
                &[
                    empty_init,
                    assign(2, Rvalue::Use(cusize(0))),
                    assign(4, Rvalue::Ref(NOT, idx_place)),
                ],
                pw,
            )
            .err(),
            Some(RvalueEvalError::IndexOutOfBounds { index: 0, len: 0 })
        );

        // 2. A 1-element slice constructed over a non-array local (`slice::from_mut(&mut _1)`
        // where `_1: (u32, u32)`) supports `Len`, `(*s)[0]` reads/writes, field projections,
        // and element/field reborrows, while faulting with `IndexOutOfBounds` on index 1.
        let pair_ty = Ty::Tuple(vec![u32_ty(), u32_ty()]);
        let decls_one = vec![
            unit(),
            pair_ty.clone(),
            raw(pair_ty.clone(), MUT),
            raw(slice(pair_ty.clone()), MUT),
            rf(slice(pair_ty.clone()), MUT),
            usize_ty(),
            u32_ty(),
            rf(u32_ty(), NOT),
        ];
        let elem0 = ProjectionElem::ConstantIndex {
            offset: 0,
            min_length: 1,
            from_end: false,
        };
        let stmts_one = vec![
            assign(
                1,
                Rvalue::Aggregate(
                    AggregateKind::Tuple,
                    vec![cint(10, u32_ty()), cint(20, u32_ty())],
                ),
            ),
            assign(2, Rvalue::RawPtr(MUT, local(1))),
            assign(
                3,
                Rvalue::Aggregate(
                    AggregateKind::RawPtr {
                        pointee: slice(pair_ty.clone()),
                        mutability: MUT,
                    },
                    vec![copy(2), cusize(1)],
                ),
            ),
            assign(4, Rvalue::Ref(MUT, deref(3))),
            assign(5, Rvalue::Len(deref(4))),
            // `(*_4)[0].1 = 77`
            Statement::Assign(
                proj(
                    4,
                    vec![
                        ProjectionElem::Deref,
                        elem0.clone(),
                        ProjectionElem::Field(1, u32_ty()),
                    ],
                ),
                Rvalue::Use(cint(77, u32_ty())),
            ),
            // `_7 = &((*_4)[0].1)`
            assign(
                7,
                Rvalue::Ref(
                    NOT,
                    proj(
                        4,
                        vec![
                            ProjectionElem::Deref,
                            elem0,
                            ProjectionElem::Field(1, u32_ty()),
                        ],
                    ),
                ),
            ),
            assign(6, Rvalue::Use(Operand::Copy(deref(7)))),
        ];
        let state_one = run(&decls_one, &stmts_one, pw).unwrap();
        assert_eq!(value(&state_one, 5), usizev(1));
        assert_eq!(value(&state_one, 6), u32v(77));
        assert_eq!(
            value(&state_one, 1),
            MirValue::Tuple(vec![u32v(10), u32v(77)])
        );

        let mut oob_stmts = stmts_one;
        oob_stmts.extend([
            assign(5, Rvalue::Use(cusize(1))),
            assign(
                7,
                Rvalue::Ref(
                    NOT,
                    proj(
                        4,
                        vec![
                            ProjectionElem::Deref,
                            ProjectionElem::Index(Local(5)),
                            ProjectionElem::Field(0, u32_ty()),
                        ],
                    ),
                ),
            ),
        ]);
        assert_eq!(
            run(&decls_one, &oob_stmts, pw).err(),
            Some(RvalueEvalError::IndexOutOfBounds { index: 1, len: 1 })
        );
    }
}

#[test]
fn b1_capturing_closure_upvar_projections_offset_of_and_retag() {
    for pw in PWS {
        let ref_u32 = rf(u32_ty(), NOT);
        let closure_ty = Ty::closure("capturing_closure", vec![ref_u32.clone(), usize_ty()]);
        let canon_closure_ty = Ty::closure("canon_closure", vec![u32_ty(), u32_ty()]);
        let decls = vec![
            unit(),
            u32_ty(),
            ref_u32.clone(),
            closure_ty.clone(),
            u32_ty(),
            usize_ty(),
        ];
        let stmts = vec![
            assign(1, Rvalue::Use(cint(42, u32_ty()))),
            assign(2, Rvalue::Ref(NOT, local(1))),
            assign(
                3,
                Rvalue::Aggregate(AggregateKind::Closure, vec![copy(2), cusize(9)]),
            ),
            Statement::Retag(RetagKind::Default, local(3)),
            // Read `*(_3.0)` and `OffsetOf` of upvar 1 on a canonical closure layout.
            assign(
                4,
                Rvalue::Use(Operand::Copy(proj(
                    3,
                    vec![
                        ProjectionElem::Field(0, ref_u32.clone()),
                        ProjectionElem::Deref,
                    ],
                ))),
            ),
            assign(
                5,
                Rvalue::NullaryOp(NullOp::OffsetOf(vec![(0, 1)]), canon_closure_ty),
            ),
        ];
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 4), u32v(42));
        assert_eq!(value(&state, 5), usizev(4));

        // When the local referenced by upvar 0 dies, `Retag` on the closure faults with
        // `DeadLocal(Local(1))`.
        let mut dead_stmts = stmts;
        dead_stmts.extend([
            Statement::StorageDead(Local(1)),
            Statement::Retag(RetagKind::Default, local(3)),
        ]);
        assert_eq!(
            run(&decls, &dead_stmts, pw).err(),
            Some(RvalueEvalError::DeadLocal(Local(1)))
        );
    }
}

#[test]
fn b1_exposed_multiple_fn_ptr_provenances_recover_matching_callee_on_int_to_ptr_and_transmute() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let add_one_body = {
            let body = Body {
                local_decls: vec![u32_ty(), u32_ty()],
                basic_blocks: vec![block(
                    vec![assign(
                        0,
                        Rvalue::BinaryOp(BinOp::Add, copy(1), cint(1, u32_ty())),
                    )],
                    Terminator::Return,
                )],
            };
            lower_body(&body, pw).unwrap()
        };
        let table = CallTable::new()
            .with_callee("double", 1, double_body(pw))
            .with_callee("add_one", 1, add_one_body);

        // Expose both `double` and `add_one` (in that order), then recover each from its
        // exposed integer address in reverse order (`add_one` first, then `double`) via
        // `PointerWithExposedProvenance` -> `Transmute` -> `fn(u32) -> u32`, and call both!
        let body = Body {
            local_decls: vec![
                u32_ty(),         // _0: return
                u32_ty(),         // _1: arg
                f_ty.clone(),     // _2: double fn ptr
                f_ty.clone(),     // _3: add_one fn ptr
                usize_ty(),       // _4: exposed addr of double
                usize_ty(),       // _5: exposed addr of add_one
                raw(unit(), NOT), // _6: recovered *const () for add_one
                raw(unit(), NOT), // _7: recovered *const () for double
                f_ty.clone(),     // _8: transmuted add_one fn ptr
                f_ty.clone(),     // _9: transmuted double fn ptr
                u32_ty(),         // _10: intermediate call result
            ],
            basic_blocks: vec![
                block(
                    vec![
                        Statement::StorageLive(Local(2)),
                        Statement::StorageLive(Local(3)),
                        Statement::StorageLive(Local(4)),
                        Statement::StorageLive(Local(5)),
                        Statement::StorageLive(Local(6)),
                        Statement::StorageLive(Local(7)),
                        Statement::StorageLive(Local(8)),
                        Statement::StorageLive(Local(9)),
                        Statement::StorageLive(Local(10)),
                        assign(
                            2,
                            reify(
                                PointerCoercionKind::ReifyFnPointer,
                                Operand::callee("double"),
                                f_ty.clone(),
                            ),
                        ),
                        assign(
                            3,
                            reify(
                                PointerCoercionKind::ReifyFnPointer,
                                Operand::callee("add_one"),
                                f_ty.clone(),
                            ),
                        ),
                        assign(
                            4,
                            cast(CastKind::PointerExposeProvenance, copy(2), usize_ty()),
                        ),
                        assign(
                            5,
                            cast(CastKind::PointerExposeProvenance, copy(3), usize_ty()),
                        ),
                        assign(
                            6,
                            cast(
                                CastKind::PointerWithExposedProvenance,
                                copy(5),
                                raw(unit(), NOT),
                            ),
                        ),
                        assign(
                            7,
                            cast(
                                CastKind::PointerWithExposedProvenance,
                                copy(4),
                                raw(unit(), NOT),
                            ),
                        ),
                        assign(8, cast(CastKind::Transmute, copy(6), f_ty.clone())),
                        assign(9, cast(CastKind::Transmute, copy(7), f_ty.clone())),
                    ],
                    Terminator::Call {
                        func: copy(8),
                        args: vec![copy(1)],
                        destination: local(10),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                block(
                    vec![],
                    Terminator::Call {
                        func: copy(9),
                        args: vec![copy(10)],
                        destination: local(0),
                        target: Some(2),
                        unwind: UnwindAction::Continue,
                    },
                ),
                block(vec![], Terminator::Return),
            ],
        };
        let lowered = lower_body(&body, pw).unwrap();
        // `double(add_one(10)) == 22`.
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&lowered, &[u32v(10)], 100, &table),
            Ok(CfgEvalOutcome::Returned(u32v(22)))
        );
    }
}

// ---------------------------------------------------------------------------------------------
// A1: borrowck place mutability, ambiguous exposed function provenance, in-bounds raw
// `Subslice` offsets, and zero-byte references at function addresses
// ---------------------------------------------------------------------------------------------

#[test]
fn a1_place_mutability_follows_borrowck() {
    for pw in PWS {
        let elem = |i: u64| ProjectionElem::ConstantIndex {
            offset: i,
            min_length: i + 1,
            from_end: false,
        };
        let (mut decls, mut stmts) = slice_frame();
        // `_9: &&mut [u32] = &_3`, `_10: *mut [u32] = &raw mut *_3`, `_11: &*mut [u32] = &_10`,
        // `_12: &mut &mut [u32] = &mut _3`, `_13: *const &mut [u32] = &raw const _3`.
        decls.extend([
            rf(rf(slice(u32_ty()), MUT), NOT),
            raw(slice(u32_ty()), MUT),
            rf(raw(slice(u32_ty()), MUT), NOT),
            rf(rf(slice(u32_ty()), MUT), MUT),
            raw(rf(slice(u32_ty()), MUT), NOT),
        ]);
        stmts.extend([
            assign(9, Rvalue::Ref(NOT, local(3))),
            assign(10, Rvalue::RawPtr(MUT, deref(3))),
            assign(11, Rvalue::Ref(NOT, local(10))),
            assign(12, Rvalue::Ref(MUT, local(3))),
            assign(13, Rvalue::RawPtr(NOT, local(3))),
        ]);
        let dd = |i: usize, e: ProjectionElem| {
            proj(i, vec![ProjectionElem::Deref, ProjectionElem::Deref, e])
        };
        // A `&mut` behind `&` or `*const` is immutable (E0594 / E0596).
        for outer in [9usize, 13] {
            assert!(
                lower_statement(
                    &Statement::Assign(dd(outer, elem(0)), Rvalue::Use(cint(1, u32_ty()))),
                    &decls,
                    pw
                )
                .is_err(),
                "write through _{outer}"
            );
            assert!(
                lower_rvalue(&Rvalue::Ref(MUT, dd(outer, elem(0))), &decls, pw).is_err(),
                "&mut through _{outer}"
            );
            assert!(
                lower_rvalue(
                    &Rvalue::RawPtr(
                        MUT,
                        proj(outer, vec![ProjectionElem::Deref, ProjectionElem::Deref])
                    ),
                    &decls,
                    pw
                )
                .is_err(),
                "&raw mut through _{outer}"
            );
            // ... but readable.
            assert!(
                lower_rvalue(&Rvalue::Use(Operand::Copy(dd(outer, elem(0)))), &decls, pw).is_ok()
            );
        }
        // A `*mut` is mutable wherever it is read from, and a `&mut` behind a `&mut` is too
        // (writes, and a mutable reborrow `_6 = &mut **_12`).
        stmts.extend([
            Statement::Assign(dd(11, elem(1)), Rvalue::Use(cint(77, u32_ty()))),
            Statement::Assign(dd(12, elem(2)), Rvalue::Use(cint(66, u32_ty()))),
            assign(
                6,
                Rvalue::Ref(
                    MUT,
                    proj(12, vec![ProjectionElem::Deref, ProjectionElem::Deref]),
                ),
            ),
        ]);
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 1), array_val(u32_ty(), &[10, 77, 66, 13]));
        assert_eq!(value(&state, 6).as_wide_ptr(), Some((stack_ptr(1, 0), 4)));
        // At runtime (hand-built lowered MIR), only the last `Deref` matters: a `&mut` behind a
        // `*const` stays mutably borrowable (as for writes), a final `*const` `Deref` does not.
        let mut state = run(&decls, &stmts, pw).unwrap();
        let hand = LoweredRvalue::Ref {
            mutability: MUT,
            place: proj(13, vec![ProjectionElem::Deref, ProjectionElem::Deref]),
            ty: rf(slice(u32_ty()), MUT),
        };
        assert!(eval_lowered_rvalue_in_state(&hand, &mut state).is_ok());
        let hand_const = LoweredRvalue::RawPtr {
            mutability: MUT,
            place: proj(8, vec![ProjectionElem::Deref, elem(0)]),
            ty: raw(u32_ty(), MUT),
        };
        stmts.push(assign(8, Rvalue::RawPtr(NOT, deref(3))));
        let mut state = run(&decls, &stmts, pw).unwrap();
        assert!(matches!(
            eval_lowered_rvalue_in_state(&hand_const, &mut state),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
    }
}

/// Two distinct symbols whose function pointers share a synthetic address.
fn colliding_fn_symbols() -> (CalleeSymbol, CalleeSymbol) {
    let mut seen = std::collections::BTreeMap::new();
    for i in 0.. {
        let sym = CalleeSymbol::new(format!("collide_{i}"));
        if let Some(prev) = seen.insert(fn_ptr_addr(&sym), sym.clone()) {
            return (prev, sym);
        }
    }
    unreachable!()
}

#[test]
fn a1_ambiguous_exposed_fn_provenances_are_not_guessed() {
    let (f, g) = colliding_fn_symbols();
    assert_ne!(f, g);
    assert_eq!(fn_ptr_addr(&f), fn_ptr_addr(&g));
    for pw in PWS {
        let f_ty = fn_ty(vec![], unit());
        let decls = vec![
            unit(),
            f_ty.clone(),
            f_ty.clone(),
            usize_ty(),
            usize_ty(),
            raw(unit(), NOT),
            f_ty.clone(),
        ];
        let reify_f = assign(
            1,
            reify(
                PointerCoercionKind::ReifyFnPointer,
                Operand::callee(f.as_str()),
                f_ty.clone(),
            ),
        );
        let reify_g = assign(
            2,
            reify(
                PointerCoercionKind::ReifyFnPointer,
                Operand::callee(g.as_str()),
                f_ty.clone(),
            ),
        );
        let expose = |dst: usize, src: usize| {
            assign(
                dst,
                cast(CastKind::PointerExposeProvenance, copy(src), usize_ty()),
            )
        };
        let recover = [
            assign(
                5,
                cast(
                    CastKind::PointerWithExposedProvenance,
                    copy(3),
                    raw(unit(), NOT),
                ),
            ),
            assign(6, cast(CastKind::Transmute, copy(5), f_ty.clone())),
        ];
        // Only `f` exposed: its provenance is recovered.
        let mut stmts = vec![reify_f.clone(), reify_g.clone(), expose(3, 1)];
        stmts.extend(recover.clone());
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 6), value(&state, 1));
        // Both exposed at the same address: neither is guessed.
        let mut stmts = vec![reify_f, reify_g, expose(3, 1), expose(4, 2)];
        stmts.extend(recover);
        let err = run(&decls, &stmts, pw).err();
        assert!(
            matches!(err, Some(RvalueEvalError::UnsupportedMemoryAccess(_))),
            "{err:?}"
        );
    }
}

#[test]
fn a1_raw_subslice_reborrows_offset_in_bounds() {
    for pw in PWS {
        // `_4: *const [u32]` claims 10 elements of the 4-element `_1`.
        let decls = vec![
            unit(),
            arr(u32_ty(), 4),
            raw(arr(u32_ty(), 4), NOT),
            raw(u32_ty(), NOT),
            raw(slice(u32_ty()), NOT),
            raw(slice(u32_ty()), NOT),
        ];
        let prelude = vec![
            assign(1, array_rv(u32_ty(), &[1, 2, 3, 4])),
            assign(2, Rvalue::RawPtr(NOT, local(1))),
            assign(
                3,
                cast(
                    CastKind::PointerCoercion(PointerCoercionKind::ArrayToPointer),
                    copy(2),
                    raw(u32_ty(), NOT),
                ),
            ),
            assign(
                4,
                Rvalue::Aggregate(
                    AggregateKind::RawPtr {
                        pointee: slice(u32_ty()),
                        mutability: NOT,
                    },
                    vec![copy(3), cusize(10)],
                ),
            ),
        ];
        let sub = |from: u64, to: u64| {
            Rvalue::RawPtr(
                NOT,
                proj(
                    4,
                    vec![
                        ProjectionElem::Deref,
                        ProjectionElem::Subslice {
                            from,
                            to,
                            from_end: false,
                        },
                    ],
                ),
            )
        };
        // An in-bounds offset is fine, even though the claimed length is not.
        let mut stmts = prelude.clone();
        stmts.push(assign(5, sub(2, 9)));
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 5).as_wide_ptr(), Some((stack_ptr(1, 8), 7)));
        // One past the end is in bounds; beyond it is not.
        let mut stmts = prelude.clone();
        stmts.push(assign(5, sub(4, 4)));
        assert!(run(&decls, &stmts, pw).is_ok());
        let mut stmts = prelude.clone();
        stmts.push(assign(5, sub(6, 8)));
        assert_eq!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: base(1),
                byte_len: 24
            })
        );
        // The backing local must be live.
        let mut stmts = prelude.clone();
        stmts.extend([Statement::StorageDead(Local(1)), assign(5, sub(1, 2))]);
        assert_eq!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::DeadLocal(Local(1)))
        );
    }
}

#[test]
fn a1_zero_byte_slice_references_at_function_addresses() {
    for pw in PWS {
        let f_ty = fn_ty(vec![], unit());
        let decls = vec![
            unit(),
            f_ty.clone(),
            raw(arr(u8_ty(), 0), NOT),
            rf(arr(u8_ty(), 0), NOT),
            rf(slice(u8_ty()), NOT),
            usize_ty(),
            raw(arr(u8_ty(), 4), NOT),
            rf(arr(u8_ty(), 4), NOT),
        ];
        let sym = CalleeSymbol::new("zero_byte_target");
        let stmts = vec![
            assign(
                1,
                reify(
                    PointerCoercionKind::ReifyFnPointer,
                    Operand::callee(sym.as_str()),
                    f_ty.clone(),
                ),
            ),
            assign(
                2,
                cast(CastKind::FnPtrToPtr, copy(1), raw(arr(u8_ty(), 0), NOT)),
            ),
            assign(
                3,
                cast(CastKind::Transmute, copy(2), rf(arr(u8_ty(), 0), NOT)),
            ),
            assign(4, unsize(copy(3), rf(slice(u8_ty()), NOT))),
            assign(5, Rvalue::Len(deref(4))),
        ];
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(
            value(&state, 4).as_wide_ptr(),
            Some((
                PointerValue {
                    addr: fn_ptr_addr(&sym),
                    provenance: fn_ptr_provenance(&sym),
                },
                0
            ))
        );
        assert_eq!(value(&state, 5), usizev(0));
        // A non-empty reference to a function's bytes is invalid.
        let stmts = vec![
            stmts[0].clone(),
            assign(
                6,
                cast(CastKind::FnPtrToPtr, copy(1), raw(arr(u8_ty(), 4), NOT)),
            ),
            assign(
                7,
                cast(CastKind::Transmute, copy(6), rf(arr(u8_ty(), 4), NOT)),
            ),
            assign(4, unsize(copy(7), rf(slice(u8_ty()), NOT))),
        ];
        assert_eq!(
            run(&decls, &stmts, pw).err(),
            Some(RvalueEvalError::FnPtrMemoryAccess {
                addr: fn_ptr_addr(&sym)
            })
        );
    }
}

#[test]
fn a1_retag_checks_wide_reference_bounds() {
    for pw in PWS {
        let pair = Ty::Tuple(vec![raw(u32_ty(), NOT), usize_ty()]);
        let decls = vec![
            unit(),
            arr(u32_ty(), 4),
            raw(arr(u32_ty(), 4), NOT),
            raw(u32_ty(), NOT),
            pair.clone(),
            rf(slice(u32_ty()), NOT),
        ];
        let with_len = |len: u128| {
            vec![
                assign(1, array_rv(u32_ty(), &[1, 2, 3, 4])),
                assign(2, Rvalue::RawPtr(NOT, local(1))),
                assign(
                    3,
                    cast(
                        CastKind::PointerCoercion(PointerCoercionKind::ArrayToPointer),
                        copy(2),
                        raw(u32_ty(), NOT),
                    ),
                ),
                assign(
                    4,
                    Rvalue::Aggregate(AggregateKind::Tuple, vec![copy(3), cusize(len)]),
                ),
                assign(
                    5,
                    cast(CastKind::Transmute, copy(4), rf(slice(u32_ty()), NOT)),
                ),
                Statement::Retag(RetagKind::Default, local(5)),
            ]
        };
        assert!(run(&decls, &with_len(4), pw).is_ok());
        assert_eq!(
            run(&decls, &with_len(5), pw).err(),
            Some(RvalueEvalError::PointerOutOfBounds {
                addr: base(1),
                byte_len: 20
            })
        );
    }
}

// ---------------------------------------------------------------------------------------------
// B2: `Retag` provenance/ZST/empty-offset validation, raw `Subslice` `isize::MAX` offset &
// zero-offset bounds, and address-only raw slice element reborrows
// ---------------------------------------------------------------------------------------------

trait StatementEvalStateExt {
    fn set_local(&mut self, local: Local, state: LocalSlotState);
}
impl StatementEvalStateExt for StatementEvalState {
    fn set_local(&mut self, local: Local, state: LocalSlotState) {
        self.slots[local.0] = state;
    }
}

fn eval_statement(stmt: &Statement, state: &mut StatementEvalState) -> Result<(), RvalueEvalError> {
    let lowered = lower_statement(stmt, &state.local_decls, state.ptr_width)
        .unwrap_or_else(|err| panic!("lowering {stmt:?}: {err:?}"));
    eval_lowered_statement(&lowered, state)
}

#[test]
fn b2_retag_rejects_fn_provenance_provenanceless_and_oob_empty_or_zst_slices() {
    for pw in PWS {
        // 1. Function-pointer provenance: non-zero-byte thin `&u32` and wide `&[u8]` (len 4)
        // fault with `FnPtrMemoryAccess` on `Retag`, while zero-byte `&()` and `&[u8]` (len 0)
        // or `&[()]` (len 4) succeed.
        let f_ty = fn_ty(vec![], unit());
        let sym = CalleeSymbol::new("b2_retag_fn_target");
        let fn_ptr_val = MirValue::fn_ptr(sym.clone(), f_ty.clone());
        let fn_data_ptr = PointerValue {
            addr: fn_ptr_addr(&sym),
            provenance: fn_ptr_provenance(&sym),
        };
        let decls = vec![
            unit(),
            f_ty,
            rf(u32_ty(), NOT),
            rf(unit(), NOT),
            rf(slice(u8_ty()), NOT),
            rf(slice(unit()), NOT),
        ];
        let mut state = StatementEvalState::from_local_decls(decls.clone(), pw);
        state.set_local(Local(1), LocalSlotState::Init(fn_ptr_val));
        state.set_local(
            Local(2),
            LocalSlotState::Init(MirValue::ptr(fn_data_ptr, rf(u32_ty(), NOT))),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(2)), &mut state),
            Err(RvalueEvalError::FnPtrMemoryAccess {
                addr: fn_ptr_addr(&sym),
            })
        );
        state.set_local(
            Local(3),
            LocalSlotState::Init(MirValue::ptr(fn_data_ptr, rf(unit(), NOT))),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(3)), &mut state),
            Ok(())
        );
        state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: fn_data_ptr,
                len: 4,
                ty: rf(slice(u8_ty()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(4)), &mut state),
            Err(RvalueEvalError::FnPtrMemoryAccess {
                addr: fn_ptr_addr(&sym),
            })
        );
        state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: fn_data_ptr,
                len: 0,
                ty: rf(slice(u8_ty()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(4)), &mut state),
            Ok(())
        );
        state.set_local(
            Local(5),
            LocalSlotState::Init(MirValue::WidePtr {
                data: fn_data_ptr,
                len: 4,
                ty: rf(slice(unit()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(5)), &mut state),
            Ok(())
        );

        // 2. Provenance-less wide references: `len == 0` at a non-null aligned address succeeds,
        // while `len > 0` faults with `PointerOutOfBounds` (both sized and ZST elements).
        let dangling = PointerValue::without_provenance(0x40);
        state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: dangling,
                len: 0,
                ty: rf(slice(u8_ty()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(4)), &mut state),
            Ok(())
        );
        state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: dangling,
                len: 3,
                ty: rf(slice(u8_ty()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(4)), &mut state),
            Err(RvalueEvalError::PointerOutOfBounds {
                addr: 0x40,
                byte_len: 3,
            })
        );
        state.set_local(
            Local(5),
            LocalSlotState::Init(MirValue::WidePtr {
                data: dangling,
                len: 2,
                ty: rf(slice(unit()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(&Statement::Retag(RetagKind::Default, local(5)), &mut state),
            Err(RvalueEvalError::PointerOutOfBounds {
                addr: 0x40,
                byte_len: 0,
            })
        );

        // 3. Out-of-bounds empty (`len == 0`) and ZST (`&[()]`) wide references into a stack local.
        let local_decls = vec![
            unit(),
            arr(u32_ty(), 4),
            arr(unit(), 2),
            rf(slice(u32_ty()), NOT),
            rf(slice(unit()), NOT),
        ];
        let mut local_state = StatementEvalState::from_local_decls(local_decls, pw);
        local_state.set_local(
            Local(1),
            LocalSlotState::Init(array_val(u32_ty(), &[1, 2, 3, 4])),
        );
        local_state.set_local(
            Local(2),
            LocalSlotState::Init(MirValue::Array {
                elements: vec![MirValue::Unit, MirValue::Unit],
                elem_ty: unit(),
            }),
        );
        // Empty slice one past the end of `_1` (offset 16) is in bounds; offset 20 is out of bounds.
        local_state.set_local(
            Local(3),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(1, 16),
                len: 0,
                ty: rf(slice(u32_ty()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(
                &Statement::Retag(RetagKind::Default, local(3)),
                &mut local_state
            ),
            Ok(())
        );
        local_state.set_local(
            Local(3),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(1, 20),
                len: 0,
                ty: rf(slice(u32_ty()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(
                &Statement::Retag(RetagKind::Default, local(3)),
                &mut local_state
            ),
            Err(RvalueEvalError::PointerOutOfBounds {
                addr: base(1) + 20,
                byte_len: 0,
            })
        );
        // ZST slice `&[()]` into `_2: [(); 2]`: `len = 2` is backed, `len = 3` is out of bounds.
        local_state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(2, 0),
                len: 2,
                ty: rf(slice(unit()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(
                &Statement::Retag(RetagKind::Default, local(4)),
                &mut local_state
            ),
            Ok(())
        );
        local_state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(2, 0),
                len: 3,
                ty: rf(slice(unit()), NOT),
            }),
        );
        assert_eq!(
            eval_statement(
                &Statement::Retag(RetagKind::Default, local(4)),
                &mut local_state
            ),
            Err(RvalueEvalError::PointerOutOfBounds {
                addr: base(2),
                byte_len: 0,
            })
        );
    }
}

#[test]
fn b2_raw_subslice_enforces_isize_max_offset_and_zero_offset_local_bounds() {
    for pw in PWS {
        let max_isize = pw.max_isize();
        let half_plus_one = (max_isize / 2) + 1;
        let raw_u16_slice = raw(slice(u16_ty()), NOT);
        let decls = vec![
            unit(),
            arr(u32_ty(), 4),
            raw_u16_slice.clone(),
            raw_u16_slice.clone(),
            raw(slice(u32_ty()), NOT),
            raw(slice(u32_ty()), NOT),
        ];
        let mut state = StatementEvalState::from_local_decls(decls, pw);
        state.set_local(
            Local(1),
            LocalSlotState::Init(array_val(u32_ty(), &[1, 2, 3, 4])),
        );
        // 1. `start * size_of::<u16>() == max_isize + 1 > isize::MAX` (even though `addr + offset <= usize::MAX`).
        state.set_local(
            Local(2),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(1, 0),
                len: (half_plus_one + 1) as usize,
                ty: raw_u16_slice,
            }),
        );
        let overflow_sub = assign(
            3,
            Rvalue::RawPtr(
                NOT,
                proj(
                    2,
                    vec![
                        ProjectionElem::Deref,
                        ProjectionElem::Subslice {
                            from: half_plus_one as u64,
                            to: (half_plus_one + 1) as u64,
                            from_end: false,
                        },
                    ],
                ),
            ),
        );
        assert_eq!(
            eval_statement(&overflow_sub, &mut state),
            Err(RvalueEvalError::PointerOffsetOverflow {
                base_addr: base(1),
                offset: half_plus_one,
                pointee_size: 2,
            })
        );

        // 2. Zero-offset raw `Subslice` (`[0..2]`) still checks that a local allocation is live
        // and that `base_addr` is within `[local_base, local_base + alloc_size]`.
        state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(1, 20),
                len: 4,
                ty: raw(slice(u32_ty()), NOT),
            }),
        );
        let zero_sub = assign(
            5,
            Rvalue::RawPtr(
                NOT,
                proj(
                    4,
                    vec![
                        ProjectionElem::Deref,
                        ProjectionElem::Subslice {
                            from: 0,
                            to: 2,
                            from_end: false,
                        },
                    ],
                ),
            ),
        );
        assert_eq!(
            eval_statement(&zero_sub, &mut state),
            Err(RvalueEvalError::PointerOutOfBounds {
                addr: base(1) + 20,
                byte_len: 0,
            })
        );
        state.set_local(
            Local(4),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(1, 0),
                len: 4,
                ty: raw(slice(u32_ty()), NOT),
            }),
        );
        state.set_local(Local(1), LocalSlotState::Dead);
        assert_eq!(
            eval_statement(&zero_sub, &mut state),
            Err(RvalueEvalError::DeadLocal(Local(1)))
        );
    }
}

#[test]
fn b2_raw_slice_element_reborrow_checks_accessed_offset_and_fault_order() {
    for pw in PWS {
        let raw_u32_slice = raw(slice(u32_ty()), NOT);
        let raw_u32 = raw(u32_ty(), NOT);
        let ref_u32 = rf(u32_ty(), NOT);
        let decls = vec![
            unit(),
            arr(u32_ty(), 4),
            raw_u32_slice.clone(),
            usize_ty(),
            raw_u32.clone(),
            ref_u32.clone(),
            u32_ty(),
        ];
        let mut state = StatementEvalState::from_local_decls(decls, pw);
        state.set_local(
            Local(1),
            LocalSlotState::Init(array_val(u32_ty(), &[10, 20, 30, 40])),
        );
        // 1. Overhanging raw slice `_2: *const [u32]` claiming `len = 10` over 4-element `_1`:
        // `&raw const (*_2)[2]` offsets by 8 bytes (<= 16) and succeeds, while `&(*_2)[2]`
        // requires the whole slice to be backed (`PointerOutOfBounds { byte_len: 40 }`), and
        // `&raw const (*_2)[6]` (offset 24 > 16) is rejected.
        state.set_local(
            Local(2),
            LocalSlotState::Init(MirValue::WidePtr {
                data: stack_ptr(1, 0),
                len: 10,
                ty: raw_u32_slice.clone(),
            }),
        );
        state.set_local(Local(3), LocalSlotState::Init(usizev(2)));
        let idx_place = proj(
            2,
            vec![ProjectionElem::Deref, ProjectionElem::Index(Local(3))],
        );
        assert_eq!(
            eval_statement(
                &assign(4, Rvalue::RawPtr(NOT, idx_place.clone())),
                &mut state
            ),
            Ok(())
        );
        assert_eq!(
            state.get_local(Local(4)),
            Some(&LocalSlotState::Init(MirValue::ptr(
                stack_ptr(1, 8),
                raw_u32.clone()
            )))
        );
        assert_eq!(
            eval_statement(&assign(6, Rvalue::Use(Operand::Copy(deref(4)))), &mut state),
            Ok(())
        );
        assert_eq!(value(&state, 6), u32v(30));
        assert_eq!(
            eval_statement(&assign(5, Rvalue::Ref(NOT, idx_place.clone())), &mut state),
            Err(RvalueEvalError::PointerOutOfBounds {
                addr: base(1),
                byte_len: 40,
            })
        );
        state.set_local(Local(3), LocalSlotState::Init(usizev(6)));
        assert_eq!(
            eval_statement(
                &assign(4, Rvalue::RawPtr(NOT, idx_place.clone())),
                &mut state
            ),
            Err(RvalueEvalError::UnsupportedPlaceProjection(
                idx_place.clone()
            ))
        );

        // 2. Fault ordering for `&raw const (*_2)[_3]` matches thin array pointer reborrows:
        // null or dead base faults before an uninitialized index `_3`; with `_3 = 0`, offset-0
        // address-only raw reborrow succeeds; with `_3 = 1`, it faults with `NullPointerAccess`
        // or `DeadLocal(Local(1))`; with `_3 = 10` (`>= len`), it faults with `IndexOutOfBounds`.
        for (base_ptr, expected_fault) in [
            (
                PointerValue::without_provenance(0),
                RvalueEvalError::NullPointerAccess,
            ),
            (stack_ptr(1, 0), RvalueEvalError::DeadLocal(Local(1))),
        ] {
            state.set_local(Local(1), LocalSlotState::Dead);
            state.set_local(
                Local(2),
                LocalSlotState::Init(MirValue::WidePtr {
                    data: base_ptr,
                    len: 4,
                    ty: raw_u32_slice.clone(),
                }),
            );
            state.set_local(Local(3), LocalSlotState::Uninit);
            assert_eq!(
                eval_statement(
                    &assign(4, Rvalue::RawPtr(NOT, idx_place.clone())),
                    &mut state
                ),
                Err(expected_fault.clone())
            );
            state.set_local(Local(3), LocalSlotState::Init(usizev(0)));
            assert_eq!(
                eval_statement(
                    &assign(4, Rvalue::RawPtr(NOT, idx_place.clone())),
                    &mut state
                ),
                Ok(())
            );
            assert_eq!(
                state.get_local(Local(4)),
                Some(&LocalSlotState::Init(MirValue::ptr(
                    base_ptr,
                    raw_u32.clone()
                )))
            );
            state.set_local(Local(3), LocalSlotState::Init(usizev(1)));
            assert_eq!(
                eval_statement(
                    &assign(4, Rvalue::RawPtr(NOT, idx_place.clone())),
                    &mut state
                ),
                Err(expected_fault)
            );
            state.set_local(Local(3), LocalSlotState::Init(usizev(4)));
            assert_eq!(
                eval_statement(
                    &assign(4, Rvalue::RawPtr(NOT, idx_place.clone())),
                    &mut state
                ),
                Err(RvalueEvalError::IndexOutOfBounds { index: 4, len: 4 })
            );
        }
    }
}

// ---------------------------------------------------------------------------------------------
// A2: slices of aggregates and slices, element reborrows, higher-order indirect calls across
// frames, and niche round trips of `Option<&str>` / `Option<&mut [T]>`
// ---------------------------------------------------------------------------------------------

#[test]
fn a2_slice_element_fields_and_element_reborrows() {
    for pw in PWS {
        let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
        let elem = |i: u64| ProjectionElem::ConstantIndex {
            offset: i,
            min_length: i + 1,
            from_end: false,
        };
        // `_1: [(u32, u32); 2]`, `_2 = &mut _1`, `_3 = _2 as &mut [(u32, u32)]`,
        // `(*_3)[1].1 = 9`, `_4 = &mut (*_3)[0].0`, `*_4 = 7`, `_5 = (*_3)[1]`.
        let decls = vec![
            unit(),
            arr(pair.clone(), 2),
            rf(arr(pair.clone(), 2), MUT),
            rf(slice(pair.clone()), MUT),
            rf(u32_ty(), MUT),
            pair.clone(),
            pair.clone(),
            pair.clone(),
        ];
        let tuple_rv = |a: u128, b: u128| {
            Rvalue::Aggregate(
                AggregateKind::Tuple,
                vec![cint(a, u32_ty()), cint(b, u32_ty())],
            )
        };
        let stmts = vec![
            assign(6, tuple_rv(1, 2)),
            assign(7, tuple_rv(3, 4)),
            assign(
                1,
                Rvalue::Aggregate(
                    AggregateKind::Array(pair.clone()),
                    vec![Operand::Move(local(6)), Operand::Move(local(7))],
                ),
            ),
            assign(2, Rvalue::Ref(MUT, local(1))),
            assign(3, unsize(copy(2), rf(slice(pair.clone()), MUT))),
            Statement::Assign(
                proj(
                    3,
                    vec![
                        ProjectionElem::Deref,
                        elem(1),
                        ProjectionElem::Field(1, u32_ty()),
                    ],
                ),
                Rvalue::Use(cint(9, u32_ty())),
            ),
            assign(
                4,
                Rvalue::Ref(
                    MUT,
                    proj(
                        3,
                        vec![
                            ProjectionElem::Deref,
                            elem(0),
                            ProjectionElem::Field(0, u32_ty()),
                        ],
                    ),
                ),
            ),
            Statement::Assign(deref(4), Rvalue::Use(cint(7, u32_ty()))),
            assign(
                5,
                Rvalue::Use(Operand::Copy(proj(3, vec![ProjectionElem::Deref, elem(1)]))),
            ),
        ];
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 5), MirValue::Tuple(vec![u32v(3), u32v(9)]));
        assert_eq!(
            value(&state, 1),
            MirValue::Array {
                elements: vec![
                    MirValue::Tuple(vec![u32v(7), u32v(2)]),
                    MirValue::Tuple(vec![u32v(3), u32v(9)]),
                ],
                elem_ty: pair.clone(),
            }
        );
    }
}

#[test]
fn a2_slices_of_slices() {
    for pw in PWS {
        let elem = |i: u64| ProjectionElem::ConstantIndex {
            offset: i,
            min_length: i + 1,
            from_end: false,
        };
        let s_ty = rf(slice(u16_ty()), NOT);
        // `_1: [u16; 3]`, `_2 = &_1 as &[u16]`, `_3 = &_1[1..] as &[u16]` (via a reborrow),
        // `_4: [&[u16]; 2] = [_2, _3]`, `_5 = &_4 as &[&[u16]]`, `_6 = (*(*_5)[1])[1]`.
        let decls = vec![
            unit(),
            arr(u16_ty(), 3),
            s_ty.clone(),
            s_ty.clone(),
            arr(s_ty.clone(), 2),
            rf(slice(s_ty.clone()), NOT),
            u16_ty(),
            rf(arr(u16_ty(), 3), NOT),
            rf(arr(s_ty.clone(), 2), NOT),
            usize_ty(),
        ];
        let stmts = vec![
            assign(1, array_rv(u16_ty(), &[5, 6, 7])),
            assign(7, Rvalue::Ref(NOT, local(1))),
            assign(2, unsize(copy(7), s_ty.clone())),
            assign(
                3,
                Rvalue::Ref(
                    NOT,
                    proj(
                        2,
                        vec![
                            ProjectionElem::Deref,
                            ProjectionElem::Subslice {
                                from: 1,
                                to: 0,
                                from_end: true,
                            },
                        ],
                    ),
                ),
            ),
            assign(
                4,
                Rvalue::Aggregate(AggregateKind::Array(s_ty.clone()), vec![copy(2), copy(3)]),
            ),
            assign(8, Rvalue::Ref(NOT, local(4))),
            assign(5, unsize(copy(8), rf(slice(s_ty.clone()), NOT))),
            assign(
                6,
                Rvalue::Use(Operand::Copy(proj(
                    5,
                    vec![
                        ProjectionElem::Deref,
                        elem(1),
                        ProjectionElem::Deref,
                        elem(1),
                    ],
                ))),
            ),
            assign(
                9,
                Rvalue::Len(proj(
                    5,
                    vec![ProjectionElem::Deref, elem(1), ProjectionElem::Deref],
                )),
            ),
        ];
        let state = run(&decls, &stmts, pw).unwrap();
        assert_eq!(value(&state, 3).as_wide_ptr(), Some((stack_ptr(1, 2), 2)));
        assert_eq!(value(&state, 6), uv(7, u16_ty()));
        assert_eq!(value(&state, 9), usizev(2));
    }
}

#[test]
fn a2_higher_order_indirect_calls_across_frames() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        // `fn apply(f: fn(u32) -> u32, x: u32) -> u32 { f(x) }`.
        let apply = Body {
            local_decls: vec![u32_ty(), f_ty.clone(), u32_ty()],
            basic_blocks: vec![
                block(
                    vec![],
                    Terminator::Call {
                        func: copy(1),
                        args: vec![copy(2)],
                        destination: local(0),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                block(vec![], Terminator::Return),
            ],
        };
        let apply = lower_body(&apply, pw).unwrap();
        // `fn main(x: u32) -> u32 { apply(callee as fn(u32) -> u32, x) }`.
        let main = |callee: &str| {
            let body = Body {
                local_decls: vec![u32_ty(), u32_ty(), f_ty.clone()],
                basic_blocks: vec![
                    block(
                        vec![
                            Statement::StorageLive(Local(2)),
                            assign(
                                2,
                                reify(
                                    PointerCoercionKind::ReifyFnPointer,
                                    Operand::callee(callee),
                                    f_ty.clone(),
                                ),
                            ),
                        ],
                        Terminator::Call {
                            func: Operand::callee("apply"),
                            args: vec![copy(2), copy(1)],
                            destination: local(0),
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                    ),
                    block(vec![], Terminator::Return),
                ],
            };
            lower_body(&body, pw).unwrap()
        };
        let table = CallTable::new().with_callee("apply", 2, apply).with_callee(
            "double",
            1,
            double_body(pw),
        );
        // The function pointer crosses into `apply`'s frame and calls `double` from there.
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&main("double"), &[u32v(21)], 100, &table),
            Ok(CfgEvalOutcome::Returned(u32v(42)))
        );
        // An unlinked target called from inside `apply` reaches the handler with the call
        // stack of the linked call in progress.
        let ext = CalleeSymbol::new("ext_from_apply");
        let outcome = eval_lowered_body_cfg_with_call_table_and_calls(
            &main(ext.as_str()),
            &[u32v(5)],
            100,
            &table,
            |call: &ExternalCall<'_>| {
                assert_eq!(call.callee, Some(&ext));
                assert_eq!(
                    call.call_stack,
                    &[CallSite {
                        bb: 0,
                        callee: CalleeSymbol::new("apply"),
                    }]
                );
                Ok(CallOutcome::Return(u32v(11)))
            },
        );
        assert_eq!(outcome, Ok(CfgEvalOutcome::Returned(u32v(11))));
        // Without a handler, it is an unknown callee inside `apply`.
        assert!(matches!(
            eval_lowered_body_cfg_with_call_table(&main(ext.as_str()), &[u32v(5)], 100, &table),
            Err(CfgEvalError::InCallee { ref error, .. })
                if matches!(**error, CfgEvalError::UnknownCallee { ref callee, .. } if *callee == ext)
        ));
    }
}

#[test]
fn a2_option_str_and_mut_slice_niche_round_trips() {
    for pw in PWS {
        let zero_ty = if pw == PtrWidth::Bits32 {
            u64_ty()
        } else {
            Ty::Uint(UintTy::U128)
        };
        for payload in [rf(Ty::Str, NOT), rf(slice(u16_ty()), MUT)] {
            let (opt_def, opt) = option_of(payload.clone());
            let elem = payload.wide_ptr_elem_ty().unwrap().clone();
            let data_ty = raw(elem.clone(), NOT);
            let pair = Ty::Tuple(vec![data_ty.clone(), usize_ty()]);
            // `_1: [elem; 4]`, `_2 = (&raw const _1 as *const elem, 3)`, `_3: payload =
            // transmute(_2)`, `_4: Option<payload> = transmute(_2)`, `_5 = transmute(_4)` back
            // to the pair, `_6: Option<payload>` from zero bytes, `_7 = transmute(zero, 9)`.
            let decls = vec![
                unit(),
                arr(elem.clone(), 4),
                pair.clone(),
                payload.clone(),
                opt.clone(),
                pair.clone(),
                opt.clone(),
                opt.clone(),
                raw(arr(elem.clone(), 4), NOT),
                data_ty.clone(),
                pair.clone(),
            ];
            let stmts = vec![
                assign(1, Rvalue::Repeat(cint(1, elem.clone()), 4)),
                assign(8, Rvalue::RawPtr(NOT, local(1))),
                assign(
                    9,
                    cast(
                        CastKind::PointerCoercion(PointerCoercionKind::ArrayToPointer),
                        copy(8),
                        data_ty.clone(),
                    ),
                ),
                assign(
                    2,
                    Rvalue::Aggregate(AggregateKind::Tuple, vec![copy(9), cusize(3)]),
                ),
                assign(3, cast(CastKind::Transmute, copy(2), payload.clone())),
                assign(4, cast(CastKind::Transmute, copy(2), opt.clone())),
                assign(5, cast(CastKind::Transmute, copy(4), pair.clone())),
                assign(
                    6,
                    cast(
                        CastKind::Transmute,
                        Operand::Constant(Constant::Int(0, zero_ty.clone())),
                        opt.clone(),
                    ),
                ),
                // A null data pointer is `None` whatever the metadata bytes hold.
                assign(
                    10,
                    Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![
                            Operand::Constant(Constant::Ptr(
                                PointerValue::without_provenance(0),
                                data_ty.clone(),
                            )),
                            cusize(9),
                        ],
                    ),
                ),
                assign(7, cast(CastKind::Transmute, copy(10), opt.clone())),
            ];
            let state = run(&decls, &stmts, pw).unwrap();
            let wide = MirValue::WidePtr {
                data: stack_ptr(1, 0),
                len: 3,
                ty: payload.clone(),
            };
            assert_eq!(value(&state, 3), wide);
            assert_eq!(
                value(&state, 4),
                MirValue::adt(&opt_def, 1, vec![wide.clone()])
            );
            assert_eq!(value(&state, 5), value(&state, 2));
            assert_eq!(value(&state, 6), MirValue::adt(&opt_def, 0, vec![]));
            assert_eq!(value(&state, 7), MirValue::adt(&opt_def, 0, vec![]));
            // `None`'s metadata bytes are uninitialized: reading them as a pair is unsupported
            // (never a fabricated length).
            let mut stmts = stmts.clone();
            stmts.push(assign(5, cast(CastKind::Transmute, copy(6), pair.clone())));
            assert!(matches!(
                run(&decls, &stmts, pw).err(),
                Some(RvalueEvalError::UnsupportedMemoryAccess(_))
            ));
        }
    }
}

#[test]
fn a2_deinit_through_slices_matches_direct_array_elements() {
    for pw in PWS {
        let elem1 = ProjectionElem::ConstantIndex {
            offset: 1,
            min_length: 2,
            from_end: false,
        };
        let (decls, stmts) = slice_frame();
        // Arrays carry no per-element initialization state, so deinitializing one element is
        // unsupported (never undefined behavior) whether the element is reached directly, through
        // a thin array pointer, or through a slice.
        for place in [
            proj(1, vec![elem1.clone()]),
            proj(2, vec![ProjectionElem::Deref, elem1.clone()]),
            proj(3, vec![ProjectionElem::Deref, elem1.clone()]),
        ] {
            let mut all = stmts.clone();
            all.push(Statement::Deinit(place.clone()));
            assert_eq!(
                run(&decls, &all, pw).err(),
                Some(RvalueEvalError::UnsupportedPlaceProjection(place))
            );
        }
        // Deinitializing the unsized place `*_3` itself is rejected statically.
        assert!(matches!(
            lower_statement(&Statement::Deinit(deref(3)), &decls, pw),
            Err(RvalueLowerError::UnsizedType(_))
        ));
    }
}

#[test]
fn a2_calls_through_function_item_values_are_direct_calls() {
    for pw in PWS {
        // `fn main(x: u32) -> u32 { let f = callee; f(x) }` with `f: Ty::FnDef(callee)`.
        let main = |target: CallTarget| {
            let body = Body {
                local_decls: vec![u32_ty(), u32_ty(), Ty::FnDef(target.clone())],
                basic_blocks: vec![
                    block(
                        vec![
                            Statement::StorageLive(Local(2)),
                            assign(
                                2,
                                Rvalue::Use(Operand::Constant(Constant::FnDef(target.clone()))),
                            ),
                        ],
                        Terminator::Call {
                            func: Operand::Move(local(2)),
                            args: vec![copy(1)],
                            destination: local(0),
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                    ),
                    block(vec![], Terminator::Return),
                ],
            };
            lower_body(&body, pw).unwrap()
        };
        let table = CallTable::new().with_callee("double", 1, double_body(pw));
        let linked = main(CallTarget::callee("double"));
        assert_eq!(
            linked.basic_blocks[0]
                .terminator
                .as_ref()
                .and_then(LoweredTerminator::call_target),
            Some(&CallTarget::callee("double"))
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&linked, &[u32v(4)], 100, &table),
            Ok(CfgEvalOutcome::Returned(u32v(8)))
        );
        // An inline intrinsic named by a function item value runs inline.
        let ctpop = main(CallTarget::intrinsic(IntrinsicOp::Ctpop));
        assert_eq!(
            eval_lowered_body_cfg(&ctpop, &[u32v(0b1011)], 100),
            Ok(CfgEvalOutcome::Returned(u32v(3)))
        );
        // ... after the intrinsic's signature check at lowering.
        let bad = Body {
            local_decls: vec![
                u64_ty(),
                u32_ty(),
                Ty::FnDef(CallTarget::intrinsic(IntrinsicOp::Ctpop)),
            ],
            basic_blocks: vec![
                block(
                    vec![],
                    Terminator::Call {
                        func: copy(2),
                        args: vec![copy(1)],
                        destination: local(0),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                block(vec![], Terminator::Return),
            ],
        };
        assert!(matches!(
            lower_body(&bad, pw),
            Err(RvalueLowerError::InvalidTerminator {
                error: TerminatorLowerError::InvalidIntrinsicCall { .. },
                ..
            })
        ));
        // An unlinked symbol reaches the handler by name, or is an unknown callee.
        let unlinked = main(CallTarget::callee("ext_item"));
        let outcome = eval_lowered_body_cfg_with_call_table_and_calls(
            &unlinked,
            &[u32v(1)],
            100,
            &table,
            |call: &ExternalCall<'_>| {
                assert_eq!(call.callee, Some(&CalleeSymbol::new("ext_item")));
                assert_eq!(call.func, &MirValue::Unit);
                Ok(CallOutcome::Return(u32v(5)))
            },
        );
        assert_eq!(outcome, Ok(CfgEvalOutcome::Returned(u32v(5))));
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&unlinked, &[u32v(1)], 100, &table),
            Err(CfgEvalError::UnknownCallee {
                bb: 0,
                callee: CalleeSymbol::new("ext_item"),
            })
        );
    }
}

// ---------------------------------------------------------------------------------------------
// A3: indirect calls with unwinding, projected return places, and reified closures
// ---------------------------------------------------------------------------------------------

/// `fn boom(x: u32) -> u32 { panic!() }` (an unwinding panic).
fn boom_body(pw: PtrWidth) -> LoweredBody {
    let body = Body {
        local_decls: vec![u32_ty(), u32_ty()],
        basic_blocks: vec![block(
            vec![],
            Terminator::Call {
                func: Operand::intrinsic(IntrinsicOp::PanicUnwind),
                args: vec![],
                destination: local(0),
                target: None,
                unwind: UnwindAction::Continue,
            },
        )],
    };
    lower_body(&body, pw).unwrap()
}

#[test]
fn a3_indirect_calls_unwind_into_caller_cleanup() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        // `main`: `_2 = boom as fn(u32) -> u32; _0 = _2(_1) -> [return: bb1, unwind: bb2]`,
        // `bb1: return`, `bb2 (cleanup): _3 = 7; resume`.
        let main = |unwind: UnwindAction| {
            let body = Body {
                local_decls: vec![u32_ty(), u32_ty(), f_ty.clone(), u32_ty()],
                basic_blocks: vec![
                    block(
                        vec![
                            Statement::StorageLive(Local(2)),
                            assign(
                                2,
                                reify(
                                    PointerCoercionKind::ReifyFnPointer,
                                    Operand::callee("boom"),
                                    f_ty.clone(),
                                ),
                            ),
                        ],
                        Terminator::Call {
                            func: copy(2),
                            args: vec![copy(1)],
                            destination: local(0),
                            target: Some(1),
                            unwind,
                        },
                    ),
                    block(vec![], Terminator::Return),
                    BasicBlockData::with_terminator(
                        vec![
                            Statement::StorageLive(Local(3)),
                            assign(3, Rvalue::Use(cint(7, u32_ty()))),
                        ],
                        Terminator::UnwindResume,
                        true,
                    ),
                ],
            };
            lower_body(&body, pw).unwrap()
        };
        let table = CallTable::new().with_callee("boom", 1, boom_body(pw));
        // The panic unwinds out of `boom`, runs the caller's cleanup block, and resumes.
        assert!(matches!(
            eval_lowered_body_cfg_with_call_table(
                &main(UnwindAction::Cleanup(2)),
                &[u32v(1)],
                100,
                &table
            ),
            Ok(CfgEvalOutcome::Panicked { bb: 0, .. })
        ));
        // `Terminate` aborts and `Unreachable` is undefined behavior, as for direct calls.
        assert!(matches!(
            eval_lowered_body_cfg_with_call_table(
                &main(UnwindAction::Terminate),
                &[u32v(1)],
                100,
                &table
            ),
            Ok(CfgEvalOutcome::Terminated { bb: 0, .. })
        ));
        assert!(matches!(
            eval_lowered_body_cfg_with_call_table(
                &main(UnwindAction::Unreachable),
                &[u32v(1)],
                100,
                &table
            ),
            Err(CfgEvalError::UnwindIntoUnreachable { bb: 0, .. })
        ));
    }
}

#[test]
fn a3_indirect_calls_write_projected_return_places() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
        // `fn main(x: u32) -> (u32, u32) { _0.0 = 1; _0.1 = f(x); }` with `f = double`.
        let body = Body {
            local_decls: vec![pair.clone(), u32_ty(), f_ty.clone()],
            basic_blocks: vec![
                block(
                    vec![
                        Statement::StorageLive(Local(2)),
                        Statement::Assign(
                            proj(0, vec![ProjectionElem::Field(0, u32_ty())]),
                            Rvalue::Use(cint(1, u32_ty())),
                        ),
                        assign(
                            2,
                            reify(
                                PointerCoercionKind::ReifyFnPointer,
                                Operand::callee("double"),
                                f_ty.clone(),
                            ),
                        ),
                    ],
                    Terminator::Call {
                        func: copy(2),
                        args: vec![copy(1)],
                        destination: proj(0, vec![ProjectionElem::Field(1, u32_ty())]),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                ),
                block(vec![], Terminator::Return),
            ],
        };
        let lowered = lower_body(&body, pw).unwrap();
        let table = CallTable::new().with_callee("double", 1, double_body(pw));
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&lowered, &[u32v(5)], 100, &table),
            Ok(CfgEvalOutcome::Returned(MirValue::Tuple(vec![
                u32v(1),
                u32v(10)
            ])))
        );
        // A projected destination of the wrong type is rejected statically.
        let mut bad = body.clone();
        if let Some(Terminator::Call { destination, .. }) = &mut bad.basic_blocks[0].terminator {
            *destination = proj(
                0,
                vec![ProjectionElem::Field(0, u32_ty()), ProjectionElem::Deref],
            );
        }
        assert!(lower_body(&bad, pw).is_err());
    }
}

#[test]
fn a3_reified_closures_call_their_linked_bodies() {
    for pw in PWS {
        let f_ty = fn_ty(vec![u32_ty()], u32_ty());
        let closure_ty = Ty::closure("double", vec![]);
        // `let c = || ..; let f: fn(u32) -> u32 = c; f(x)` with the closure's body linked as
        // `double` (the reified closure is called with the function pointer's arguments).
        let main = |coercion: PointerCoercionKind, ptr_ty: Ty| {
            let body = Body {
                local_decls: vec![u32_ty(), u32_ty(), closure_ty.clone(), ptr_ty.clone()],
                basic_blocks: vec![
                    block(
                        vec![
                            Statement::StorageLive(Local(2)),
                            Statement::StorageLive(Local(3)),
                            assign(2, Rvalue::Aggregate(AggregateKind::Closure, vec![])),
                            assign(3, reify(coercion, Operand::Move(local(2)), ptr_ty.clone())),
                        ],
                        Terminator::Call {
                            func: copy(3),
                            args: vec![copy(1)],
                            destination: local(0),
                            target: Some(1),
                            unwind: UnwindAction::Continue,
                        },
                    ),
                    block(vec![], Terminator::Return),
                ],
            };
            lower_body(&body, pw).unwrap()
        };
        let table = CallTable::new().with_callee("double", 1, double_body(pw));
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(
                &main(
                    PointerCoercionKind::ClosureFnPointer(Safety::Safe),
                    f_ty.clone()
                ),
                &[u32v(8)],
                100,
                &table
            ),
            Ok(CfgEvalOutcome::Returned(u32v(16)))
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(
                &main(
                    PointerCoercionKind::ClosureFnPointerAnySafety,
                    unsafe_fn_ty(vec![u32_ty()], u32_ty())
                ),
                &[u32v(8)],
                100,
                &table
            ),
            Ok(CfgEvalOutcome::Returned(u32v(16)))
        );
        // Reifying the closure at a signature its body does not have is undefined behavior.
        let wrong_ty = fn_ty(vec![u32_ty()], u64_ty());
        let body = Body {
            local_decls: vec![u32_ty(), closure_ty.clone(), wrong_ty.clone()],
            basic_blocks: vec![block(
                vec![
                    Statement::StorageLive(Local(1)),
                    Statement::StorageLive(Local(2)),
                    assign(1, Rvalue::Aggregate(AggregateKind::Closure, vec![])),
                    assign(
                        2,
                        reify(
                            PointerCoercionKind::ClosureFnPointerAnySafety,
                            copy(1),
                            wrong_ty.clone(),
                        ),
                    ),
                    assign(0, Rvalue::Use(cint(0, u32_ty()))),
                ],
                Terminator::Return,
            )],
        };
        assert!(matches!(
            eval_lowered_body_cfg_with_call_table(
                &lower_body(&body, pw).unwrap(),
                &[],
                100,
                &table
            ),
            Err(CfgEvalError::Statement {
                bb: 0,
                index: 3,
                error: RvalueEvalError::FnPtrSignatureMismatch { .. },
            })
        ));
    }
}

#[test]
fn a3_unsize_requires_an_initialized_backing_local() {
    for pw in PWS {
        // `_1: [u8; 3]` is live but uninitialized: `Trusted`'s `evalUnsizeCoercion` reads the
        // backing array out of the borrowed local, so unsizing a pointer to it is undefined
        // behavior for references and raw pointers alike (as `Len` is, see
        // `eval_slice_len_in`), whereas only metadata-free raw pointer operations remain fine.
        let a3 = arr(u8_ty(), 3);
        let decls = vec![
            unit(),
            a3.clone(),
            raw(a3.clone(), MUT),
            raw(slice(u8_ty()), MUT),
            rf(a3.clone(), MUT),
            rf(slice(u8_ty()), MUT),
        ];
        let raw_unsize = vec![
            assign(2, Rvalue::RawPtr(MUT, local(1))),
            assign(3, unsize(copy(2), raw(slice(u8_ty()), MUT))),
        ];
        assert_eq!(
            run(&decls, &raw_unsize, pw).err(),
            Some(RvalueEvalError::UninitializedLocal(Local(1)))
        );
        let ref_unsize = vec![
            assign(4, Rvalue::Ref(MUT, local(1))),
            assign(5, unsize(copy(4), rf(slice(u8_ty()), MUT))),
        ];
        assert_eq!(
            run(&decls, &ref_unsize, pw).err(),
            Some(RvalueEvalError::UninitializedLocal(Local(1)))
        );
        // A raw slice built from parts (`ptr::slice_from_raw_parts_mut`) is not an `Unsize`.
        let parts_decls = vec![
            unit(),
            a3.clone(),
            raw(a3.clone(), MUT),
            raw(u8_ty(), MUT),
            raw(slice(u8_ty()), MUT),
        ];
        let parts = vec![
            assign(2, Rvalue::RawPtr(MUT, local(1))),
            assign(
                3,
                cast(
                    CastKind::PointerCoercion(PointerCoercionKind::ArrayToPointer),
                    copy(2),
                    raw(u8_ty(), MUT),
                ),
            ),
            assign(
                4,
                Rvalue::Aggregate(
                    AggregateKind::RawPtr {
                        pointee: slice(u8_ty()),
                        mutability: MUT,
                    },
                    vec![copy(3), cusize(3)],
                ),
            ),
        ];
        let state = run(&parts_decls, &parts, pw).unwrap();
        assert_eq!(value(&state, 4).as_wide_ptr(), Some((stack_ptr(1, 0), 3)));
        // Once initialized, both unsizings succeed.
        let init = assign(1, array_rv(u8_ty(), &[1, 2, 3]));
        for stmts in [raw_unsize, ref_unsize] {
            let mut all = vec![init.clone()];
            all.extend(stmts);
            assert!(run(&decls, &all, pw).is_ok());
        }
    }
}
