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
