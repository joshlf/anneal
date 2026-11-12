//! Episode 1 (`ep1-rust-lower-inline-intrinsics-and-call-table`) tests: inline compiler
//! intrinsics ([`IntrinsicOp`]), the `V2026_06_01` `DefPath` adapter, and multi-callee
//! [`CallTable`] dispatch, checked against `Trusted.Rustc.V2026_06_01.MirSemantics`
//! (`Terminators.lean`: `evalNonSelectIntrinsicCall`, `isUnreachableCallTarget`,
//! `isAbortingPanicDefPath`, `isUnwindingPanicDefPath`, `pushCalleeFrame`,
//! `unwindFromCallStack`; `Scalars.lean`: `evalCtlz` ... `evalArithOffset`) and against
//! native fixed-width Rust integer operations as an independent reference model, on both
//! `PtrWidth::Bits32` and `PtrWidth::Bits64`.

use std::sync::Arc;

use anneal_mir::*;

const PWS: [PtrWidth; 2] = [PtrWidth::Bits32, PtrWidth::Bits64];
const PW: PtrWidth = PtrWidth::Bits64;

// ---------------------------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------------------------

fn int_tys() -> Vec<Ty> {
    vec![
        Ty::Int(IntTy::I8),
        Ty::Int(IntTy::I16),
        Ty::Int(IntTy::I32),
        Ty::Int(IntTy::I64),
        Ty::Int(IntTy::I128),
        Ty::Int(IntTy::Isize),
        Ty::Uint(UintTy::U8),
        Ty::Uint(UintTy::U16),
        Ty::Uint(UintTy::U32),
        Ty::Uint(UintTy::U64),
        Ty::Uint(UintTy::U128),
        Ty::Uint(UintTy::Usize),
    ]
}

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
fn isize_ty() -> Ty {
    Ty::Int(IntTy::Isize)
}
fn i8_ty() -> Ty {
    Ty::Int(IntTy::I8)
}
fn unit() -> Ty {
    Ty::unit()
}
fn raw(pointee: Ty, m: Mutability) -> Ty {
    Ty::RawPtr(Box::new(pointee), m)
}
fn reference(pointee: Ty, m: Mutability) -> Ty {
    Ty::Ref(Box::new(pointee), m)
}

fn width(ty: &Ty, pw: PtrWidth) -> u32 {
    ty.scalar_bit_width(pw).unwrap()
}

/// Integer value of type `ty` holding the low bits of `bits`.
fn iv(ty: &Ty, bits: u128, pw: PtrWidth) -> MirValue {
    MirValue::Int {
        bits: bits & width_mask(width(ty, pw)),
        ty: ty.clone(),
    }
}
fn u32v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U32, PW)
}
fn u64v(v: u128) -> MirValue {
    MirValue::unsigned(v, UintTy::U64, PW)
}
fn usizev(v: u128, pw: PtrWidth) -> MirValue {
    MirValue::unsigned(v, UintTy::Usize, pw)
}
fn isizev(v: i128, pw: PtrWidth) -> MirValue {
    MirValue::signed(v, IntTy::Isize, pw)
}

/// Representative bit patterns of a `w`-bit integer: small values, the signed and unsigned
/// extremes and their neighbors, powers of two, and dense mixed patterns.
fn samples(w: u32) -> Vec<u128> {
    let mask = width_mask(w);
    let half = 1u128 << (w - 1);
    let mut v = vec![
        0,
        1,
        2,
        3,
        5,
        7,
        half - 1,
        half,
        half + 1,
        half >> 1,
        mask,
        mask - 1,
        mask - 2,
        (1u128 << (w / 2)) & mask,
        0x5A5A_5A5A_5A5A_5A5A_5A5A_5A5A_5A5A_5A5A & mask,
        0xA5A5_A5A5_A5A5_A5A5_A5A5_A5A5_A5A5_A5A5 & mask,
        0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210 & mask,
    ];
    v.sort_unstable();
    v.dedup();
    v
}

fn sign_extend(bits: u128, w: u32) -> i128 {
    sign_extend_bits(bits, w)
}

/// Reference semantics of the two-operand integer intrinsics on native fixed-width Rust
/// integers of the given signedness and width (`None` = undefined behavior).
fn native2(op: IntrinsicOp, signed: bool, w: u32, a: u128, b: u128) -> Option<u128> {
    macro_rules! go {
        ($t:ty, $u:ty) => {{
            let x = a as $u as $t;
            let y = b as $u as $t;
            let r: Option<$t> = match op {
                IntrinsicOp::WrappingAdd => Some(x.wrapping_add(y)),
                IntrinsicOp::WrappingSub => Some(x.wrapping_sub(y)),
                IntrinsicOp::WrappingMul => Some(x.wrapping_mul(y)),
                IntrinsicOp::SaturatingAdd => Some(x.saturating_add(y)),
                IntrinsicOp::SaturatingSub => Some(x.saturating_sub(y)),
                IntrinsicOp::UncheckedAdd => x.checked_add(y),
                IntrinsicOp::UncheckedSub => x.checked_sub(y),
                IntrinsicOp::UncheckedMul => x.checked_mul(y),
                IntrinsicOp::UncheckedDiv => x.checked_div(y),
                IntrinsicOp::UncheckedRem => x.checked_rem(y),
                IntrinsicOp::ExactDiv => match (x.checked_div(y), x.checked_rem(y)) {
                    (Some(q), Some(0)) => Some(q),
                    _ => None,
                },
                _ => unreachable!("not a two-operand integer intrinsic: {op:?}"),
            };
            r.map(|v| v as $u as u128)
        }};
    }
    match (signed, w) {
        (false, 8) => go!(u8, u8),
        (true, 8) => go!(i8, u8),
        (false, 16) => go!(u16, u16),
        (true, 16) => go!(i16, u16),
        (false, 32) => go!(u32, u32),
        (true, 32) => go!(i32, u32),
        (false, 64) => go!(u64, u64),
        (true, 64) => go!(i64, u64),
        (false, 128) => go!(u128, u128),
        (true, 128) => go!(i128, u128),
        _ => unreachable!(),
    }
}

/// Reference `ctlz`/`cttz`/`ctpop` on native fixed-width unsigned integers.
fn native_count(op: IntrinsicOp, w: u32, bits: u128) -> u32 {
    macro_rules! go {
        ($u:ty) => {{
            let x = bits as $u;
            match op {
                IntrinsicOp::Ctlz | IntrinsicOp::CtlzNonzero => x.leading_zeros(),
                IntrinsicOp::Cttz | IntrinsicOp::CttzNonzero => x.trailing_zeros(),
                IntrinsicOp::Ctpop => x.count_ones(),
                _ => unreachable!(),
            }
        }};
    }
    match w {
        8 => go!(u8),
        16 => go!(u16),
        32 => go!(u32),
        64 => go!(u64),
        128 => go!(u128),
        _ => unreachable!(),
    }
}

/// Reference `bswap`/`bitreverse` on native fixed-width unsigned integers.
fn native_perm(op: IntrinsicOp, w: u32, bits: u128) -> u128 {
    macro_rules! go {
        ($u:ty) => {{
            let x = bits as $u;
            (match op {
                IntrinsicOp::Bswap => x.swap_bytes(),
                IntrinsicOp::Bitreverse => x.reverse_bits(),
                _ => unreachable!(),
            }) as u128
        }};
    }
    match w {
        8 => go!(u8),
        16 => go!(u16),
        32 => go!(u32),
        64 => go!(u64),
        128 => go!(u128),
        _ => unreachable!(),
    }
}

/// Reference `unchecked_shl`/`unchecked_shr` (`None` = undefined behavior).
fn native_shift(
    op: IntrinsicOp,
    signed: bool,
    w: u32,
    a: u128,
    amount: Option<u128>,
) -> Option<u128> {
    let s = amount.filter(|s| *s < u128::from(w))? as u32;
    macro_rules! go {
        ($t:ty, $u:ty) => {{
            let x = a as $u as $t;
            (match op {
                IntrinsicOp::UncheckedShl => x << s,
                IntrinsicOp::UncheckedShr => x >> s,
                _ => unreachable!(),
            }) as $u as u128
        }};
    }
    Some(match (signed, w) {
        (false, 8) => go!(u8, u8),
        (true, 8) => go!(i8, u8),
        (false, 16) => go!(u16, u16),
        (true, 16) => go!(i16, u16),
        (false, 32) => go!(u32, u32),
        (true, 32) => go!(i32, u32),
        (false, 64) => go!(u64, u64),
        (true, 64) => go!(i64, u64),
        (false, 128) => go!(u128, u128),
        (true, 128) => go!(i128, u128),
        _ => unreachable!(),
    })
}

fn blk(stmts: Vec<Statement>, term: Terminator) -> BasicBlockData {
    BasicBlockData::with_terminator(stmts, term, false)
}
fn cleanup_blk(stmts: Vec<Statement>, term: Terminator) -> BasicBlockData {
    BasicBlockData::with_terminator(stmts, term, true)
}
fn mk(local_decls: Vec<Ty>, basic_blocks: Vec<BasicBlockData>) -> Body {
    Body {
        local_decls,
        basic_blocks,
    }
}
fn lower(body: &Body, pw: PtrWidth) -> LoweredBody {
    lower_body(body, pw).unwrap_or_else(|err| panic!("lowering failed: {err}"))
}
fn lower_err(body: &Body, pw: PtrWidth) -> RvalueLowerError {
    match lower_body(body, pw) {
        Err(err) => err,
        Ok(_) => panic!("expected a lowering error"),
    }
}
fn place(l: usize) -> Place {
    Place::from_local(l)
}
fn cp(l: usize) -> Operand {
    Operand::Copy(place(l))
}
fn mv(l: usize) -> Operand {
    Operand::Move(place(l))
}
fn cst(bits: u128, ty: Ty) -> Operand {
    Operand::Constant(Constant::Int(bits, ty))
}
fn assign(l: usize, rv: Rvalue) -> Statement {
    Statement::Assign(place(l), rv)
}
fn live(l: usize) -> Statement {
    Statement::StorageLive(Local(l))
}
fn intrinsic(op: IntrinsicOp) -> Constant {
    Constant::intrinsic(op)
}
fn callee(name: &str) -> Constant {
    Constant::callee(name)
}
fn call(
    func: Constant,
    args: Vec<Operand>,
    dest: usize,
    target: Option<usize>,
    unwind: UnwindAction,
) -> Terminator {
    Terminator::Call {
        func: Operand::Constant(func),
        args,
        destination: place(dest),
        target,
        unwind,
    }
}
fn returned(outcome: Result<CfgEvalOutcome, CfgEvalError>) -> MirValue {
    match outcome {
        Ok(CfgEvalOutcome::Returned(val)) => val,
        other => panic!("expected Returned, got {other:?}"),
    }
}
fn term_err(outcome: Result<CfgEvalOutcome, CfgEvalError>) -> (usize, RvalueEvalError) {
    match outcome {
        Err(CfgEvalError::Terminator { bb, error }) => (bb, error),
        other => panic!("expected a terminator error, got {other:?}"),
    }
}

/// `fn(_1: arg_tys[0], ..) -> ret_ty { bb0: _0 = op(move _1, ..) -> bb1; bb1: return }`.
fn intrinsic_fn(op: IntrinsicOp, arg_tys: Vec<Ty>, ret_ty: Ty) -> Body {
    let n = arg_tys.len();
    let mut decls = vec![ret_ty];
    decls.extend(arg_tys);
    mk(
        decls,
        vec![
            blk(
                vec![],
                call(
                    intrinsic(op),
                    (1..=n).map(mv).collect(),
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    )
}

/// `core::cmp::Ordering`-shaped `#[repr(i8)]` enum with its variants in `order`.
fn ordering_ty(order: [(&str, i8); 3]) -> Ty {
    AdtDef::new_enum(
        "core::cmp::Ordering",
        Some(ScalarTy::Int(IntTy::I8)),
        order
            .iter()
            .map(|(name, d)| VariantDef::new(*name, vec![]).with_discriminant(u128::from(*d as u8)))
            .collect(),
    )
    .into_ty()
}

fn adt_def(ty: &Ty) -> &Arc<AdtDef> {
    match ty {
        Ty::Adt(def) => def,
        _ => panic!("not an ADT: {ty:?}"),
    }
}

// ---------------------------------------------------------------------------------------------
// `V2026_06_01` adapter
// ---------------------------------------------------------------------------------------------

#[test]
fn test_adapter_maps_every_trusted_def_path_and_nothing_else() {
    // `classifyRustIntrinsic?` (minus `const_eval_select`) + `exact_div` + the memory
    // intrinsics; `isUnreachableCallTarget`; `isAbortingPanicDefPath`; `isUnwindingPanicDefPath`.
    assert_eq!(RUST_INTRINSIC_DEF_PATHS_V2026_06_01.len(), 27);
    assert_eq!(UNREACHABLE_DEF_PATHS_V2026_06_01.len(), 3);
    assert_eq!(ABORTING_PANIC_DEF_PATHS_V2026_06_01.len(), 10);
    assert_eq!(UNWINDING_PANIC_DEF_PATHS_V2026_06_01.len(), 26);
    let mut all_paths: Vec<(&str, IntrinsicOp)> = RUST_INTRINSIC_DEF_PATHS_V2026_06_01.to_vec();
    all_paths.extend(
        UNREACHABLE_DEF_PATHS_V2026_06_01
            .iter()
            .map(|p| (*p, IntrinsicOp::UnreachableUnchecked)),
    );
    all_paths.extend(
        ABORTING_PANIC_DEF_PATHS_V2026_06_01
            .iter()
            .map(|p| (*p, IntrinsicOp::Abort)),
    );
    all_paths.extend(
        UNWINDING_PANIC_DEF_PATHS_V2026_06_01
            .iter()
            .map(|p| (*p, IntrinsicOp::PanicUnwind)),
    );
    let mut seen = std::collections::BTreeSet::new();
    for (path, op) in &all_paths {
        assert!(seen.insert(*path), "{path} listed twice");
        assert_eq!(lower_intrinsic_kind_v2026_06_01(path), Some(*op), "{path}");
        assert_eq!(
            lower_call_target_v2026_06_01(path),
            Some(CallTarget::Intrinsic(*op))
        );
        assert_eq!(
            classify_call_target_v2026_06_01(path),
            CallTarget::Intrinsic(*op)
        );
    }
    // Every intrinsic is reachable from some `V2026_06_01` path.
    for op in IntrinsicOp::ALL {
        assert!(all_paths.iter().any(|(_, o)| *o == op), "{op} unreachable");
    }
    // Exact spellings straight from `Terminators.lean`.
    for (path, op) in [
        ("core::intrinsics::exact_div", IntrinsicOp::ExactDiv),
        ("core::intrinsics::ctlz_nonzero", IntrinsicOp::CtlzNonzero),
        (
            "core::intrinsics::three_way_compare",
            IntrinsicOp::ThreeWayCompare,
        ),
        (
            "core::hint::unreachable_unchecked",
            IntrinsicOp::UnreachableUnchecked,
        ),
        (
            "std::hint::unreachable_unchecked",
            IntrinsicOp::UnreachableUnchecked,
        ),
        ("core::intrinsics::abort", IntrinsicOp::Abort),
        (
            "core::panicking::panic_nounwind_fmt::panic_impl",
            IntrinsicOp::Abort,
        ),
        (
            "core::panicking::panic_fmt::panic_impl",
            IntrinsicOp::PanicUnwind,
        ),
        (
            "core::panicking::panic_const::panic_const_rem_by_zero",
            IntrinsicOp::PanicUnwind,
        ),
        ("core::result::unwrap_failed", IntrinsicOp::PanicUnwind),
    ] {
        assert_eq!(lower_intrinsic_kind_v2026_06_01(path), Some(op));
    }
    // Near misses, wrappers, and unmodeled intrinsics are ordinary functions.
    for path in [
        "core::intrinsics::const_eval_select",
        "core::ptr::copy_nonoverlapping",
        "core::ptr::write_bytes",
        "std::intrinsics::ctlz",
        "core::intrinsics::ctlz ",
        "core::intrinsics::Ctlz",
        "core::panicking::panic_fmt::other",
        "core::num::<impl u32>::leading_zeros",
        "",
    ] {
        assert_eq!(lower_intrinsic_kind_v2026_06_01(path), None, "{path}");
        assert_eq!(lower_call_target_v2026_06_01(path), None);
        assert_eq!(
            classify_call_target_v2026_06_01(path),
            CallTarget::Fn(CalleeSymbol::new(path))
        );
    }
}

#[test]
fn test_adapter_prefers_linked_bodies_like_trusted_lookup_callee() {
    let unit_fn = lower(
        &mk(
            vec![unit()],
            vec![blk(
                vec![assign(0, Rvalue::Use(Operand::Constant(Constant::Unit)))],
                Terminator::Return,
            )],
        ),
        PW,
    );
    let table = CallTable::new().with_callee("core::panicking::panic", 0, unit_fn);
    assert_eq!(
        classify_linked_call_target_v2026_06_01("core::panicking::panic", &table),
        CallTarget::Fn(CalleeSymbol::new("core::panicking::panic"))
    );
    assert_eq!(
        classify_linked_call_target_v2026_06_01("core::intrinsics::abort", &table),
        CallTarget::Intrinsic(IntrinsicOp::Abort)
    );
    assert_eq!(
        classify_linked_call_target_v2026_06_01("my_crate::f", &table),
        CallTarget::Fn(CalleeSymbol::new("my_crate::f"))
    );
}

#[test]
fn test_intrinsic_op_metadata_and_fn_def_constants() {
    let names: std::collections::BTreeSet<&str> =
        IntrinsicOp::ALL.iter().map(|op| op.name()).collect();
    assert_eq!(names.len(), IntrinsicOp::ALL.len());
    let diverging: Vec<IntrinsicOp> = IntrinsicOp::ALL
        .into_iter()
        .filter(|op| op.is_diverging())
        .collect();
    assert_eq!(
        diverging,
        vec![
            IntrinsicOp::UnreachableUnchecked,
            IntrinsicOp::Abort,
            IntrinsicOp::PanicUnwind
        ]
    );
    let memory: Vec<IntrinsicOp> = IntrinsicOp::ALL
        .into_iter()
        .filter(|op| op.accesses_memory())
        .collect();
    assert_eq!(
        memory,
        vec![IntrinsicOp::CopyNonOverlapping, IntrinsicOp::WriteBytes]
    );
    assert_eq!(IntrinsicOp::Ctlz.to_string(), "ctlz");
    // A function item is a zero-sized `()` constant outside a call.
    let item = Constant::callee("f");
    assert_eq!(item.ty(), unit());
    assert_eq!(
        item.call_target(),
        Some(&CallTarget::Fn(CalleeSymbol::new("f")))
    );
    assert_eq!(Constant::Unit.call_target(), None);
    assert_eq!(eval_constant(&item, PW), Ok(MirValue::Unit));
    let body = mk(
        vec![unit()],
        vec![blk(
            vec![assign(
                0,
                Rvalue::Use(Operand::Constant(intrinsic(IntrinsicOp::Ctlz))),
            )],
            Terminator::Return,
        )],
    );
    assert_eq!(
        returned(eval_lowered_body_cfg(&lower(&body, PW), &[], 2)),
        MirValue::Unit
    );
}

// ---------------------------------------------------------------------------------------------
// Bit manipulation: `ctlz`, `cttz`, `ctpop` (`T -> u32`), `bswap`, `bitreverse` (`T -> T`)
// ---------------------------------------------------------------------------------------------

#[test]
fn test_bit_counts_return_u32_for_every_width_and_pointer_width() {
    for pw in PWS {
        for ty in int_tys() {
            let w = width(&ty, pw);
            for bits in samples(w) {
                for op in [
                    IntrinsicOp::Ctlz,
                    IntrinsicOp::Cttz,
                    IntrinsicOp::Ctpop,
                    IntrinsicOp::CtlzNonzero,
                    IntrinsicOp::CttzNonzero,
                ] {
                    let got = eval_intrinsic(op, &[iv(&ty, bits, pw)], &u32_ty(), pw);
                    if bits == 0
                        && matches!(op, IntrinsicOp::CtlzNonzero | IntrinsicOp::CttzNonzero)
                    {
                        assert!(
                            matches!(got, Err(RvalueEvalError::IntrinsicUb { op: o, .. }) if o == op),
                            "{op}({ty:?} 0) must be UB, got {got:?}"
                        );
                        continue;
                    }
                    let expected = native_count(op, w, bits);
                    assert_eq!(
                        got,
                        Ok(MirValue::unsigned(u128::from(expected), UintTy::U32, pw)),
                        "{op}({ty:?} {bits:#x}) on {pw:?}"
                    );
                }
            }
            // `ctlz(0)` and `cttz(0)` are the bit width (`isize`/`usize` follow `ptr_width`).
            for op in [IntrinsicOp::Ctlz, IntrinsicOp::Cttz] {
                assert_eq!(
                    eval_intrinsic(op, &[iv(&ty, 0, pw)], &u32_ty(), pw),
                    Ok(MirValue::unsigned(u128::from(w), UintTy::U32, pw))
                );
            }
        }
    }
    // `usize` is 32 bits on `Bits32`, 64 on `Bits64`.
    assert_eq!(
        eval_intrinsic(
            IntrinsicOp::Ctlz,
            &[usizev(1, PtrWidth::Bits32)],
            &u32_ty(),
            PtrWidth::Bits32
        ),
        Ok(MirValue::unsigned(31, UintTy::U32, PtrWidth::Bits32))
    );
    assert_eq!(
        eval_intrinsic(IntrinsicOp::Ctlz, &[usizev(1, PW)], &u32_ty(), PW),
        Ok(u32v(63))
    );
}

#[test]
fn test_bswap_and_bitreverse_permute_within_the_type_width() {
    for pw in PWS {
        for ty in int_tys() {
            let w = width(&ty, pw);
            for bits in samples(w) {
                for op in [IntrinsicOp::Bswap, IntrinsicOp::Bitreverse] {
                    assert_eq!(
                        eval_intrinsic(op, &[iv(&ty, bits, pw)], &ty, pw),
                        Ok(iv(&ty, native_perm(op, w, bits), pw)),
                        "{op}({ty:?} {bits:#x}) on {pw:?}"
                    );
                }
            }
        }
    }
    // A one-byte `bswap` is the identity; `bitreverse(1u8) == 0x80`.
    assert_eq!(
        eval_intrinsic(IntrinsicOp::Bswap, &[iv(&u8_ty(), 0x12, PW)], &u8_ty(), PW),
        Ok(iv(&u8_ty(), 0x12, PW))
    );
    assert_eq!(
        eval_intrinsic(
            IntrinsicOp::Bitreverse,
            &[iv(&u8_ty(), 1, PW)],
            &u8_ty(),
            PW
        ),
        Ok(iv(&u8_ty(), 0x80, PW))
    );
}

// ---------------------------------------------------------------------------------------------
// Arithmetic: `exact_div`, `wrapping_*`, `saturating_*`, `unchecked_*`
// ---------------------------------------------------------------------------------------------

#[test]
fn test_two_operand_arithmetic_matches_native_reference_on_every_width() {
    let ops = [
        IntrinsicOp::ExactDiv,
        IntrinsicOp::WrappingAdd,
        IntrinsicOp::WrappingSub,
        IntrinsicOp::WrappingMul,
        IntrinsicOp::SaturatingAdd,
        IntrinsicOp::SaturatingSub,
        IntrinsicOp::UncheckedAdd,
        IntrinsicOp::UncheckedSub,
        IntrinsicOp::UncheckedMul,
        IntrinsicOp::UncheckedDiv,
        IntrinsicOp::UncheckedRem,
    ];
    for pw in PWS {
        for ty in int_tys() {
            let w = width(&ty, pw);
            let signed = ty.is_signed_int();
            for a in samples(w) {
                for b in samples(w) {
                    for op in ops {
                        let got = eval_intrinsic(op, &[iv(&ty, a, pw), iv(&ty, b, pw)], &ty, pw);
                        match native2(op, signed, w, a, b) {
                            Some(expected) => assert_eq!(
                                got,
                                Ok(iv(&ty, expected, pw)),
                                "{op}({ty:?} {a:#x}, {b:#x}) on {pw:?}"
                            ),
                            None => assert!(got.is_err(), "{op}({ty:?} {a:#x}, {b:#x}) must be UB"),
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn test_exact_div_faults_on_zero_int_min_by_minus_one_and_remainders() {
    for pw in PWS {
        for ty in int_tys() {
            let w = width(&ty, pw);
            let ed = |a: u128, b: u128| {
                eval_intrinsic(
                    IntrinsicOp::ExactDiv,
                    &[iv(&ty, a, pw), iv(&ty, b, pw)],
                    &ty,
                    pw,
                )
            };
            assert_eq!(ed(12, 0), Err(RvalueEvalError::DivisionByZero));
            assert_eq!(ed(0, 0), Err(RvalueEvalError::DivisionByZero));
            assert!(matches!(
                ed(13, 4),
                Err(RvalueEvalError::IntrinsicUb {
                    op: IntrinsicOp::ExactDiv,
                    ..
                })
            ));
            assert_eq!(ed(12, 4), Ok(iv(&ty, 3, pw)));
            assert_eq!(ed(0, 7), Ok(iv(&ty, 0, pw)));
            if let Ty::Int(it) = &ty {
                let min = 1u128 << (w - 1);
                let minus_one = width_mask(w);
                assert_eq!(
                    ed(min, minus_one),
                    Err(RvalueEvalError::SignedDivisionOverflow {
                        min_val: it.min_value(pw),
                        bit_width: w,
                    })
                );
                // `INT_MIN / 1` and `INT_MIN / 2` are exact.
                assert_eq!(ed(min, 1), Ok(iv(&ty, min, pw)));
                assert_eq!(ed(min, 2), Ok(iv(&ty, min | (min >> 1), pw)));
                // Signs: -12 / 4 = -3, 12 / -4 = -3, -12 / -4 = 3, -13 / 4 is UB.
                let neg = |v: i128| it.truncate_signed(v, pw);
                assert_eq!(ed(neg(-12), 4), Ok(iv(&ty, neg(-3), pw)));
                assert_eq!(ed(12, neg(-4)), Ok(iv(&ty, neg(-3), pw)));
                assert_eq!(ed(neg(-12), neg(-4)), Ok(iv(&ty, 3, pw)));
                assert!(matches!(
                    ed(neg(-13), 4),
                    Err(RvalueEvalError::IntrinsicUb { .. })
                ));
            }
        }
    }
}

#[test]
fn test_unchecked_intrinsics_agree_with_unchecked_and_with_overflow_binops() {
    let parity = [
        (
            IntrinsicOp::UncheckedAdd,
            BinOp::AddUnchecked,
            BinOp::AddWithOverflow,
            IntrinsicOp::WrappingAdd,
            Some(IntrinsicOp::SaturatingAdd),
        ),
        (
            IntrinsicOp::UncheckedSub,
            BinOp::SubUnchecked,
            BinOp::SubWithOverflow,
            IntrinsicOp::WrappingSub,
            Some(IntrinsicOp::SaturatingSub),
        ),
        (
            IntrinsicOp::UncheckedMul,
            BinOp::MulUnchecked,
            BinOp::MulWithOverflow,
            IntrinsicOp::WrappingMul,
            None,
        ),
    ];
    for pw in PWS {
        for ty in int_tys() {
            let w = width(&ty, pw);
            for a in samples(w) {
                for b in samples(w) {
                    let (x, y) = (iv(&ty, a, pw), iv(&ty, b, pw));
                    for (unchecked, unchecked_binop, overflow_binop, wrapping, saturating) in parity
                    {
                        let intrinsic_res =
                            eval_intrinsic(unchecked, &[x.clone(), y.clone()], &ty, pw);
                        // 1. Exactly `BinOp::*Unchecked`, errors included.
                        assert_eq!(intrinsic_res, eval_binop(unchecked_binop, &x, &y, pw));
                        // 2. `*WithOverflow` = (wrapping result, unchecked is UB).
                        let pair = eval_binop(overflow_binop, &x, &y, pw).unwrap();
                        let (wrapped, overflowed) = pair.as_checked_pair().unwrap();
                        assert_eq!(
                            eval_intrinsic(wrapping, &[x.clone(), y.clone()], &ty, pw),
                            Ok(iv(&ty, wrapped, pw))
                        );
                        assert_eq!(
                            overflowed,
                            intrinsic_res.is_err(),
                            "{unchecked}({ty:?} {a:#x}, {b:#x})"
                        );
                        if overflowed {
                            assert_eq!(
                                intrinsic_res,
                                Err(RvalueEvalError::ArithmeticOverflow {
                                    op: unchecked_binop
                                })
                            );
                        } else {
                            assert_eq!(intrinsic_res, Ok(iv(&ty, wrapped, pw)));
                        }
                        // 3. Saturating = wrapped unless the operation overflowed.
                        if let Some(saturating) = saturating {
                            let sat = eval_intrinsic(saturating, &[x.clone(), y.clone()], &ty, pw)
                                .unwrap();
                            if !overflowed {
                                assert_eq!(sat, iv(&ty, wrapped, pw));
                            } else {
                                assert_ne!(sat, iv(&ty, wrapped, pw));
                            }
                        }
                    }
                    // `unchecked_div`/`unchecked_rem` are exactly `BinOp::Div`/`BinOp::Rem`.
                    for (op, binop) in [
                        (IntrinsicOp::UncheckedDiv, BinOp::Div),
                        (IntrinsicOp::UncheckedRem, BinOp::Rem),
                    ] {
                        assert_eq!(
                            eval_intrinsic(op, &[x.clone(), y.clone()], &ty, pw),
                            eval_binop(binop, &x, &y, pw)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn test_unchecked_div_and_rem_fault_like_binop_div_and_rem() {
    for pw in PWS {
        for ty in int_tys().into_iter().filter(Ty::is_signed_int) {
            let w = width(&ty, pw);
            let Ty::Int(it) = &ty else { unreachable!() };
            let min = iv(&ty, 1u128 << (w - 1), pw);
            let minus_one = iv(&ty, width_mask(w), pw);
            for op in [IntrinsicOp::UncheckedDiv, IntrinsicOp::UncheckedRem] {
                assert_eq!(
                    eval_intrinsic(op, &[min.clone(), minus_one.clone()], &ty, pw),
                    Err(RvalueEvalError::SignedDivisionOverflow {
                        min_val: it.min_value(pw),
                        bit_width: w,
                    })
                );
                assert_eq!(
                    eval_intrinsic(op, &[min.clone(), iv(&ty, 0, pw)], &ty, pw),
                    Err(RvalueEvalError::DivisionByZero)
                );
            }
        }
    }
}

#[test]
fn test_unchecked_shifts_agree_with_binops_for_signed_and_unsigned_amounts() {
    for pw in PWS {
        for lhs_ty in int_tys() {
            let lw = width(&lhs_ty, pw);
            for rhs_ty in int_tys() {
                let rw = width(&rhs_ty, pw);
                let mut amounts: Vec<u128> = vec![0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 127];
                amounts.extend([
                    u128::from(lw) - 1,
                    u128::from(lw),
                    u128::from(lw) + 1,
                    width_mask(rw),
                    width_mask(rw) - 1,
                ]);
                for raw_amount in amounts {
                    let amount_bits = raw_amount & width_mask(rw);
                    let amount = if rhs_ty.is_signed_int() {
                        let s = sign_extend(amount_bits, rw);
                        (s >= 0).then_some(s as u128)
                    } else {
                        Some(amount_bits)
                    };
                    for a in [0u128, 1, 0x81, width_mask(lw), 1u128 << (lw - 1)] {
                        let (x, y) = (iv(&lhs_ty, a, pw), iv(&rhs_ty, amount_bits, pw));
                        for (op, binop) in [
                            (IntrinsicOp::UncheckedShl, BinOp::ShlUnchecked),
                            (IntrinsicOp::UncheckedShr, BinOp::ShrUnchecked),
                        ] {
                            let got = eval_intrinsic(op, &[x.clone(), y.clone()], &lhs_ty, pw);
                            assert_eq!(got, eval_binop(binop, &x, &y, pw));
                            match native_shift(op, lhs_ty.is_signed_int(), lw, a, amount) {
                                Some(expected) => assert_eq!(got, Ok(iv(&lhs_ty, expected, pw))),
                                None => assert!(
                                    matches!(got, Err(RvalueEvalError::ShiftOverflow { .. })),
                                    "{op}({lhs_ty:?} {a:#x}, {rhs_ty:?} {amount_bits:#x}) must be UB: {got:?}"
                                ),
                            }
                            // The checked `Shl`/`Shr` overflow flag is exactly the UB condition.
                            let checked_binop = if op == IntrinsicOp::UncheckedShl {
                                BinOp::Shl
                            } else {
                                BinOp::Shr
                            };
                            let (_, overflowed) =
                                eval_checked_binop(checked_binop, &x, &y, pw).unwrap();
                            assert_eq!(overflowed, got.is_err());
                        }
                    }
                }
            }
        }
    }
    // Arithmetic right shift for signed `T`, logical for unsigned.
    assert_eq!(
        eval_intrinsic(
            IntrinsicOp::UncheckedShr,
            &[iv(&i8_ty(), 0x80, PW), iv(&u8_ty(), 7, PW)],
            &i8_ty(),
            PW
        ),
        Ok(iv(&i8_ty(), 0xFF, PW))
    );
    assert_eq!(
        eval_intrinsic(
            IntrinsicOp::UncheckedShr,
            &[iv(&u8_ty(), 0x80, PW), iv(&i8_ty(), 7, PW)],
            &u8_ty(),
            PW
        ),
        Ok(iv(&u8_ty(), 1, PW))
    );
}

// ---------------------------------------------------------------------------------------------
// `three_way_compare`, `ub_checks`
// ---------------------------------------------------------------------------------------------

#[test]
fn test_three_way_compare_matches_binop_cmp_and_supports_ordering_enums() {
    let ordering = ordering_ty([("Less", -1), ("Equal", 0), ("Greater", 1)]);
    let shuffled = ordering_ty([("Greater", 1), ("Less", -1), ("Equal", 0)]);
    for pw in PWS {
        for ty in int_tys() {
            let w = width(&ty, pw);
            for a in samples(w) {
                for b in samples(w) {
                    let (x, y) = (iv(&ty, a, pw), iv(&ty, b, pw));
                    let got = eval_intrinsic(
                        IntrinsicOp::ThreeWayCompare,
                        &[x.clone(), y.clone()],
                        &i8_ty(),
                        pw,
                    );
                    assert_eq!(got, eval_binop(BinOp::Cmp, &x, &y, pw));
                    let expected: i8 = if ty.is_signed_int() {
                        sign_extend(a, w).cmp(&sign_extend(b, w)) as i8
                    } else {
                        a.cmp(&b) as i8
                    };
                    assert_eq!(
                        got,
                        Ok(MirValue::signed(i128::from(expected), IntTy::I8, pw))
                    );
                    for ord in [&ordering, &shuffled] {
                        let def = adt_def(ord);
                        let variant = ordering_variant(ord, expected, pw).unwrap();
                        assert_eq!(
                            eval_intrinsic(
                                IntrinsicOp::ThreeWayCompare,
                                &[x.clone(), y.clone()],
                                ord,
                                pw
                            ),
                            Ok(MirValue::adt(def, variant, vec![]))
                        );
                    }
                }
            }
        }
    }
    // `char` compares by code point (`allowChar := true`).
    let c = |ch: char| MirValue::Char(ch);
    assert_eq!(
        eval_intrinsic(
            IntrinsicOp::ThreeWayCompare,
            &[c('a'), c('\u{10FFFF}')],
            &i8_ty(),
            PW
        ),
        Ok(MirValue::signed(-1, IntTy::I8, PW))
    );
    assert_eq!(
        eval_intrinsic(
            IntrinsicOp::ThreeWayCompare,
            &[c('z'), c('z')],
            &ordering,
            PW
        ),
        Ok(MirValue::adt(adt_def(&ordering), 1, vec![]))
    );
    // `bool`, pointers, mismatched operand types, and other result types are rejected.
    let p = MirValue::ptr(
        PointerValue::without_provenance(8),
        raw(u8_ty(), Mutability::Not),
    );
    for (args, dest) in [
        (vec![MirValue::Bool(false), MirValue::Bool(true)], i8_ty()),
        (vec![p.clone(), p], i8_ty()),
        (vec![iv(&u8_ty(), 1, PW), iv(&u16_ty(), 1, PW)], i8_ty()),
        (vec![iv(&u8_ty(), 1, PW), iv(&u8_ty(), 1, PW)], u8_ty()),
    ] {
        assert!(matches!(
            eval_intrinsic(IntrinsicOp::ThreeWayCompare, &args, &dest, PW),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
    }
    // Enums that are not `Ordering`-shaped are not accepted as results.
    let unsigned_tag = AdtDef::new_enum(
        "E",
        Some(ScalarTy::Uint(UintTy::U8)),
        vec![
            VariantDef::new("A", vec![]),
            VariantDef::new("B", vec![]),
            VariantDef::new("C", vec![]),
        ],
    )
    .into_ty();
    let wrong_discrs = ordering_ty([("Less", -2), ("Equal", 0), ("Greater", 2)]);
    for ty in [unsigned_tag, wrong_discrs] {
        assert_eq!(ordering_variant(&ty, 0, PW), None);
    }
}

#[test]
fn test_ub_checks_returns_true_and_follows_the_state_like_nullop_ub_checks() {
    assert_eq!(
        eval_intrinsic(IntrinsicOp::UbChecks, &[], &Ty::Bool, PW),
        Ok(MirValue::Bool(true))
    );
    assert!(matches!(
        eval_intrinsic(IntrinsicOp::UbChecks, &[iv(&u8_ty(), 0, PW)], &Ty::Bool, PW),
        Err(RvalueEvalError::TypeMismatch(_))
    ));
    // `fn() -> (bool, bool) { _1 = ub_checks(); _2 = UbChecks; _0 = (_1, _2) }`
    let body = mk(
        vec![Ty::Tuple(vec![Ty::Bool, Ty::Bool]), Ty::Bool, Ty::Bool],
        vec![
            blk(
                vec![live(1), live(2)],
                call(
                    intrinsic(IntrinsicOp::UbChecks),
                    vec![],
                    1,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(
                vec![
                    assign(2, Rvalue::NullaryOp(NullOp::UbChecks, Ty::Bool)),
                    assign(
                        0,
                        Rvalue::Aggregate(AggregateKind::Tuple, vec![cp(1), cp(2)]),
                    ),
                ],
                Terminator::Return,
            ),
        ],
    );
    let lowered = lower(&body, PW);
    for ub_checks in [true, false] {
        let mut state = StatementEvalState::from_body(&lowered, &[]).unwrap();
        state.ub_checks = ub_checks;
        assert_eq!(
            returned(eval_cfg_in_state(&lowered, state, 0, 4, None)),
            MirValue::Tuple(vec![MirValue::Bool(ub_checks), MirValue::Bool(ub_checks)])
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Pointers: `arith_offset`, `size_of_val`, `align_of_val`
// ---------------------------------------------------------------------------------------------

#[test]
fn test_arith_offset_wraps_the_address_space_and_keeps_provenance() {
    for pw in PWS {
        let max = pw.max_usize();
        let modulus = i128::from(pw.max_usize() as u64) + 1;
        let ptr_ty = raw(u32_ty(), Mutability::Not);
        let off = |addr: u64, prov: Option<(u64, u64)>, count: i128, pointee: Ty| {
            let ptr = match prov {
                Some((alloc, tag)) => PointerValue::with_provenance(addr, alloc, tag),
                None => PointerValue::without_provenance(addr),
            };
            let ty = raw(pointee.clone(), Mutability::Not);
            eval_intrinsic(
                IntrinsicOp::ArithOffset,
                &[MirValue::ptr(ptr, ty.clone()), isizev(count, pw)],
                &ty,
                pw,
            )
        };
        let expect = |addr: i128, prov: Option<(u64, u64)>| {
            let addr = addr.rem_euclid(modulus) as u64;
            let ptr = match prov {
                Some((alloc, tag)) => PointerValue::with_provenance(addr, alloc, tag),
                None => PointerValue::without_provenance(addr),
            };
            Ok(MirValue::ptr(ptr, ptr_ty.clone()))
        };
        let prov = Some((7, 99));
        assert_eq!(off(0x1000, prov, 3, u32_ty()), expect(0x100C, prov));
        assert_eq!(off(0x1000, prov, -3, u32_ty()), expect(0x0FF4, prov));
        // Wrapping below zero and past the top of the address space (no UB, unlike `Offset`).
        assert_eq!(off(4, prov, -2, u32_ty()), expect(-4, prov));
        assert_eq!(
            off(max as u64 - 3, prov, 2, u32_ty()),
            expect(i128::from(max as u64) + 5, prov)
        );
        // Null without provenance, and extreme counts (no intermediate overflow).
        assert_eq!(off(0, None, 1, u32_ty()), expect(4, None));
        let isize_max = pw.max_isize();
        let isize_min = pw.min_isize();
        assert_eq!(
            off(0x40, prov, isize_max, u32_ty()),
            expect(0x40 + isize_max * 4, prov)
        );
        assert_eq!(
            off(0x40, prov, isize_min, u32_ty()),
            expect(0x40 + isize_min * 4, prov)
        );
        // Zero-sized pointees never move; arrays stride by their whole size.
        let zst_ty = raw(unit(), Mutability::Not);
        assert_eq!(
            off(0x10, prov, isize_max, unit()),
            Ok(MirValue::ptr(
                PointerValue::with_provenance(0x10, 7, 99),
                zst_ty
            ))
        );
        let arr = Ty::Array(Box::new(u32_ty()), 3);
        assert_eq!(
            off(0x100, prov, 2, arr.clone()),
            Ok(MirValue::ptr(
                PointerValue::with_provenance(0x118, 7, 99),
                raw(arr, Mutability::Not)
            ))
        );
        // A `&T` argument is accepted; the result is a raw pointer, even when wrapped to null.
        let r = MirValue::ptr(
            PointerValue::with_provenance(4, 1, 1),
            reference(u32_ty(), Mutability::Not),
        );
        assert_eq!(
            eval_intrinsic(IntrinsicOp::ArithOffset, &[r, isizev(-1, pw)], &ptr_ty, pw),
            Ok(MirValue::ptr(
                PointerValue::with_provenance(0, 1, 1),
                ptr_ty.clone()
            ))
        );
    }
    // The count must be an `isize`, and the result a raw pointer to the same pointee.
    let p = MirValue::ptr(
        PointerValue::without_provenance(8),
        raw(u32_ty(), Mutability::Not),
    );
    for (args, dest) in [
        (
            vec![p.clone(), usizev(1, PW)],
            raw(u32_ty(), Mutability::Not),
        ),
        (
            vec![p.clone(), isizev(1, PW)],
            reference(u32_ty(), Mutability::Not),
        ),
        (
            vec![p.clone(), isizev(1, PW)],
            raw(u8_ty(), Mutability::Not),
        ),
        (
            vec![iv(&usize_ty(), 8, PW), isizev(1, PW)],
            raw(u32_ty(), Mutability::Not),
        ),
    ] {
        assert!(matches!(
            eval_intrinsic(IntrinsicOp::ArithOffset, &args, &dest, PW),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
    }
}

#[test]
fn test_size_and_align_of_val_follow_the_pointee_layout_without_dereferencing() {
    let packed = AdtDef::new_struct("S", vec![u8_ty(), u32_ty()])
        .with_repr(AdtRepr::c())
        .into_ty();
    for pw in PWS {
        let cases = [
            (u8_ty(), 1u128, 1u128),
            (u64_ty(), 8, 8),
            (usize_ty(), pw.byte_size() as u128, pw.byte_size() as u128),
            (Ty::Array(Box::new(u16_ty()), 5), 10, 2),
            (unit(), 0, 1),
            (packed.clone(), 8, 4),
            (
                raw(u8_ty(), Mutability::Mut),
                pw.byte_size() as u128,
                pw.byte_size() as u128,
            ),
        ];
        for (pointee, size, align) in cases {
            // Raw pointers may be null or dangling: nothing is read.
            for ptr_ty in [
                raw(pointee.clone(), Mutability::Not),
                raw(pointee.clone(), Mutability::Mut),
                reference(pointee.clone(), Mutability::Not),
            ] {
                let addr = if ptr_ty.is_ref() { 0x1000 } else { 0 };
                let p = MirValue::ptr(PointerValue::without_provenance(addr), ptr_ty);
                assert_eq!(
                    eval_intrinsic(
                        IntrinsicOp::SizeOfVal,
                        std::slice::from_ref(&p),
                        &usize_ty(),
                        pw
                    ),
                    Ok(usizev(size, pw)),
                    "size_of_val::<{pointee:?}> on {pw:?}"
                );
                assert_eq!(
                    eval_intrinsic(IntrinsicOp::AlignOfVal, &[p], &usize_ty(), pw),
                    Ok(usizev(align, pw))
                );
            }
        }
    }
    // A pointee whose layout is unspecified (a tagless multi-variant enum) or too large for the
    // target is rejected, like `NullOp::SizeOf`.
    let unspecified = AdtDef::new_enum(
        "E",
        None,
        vec![
            VariantDef::new("A", vec![u8_ty()]),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    )
    .into_ty();
    let p = MirValue::ptr(
        PointerValue::without_provenance(0),
        raw(unspecified.clone(), Mutability::Not),
    );
    assert_eq!(
        eval_intrinsic(IntrinsicOp::SizeOfVal, &[p], &usize_ty(), PW),
        Err(RvalueEvalError::CastEval(
            CastEvalError::UnsupportedLayout { ty: unspecified }
        ))
    );
    let huge = Ty::Array(Box::new(u8_ty()), 1 << 31);
    let p = MirValue::ptr(
        PointerValue::without_provenance(0),
        raw(huge.clone(), Mutability::Not),
    );
    assert_eq!(
        eval_intrinsic(IntrinsicOp::AlignOfVal, &[p], &usize_ty(), PtrWidth::Bits32),
        Err(RvalueEvalError::CastEval(CastEvalError::LayoutTooLarge {
            ty: huge
        }))
    );
}

#[test]
fn test_eval_intrinsic_rejects_ill_typed_or_ill_formed_arguments_and_stateful_ops() {
    // Not an integer, wrong arity, mismatched operand types, wrong destination.
    for (op, args, dest) in [
        (IntrinsicOp::Ctlz, vec![MirValue::Bool(true)], u32_ty()),
        (IntrinsicOp::Ctlz, vec![iv(&u8_ty(), 1, PW)], u8_ty()),
        (IntrinsicOp::Ctlz, vec![], u32_ty()),
        (IntrinsicOp::Bswap, vec![iv(&u16_ty(), 1, PW)], u32_ty()),
        (
            IntrinsicOp::WrappingAdd,
            vec![iv(&u8_ty(), 1, PW), iv(&i8_ty(), 1, PW)],
            u8_ty(),
        ),
        (
            IntrinsicOp::UncheckedShl,
            vec![iv(&u8_ty(), 1, PW), MirValue::Bool(true)],
            u8_ty(),
        ),
        (
            IntrinsicOp::SizeOfVal,
            vec![iv(&usize_ty(), 1, PW)],
            usize_ty(),
        ),
    ] {
        assert!(
            matches!(
                eval_intrinsic(op, &args, &dest, PW),
                Err(RvalueEvalError::TypeMismatch(_))
            ),
            "{op} {args:?} -> {dest:?}"
        );
    }
    // Out-of-width bits are ill formed, never truncated.
    let bad = MirValue::Int {
        bits: 0x100,
        ty: u8_ty(),
    };
    assert_eq!(
        eval_intrinsic(IntrinsicOp::Ctpop, &[bad], &u32_ty(), PW),
        Err(RvalueEvalError::CastEval(
            CastEvalError::InvalidBitPattern {
                target_ty: u8_ty(),
                bits: 0x100
            }
        ))
    );
    // Memory and diverging intrinsics need an evaluation state.
    for op in [
        IntrinsicOp::CopyNonOverlapping,
        IntrinsicOp::WriteBytes,
        IntrinsicOp::UnreachableUnchecked,
        IntrinsicOp::Abort,
        IntrinsicOp::PanicUnwind,
    ] {
        assert!(matches!(
            eval_intrinsic(op, &[], &unit(), PW),
            Err(RvalueEvalError::TypeMismatch(_))
        ));
    }
}

// ---------------------------------------------------------------------------------------------
// Lowering
// ---------------------------------------------------------------------------------------------

#[test]
fn test_lower_terminator_type_checks_intrinsic_calls() {
    let invalid = |op: IntrinsicOp, arg_tys: Vec<Ty>, ret: Ty| match lower_err(
        &intrinsic_fn(op, arg_tys, ret),
        PW,
    ) {
        RvalueLowerError::InvalidTerminator {
            bb: 0,
            error: TerminatorLowerError::InvalidIntrinsicCall { op: o, .. },
        } => assert_eq!(o, op),
        other => panic!("expected InvalidIntrinsicCall for {op}, got {other:?}"),
    };
    let cp_u8 = raw(u8_ty(), Mutability::Not);
    let mp_u8 = raw(u8_ty(), Mutability::Mut);
    invalid(IntrinsicOp::Ctlz, vec![u8_ty(), u8_ty()], u32_ty());
    invalid(IntrinsicOp::Ctlz, vec![Ty::Bool], u32_ty());
    invalid(IntrinsicOp::Ctlz, vec![u8_ty()], u8_ty());
    invalid(IntrinsicOp::Ctpop, vec![Ty::Char], u32_ty());
    invalid(IntrinsicOp::Bitreverse, vec![u8_ty()], u16_ty());
    invalid(IntrinsicOp::WrappingAdd, vec![u8_ty(), u16_ty()], u8_ty());
    invalid(IntrinsicOp::ExactDiv, vec![u8_ty(), u8_ty()], u16_ty());
    invalid(IntrinsicOp::UncheckedShl, vec![u8_ty(), Ty::Bool], u8_ty());
    invalid(IntrinsicOp::UncheckedShr, vec![u8_ty(), u32_ty()], u32_ty());
    invalid(
        IntrinsicOp::ThreeWayCompare,
        vec![Ty::Bool, Ty::Bool],
        i8_ty(),
    );
    invalid(
        IntrinsicOp::ThreeWayCompare,
        vec![u8_ty(), u8_ty()],
        Ty::Bool,
    );
    invalid(IntrinsicOp::UbChecks, vec![u8_ty()], Ty::Bool);
    invalid(IntrinsicOp::UbChecks, vec![], u8_ty());
    invalid(
        IntrinsicOp::ArithOffset,
        vec![cp_u8.clone(), usize_ty()],
        cp_u8.clone(),
    );
    invalid(
        IntrinsicOp::ArithOffset,
        vec![cp_u8.clone(), isize_ty()],
        reference(u8_ty(), Mutability::Not),
    );
    invalid(IntrinsicOp::SizeOfVal, vec![usize_ty()], usize_ty());
    invalid(IntrinsicOp::AlignOfVal, vec![cp_u8.clone()], u32_ty());
    invalid(
        IntrinsicOp::CopyNonOverlapping,
        vec![cp_u8.clone(), cp_u8.clone(), usize_ty()],
        unit(),
    );
    invalid(
        IntrinsicOp::CopyNonOverlapping,
        vec![cp_u8.clone(), raw(u16_ty(), Mutability::Mut), usize_ty()],
        unit(),
    );
    invalid(
        IntrinsicOp::CopyNonOverlapping,
        vec![cp_u8.clone(), mp_u8.clone(), usize_ty()],
        u8_ty(),
    );
    invalid(
        IntrinsicOp::WriteBytes,
        vec![mp_u8.clone(), u16_ty(), usize_ty()],
        unit(),
    );
    invalid(
        IntrinsicOp::WriteBytes,
        vec![cp_u8.clone(), u8_ty(), usize_ty()],
        unit(),
    );
    // Well-typed calls lower, including diverging entry points with arbitrary arguments.
    lower(
        &intrinsic_fn(IntrinsicOp::Ctlz, vec![u8_ty()], u32_ty()),
        PW,
    );
    lower(
        &intrinsic_fn(
            IntrinsicOp::ThreeWayCompare,
            vec![Ty::Char, Ty::Char],
            i8_ty(),
        ),
        PW,
    );
    lower(
        &intrinsic_fn(
            IntrinsicOp::CopyNonOverlapping,
            vec![
                reference(u8_ty(), Mutability::Not),
                mp_u8.clone(),
                usize_ty(),
            ],
            unit(),
        ),
        PW,
    );
    lower(
        &intrinsic_fn(IntrinsicOp::PanicUnwind, vec![u8_ty(), Ty::Bool], unit()),
        PW,
    );
    // A pointee without an exact layout is a layout error, like `NullOp::SizeOf`.
    let unspecified = AdtDef::new_enum(
        "E",
        None,
        vec![
            VariantDef::new("A", vec![u8_ty()]),
            VariantDef::new("B", vec![u32_ty()]),
        ],
    )
    .into_ty();
    assert_eq!(
        lower_err(
            &intrinsic_fn(
                IntrinsicOp::SizeOfVal,
                vec![raw(unspecified.clone(), Mutability::Not)],
                usize_ty()
            ),
            PW
        ),
        RvalueLowerError::UnsupportedLayout(unspecified)
    );
    // Calls of ordinary functions are not checked statically (the callee is linked later).
    lower(
        &mk(
            vec![u8_ty(), Ty::Bool],
            vec![
                blk(
                    vec![],
                    call(callee("f"), vec![mv(1)], 0, Some(1), UnwindAction::Continue),
                ),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
}

// ---------------------------------------------------------------------------------------------
// Intrinsic calls in the control-flow evaluator
// ---------------------------------------------------------------------------------------------

#[test]
fn test_cfg_evaluates_intrinsic_calls_inline_on_both_pointer_widths() {
    for pw in PWS {
        let body = lower(
            &intrinsic_fn(IntrinsicOp::Ctlz, vec![usize_ty()], u32_ty()),
            pw,
        );
        let expected = u128::from(pw.bit_width()) - 5;
        assert_eq!(
            returned(eval_lowered_body_cfg(&body, &[usizev(0x10, pw)], 2)),
            MirValue::unsigned(expected, UintTy::U32, pw)
        );
        // The call handler is never consulted for an intrinsic.
        assert_eq!(
            returned(eval_lowered_body_cfg_with_calls(
                &body,
                &[usizev(0x10, pw)],
                2,
                |_, _, _| { panic!("the call handler must not see intrinsic calls") }
            )),
            MirValue::unsigned(expected, UintTy::U32, pw)
        );
        let body = lower(
            &intrinsic_fn(
                IntrinsicOp::WrappingSub,
                vec![isize_ty(), isize_ty()],
                isize_ty(),
            ),
            pw,
        );
        assert_eq!(
            returned(eval_lowered_body_cfg(
                &body,
                &[isizev(pw.min_isize(), pw), isizev(1, pw)],
                2
            )),
            isizev(pw.max_isize(), pw)
        );
    }
    // UB inside an intrinsic is a terminator error of the calling block.
    let nz = lower(
        &intrinsic_fn(IntrinsicOp::CttzNonzero, vec![u64_ty()], u32_ty()),
        PW,
    );
    assert_eq!(
        term_err(eval_lowered_body_cfg(&nz, &[u64v(0)], 2)),
        (
            0,
            RvalueEvalError::IntrinsicUb {
                op: IntrinsicOp::CttzNonzero,
                reason: "the argument is zero"
            }
        )
    );
    let shl = lower(
        &intrinsic_fn(IntrinsicOp::UncheckedShl, vec![u32_ty(), i8_ty()], u32_ty()),
        PW,
    );
    assert!(matches!(
        term_err(eval_lowered_body_cfg(
            &shl,
            &[u32v(1), MirValue::signed(-1, IntTy::I8, PW)],
            2
        )),
        (0, RvalueEvalError::ShiftOverflow { .. })
    ));
}

#[test]
fn test_cfg_intrinsic_calls_move_arguments_and_require_a_target_to_return() {
    // `_0 = ctlz(move _1) -> bb1; bb1: _0 = Add(copy _0, copy _1)` reads a moved-out local.
    let body = mk(
        vec![u32_ty(), u32_ty()],
        vec![
            blk(
                vec![],
                call(
                    intrinsic(IntrinsicOp::Ctlz),
                    vec![mv(1)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(
                vec![assign(0, Rvalue::BinaryOp(BinOp::Add, cp(0), cp(1)))],
                Terminator::Return,
            ),
        ],
    );
    assert_eq!(
        eval_lowered_body_cfg(&lower(&body, PW), &[u32v(1)], 4),
        Err(CfgEvalError::Statement {
            bb: 1,
            index: 0,
            error: RvalueEvalError::UninitializedLocal(Local(1))
        })
    );
    // A value-returning intrinsic called without a return target must not return.
    let no_target = mk(
        vec![u32_ty(), u32_ty()],
        vec![blk(
            vec![],
            call(
                intrinsic(IntrinsicOp::Ctpop),
                vec![cp(1)],
                0,
                None,
                UnwindAction::Continue,
            ),
        )],
    );
    assert_eq!(
        eval_lowered_body_cfg(&lower(&no_target, PW), &[u32v(3)], 2),
        Err(CfgEvalError::UnreachableReached { bb: 0 })
    );
    // A faulting argument is reported before the destination is checked.
    let mut dead = no_target.clone();
    dead.local_decls.push(u32_ty());
    dead.basic_blocks[0].terminator = Some(call(
        intrinsic(IntrinsicOp::Ctpop),
        vec![cp(2)],
        2,
        Some(0),
        UnwindAction::Continue,
    ));
    assert_eq!(
        term_err(eval_lowered_body_cfg(&lower(&dead, PW), &[u32v(3)], 2)),
        (0, RvalueEvalError::DeadLocal(Local(2)))
    );
    // A hand-built ill-typed intrinsic call is rejected at runtime.
    let hand = LoweredBody {
        local_decls: vec![u8_ty(), u8_ty()],
        basic_blocks: vec![LoweredBasicBlock {
            statements: vec![],
            terminator: Some(LoweredTerminator::Call {
                func: Operand::Constant(intrinsic(IntrinsicOp::Ctlz)),
                func_ty: unit(),
                args: vec![cp(1)],
                arg_tys: vec![u8_ty()],
                destination: place(0),
                dest_ty: u8_ty(),
                target: Some(0),
                unwind: UnwindAction::Continue,
            }),
            is_cleanup: false,
        }],
        ptr_width: PW,
    };
    assert!(matches!(
        term_err(eval_lowered_body_cfg(&hand, &[iv(&u8_ty(), 1, PW)], 2)),
        (0, RvalueEvalError::TypeMismatch(_))
    ));
}

/// `fn() -> () { bb0: _1 = op() -> [target, unwind]; bb1: return; bb2 (cleanup): <cleanup> }`
fn diverging_fn(
    op: IntrinsicOp,
    target: Option<usize>,
    unwind: UnwindAction,
    cleanup: Terminator,
) -> Body {
    mk(
        vec![unit(), if target.is_some() { unit() } else { Ty::Never }],
        vec![
            blk(
                vec![live(1)],
                call(intrinsic(op), vec![], 1, target, unwind),
            ),
            blk(
                vec![assign(0, Rvalue::Use(Operand::Constant(Constant::Unit)))],
                Terminator::Return,
            ),
            cleanup_blk(vec![], cleanup),
        ],
    )
}

#[test]
fn test_cfg_diverging_intrinsics_unreachable_abort_and_panic() {
    let unreachable = diverging_fn(
        IntrinsicOp::UnreachableUnchecked,
        None,
        UnwindAction::Continue,
        Terminator::UnwindResume,
    );
    assert_eq!(
        eval_lowered_body_cfg(&lower(&unreachable, PW), &[], 3),
        Err(CfgEvalError::UnreachableReached { bb: 0 })
    );
    let abort_msg = PanicMessage::Intrinsic(IntrinsicOp::Abort);
    let panic_msg = PanicMessage::Intrinsic(IntrinsicOp::PanicUnwind);
    // `Abort` terminates at once, never entering the cleanup block (one unit of fuel
    // suffices), whatever its `target` and `unwind`.
    for target in [None, Some(1)] {
        for unwind in [
            UnwindAction::Cleanup(2),
            UnwindAction::Continue,
            UnwindAction::Unreachable,
            UnwindAction::Terminate,
        ] {
            let body = diverging_fn(IntrinsicOp::Abort, target, unwind, Terminator::UnwindResume);
            assert_eq!(
                eval_lowered_body_cfg(&lower(&body, PW), &[], 1),
                Ok(CfgEvalOutcome::Terminated {
                    bb: 0,
                    msg: abort_msg.clone()
                })
            );
        }
    }
    // `PanicUnwind` follows the call's unwind action.
    let panic = |unwind: UnwindAction, cleanup: Terminator, fuel: usize| {
        eval_lowered_body_cfg(
            &lower(
                &diverging_fn(IntrinsicOp::PanicUnwind, None, unwind, cleanup),
                PW,
            ),
            &[],
            fuel,
        )
    };
    assert_eq!(
        panic(UnwindAction::Continue, Terminator::UnwindResume, 1),
        Ok(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: panic_msg.clone()
        })
    );
    assert_eq!(
        panic(UnwindAction::Terminate, Terminator::UnwindResume, 1),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: panic_msg.clone()
        })
    );
    assert_eq!(
        panic(UnwindAction::Unreachable, Terminator::UnwindResume, 1),
        Err(CfgEvalError::UnwindIntoUnreachable {
            bb: 0,
            msg: Box::new(panic_msg.clone())
        })
    );
    assert_eq!(
        panic(UnwindAction::Cleanup(2), Terminator::UnwindResume, 2),
        Ok(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: panic_msg.clone()
        })
    );
    assert_eq!(
        panic(UnwindAction::Cleanup(2), Terminator::UnwindTerminate, 2),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: panic_msg.clone()
        })
    );
    assert!(matches!(
        panic(UnwindAction::Cleanup(2), Terminator::UnwindResume, 1),
        Ok(CfgEvalOutcome::OutOfFuel { bb: 2, .. })
    ));
    // A panic raised inside a cleanup block may only terminate.
    let in_cleanup = mk(
        vec![unit(), Ty::Never],
        vec![
            blk(
                vec![live(1)],
                Terminator::Assert {
                    cond: Operand::Constant(Constant::Bool(false)),
                    expected: true,
                    msg: AssertMessage::Custom("first".into()),
                    target: 1,
                    unwind: UnwindAction::Cleanup(2),
                },
            ),
            blk(
                vec![assign(0, Rvalue::Use(Operand::Constant(Constant::Unit)))],
                Terminator::Return,
            ),
            cleanup_blk(
                vec![],
                call(
                    intrinsic(IntrinsicOp::PanicUnwind),
                    vec![],
                    1,
                    None,
                    UnwindAction::Terminate,
                ),
            ),
        ],
    );
    assert_eq!(
        eval_lowered_body_cfg(&lower(&in_cleanup, PW), &[], 3),
        Ok(CfgEvalOutcome::Terminated {
            bb: 2,
            msg: panic_msg
        })
    );
}

// ---------------------------------------------------------------------------------------------
// Memory intrinsics: `copy_nonoverlapping` (call form) and `write_bytes`
// ---------------------------------------------------------------------------------------------

/// `fn(x: u32) -> u32 { _3 = &raw const _1; _4 = &raw mut _2; <copy>(_3, _4, count); _0 = _2 }`
/// with the copy as a call (`as_call`) or as `Statement::CopyNonOverlapping`; `src`/`dst`
/// override the pointer operands.
fn copy_body(as_call: bool, src: Operand, dst: Operand, count: Operand) -> Body {
    let decls = vec![
        u32_ty(),
        u32_ty(),
        u32_ty(),
        raw(u32_ty(), Mutability::Not),
        raw(u32_ty(), Mutability::Mut),
        unit(),
    ];
    let mut stmts = vec![
        live(2),
        live(3),
        live(4),
        live(5),
        assign(3, Rvalue::RawPtr(Mutability::Not, place(1))),
        assign(4, Rvalue::RawPtr(Mutability::Mut, place(2))),
    ];
    let first = if as_call {
        blk(
            stmts,
            call(
                intrinsic(IntrinsicOp::CopyNonOverlapping),
                vec![src, dst, count],
                5,
                Some(1),
                UnwindAction::Continue,
            ),
        )
    } else {
        stmts.push(Statement::CopyNonOverlapping { src, dst, count });
        blk(stmts, Terminator::Goto { target: 1 })
    };
    mk(
        decls,
        vec![
            first,
            blk(vec![assign(0, Rvalue::Use(cp(2)))], Terminator::Return),
        ],
    )
}

#[test]
fn test_copy_nonoverlapping_call_form_matches_the_statement_form() {
    let ptr = |addr: u64, alloc: u64, m: Mutability| {
        Operand::Constant(Constant::Ptr(
            PointerValue::with_provenance(addr, alloc, 1),
            raw(u32_ty(), m),
        ))
    };
    let count = |n: u128| cst(n, usize_ty());
    let cases: Vec<(Operand, Operand, Operand)> = vec![
        (cp(3), cp(4), count(1)),
        (cp(3), cp(4), count(0)),
        (ptr(0, 9, Mutability::Not), cp(4), count(0)),
        (cp(3), ptr(0, 9, Mutability::Mut), count(1)),
        (ptr(0x1001, 9, Mutability::Not), cp(4), count(0)),
        (cp(3), cp(4), count(u128::from(u64::MAX >> 2))),
        (
            ptr(0x1000, 2, Mutability::Not),
            ptr(0x1002, 2, Mutability::Mut),
            count(0),
        ),
        (
            ptr(0x2000, 7, Mutability::Not),
            ptr(0x2000, 7, Mutability::Mut),
            count(1),
        ),
        (cp(3), cp(4), count(2)),
    ];
    for (src, dst, n) in cases {
        let via_call = eval_lowered_body_cfg(
            &lower(&copy_body(true, src.clone(), dst.clone(), n.clone()), PW),
            &[u32v(0xDEAD)],
            4,
        );
        let via_stmt = eval_lowered_body_cfg(
            &lower(&copy_body(false, src.clone(), dst.clone(), n.clone()), PW),
            &[u32v(0xDEAD)],
            4,
        );
        let normalize = |r: Result<CfgEvalOutcome, CfgEvalError>| match r {
            Ok(outcome) => Ok(outcome),
            Err(CfgEvalError::Terminator { error, .. } | CfgEvalError::Statement { error, .. }) => {
                Err(error)
            }
            Err(other) => panic!("unexpected error {other:?}"),
        };
        assert_eq!(
            normalize(via_call),
            normalize(via_stmt),
            "{src:?} {dst:?} {n:?}"
        );
    }
    assert_eq!(
        returned(eval_lowered_body_cfg(
            &lower(&copy_body(true, cp(3), cp(4), count(1)), PW),
            &[u32v(0xDEAD)],
            4
        )),
        u32v(0xDEAD)
    );
    assert_eq!(
        term_err(eval_lowered_body_cfg(
            &lower(
                &copy_body(true, ptr(0, 9, Mutability::Not), cp(4), count(0)),
                PW
            ),
            &[u32v(1)],
            4
        )),
        (0, RvalueEvalError::NullPointerAccess)
    );
    assert!(matches!(
        term_err(eval_lowered_body_cfg(
            &lower(
                &copy_body(
                    true,
                    ptr(0x2000, 7, Mutability::Not),
                    ptr(0x2000, 7, Mutability::Mut),
                    count(1)
                ),
                PW
            ),
            &[u32v(1)],
            4
        )),
        (0, RvalueEvalError::CopyNonOverlappingOverlap { .. })
    ));
}

/// `fn(init: T) -> T { _2 = init; _3 = &raw mut _2 (or of `dst_proj`); write_bytes(_3, val, count); _0 = _2 }`
fn write_bytes_body(
    local_ty: Ty,
    elem_ty: Ty,
    dst_proj: Vec<ProjectionElem>,
    val: u128,
    count: Operand,
) -> Body {
    let decls = vec![
        local_ty.clone(),
        local_ty,
        raw(elem_ty, Mutability::Mut),
        unit(),
    ];
    mk(
        decls,
        vec![
            blk(
                vec![
                    live(2),
                    live(3),
                    assign(
                        2,
                        Rvalue::RawPtr(Mutability::Mut, Place::with_projection(1, dst_proj)),
                    ),
                ],
                call(
                    intrinsic(IntrinsicOp::WriteBytes),
                    vec![cp(2), cst(val, u8_ty()), count],
                    3,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![assign(0, Rvalue::Use(cp(1)))], Terminator::Return),
        ],
    )
}

#[test]
fn test_write_bytes_sets_every_byte_of_the_written_elements() {
    let count = |n: u128| cst(n, usize_ty());
    for pw in PWS {
        let run = |local_ty: Ty,
                   elem_ty: Ty,
                   proj: Vec<ProjectionElem>,
                   val: u128,
                   n: u128,
                   init: MirValue| {
            eval_lowered_body_cfg(
                &lower(
                    &write_bytes_body(local_ty, elem_ty, proj, val, count(n)),
                    pw,
                ),
                &[init],
                4,
            )
        };
        assert_eq!(
            returned(run(
                u32_ty(),
                u32_ty(),
                vec![],
                0xAB,
                1,
                iv(&u32_ty(), 7, pw)
            )),
            iv(&u32_ty(), 0xABAB_ABAB, pw)
        );
        assert_eq!(
            returned(run(usize_ty(), usize_ty(), vec![], 0xFF, 1, usizev(0, pw))),
            usizev(pw.max_usize(), pw)
        );
        assert_eq!(
            returned(run(Ty::Bool, Ty::Bool, vec![], 1, 1, MirValue::Bool(false))),
            MirValue::Bool(true)
        );
        // A zero count writes nothing.
        assert_eq!(
            returned(run(
                u32_ty(),
                u32_ty(),
                vec![],
                0xAB,
                0,
                iv(&u32_ty(), 7, pw)
            )),
            iv(&u32_ty(), 7, pw)
        );
        // Array windows: elements `1..3` of `[u16; 4]`, and the whole array.
        let arr = Ty::Array(Box::new(u16_ty()), 4);
        let arr_val = |e: [u128; 4]| MirValue::Array {
            elements: e.iter().map(|b| iv(&u16_ty(), *b, pw)).collect(),
            elem_ty: u16_ty(),
        };
        let elem = |i: u64| {
            vec![ProjectionElem::ConstantIndex {
                offset: i,
                min_length: 4,
                from_end: false,
            }]
        };
        assert_eq!(
            returned(run(
                arr.clone(),
                u16_ty(),
                elem(1),
                0x11,
                2,
                arr_val([1, 2, 3, 4])
            )),
            arr_val([1, 0x1111, 0x1111, 4])
        );
        assert_eq!(
            returned(run(
                arr.clone(),
                u16_ty(),
                elem(0),
                0x22,
                4,
                arr_val([1, 2, 3, 4])
            )),
            arr_val([0x2222; 4])
        );
        assert_eq!(
            returned(run(
                arr.clone(),
                u16_ty(),
                elem(3),
                0x33,
                1,
                arr_val([1, 2, 3, 4])
            )),
            arr_val([1, 2, 3, 0x3333])
        );
        // Past the end of the array: not a resolvable window (no byte-level memory).
        assert!(matches!(
            term_err(run(
                arr.clone(),
                u16_ty(),
                elem(3),
                0x33,
                2,
                arr_val([1, 2, 3, 4])
            )),
            (0, RvalueEvalError::UnsupportedMemoryAccess(_))
        ));
        // Bytes that are no valid value cannot be stored: `bool` from `2`, a null `&T`.
        assert!(matches!(
            term_err(run(Ty::Bool, Ty::Bool, vec![], 2, 1, MirValue::Bool(false))),
            (0, RvalueEvalError::UnsupportedMemoryAccess(_))
        ));
        let r = reference(u8_ty(), Mutability::Not);
        let r_val = MirValue::ptr(PointerValue::with_provenance(0x10, 77, 0), r.clone());
        assert!(matches!(
            term_err(run(r.clone(), r.clone(), vec![], 0, 1, r_val)),
            (0, RvalueEvalError::UnsupportedMemoryAccess(_))
        ));
        // Raw pointers decode without provenance.
        let p = raw(u8_ty(), Mutability::Not);
        let p_val = MirValue::ptr(PointerValue::with_provenance(0x10, 77, 0), p.clone());
        assert_eq!(
            returned(run(p.clone(), p.clone(), vec![], 0, 1, p_val)),
            MirValue::ptr(PointerValue::without_provenance(0), p)
        );
    }
}

#[test]
fn test_write_bytes_checks_alignment_even_for_empty_writes_and_validity_for_non_empty_ones() {
    let mp = raw(u32_ty(), Mutability::Mut);
    let wb = |dst: PointerValue, n: u128| {
        let body = mk(
            vec![unit(), mp.clone()],
            vec![
                blk(
                    vec![],
                    call(
                        intrinsic(IntrinsicOp::WriteBytes),
                        vec![cp(1), cst(0, u8_ty()), cst(n, usize_ty())],
                        0,
                        Some(1),
                        UnwindAction::Continue,
                    ),
                ),
                blk(vec![], Terminator::Return),
            ],
        );
        eval_lowered_body_cfg(&lower(&body, PW), &[MirValue::ptr(dst, mp.clone())], 4)
    };
    let p = |addr: u64| PointerValue::with_provenance(addr, 1000, 0);
    // Every (aligned) pointer, even null, is valid for a zero-byte write (A1); a non-empty
    // write through null is UB.
    assert_eq!(returned(wb(p(0), 0)), MirValue::Unit);
    assert_eq!(
        returned(wb(PointerValue::without_provenance(0), 0)),
        MirValue::Unit
    );
    assert_eq!(
        term_err(wb(p(0), 1)),
        (0, RvalueEvalError::NullPointerAccess)
    );
    assert_eq!(
        term_err(wb(p(0x1002), 0)),
        (
            0,
            RvalueEvalError::MisalignedPointer {
                addr: 0x1002,
                required_align: 4
            }
        )
    );
    assert_eq!(returned(wb(p(0x1000), 0)), MirValue::Unit);
    assert_eq!(
        term_err(wb(p(0x1000), 1u128 << 62)),
        (
            0,
            RvalueEvalError::CopyLengthOverflow {
                count: 1 << 62,
                elem_size: 4
            }
        )
    );
    assert_eq!(
        term_err(wb(p(u64::MAX - 3), 2)),
        (
            0,
            RvalueEvalError::PointerRangeOverflow {
                addr: u64::MAX - 3,
                byte_len: 8
            }
        )
    );
    // An unresolvable non-empty write is unsupported, never guessed.
    assert!(matches!(
        term_err(wb(p(0x1000), 1)),
        (0, RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
    // Zero-sized elements access no memory: any non-null pointer is fine.
    let zp = raw(unit(), Mutability::Mut);
    let zst = mk(
        vec![unit(), zp.clone()],
        vec![
            blk(
                vec![],
                call(
                    intrinsic(IntrinsicOp::WriteBytes),
                    vec![cp(1), cst(0xFF, u8_ty()), cst(5, usize_ty())],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    assert_eq!(
        returned(eval_lowered_body_cfg(
            &lower(&zst, PW),
            &[MirValue::ptr(PointerValue::without_provenance(8), zp)],
            4
        )),
        MirValue::Unit
    );
    // A write into a storage-dead local is UB.
    let dead = mk(
        vec![unit(), u32_ty(), mp.clone()],
        vec![
            blk(
                vec![
                    live(1),
                    live(2),
                    assign(2, Rvalue::RawPtr(Mutability::Mut, place(1))),
                    Statement::StorageDead(Local(1)),
                ],
                call(
                    intrinsic(IntrinsicOp::WriteBytes),
                    vec![cp(2), cst(0, u8_ty()), cst(1, usize_ty())],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    assert_eq!(
        term_err(eval_lowered_body_cfg(&lower(&dead, PW), &[], 4)),
        (0, RvalueEvalError::DeadLocal(Local(1)))
    );
}

// ---------------------------------------------------------------------------------------------
// Multi-callee `CallTable`
// ---------------------------------------------------------------------------------------------

/// `fn double(x: u32) -> u32 { x + x }`
fn double_fn() -> Body {
    mk(
        vec![u32_ty(), u32_ty()],
        vec![blk(
            vec![assign(0, Rvalue::BinaryOp(BinOp::Add, cp(1), cp(1)))],
            Terminator::Return,
        )],
    )
}

/// `fn inc_double(x: u32) -> u32 { double(x + 1) }`
fn inc_double_fn() -> Body {
    mk(
        vec![u32_ty(), u32_ty(), u32_ty()],
        vec![
            blk(
                vec![
                    live(2),
                    assign(2, Rvalue::BinaryOp(BinOp::Add, cp(1), cst(1, u32_ty()))),
                ],
                call(
                    callee("double"),
                    vec![mv(2)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    )
}

/// `fn main(x: u32) -> u32 { _2 = <callee>(copy _1) -> [bb1, unwind]; bb1: _0 = _2; bb2: cleanup }`
fn main_fn(
    callee_name: &str,
    target: Option<usize>,
    unwind: UnwindAction,
    cleanup: Terminator,
) -> Body {
    mk(
        vec![u32_ty(), u32_ty(), u32_ty()],
        vec![
            blk(
                vec![live(2)],
                call(callee(callee_name), vec![cp(1)], 2, target, unwind),
            ),
            blk(vec![assign(0, Rvalue::Use(cp(2)))], Terminator::Return),
            cleanup_blk(vec![], cleanup),
        ],
    )
}

fn table(pw: PtrWidth) -> CallTable {
    CallTable::new()
        .with_callee("double", 1, lower(&double_fn(), pw))
        .with_callee("inc_double", 1, lower(&inc_double_fn(), pw))
}

#[test]
fn test_call_table_runs_two_deep_call_chains_with_shared_fuel() {
    for pw in PWS {
        let table = table(pw);
        let main = lower(
            &main_fn(
                "inc_double",
                Some(1),
                UnwindAction::Continue,
                Terminator::UnwindResume,
            ),
            pw,
        );
        // main.bb0 -> inc_double.bb0 -> double.bb0 -> inc_double.bb1 -> main.bb1: five blocks.
        assert_eq!(
            returned(eval_lowered_body_cfg_with_call_table(
                &main,
                &[iv(&u32_ty(), 20, pw)],
                5,
                &table
            )),
            iv(&u32_ty(), 42, pw)
        );
        // With four units, the callees complete and main is out of fuel at its return block.
        match eval_lowered_body_cfg_with_call_table(&main, &[iv(&u32_ty(), 20, pw)], 4, &table) {
            Ok(CfgEvalOutcome::OutOfFuel { bb: 1, state }) => {
                assert_eq!(state.slots[2], LocalSlotState::Init(iv(&u32_ty(), 42, pw)));
                assert_eq!(
                    returned(eval_cfg_in_state_with_call_table(
                        &main, state, 1, 1, &table, None
                    )),
                    iv(&u32_ty(), 42, pw)
                );
            }
            other => panic!("expected OutOfFuel at main.bb1, got {other:?}"),
        }
        // Out of fuel inside a callee: main's calling block with main's state on entry to it,
        // from which the evaluation resumes (re-running the call).
        for fuel in 1..=3 {
            match eval_lowered_body_cfg_with_call_table(
                &main,
                &[iv(&u32_ty(), 20, pw)],
                fuel,
                &table,
            ) {
                Ok(CfgEvalOutcome::OutOfFuel { bb: 0, state }) => {
                    let entry =
                        StatementEvalState::from_body(&main, &[iv(&u32_ty(), 20, pw)]).unwrap();
                    assert_eq!(state, entry);
                    assert_eq!(
                        returned(eval_cfg_in_state_with_call_table(
                            &main, state, 0, 5, &table, None
                        )),
                        iv(&u32_ty(), 42, pw)
                    );
                }
                other => panic!("expected OutOfFuel at main.bb0 with fuel {fuel}, got {other:?}"),
            }
        }
        assert!(matches!(
            eval_lowered_body_cfg_with_call_table(&main, &[iv(&u32_ty(), 20, pw)], 0, &table),
            Ok(CfgEvalOutcome::OutOfFuel { bb: 0, .. })
        ));
    }
}

#[test]
fn test_call_table_propagates_callee_panics_through_caller_unwind_actions() {
    // `fn boom(x: u32) -> u32 { panic() }`
    let boom = mk(
        vec![u32_ty(), u32_ty(), Ty::Never],
        vec![blk(
            vec![live(2)],
            call(
                intrinsic(IntrinsicOp::PanicUnwind),
                vec![],
                2,
                None,
                UnwindAction::Continue,
            ),
        )],
    );
    let table = CallTable::new().with_callee("boom", 1, lower(&boom, PW));
    let msg = PanicMessage::Intrinsic(IntrinsicOp::PanicUnwind);
    let run = |unwind: UnwindAction, cleanup: Terminator, fuel: usize| {
        eval_lowered_body_cfg_with_call_table(
            &lower(&main_fn("boom", Some(1), unwind, cleanup), PW),
            &[u32v(1)],
            fuel,
            &table,
        )
    };
    // Caught by the caller's cleanup block (main.bb0, boom.bb0, main.bb2).
    assert_eq!(
        run(UnwindAction::Cleanup(2), Terminator::UnwindResume, 3),
        Ok(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: msg.clone()
        })
    );
    assert!(matches!(
        run(UnwindAction::Cleanup(2), Terminator::UnwindResume, 2),
        Ok(CfgEvalOutcome::OutOfFuel { bb: 2, .. })
    ));
    assert_eq!(
        run(UnwindAction::Cleanup(2), Terminator::UnwindTerminate, 3),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: msg.clone()
        })
    );
    assert_eq!(
        run(UnwindAction::Continue, Terminator::UnwindResume, 2),
        Ok(CfgEvalOutcome::Panicked {
            bb: 0,
            msg: msg.clone()
        })
    );
    assert_eq!(
        run(UnwindAction::Terminate, Terminator::UnwindResume, 2),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: msg.clone()
        })
    );
    assert_eq!(
        run(UnwindAction::Unreachable, Terminator::UnwindResume, 2),
        Err(CfgEvalError::UnwindIntoUnreachable {
            bb: 0,
            msg: Box::new(msg.clone())
        })
    );
    // Through two frames: `relay` calls `boom` with `Continue`, so the panic reaches main.
    let relay = mk(
        vec![u32_ty(), u32_ty()],
        vec![
            blk(
                vec![],
                call(
                    callee("boom"),
                    vec![cp(1)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    let table = table.with_callee("relay", 1, lower(&relay, PW));
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(
            &lower(
                &main_fn(
                    "relay",
                    Some(1),
                    UnwindAction::Cleanup(2),
                    Terminator::UnwindResume
                ),
                PW
            ),
            &[u32v(1)],
            4,
            &table
        ),
        Ok(CfgEvalOutcome::Panicked { bb: 0, msg })
    );
}

#[test]
fn test_call_table_callee_aborts_bypass_caller_cleanup_and_errors_carry_the_call_stack() {
    // `fn die(x) -> u32 { abort() }`, `fn ub(x) -> u32 { unreachable_unchecked() }`.
    let diverge = |op: IntrinsicOp| {
        mk(
            vec![u32_ty(), u32_ty(), Ty::Never],
            vec![blk(
                vec![live(2)],
                call(intrinsic(op), vec![], 2, None, UnwindAction::Continue),
            )],
        )
    };
    let relay_to = |name: &str| {
        mk(
            vec![u32_ty(), u32_ty()],
            vec![
                blk(
                    vec![],
                    call(
                        callee(name),
                        vec![cp(1)],
                        0,
                        Some(1),
                        UnwindAction::Continue,
                    ),
                ),
                blk(vec![], Terminator::Return),
            ],
        )
    };
    let table = CallTable::new()
        .with_callee("die", 1, lower(&diverge(IntrinsicOp::Abort), PW))
        .with_callee(
            "ub",
            1,
            lower(&diverge(IntrinsicOp::UnreachableUnchecked), PW),
        )
        .with_callee("relay_ub", 1, lower(&relay_to("ub"), PW));
    // Two units of fuel suffice: the caller's cleanup block never runs.
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(
            &lower(
                &main_fn(
                    "die",
                    Some(1),
                    UnwindAction::Cleanup(2),
                    Terminator::UnwindResume
                ),
                PW
            ),
            &[u32v(1)],
            2,
            &table
        ),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: PanicMessage::Intrinsic(IntrinsicOp::Abort)
        })
    );
    let site = |name: &str, bb: usize| CallSite {
        bb,
        callee: CalleeSymbol::new(name),
    };
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(
            &lower(
                &main_fn(
                    "ub",
                    Some(1),
                    UnwindAction::Cleanup(2),
                    Terminator::UnwindResume
                ),
                PW
            ),
            &[u32v(1)],
            8,
            &table
        ),
        Err(CfgEvalError::InCallee {
            call_stack: vec![site("ub", 0)],
            error: Box::new(CfgEvalError::UnreachableReached { bb: 0 }),
        })
    );
    let err = eval_lowered_body_cfg_with_call_table(
        &lower(
            &main_fn(
                "relay_ub",
                Some(1),
                UnwindAction::Continue,
                Terminator::UnwindResume,
            ),
            PW,
        ),
        &[u32v(1)],
        8,
        &table,
    )
    .unwrap_err();
    assert_eq!(
        err,
        CfgEvalError::InCallee {
            call_stack: vec![site("relay_ub", 0), site("ub", 0)],
            error: Box::new(CfgEvalError::UnreachableReached { bb: 0 }),
        }
    );
    assert!(err.to_string().contains("`relay_ub`") && err.to_string().contains("`ub`"));
}

/// `fn fact(n: u64) -> u64 { if n == 0 { 1 } else { n * fact(n - 1) } }`
fn fact_fn() -> Body {
    mk(
        vec![u64_ty(), u64_ty(), Ty::Bool, u64_ty(), u64_ty()],
        vec![
            blk(
                vec![
                    live(2),
                    assign(2, Rvalue::BinaryOp(BinOp::Eq, cp(1), cst(0, u64_ty()))),
                ],
                Terminator::SwitchInt {
                    discr: mv(2),
                    targets: SwitchTargets::static_if(1, 1, 2),
                },
            ),
            blk(
                vec![assign(0, Rvalue::Use(cst(1, u64_ty())))],
                Terminator::Return,
            ),
            blk(
                vec![
                    live(3),
                    live(4),
                    assign(3, Rvalue::BinaryOp(BinOp::Sub, cp(1), cst(1, u64_ty()))),
                ],
                call(
                    callee("fact"),
                    vec![mv(3)],
                    4,
                    Some(3),
                    UnwindAction::Continue,
                ),
            ),
            blk(
                vec![assign(0, Rvalue::BinaryOp(BinOp::Mul, cp(1), cp(4)))],
                Terminator::Return,
            ),
        ],
    )
}

/// `fn is_even(n: u32) -> bool { n == 0 || is_odd(n - 1) }` (and `is_odd` symmetrically).
fn parity_fn(other: &str, base: bool) -> Body {
    mk(
        vec![Ty::Bool, u32_ty(), Ty::Bool, u32_ty()],
        vec![
            blk(
                vec![
                    live(2),
                    assign(2, Rvalue::BinaryOp(BinOp::Eq, cp(1), cst(0, u32_ty()))),
                ],
                Terminator::SwitchInt {
                    discr: mv(2),
                    targets: SwitchTargets::static_if(1, 1, 2),
                },
            ),
            blk(
                vec![assign(
                    0,
                    Rvalue::Use(Operand::Constant(Constant::Bool(base))),
                )],
                Terminator::Return,
            ),
            blk(
                vec![
                    live(3),
                    assign(3, Rvalue::BinaryOp(BinOp::Sub, cp(1), cst(1, u32_ty()))),
                ],
                call(
                    callee(other),
                    vec![mv(3)],
                    0,
                    Some(3),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    )
}

#[test]
fn test_call_table_supports_self_and_mutual_recursion_within_the_depth_bound() {
    let fact = lower(&fact_fn(), PW);
    let table = CallTable::new().with_callee("fact", 1, fact.clone());
    assert_eq!(table.max_call_depth(), DEFAULT_MAX_CALL_DEPTH);
    assert_eq!(
        returned(eval_lowered_body_cfg_with_call_table(
            &fact,
            &[u64v(5)],
            100,
            &table
        )),
        u64v(120)
    );
    assert_eq!(
        returned(eval_lowered_body_cfg_with_call_table(
            &fact,
            &[u64v(20)],
            1000,
            &table
        )),
        u64v(2_432_902_008_176_640_000)
    );
    // `fact(5)` needs five nested callee frames.
    let shallow = table.clone().with_max_call_depth(5);
    assert_eq!(
        returned(eval_lowered_body_cfg_with_call_table(
            &fact,
            &[u64v(5)],
            100,
            &shallow
        )),
        u64v(120)
    );
    let too_shallow = table.clone().with_max_call_depth(4);
    match eval_lowered_body_cfg_with_call_table(&fact, &[u64v(5)], 100, &too_shallow) {
        Err(CfgEvalError::InCallee { call_stack, error }) => {
            assert_eq!(call_stack.len(), 4);
            assert!(
                call_stack
                    .iter()
                    .all(|s| s.bb == 2 && s.callee.as_str() == "fact")
            );
            assert_eq!(
                *error,
                CfgEvalError::CallDepthExceeded {
                    bb: 2,
                    max_call_depth: 4
                }
            );
        }
        other => panic!("expected CallDepthExceeded, got {other:?}"),
    }
    // A depth of zero forbids linked calls altogether.
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(
            &fact,
            &[u64v(5)],
            100,
            &table.clone().with_max_call_depth(0)
        ),
        Err(CfgEvalError::CallDepthExceeded {
            bb: 2,
            max_call_depth: 0
        })
    );
    let parity = CallTable::new()
        .with_callee("is_even", 1, lower(&parity_fn("is_odd", true), PW))
        .with_callee("is_odd", 1, lower(&parity_fn("is_even", false), PW));
    let is_even = parity
        .get(&CalleeSymbol::new("is_even"))
        .unwrap()
        .body
        .clone();
    for n in 0..12u128 {
        assert_eq!(
            returned(eval_lowered_body_cfg_with_call_table(
                &is_even,
                &[u32v(n)],
                1000,
                &parity
            )),
            MirValue::Bool(n % 2 == 0)
        );
    }
}

#[test]
fn test_call_table_unbounded_recursion_ends_deterministically_without_stack_overflow() {
    // `fn spin() { spin() }`
    let spin = lower(
        &mk(
            vec![unit()],
            vec![
                blk(
                    vec![],
                    call(callee("spin"), vec![], 0, Some(1), UnwindAction::Continue),
                ),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
    let table = CallTable::new()
        .with_callee("spin", 0, spin.clone())
        .with_max_call_depth(20_000);
    match eval_lowered_body_cfg_with_call_table(&spin, &[], 1_000_000, &table) {
        Err(CfgEvalError::InCallee { call_stack, error }) => {
            assert_eq!(call_stack.len(), 20_000);
            assert_eq!(
                *error,
                CfgEvalError::CallDepthExceeded {
                    bb: 0,
                    max_call_depth: 20_000
                }
            );
        }
        other => panic!("expected CallDepthExceeded, got {other:?}"),
    }
    // Shared fuel bounds the whole call tree first when it is smaller.
    match eval_lowered_body_cfg_with_call_table(&spin, &[], 5_000, &table) {
        Ok(CfgEvalOutcome::OutOfFuel { bb: 0, state }) => {
            assert_eq!(state, StatementEvalState::from_body(&spin, &[]).unwrap());
        }
        other => panic!("expected OutOfFuel, got {other:?}"),
    }
}

#[test]
fn test_call_table_validates_linkage_and_isolates_frames() {
    let table = table(PW);
    let run_main = |body: &Body, args: &[MirValue], table: &CallTable| {
        eval_lowered_body_cfg_with_call_table(&lower(body, PW), args, 16, table)
    };
    // Unlinked symbols (without a handler); with a handler, the handler decides.
    let unknown = main_fn(
        "nope",
        Some(1),
        UnwindAction::Continue,
        Terminator::UnwindResume,
    );
    assert_eq!(
        run_main(&unknown, &[u32v(1)], &table),
        Err(CfgEvalError::UnknownCallee {
            bb: 0,
            callee: CalleeSymbol::new("nope")
        })
    );
    let lowered_unknown = lower(&unknown, PW);
    let state = StatementEvalState::from_body(&lowered_unknown, &[u32v(1)]).unwrap();
    let mut handler = |bb: usize, func: &MirValue, args: &[MirValue]| {
        assert_eq!((bb, func, args), (0, &MirValue::Unit, &[u32v(1)][..]));
        Ok(CallOutcome::Return(u32v(9)))
    };
    assert_eq!(
        returned(eval_cfg_in_state_with_call_table(
            &lowered_unknown,
            state,
            0,
            4,
            &table,
            Some(&mut handler)
        )),
        u32v(9)
    );
    // Without a table, a symbol call is an unsupported call (unchanged behavior).
    assert_eq!(
        eval_lowered_body_cfg(
            &lower(
                &main_fn(
                    "double",
                    Some(1),
                    UnwindAction::Continue,
                    Terminator::UnwindResume
                ),
                PW
            ),
            &[u32v(1)],
            4
        ),
        Err(CfgEvalError::UnsupportedCall { bb: 0 })
    );
    // Argument count, argument type, return type, and pointer width must match the callee.
    let call_double = |args: Vec<Operand>, dest_ty: Ty| {
        mk(
            vec![unit(), u32_ty(), u64_ty(), dest_ty],
            vec![
                blk(
                    vec![live(3)],
                    call(callee("double"), args, 3, Some(1), UnwindAction::Continue),
                ),
                blk(
                    vec![assign(0, Rvalue::Use(Operand::Constant(Constant::Unit)))],
                    Terminator::Return,
                ),
            ],
        )
    };
    for body in [
        call_double(vec![cp(1), cp(1)], u32_ty()),
        call_double(vec![cp(2)], u32_ty()),
        call_double(vec![cp(1)], u64_ty()),
    ] {
        assert!(matches!(
            term_err(run_main(&body, &[u32v(1), u64v(1)], &table)),
            (0, RvalueEvalError::TypeMismatch(_))
        ));
    }
    let narrow = CallTable::new().with_callee("double", 1, lower(&double_fn(), PtrWidth::Bits32));
    assert!(matches!(
        term_err(run_main(
            &call_double(vec![cp(1)], u32_ty()),
            &[u32v(1), u64v(1)],
            &narrow
        )),
        (0, RvalueEvalError::TypeMismatch(_))
    ));
    // A diverging call (no target) of a callee that returns is UB in the caller.
    assert_eq!(
        run_main(
            &main_fn(
                "double",
                None,
                UnwindAction::Continue,
                Terminator::UnwindResume
            ),
            &[u32v(1)],
            &table
        ),
        Err(CfgEvalError::UnreachableReached { bb: 0 })
    );
    // A moved argument is deinitialized in the caller.
    let moved = mk(
        vec![u32_ty(), u32_ty()],
        vec![
            blk(
                vec![],
                call(
                    callee("double"),
                    vec![mv(1)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(
                vec![assign(0, Rvalue::BinaryOp(BinOp::Add, cp(0), cp(1)))],
                Terminator::Return,
            ),
        ],
    );
    assert_eq!(
        run_main(&moved, &[u32v(1)], &table),
        Err(CfgEvalError::Statement {
            bb: 1,
            index: 0,
            error: RvalueEvalError::UninitializedLocal(Local(1))
        })
    );
    // A callee without an entry block.
    let empty = CallTable::new().with_callee(
        "double",
        1,
        LoweredBody {
            local_decls: vec![u32_ty(), u32_ty()],
            basic_blocks: vec![],
            ptr_width: PW,
        },
    );
    assert_eq!(
        run_main(
            &main_fn(
                "double",
                Some(1),
                UnwindAction::Continue,
                Terminator::UnwindResume
            ),
            &[u32v(1)],
            &empty
        ),
        Err(CfgEvalError::InCallee {
            call_stack: vec![CallSite {
                bb: 0,
                callee: CalleeSymbol::new("double")
            }],
            error: Box::new(CfgEvalError::InvalidBlock { bb: 0 }),
        })
    );
}

#[test]
fn test_call_table_rejects_frame_local_pointers_crossing_call_boundaries() {
    let cp_u32 = raw(u32_ty(), Mutability::Not);
    // `fn id(p: *const u32) -> *const u32 { p }`
    let id = mk(
        vec![cp_u32.clone(), cp_u32.clone()],
        vec![blk(vec![assign(0, Rvalue::Use(cp(1)))], Terminator::Return)],
    );
    // `fn leak() -> *const u32 { let x = 5; &raw const x }`
    let leak = mk(
        vec![cp_u32.clone(), u32_ty()],
        vec![blk(
            vec![
                live(1),
                assign(1, Rvalue::Use(cst(5, u32_ty()))),
                assign(0, Rvalue::RawPtr(Mutability::Not, place(1))),
            ],
            Terminator::Return,
        )],
    );
    let table = CallTable::new()
        .with_callee("id", 1, lower(&id, PW))
        .with_callee("leak", 0, lower(&leak, PW));
    // `main(x: u32) -> *const u32 { _2 = &raw const _1; _0 = id(_2) }`
    let pass_local = mk(
        vec![cp_u32.clone(), u32_ty(), cp_u32.clone()],
        vec![
            blk(
                vec![
                    live(2),
                    assign(2, Rvalue::RawPtr(Mutability::Not, place(1))),
                ],
                call(
                    callee("id"),
                    vec![cp(2)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    assert!(matches!(
        term_err(eval_lowered_body_cfg_with_call_table(
            &lower(&pass_local, PW),
            &[u32v(1)],
            8,
            &table
        )),
        (0, RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
    // A returned pointer into the callee's (dead) frame is rejected in the caller.
    let call_leak = mk(
        vec![cp_u32.clone(), u32_ty()],
        vec![
            blk(
                vec![],
                call(callee("leak"), vec![], 0, Some(1), UnwindAction::Continue),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    assert!(matches!(
        term_err(eval_lowered_body_cfg_with_call_table(
            &lower(&call_leak, PW),
            &[u32v(1)],
            8,
            &table
        )),
        (0, RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
    // Pointers without provenance, or with provenance naming no frame-local allocation, cross.
    let pass_arg = mk(
        vec![cp_u32.clone(), cp_u32.clone()],
        vec![
            blk(
                vec![],
                call(
                    callee("id"),
                    vec![cp(1)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    for ptr in [
        PointerValue::without_provenance(0x40),
        PointerValue::with_provenance(0x40, 1000, 3),
    ] {
        let p = MirValue::ptr(ptr, cp_u32.clone());
        assert_eq!(
            returned(eval_lowered_body_cfg_with_call_table(
                &lower(&pass_arg, PW),
                std::slice::from_ref(&p),
                8,
                &table
            )),
            p
        );
    }
    // Provenance naming a local of either frame is rejected, even if foreign to the caller.
    let p = MirValue::ptr(PointerValue::with_provenance(0x40, 2, 0), cp_u32.clone());
    assert!(matches!(
        term_err(eval_lowered_body_cfg_with_call_table(
            &lower(&pass_arg, PW),
            &[p],
            8,
            &table
        )),
        (0, RvalueEvalError::UnsupportedMemoryAccess(_))
    ));
}

#[test]
fn test_call_table_callee_frames_inherit_ub_checks_and_run_intrinsics() {
    // `fn checks() -> bool { ub_checks() }`, `fn lz(x: u64) -> u32 { ctlz(x) }`
    let checks = mk(
        vec![Ty::Bool],
        vec![
            blk(
                vec![],
                call(
                    intrinsic(IntrinsicOp::UbChecks),
                    vec![],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    let table = CallTable::new()
        .with_callee("checks", 0, lower(&checks, PW))
        .with_callee(
            "lz",
            1,
            lower(
                &intrinsic_fn(IntrinsicOp::Ctlz, vec![u64_ty()], u32_ty()),
                PW,
            ),
        );
    let main = lower(
        &mk(
            vec![Ty::Bool],
            vec![
                blk(
                    vec![],
                    call(callee("checks"), vec![], 0, Some(1), UnwindAction::Continue),
                ),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
    for ub_checks in [true, false] {
        let mut state = StatementEvalState::from_body(&main, &[]).unwrap();
        state.ub_checks = ub_checks;
        assert_eq!(
            returned(eval_cfg_in_state_with_call_table(
                &main, state, 0, 8, &table, None
            )),
            MirValue::Bool(ub_checks)
        );
    }
    let main_lz = lower(
        &mk(
            vec![u32_ty(), u64_ty()],
            vec![
                blk(
                    vec![],
                    call(
                        callee("lz"),
                        vec![cp(1)],
                        0,
                        Some(1),
                        UnwindAction::Continue,
                    ),
                ),
                blk(vec![], Terminator::Return),
            ],
        ),
        PW,
    );
    assert_eq!(
        returned(eval_lowered_body_cfg_with_call_table(
            &main_lz,
            &[u64v(1)],
            8,
            &table
        )),
        u32v(63)
    );
    // Callee UB from an intrinsic is reported with the call stack.
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(
            &main_lz,
            &[u64v(1)],
            8,
            &CallTable::new().with_callee(
                "lz",
                1,
                lower(
                    &intrinsic_fn(IntrinsicOp::CtlzNonzero, vec![u64_ty()], u32_ty()),
                    PW
                )
            )
        ),
        Ok(CfgEvalOutcome::Returned(u32v(63)))
    );
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(
            &main_lz,
            &[u64v(0)],
            8,
            &CallTable::new().with_callee(
                "lz",
                1,
                lower(
                    &intrinsic_fn(IntrinsicOp::CtlzNonzero, vec![u64_ty()], u32_ty()),
                    PW
                )
            )
        ),
        Err(CfgEvalError::InCallee {
            call_stack: vec![CallSite {
                bb: 0,
                callee: CalleeSymbol::new("lz")
            }],
            error: Box::new(CfgEvalError::Terminator {
                bb: 0,
                error: RvalueEvalError::IntrinsicUb {
                    op: IntrinsicOp::CtlzNonzero,
                    reason: "the argument is zero"
                },
            }),
        })
    );
}

#[test]
fn test_call_table_api() {
    let mut table = CallTable::default();
    assert!(table.is_empty());
    assert_eq!(table.insert("double", 1, lower(&double_fn(), PW)), None);
    let replaced = table.insert("double", 1, lower(&inc_double_fn(), PW));
    assert_eq!(replaced.map(|c| c.body), Some(lower(&double_fn(), PW)));
    assert!(table.contains(&CalleeSymbol::new("double")));
    assert_eq!(table.len(), 1);
    table.set_max_call_depth(3);
    assert_eq!(table.max_call_depth(), 3);
    assert_eq!(
        table
            .iter()
            .map(|(s, c)| (s.as_str(), c.arg_count))
            .collect::<Vec<_>>(),
        vec![("double", 1)]
    );
}

#[test]
fn test_call_destinations_are_evaluated_before_the_call() {
    // `_2 = &raw mut _1; _3 = &raw mut _2; (*_2) = write_bytes::<*mut ()>(_3, 0, 1)`: the
    // memory intrinsic nulls `_2`, but the `()` result goes to the destination as evaluated
    // before the call (`_1`), as in MiniRust and Miri, instead of through the new null `_2`.
    let p_unit = raw(unit(), Mutability::Mut);
    let pp_unit = raw(p_unit.clone(), Mutability::Mut);
    let body = mk(
        vec![p_unit.clone(), unit(), p_unit.clone(), pp_unit, unit()],
        vec![
            blk(
                vec![
                    live(1),
                    live(2),
                    live(3),
                    live(4),
                    assign(2, Rvalue::RawPtr(Mutability::Mut, place(1))),
                    assign(3, Rvalue::RawPtr(Mutability::Mut, place(2))),
                ],
                Terminator::Call {
                    func: Operand::Constant(intrinsic(IntrinsicOp::WriteBytes)),
                    args: vec![cp(3), cst(0, u8_ty()), cst(1, usize_ty())],
                    destination: Place::with_projection(2, vec![ProjectionElem::Deref]),
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
            ),
            blk(
                vec![assign(4, Rvalue::Use(cp(1))), assign(0, Rvalue::Use(cp(2)))],
                Terminator::Return,
            ),
        ],
    );
    assert_eq!(
        returned(eval_lowered_body_cfg(&lower(&body, PW), &[], 4)),
        MirValue::ptr(PointerValue::without_provenance(0), p_unit)
    );
}

#[test]
fn test_call_table_entry_points_validate_the_initial_state_and_block() {
    let table = table(PW);
    let main = lower(
        &main_fn(
            "double",
            Some(1),
            UnwindAction::Cleanup(2),
            Terminator::UnwindResume,
        ),
        PW,
    );
    let state = StatementEvalState::from_body(&main, &[u32v(4)]).unwrap();
    assert_eq!(
        returned(eval_cfg_in_state_with_call_table(
            &main,
            state.clone(),
            0,
            8,
            &table,
            None
        )),
        u32v(8)
    );
    assert_eq!(
        eval_cfg_in_state_with_call_table(&main, state.clone(), 2, 8, &table, None),
        Err(CfgEvalError::InvalidEdge { from: 2, to: 2 })
    );
    assert_eq!(
        eval_cfg_in_state_with_call_table(&main, state.clone(), 9, 8, &table, None),
        Err(CfgEvalError::InvalidBlock { bb: 9 })
    );
    let mut wrong = state;
    wrong.ptr_width = PtrWidth::Bits32;
    assert!(matches!(
        eval_cfg_in_state_with_call_table(&main, wrong, 0, 8, &table, None),
        Err(CfgEvalError::InvalidArguments(_))
    ));
    assert!(matches!(
        eval_lowered_body_cfg_with_call_table(&main, &[u64v(4)], 8, &table),
        Err(CfgEvalError::InvalidArguments(_))
    ));
}

// ---------------------------------------------------------------------------------------------
// Adversarial Round B1 regression tests
// ---------------------------------------------------------------------------------------------

#[test]
fn test_b1_ordering_variant_rejects_tagless_wider_padded_and_ill_formed_enums() {
    let variants_for_width = |w: u32| {
        let neg_one = width_mask(w);
        vec![
            VariantDef::new("Less", vec![]).with_discriminant(neg_one),
            VariantDef::new("Equal", vec![]).with_discriminant(0),
            VariantDef::new("Greater", vec![]).with_discriminant(1),
        ]
    };

    for pw in PWS {
        let isize_w = width(&isize_ty(), pw);
        let tagless = AdtDef::new_enum("TaglessOrd", None, variants_for_width(isize_w)).into_ty();
        let i16_ord = AdtDef::new_enum(
            "I16Ord",
            Some(ScalarTy::Int(IntTy::I16)),
            variants_for_width(16),
        )
        .into_ty();
        let i32_ord = AdtDef::new_enum(
            "I32Ord",
            Some(ScalarTy::Int(IntTy::I32)),
            variants_for_width(32),
        )
        .into_ty();
        let i64_ord = AdtDef::new_enum(
            "I64Ord",
            Some(ScalarTy::Int(IntTy::I64)),
            variants_for_width(64),
        )
        .into_ty();
        let i128_ord = AdtDef::new_enum(
            "I128Ord",
            Some(ScalarTy::Int(IntTy::I128)),
            variants_for_width(128),
        )
        .into_ty();
        let isize_ord = AdtDef::new_enum(
            "IsizeOrd",
            Some(ScalarTy::Int(IntTy::Isize)),
            variants_for_width(isize_w),
        )
        .into_ty();
        let mut padded_def = AdtDef::new_enum(
            "PaddedOrd",
            Some(ScalarTy::Int(IntTy::I8)),
            variants_for_width(8),
        );
        padded_def.repr.align = Some(4);
        let padded_ord = padded_def.into_ty();

        let mut transparent_def = AdtDef::new_enum(
            "TransparentOrd",
            Some(ScalarTy::Int(IntTy::I8)),
            variants_for_width(8),
        );
        transparent_def.repr = AdtRepr::transparent();
        let transparent_ord = transparent_def.into_ty();

        let mut niche_enum_def = AdtDef::new_enum(
            "NicheEnumOrd",
            Some(ScalarTy::Int(IntTy::I8)),
            variants_for_width(8),
        );
        niche_enum_def.scalar_valid_range = Some(ScalarValidRange { start: 0, end: 255 });
        let niche_enum_ord = niche_enum_def.into_ty();

        for bad_ty in [
            tagless,
            i16_ord,
            i32_ord,
            i64_ord,
            i128_ord,
            isize_ord,
            padded_ord,
            transparent_ord,
            niche_enum_ord,
        ] {
            for code in [-1i8, 0, 1] {
                assert_eq!(
                    ordering_variant(&bad_ty, code, pw),
                    None,
                    "bad enum {bad_ty:?} accepted for code {code} on {pw:?}"
                );
            }
            assert!(
                check_intrinsic_call_types(
                    IntrinsicOp::ThreeWayCompare,
                    &[u32_ty(), u32_ty()],
                    &bad_ty,
                    pw,
                )
                .is_err()
            );
            assert!(matches!(
                eval_intrinsic(
                    IntrinsicOp::ThreeWayCompare,
                    &[iv(&u32_ty(), 1, pw), iv(&u32_ty(), 2, pw)],
                    &bad_ty,
                    pw,
                ),
                Err(RvalueEvalError::TypeMismatch(_))
            ));
            let body = intrinsic_fn(
                IntrinsicOp::ThreeWayCompare,
                vec![u32_ty(), u32_ty()],
                bad_ty.clone(),
            );
            let err = lower_err(&body, pw);
            if matches!(bad_ty.layout_for(pw), Err(LayoutError::IllFormed(_))) {
                assert!(matches!(err, RvalueLowerError::InvalidAdtDef { .. }));
            } else {
                assert!(matches!(
                    err,
                    RvalueLowerError::InvalidTerminator {
                        error: TerminatorLowerError::InvalidIntrinsicCall {
                            op: IntrinsicOp::ThreeWayCompare,
                            ..
                        },
                        ..
                    }
                ));
            }
        }

        // A valid `#[repr(C, i8)]` fieldless 3-variant enum still has `size == 1, align == 1`.
        let mut repr_c_i8 = AdtDef::new_enum(
            "ReprCI8Ord",
            Some(ScalarTy::Int(IntTy::I8)),
            variants_for_width(8),
        );
        repr_c_i8.repr = AdtRepr::c();
        let repr_c_i8_ty = repr_c_i8.into_ty();
        assert_eq!(ordering_variant(&repr_c_i8_ty, -1, pw), Some(0));
        assert_eq!(ordering_variant(&repr_c_i8_ty, 0, pw), Some(1));
        assert_eq!(ordering_variant(&repr_c_i8_ty, 1, pw), Some(2));
        assert_eq!(ordering_variant(&repr_c_i8_ty, 2, pw), None);
        assert_eq!(
            eval_intrinsic(
                IntrinsicOp::ThreeWayCompare,
                &[MirValue::Char('z'), MirValue::Char('a')],
                &repr_c_i8_ty,
                pw,
            ),
            Ok(MirValue::adt(adt_def(&repr_c_i8_ty), 2, vec![]))
        );
    }
}

#[test]
fn test_b1_write_bytes_preserves_ub_ordering_and_zst_dead_or_uninhabited_semantics() {
    for pw in PWS {
        // 1. `&mut (!, u32)` has non-canonical layout AND uninhabited pointee: `UninhabitedPointee`
        //    (undefined behavior) must win over `UnsupportedMemoryAccess` for both `count == 1`
        //    and `count > 1`.
        let uninh_pair = Ty::Tuple(vec![Ty::Never, u32_ty()]);
        let ref_mut_uninh = reference(uninh_pair.clone(), Mutability::Mut);
        for count in [1u128, 2] {
            let body = mk(
                vec![unit(), ref_mut_uninh.clone()],
                vec![
                    blk(
                        vec![],
                        call(
                            intrinsic(IntrinsicOp::WriteBytes),
                            vec![cp(1), cst(0, u8_ty()), cst(count, usize_ty())],
                            0,
                            Some(1),
                            UnwindAction::Continue,
                        ),
                    ),
                    blk(vec![], Terminator::Return),
                ],
            );
            let bad_ref = MirValue::ptr(
                PointerValue::with_provenance(0x100, 999, 0),
                ref_mut_uninh.clone(),
            );
            assert_eq!(
                term_err(eval_lowered_body_cfg(&lower(&body, pw), &[bad_ref], 4)),
                (0, RvalueEvalError::UninhabitedPointee(uninh_pair.clone()))
            );
        }

        // `&mut !` with `count == 1` and `count == 3` must also report `UninhabitedPointee`.
        let ref_mut_never = reference(Ty::Never, Mutability::Mut);
        for count in [1u128, 3] {
            let body = mk(
                vec![unit(), ref_mut_never.clone()],
                vec![
                    blk(
                        vec![],
                        call(
                            intrinsic(IntrinsicOp::WriteBytes),
                            vec![cp(1), cst(0, u8_ty()), cst(count, usize_ty())],
                            0,
                            Some(1),
                            UnwindAction::Continue,
                        ),
                    ),
                    blk(vec![], Terminator::Return),
                ],
            );
            let bad_ref = MirValue::ptr(PointerValue::without_provenance(8), ref_mut_never.clone());
            assert_eq!(
                term_err(eval_lowered_body_cfg(&lower(&body, pw), &[bad_ref], 4)),
                (0, RvalueEvalError::UninhabitedPointee(Ty::Never))
            );
        }

        // 2. Storage-dead ZST local: a zero-byte write accesses no memory, so it is a no-op for
        //    any `count` (A1: Rust's rule that every pointer is valid for a zero-sized access;
        //    B1 had made `count == 1` a `DeadLocal` fault).
        let raw_mut_unit = raw(unit(), Mutability::Mut);
        let dead_zst_body = |count: u128| {
            mk(
                vec![unit(), unit(), raw_mut_unit.clone()],
                vec![
                    blk(
                        vec![
                            live(1),
                            live(2),
                            assign(2, Rvalue::RawPtr(Mutability::Mut, place(1))),
                            Statement::StorageDead(Local(1)),
                        ],
                        call(
                            intrinsic(IntrinsicOp::WriteBytes),
                            vec![cp(2), cst(0xAB, u8_ty()), cst(count, usize_ty())],
                            0,
                            Some(1),
                            UnwindAction::Continue,
                        ),
                    ),
                    blk(vec![], Terminator::Return),
                ],
            )
        };
        for count in [1u128, 3] {
            assert_eq!(
                returned(eval_lowered_body_cfg(
                    &lower(&dead_zst_body(count), pw),
                    &[],
                    4
                )),
                MirValue::Unit
            );
        }

        // 3. Zero-byte `write_bytes` on external non-null pointers succeeds even for `!` and
        //    non-canonical 2-field ZST unions (`0` bytes written, no synthetic local touched).
        let zst_union =
            AdtDef::new_union("TwoZst", vec![unit(), Ty::Array(Box::new(u8_ty()), 0)]).into_ty();
        for zst_ty in [Ty::Never, zst_union] {
            let ptr_ty = raw(zst_ty, Mutability::Mut);
            for count in [1u128, 5] {
                let body = mk(
                    vec![unit(), ptr_ty.clone()],
                    vec![
                        blk(
                            vec![],
                            call(
                                intrinsic(IntrinsicOp::WriteBytes),
                                vec![cp(1), cst(0xFF, u8_ty()), cst(count, usize_ty())],
                                0,
                                Some(1),
                                UnwindAction::Continue,
                            ),
                        ),
                        blk(vec![], Terminator::Return),
                    ],
                );
                let dangling = MirValue::ptr(PointerValue::without_provenance(8), ptr_ty.clone());
                assert_eq!(
                    returned(eval_lowered_body_cfg(&lower(&body, pw), &[dangling], 4)),
                    MirValue::Unit
                );
            }
        }

        // 4. `write_bytes::<!>` into an uninhabited ZST field of a live union writes `0` bytes
        //    and preserves the active `u32` field.
        let u_def = Arc::new(AdtDef::new_union("U", vec![u32_ty(), Ty::Never]));
        let u_ty = Ty::Adt(Arc::clone(&u_def));
        let never_ptr_ty = raw(Ty::Never, Mutability::Mut);
        let union_never_write = mk(
            vec![u32_ty(), u_ty, never_ptr_ty, unit()],
            vec![
                blk(
                    vec![
                        live(1),
                        live(2),
                        live(3),
                        assign(
                            1,
                            Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    def_path: "U".to_string(),
                                    variant_idx: 0,
                                    active_field: Some(0),
                                    adt_def: Some(Arc::clone(&u_def)),
                                },
                                vec![cst(0xCAFE_BABE, u32_ty())],
                            ),
                        ),
                        assign(
                            2,
                            Rvalue::RawPtr(
                                Mutability::Mut,
                                Place {
                                    local: Local(1),
                                    projection: vec![ProjectionElem::Field(1, Ty::Never)],
                                },
                            ),
                        ),
                    ],
                    call(
                        intrinsic(IntrinsicOp::WriteBytes),
                        vec![cp(2), cst(0xFF, u8_ty()), cst(1, usize_ty())],
                        3,
                        Some(1),
                        UnwindAction::Continue,
                    ),
                ),
                blk(
                    vec![assign(
                        0,
                        Rvalue::Use(Operand::Copy(Place {
                            local: Local(1),
                            projection: vec![ProjectionElem::Field(0, u32_ty())],
                        })),
                    )],
                    Terminator::Return,
                ),
            ],
        );
        assert_eq!(
            returned(eval_lowered_body_cfg(
                &lower(&union_never_write, pw),
                &[],
                4
            )),
            MirValue::unsigned(0xCAFE_BABE, UintTy::U32, pw)
        );

        // 5a. Tagged `&raw mut _1[0]` on `[(); 4]` with `count == 4` initializes the entire
        //     zero-sized array window `[0..4]` to `[(), (), (), ()]`.
        let zst_arr = Ty::Array(Box::new(unit()), 4);
        let init_zst_arr = mk(
            vec![
                zst_arr.clone(),
                zst_arr.clone(),
                raw_mut_unit.clone(),
                unit(),
            ],
            vec![
                blk(
                    vec![
                        live(1),
                        live(2),
                        live(3),
                        assign(
                            2,
                            Rvalue::RawPtr(
                                Mutability::Mut,
                                Place {
                                    local: Local(1),
                                    projection: vec![ProjectionElem::ConstantIndex {
                                        offset: 0,
                                        min_length: 4,
                                        from_end: false,
                                    }],
                                },
                            ),
                        ),
                    ],
                    call(
                        intrinsic(IntrinsicOp::WriteBytes),
                        vec![cp(2), cst(0, u8_ty()), cst(4, usize_ty())],
                        3,
                        Some(1),
                        UnwindAction::Continue,
                    ),
                ),
                blk(vec![assign(0, Rvalue::Use(cp(1)))], Terminator::Return),
            ],
        );
        assert_eq!(
            returned(eval_lowered_body_cfg(&lower(&init_zst_arr, pw), &[], 4)),
            MirValue::Array {
                elements: vec![MirValue::Unit; 4],
                elem_ty: unit(),
            }
        );

        // 5b. A ZST pointer at an interior byte offset (`+2`) of a live `u32` local resolves to
        //     no `()` sub-place; the zero-byte write accesses no memory and is a no-op (A1;
        //     B1 had failed closed with `UnsupportedMemoryAccess`).
        let raw_mut_u32 = raw(u32_ty(), Mutability::Mut);
        let raw_mut_u8 = raw(u8_ty(), Mutability::Mut);
        let interior_zst = mk(
            vec![
                unit(),
                u32_ty(),
                raw_mut_u32,
                raw_mut_u8.clone(),
                raw_mut_u8,
                raw_mut_unit.clone(),
            ],
            vec![
                blk(
                    vec![
                        live(1),
                        live(2),
                        live(3),
                        live(4),
                        live(5),
                        assign(1, Rvalue::Use(cst(0x1122_3344, u32_ty()))),
                        assign(2, Rvalue::RawPtr(Mutability::Mut, place(1))),
                        assign(
                            3,
                            Rvalue::Cast(CastKind::PtrToPtr, cp(2), raw(u8_ty(), Mutability::Mut)),
                        ),
                    ],
                    call(
                        intrinsic(IntrinsicOp::ArithOffset),
                        vec![cp(3), cst(2, isize_ty())],
                        4,
                        Some(1),
                        UnwindAction::Continue,
                    ),
                ),
                blk(
                    vec![assign(
                        5,
                        Rvalue::Cast(CastKind::PtrToPtr, cp(4), raw_mut_unit.clone()),
                    )],
                    call(
                        intrinsic(IntrinsicOp::WriteBytes),
                        vec![cp(5), cst(0, u8_ty()), cst(2, usize_ty())],
                        0,
                        Some(2),
                        UnwindAction::Continue,
                    ),
                ),
                blk(vec![], Terminator::Return),
            ],
        );
        assert_eq!(
            returned(eval_lowered_body_cfg(&lower(&interior_zst, pw), &[], 8)),
            MirValue::Unit
        );
    }
}

#[test]
fn test_b1_call_table_supports_diverging_never_callees_into_coerced_caller_destinations() {
    for pw in PWS {
        let diverge_never = |op: IntrinsicOp| {
            mk(
                vec![Ty::Never, u32_ty()],
                vec![blk(
                    vec![],
                    call(intrinsic(op), vec![], 0, None, UnwindAction::Continue),
                )],
            )
        };
        let wrong_u64 = mk(
            vec![u64_ty(), u32_ty()],
            vec![blk(
                vec![assign(0, Rvalue::Use(cst(9, u64_ty())))],
                Terminator::Return,
            )],
        );
        let table = CallTable::new()
            .with_callee(
                "panic_never",
                1,
                lower(&diverge_never(IntrinsicOp::PanicUnwind), pw),
            )
            .with_callee(
                "abort_never",
                1,
                lower(&diverge_never(IntrinsicOp::Abort), pw),
            )
            .with_callee(
                "ub_never",
                1,
                lower(&diverge_never(IntrinsicOp::UnreachableUnchecked), pw),
            )
            .with_callee("wrong_u64", 1, lower(&wrong_u64, pw));

        // Caller coerces `fn(u32) -> !` into `_0: u32` with `target: None` (as `rustc`'s
        // `NeverToAny` + `DestinationPropagation` emits).
        let caller = |sym: &str, target: Option<usize>, unwind: UnwindAction| {
            mk(
                vec![u32_ty(), u32_ty()],
                vec![
                    blk(vec![], call(callee(sym), vec![cp(1)], 0, target, unwind)),
                    blk(vec![], Terminator::Return),
                    cleanup_blk(vec![], Terminator::UnwindResume),
                ],
            )
        };

        assert_eq!(
            eval_lowered_body_cfg_with_call_table(
                &lower(&caller("panic_never", None, UnwindAction::Cleanup(2)), pw),
                &[MirValue::unsigned(7, UintTy::U32, pw)],
                8,
                &table,
            ),
            Ok(CfgEvalOutcome::Panicked {
                bb: 0,
                msg: PanicMessage::Intrinsic(IntrinsicOp::PanicUnwind),
            })
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(
                &lower(&caller("abort_never", None, UnwindAction::Cleanup(2)), pw),
                &[MirValue::unsigned(7, UintTy::U32, pw)],
                2,
                &table,
            ),
            Ok(CfgEvalOutcome::Terminated {
                bb: 0,
                msg: PanicMessage::Intrinsic(IntrinsicOp::Abort),
            })
        );
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(
                &lower(&caller("ub_never", None, UnwindAction::Continue), pw),
                &[MirValue::unsigned(7, UintTy::U32, pw)],
                8,
                &table,
            ),
            Err(CfgEvalError::InCallee {
                call_stack: vec![CallSite {
                    bb: 0,
                    callee: CalleeSymbol::new("ub_never"),
                }],
                error: Box::new(CfgEvalError::UnreachableReached { bb: 0 }),
            })
        );

        // Converging calls (`target: Some(1)`) to `-> !` into `_0: u32`, and diverging calls
        // (`target: None`) to an inhabited mismatched return type `-> u64`, still fail with
        // `TypeMismatch`.
        assert!(matches!(
            term_err(eval_lowered_body_cfg_with_call_table(
                &lower(&caller("panic_never", Some(1), UnwindAction::Continue), pw),
                &[MirValue::unsigned(7, UintTy::U32, pw)],
                8,
                &table,
            )),
            (0, RvalueEvalError::TypeMismatch(_))
        ));
        assert!(matches!(
            term_err(eval_lowered_body_cfg_with_call_table(
                &lower(&caller("wrong_u64", None, UnwindAction::Continue), pw),
                &[MirValue::unsigned(7, UintTy::U32, pw)],
                8,
                &table,
            )),
            (0, RvalueEvalError::TypeMismatch(_))
        ));
    }
}

#[test]
fn test_b1_call_table_union_active_field_isolation_and_union_destination_write() {
    let raw_u32 = raw(u32_ty(), Mutability::Not);
    // Legacy tuple-modeled multi-slot union (`adt_def: None`, declared as `Ty::Tuple` of its
    // union fields).
    let legacy_u_ty = Ty::Tuple(vec![u64_ty(), raw_u32.clone()]);

    // `id(u: PtrOrInt) -> PtrOrInt { _0 = move _1; return }`
    let id_body = mk(
        vec![legacy_u_ty.clone(), legacy_u_ty.clone()],
        vec![blk(vec![assign(0, Rvalue::Use(mv(1)))], Terminator::Return)],
    );
    let caller_body = mk(
        vec![legacy_u_ty.clone(), legacy_u_ty.clone()],
        vec![
            blk(
                vec![],
                call(
                    callee("id"),
                    vec![mv(1)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            blk(vec![], Terminator::Return),
        ],
    );
    let table = CallTable::new().with_callee("id", 1, lower(&id_body, PW));
    let lowered_caller = lower(&caller_body, PW);

    // Multi-slot union `MirValue::Adt` with `active_field: Some(0)` (`u64`) and a stale synthetic
    // pointer in inactive slot `1`: only the active field is inspected, matching
    // `check_value_well_formed`.
    let stale_local_ptr = MirValue::ptr(PointerValue::with_provenance(0x100, 1, 0), raw_u32);
    let active_int_union = MirValue::Adt {
        def_path: "PtrOrInt".to_string(),
        adt_def: None,
        variant_idx: 0,
        active_field: Some(0),
        fields: vec![u64v(0xDEAD_BEEF), stale_local_ptr.clone()],
    };
    assert_eq!(
        returned(eval_lowered_body_cfg_with_call_table(
            &lowered_caller,
            std::slice::from_ref(&active_int_union),
            4,
            &table,
        )),
        active_int_union
    );

    // When the synthetic local pointer IS in the active union field (`active_field: Some(1)`),
    // frame isolation rejects it with `UnsupportedMemoryAccess`.
    let active_ptr_union = MirValue::Adt {
        def_path: "PtrOrInt".to_string(),
        adt_def: None,
        variant_idx: 0,
        active_field: Some(1),
        fields: vec![u64v(0), stale_local_ptr],
    };
    assert!(matches!(
        term_err(eval_lowered_body_cfg_with_call_table(
            &lowered_caller,
            &[active_ptr_union],
            4,
            &table,
        )),
        (0, RvalueEvalError::UnsupportedMemoryAccess(_))
    ));

    // Direct call destination into an inactive union field (`_1.1 = make_u32()`) switches the
    // union's active field cleanly on return.
    let u2_def = Arc::new(AdtDef::new_union("IntOrU32", vec![u64_ty(), u32_ty()]));
    let u2_ty = Ty::Adt(Arc::clone(&u2_def));
    let make_u32 = mk(
        vec![u32_ty()],
        vec![blk(
            vec![assign(0, Rvalue::Use(cst(0x1234_5678, u32_ty())))],
            Terminator::Return,
        )],
    );
    let table2 = CallTable::new().with_callee("make_u32", 0, lower(&make_u32, PW));
    let write_union_dest = mk(
        vec![u32_ty(), u2_ty],
        vec![
            blk(
                vec![
                    live(1),
                    assign(
                        1,
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                def_path: "IntOrU32".to_string(),
                                variant_idx: 0,
                                active_field: Some(0),
                                adt_def: Some(Arc::clone(&u2_def)),
                            },
                            vec![cst(99, u64_ty())],
                        ),
                    ),
                ],
                Terminator::Call {
                    func: Operand::Constant(callee("make_u32")),
                    args: vec![],
                    destination: Place {
                        local: Local(1),
                        projection: vec![ProjectionElem::Field(1, u32_ty())],
                    },
                    target: Some(1),
                    unwind: UnwindAction::Continue,
                },
            ),
            blk(
                vec![assign(
                    0,
                    Rvalue::Use(Operand::Copy(Place {
                        local: Local(1),
                        projection: vec![ProjectionElem::Field(1, u32_ty())],
                    })),
                )],
                Terminator::Return,
            ),
        ],
    );
    assert_eq!(
        returned(eval_lowered_body_cfg_with_call_table(
            &lower(&write_union_dest, PW),
            &[],
            4,
            &table2,
        )),
        u32v(0x1234_5678)
    );
}

#[test]
fn test_b1_eval_lowered_terminator_invalid_cleanup_edge_preserves_unwinding_state() {
    let body = LoweredBody {
        ptr_width: PW,
        local_decls: vec![unit()],
        basic_blocks: vec![
            LoweredBasicBlock {
                statements: vec![],
                terminator: None,
                is_cleanup: false,
            },
            LoweredBasicBlock {
                statements: vec![],
                terminator: Some(LoweredTerminator::Return { ret_ty: unit() }),
                is_cleanup: false,
            },
        ],
    };
    let mut state = StatementEvalState::from_body(&body, &[]).unwrap();

    for (unwind, expected_err) in [
        (
            UnwindAction::Cleanup(99),
            CfgEvalError::InvalidBlock { bb: 99 },
        ),
        (
            UnwindAction::Cleanup(1),
            CfgEvalError::InvalidEdge { from: 0, to: 1 },
        ),
    ] {
        let term = LoweredTerminator::Call {
            func: Operand::Constant(intrinsic(IntrinsicOp::PanicUnwind)),
            func_ty: Ty::unit(),
            args: vec![],
            arg_tys: vec![],
            destination: place(0),
            dest_ty: unit(),
            target: None,
            unwind,
        };
        let mut unwinding: UnwindState = None;
        assert_eq!(
            eval_lowered_terminator(&body, 0, &term, &mut state, &mut unwinding, None),
            Err(expected_err)
        );
        assert_eq!(
            unwinding, None,
            "failed Cleanup edge must not leave UnwindState mutated"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// A1 regression tests
// ---------------------------------------------------------------------------------------------

/// Deterministic `xorshift64*` generator for sampled (non-exhaustive) parity sweeps.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// A `w`-bit pattern biased towards boundary values: uniform bits, truncated to a random
    /// bit length, and occasionally negated (so small, huge, and near-`MIN`/`MAX` values all
    /// occur).
    fn bits(&mut self, w: u32) -> u128 {
        let raw = (u128::from(self.next()) << 64) | u128::from(self.next());
        let len = (self.next() % u64::from(w + 1)) as u32;
        let v = raw & width_mask(len);
        let v = if self.next().is_multiple_of(3) {
            v.wrapping_neg()
        } else {
            v
        };
        v & width_mask(w)
    }
}

const ARITH_OPS: [IntrinsicOp; 11] = [
    IntrinsicOp::ExactDiv,
    IntrinsicOp::WrappingAdd,
    IntrinsicOp::WrappingSub,
    IntrinsicOp::WrappingMul,
    IntrinsicOp::SaturatingAdd,
    IntrinsicOp::SaturatingSub,
    IntrinsicOp::UncheckedAdd,
    IntrinsicOp::UncheckedSub,
    IntrinsicOp::UncheckedMul,
    IntrinsicOp::UncheckedDiv,
    IntrinsicOp::UncheckedRem,
];

/// Checks every two-operand intrinsic, both unchecked shifts, `three_way_compare`, and the
/// `*WithOverflow` / checked `BinOp`s on `(a, b)` against the native reference model.
fn check_pair(ty: &Ty, rhs_tys: &[Ty], a: u128, b: u128, pw: PtrWidth) {
    let w = width(ty, pw);
    let signed = ty.is_signed_int();
    let (x, y) = (iv(ty, a, pw), iv(ty, b, pw));
    for op in ARITH_OPS {
        let got = eval_intrinsic(op, &[x.clone(), y.clone()], ty, pw);
        match native2(op, signed, w, a, b) {
            Some(expected) => {
                assert_eq!(got, Ok(iv(ty, expected, pw)), "{op}({ty:?} {a:#x}, {b:#x})")
            }
            None => assert!(
                got.is_err(),
                "{op}({ty:?} {a:#x}, {b:#x}) must be UB, got {got:?}"
            ),
        }
    }
    for (binop, checked) in [
        (BinOp::AddWithOverflow, BinOp::Add),
        (BinOp::SubWithOverflow, BinOp::Sub),
        (BinOp::MulWithOverflow, BinOp::Mul),
    ] {
        let unchecked = match binop {
            BinOp::AddWithOverflow => IntrinsicOp::UncheckedAdd,
            BinOp::SubWithOverflow => IntrinsicOp::UncheckedSub,
            _ => IntrinsicOp::UncheckedMul,
        };
        let pair = eval_binop(binop, &x, &y, pw)
            .unwrap()
            .as_checked_pair()
            .unwrap();
        assert_eq!(eval_checked_binop(checked, &x, &y, pw), Ok(pair));
        assert_eq!(pair.1, native2(unchecked, signed, w, a, b).is_none());
    }
    let ord = eval_intrinsic(
        IntrinsicOp::ThreeWayCompare,
        &[x.clone(), y.clone()],
        &i8_ty(),
        pw,
    );
    let expected: i8 = if signed {
        sign_extend(a, w).cmp(&sign_extend(b, w)) as i8
    } else {
        a.cmp(&b) as i8
    };
    assert_eq!(
        ord,
        Ok(MirValue::signed(i128::from(expected), IntTy::I8, pw))
    );
    for rhs_ty in rhs_tys {
        let rw = width(rhs_ty, pw);
        let amount_bits = b & width_mask(rw);
        let amount = if rhs_ty.is_signed_int() {
            let s = sign_extend(amount_bits, rw);
            (s >= 0).then_some(s as u128)
        } else {
            Some(amount_bits)
        };
        let z = iv(rhs_ty, amount_bits, pw);
        for (op, binop) in [
            (IntrinsicOp::UncheckedShl, BinOp::ShlUnchecked),
            (IntrinsicOp::UncheckedShr, BinOp::ShrUnchecked),
        ] {
            let got = eval_intrinsic(op, &[x.clone(), z.clone()], ty, pw);
            assert_eq!(got, eval_binop(binop, &x, &z, pw));
            match native_shift(op, signed, w, a, amount) {
                Some(expected) => assert_eq!(got, Ok(iv(ty, expected, pw))),
                None => assert!(got.is_err()),
            }
        }
    }
}

#[test]
fn test_a1_exhaustive_8_bit_parity_with_native_reference_and_binops() {
    let rhs_tys = [u8_ty(), i8_ty()];
    for ty in [u8_ty(), i8_ty()] {
        for a in 0..=255u128 {
            for op in [IntrinsicOp::Ctlz, IntrinsicOp::Cttz, IntrinsicOp::Ctpop] {
                assert_eq!(
                    eval_intrinsic(op, &[iv(&ty, a, PW)], &u32_ty(), PW),
                    Ok(u32v(u128::from(native_count(op, 8, a))))
                );
            }
            for op in [IntrinsicOp::Bswap, IntrinsicOp::Bitreverse] {
                assert_eq!(
                    eval_intrinsic(op, &[iv(&ty, a, PW)], &ty, PW),
                    Ok(iv(&ty, native_perm(op, 8, a), PW))
                );
            }
            for b in 0..=255u128 {
                check_pair(&ty, &rhs_tys, a, b, PW);
            }
        }
    }
}

#[test]
fn test_a1_sampled_parity_on_every_wider_width_and_both_pointer_widths() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    for pw in PWS {
        let rhs_tys = int_tys();
        for ty in int_tys().into_iter().filter(|t| width(t, pw) > 8) {
            let w = width(&ty, pw);
            for _ in 0..1500 {
                let (a, b) = (rng.bits(w), rng.bits(w));
                check_pair(&ty, &rhs_tys, a, b, pw);
                for op in [IntrinsicOp::Ctlz, IntrinsicOp::Cttz, IntrinsicOp::Ctpop] {
                    assert_eq!(
                        eval_intrinsic(op, &[iv(&ty, a, pw)], &u32_ty(), pw),
                        Ok(MirValue::unsigned(
                            u128::from(native_count(op, w, a)),
                            UintTy::U32,
                            pw
                        ))
                    );
                }
                for op in [IntrinsicOp::Bswap, IntrinsicOp::Bitreverse] {
                    assert_eq!(
                        eval_intrinsic(op, &[iv(&ty, a, pw)], &ty, pw),
                        Ok(iv(&ty, native_perm(op, w, a), pw))
                    );
                }
            }
        }
    }
}

/// `fn(_1: usize) -> R { _2 = 7u32; _3 = &raw mut _2; _4 = _3 as usize (exposed); <rest> }`.
fn exposing_fn(ret_ty: Ty, extra_decls: Vec<Ty>, rest: Vec<Statement>, term: Terminator) -> Body {
    let mut decls = vec![
        ret_ty,
        usize_ty(),
        u32_ty(),
        raw(u32_ty(), Mutability::Mut),
        usize_ty(),
    ];
    decls.extend(extra_decls);
    let mut stmts = (2..decls.len()).map(live).collect::<Vec<_>>();
    stmts.extend([
        assign(2, Rvalue::Use(cst(7, u32_ty()))),
        assign(3, Rvalue::RawPtr(Mutability::Mut, place(2))),
        assign(
            4,
            Rvalue::Cast(CastKind::PointerExposeProvenance, cp(3), usize_ty()),
        ),
    ]);
    stmts.extend(rest);
    mk(
        decls,
        vec![blk(stmts, term), blk(vec![], Terminator::Return)],
    )
}

#[test]
fn test_a1_linked_frames_have_disjoint_synthetic_addresses() {
    for pw in PWS {
        // `same_addr(n) == (&raw mut its own _2 as usize == n)`.
        let same_addr = lower(
            &exposing_fn(
                Ty::Bool,
                vec![],
                vec![assign(0, Rvalue::BinaryOp(BinOp::Eq, cp(4), cp(1)))],
                Terminator::Return,
            ),
            pw,
        );
        // As an evaluated body, its `_2` lives at the frame-relative address 0x3000 ...
        assert_eq!(
            returned(eval_lowered_body_cfg(&same_addr, &[usizev(0x3000, pw)], 2)),
            MirValue::Bool(true)
        );
        // ... and so does the `_2` of an identically laid-out caller, but in a callee frame the
        // allocations lie above the caller's, so the exposed addresses differ.
        let caller = lower(
            &exposing_fn(
                Ty::Bool,
                vec![],
                vec![],
                call(
                    callee("same_addr"),
                    vec![cp(4)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            pw,
        );
        let table = CallTable::new().with_callee("same_addr", 1, same_addr.clone());
        assert_eq!(
            returned(eval_lowered_body_cfg_with_call_table(
                &caller,
                &[usizev(0, pw)],
                4,
                &table
            )),
            MirValue::Bool(false)
        );
        // An exposed caller address cast back to a pointer in the callee never designates one
        // of the callee's locals (it would read the callee's `_2 = 7`, never the caller's).
        let reread = lower(
            &exposing_fn(
                u32_ty(),
                vec![raw(u32_ty(), Mutability::Mut)],
                vec![
                    assign(
                        5,
                        Rvalue::Cast(
                            CastKind::PointerWithExposedProvenance,
                            cp(1),
                            raw(u32_ty(), Mutability::Mut),
                        ),
                    ),
                    assign(
                        0,
                        Rvalue::Use(Operand::Copy(Place::with_projection(
                            5,
                            vec![ProjectionElem::Deref],
                        ))),
                    ),
                ],
                Terminator::Return,
            ),
            pw,
        );
        let caller = lower(
            &exposing_fn(
                u32_ty(),
                vec![],
                vec![],
                call(
                    callee("reread"),
                    vec![cp(4)],
                    0,
                    Some(1),
                    UnwindAction::Continue,
                ),
            ),
            pw,
        );
        let table = CallTable::new().with_callee("reread", 1, reread);
        match eval_lowered_body_cfg_with_call_table(&caller, &[usizev(0, pw)], 4, &table) {
            Err(CfgEvalError::InCallee { call_stack, error }) => {
                assert_eq!(
                    call_stack,
                    vec![CallSite {
                        bb: 0,
                        callee: CalleeSymbol::new("reread")
                    }]
                );
                assert!(
                    matches!(
                        *error,
                        CfgEvalError::Statement {
                            bb: 0,
                            error: RvalueEvalError::UnsupportedPlaceProjection(_),
                            ..
                        }
                    ),
                    "{error:?}"
                );
            }
            other => panic!("expected an unsupported cross-frame dereference, got {other:?}"),
        }
    }
}

#[test]
fn test_a1_abort_and_callee_aborts_still_reject_ill_formed_unwind_edges() {
    let hand_abort = |unwind: UnwindAction| LoweredBody {
        local_decls: vec![unit(), Ty::Never],
        basic_blocks: vec![
            LoweredBasicBlock {
                statements: vec![LoweredStatement::StorageLive(Local(1))],
                terminator: Some(LoweredTerminator::Call {
                    func: Operand::Constant(intrinsic(IntrinsicOp::Abort)),
                    func_ty: unit(),
                    args: vec![],
                    arg_tys: vec![],
                    destination: place(1),
                    dest_ty: Ty::Never,
                    target: None,
                    unwind,
                }),
                is_cleanup: false,
            },
            LoweredBasicBlock {
                statements: vec![],
                terminator: Some(LoweredTerminator::UnwindResume),
                is_cleanup: true,
            },
            LoweredBasicBlock {
                statements: vec![],
                terminator: Some(LoweredTerminator::Goto { target: 0 }),
                is_cleanup: false,
            },
        ],
        ptr_width: PW,
    };
    let abort_msg = PanicMessage::Intrinsic(IntrinsicOp::Abort);
    assert_eq!(
        eval_lowered_body_cfg(&hand_abort(UnwindAction::Cleanup(1)), &[], 2),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: abort_msg.clone()
        })
    );
    assert_eq!(
        eval_lowered_body_cfg(&hand_abort(UnwindAction::Cleanup(9)), &[], 2),
        Err(CfgEvalError::InvalidBlock { bb: 9 })
    );
    assert_eq!(
        eval_lowered_body_cfg(&hand_abort(UnwindAction::Cleanup(2)), &[], 2),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 2 })
    );
    // The same for a linked callee that aborts: the caller's call edge is still checked.
    let die = lower(
        &mk(
            vec![Ty::Never, Ty::Never],
            vec![blk(
                vec![live(1)],
                call(
                    intrinsic(IntrinsicOp::Abort),
                    vec![],
                    1,
                    None,
                    UnwindAction::Continue,
                ),
            )],
        ),
        PW,
    );
    let table = CallTable::new().with_callee("die", 0, die);
    let mut caller = hand_abort(UnwindAction::Cleanup(2));
    if let Some(LoweredTerminator::Call { func, .. }) = &mut caller.basic_blocks[0].terminator {
        *func = Operand::Constant(callee("die"));
    }
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(&caller, &[], 4, &table),
        Err(CfgEvalError::InvalidEdge { from: 0, to: 2 })
    );
    if let Some(LoweredTerminator::Call { unwind, .. }) = &mut caller.basic_blocks[0].terminator {
        *unwind = UnwindAction::Cleanup(1);
    }
    assert_eq!(
        eval_lowered_body_cfg_with_call_table(&caller, &[], 4, &table),
        Ok(CfgEvalOutcome::Terminated {
            bb: 0,
            msg: abort_msg
        })
    );
}

#[test]
fn test_a1_linked_calls_from_cleanup_blocks_return_into_the_unwinding_caller() {
    for pw in PWS {
        let table = table(pw);
        // `bb0: assert(false) -> unwind bb2; bb2 (cleanup): _2 = <callee>(_1) -> [bb3, unwind
        // terminate]; bb3 (cleanup): resume`.
        let body = |name: &str| {
            mk(
                vec![u32_ty(), u32_ty(), u32_ty()],
                vec![
                    blk(
                        vec![live(2)],
                        Terminator::Assert {
                            cond: Operand::Constant(Constant::Bool(false)),
                            expected: true,
                            msg: AssertMessage::Custom("first".into()),
                            target: 1,
                            unwind: UnwindAction::Cleanup(2),
                        },
                    ),
                    blk(vec![assign(0, Rvalue::Use(cp(2)))], Terminator::Return),
                    cleanup_blk(
                        vec![],
                        call(
                            callee(name),
                            vec![cp(1)],
                            2,
                            Some(3),
                            UnwindAction::Terminate,
                        ),
                    ),
                    cleanup_blk(vec![], Terminator::UnwindResume),
                ],
            )
        };
        let first = PanicMessage::Custom("first".into());
        let lowered = lower(&body("double"), pw);
        // bb0, bb2, double.bb0, bb3.
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(&lowered, &[iv(&u32_ty(), 21, pw)], 4, &table),
            Ok(CfgEvalOutcome::Panicked {
                bb: 0,
                msg: first.clone()
            })
        );
        match eval_lowered_body_cfg_with_call_table(&lowered, &[iv(&u32_ty(), 21, pw)], 3, &table) {
            Ok(CfgEvalOutcome::OutOfFuel { bb: 3, state }) => {
                assert_eq!(state.slots[2], LocalSlotState::Init(iv(&u32_ty(), 42, pw)));
            }
            other => panic!("expected OutOfFuel at the cleanup block bb3, got {other:?}"),
        }
        // A callee panic during cleanup takes the call's `Terminate` edge.
        let boom = mk(
            vec![u32_ty(), u32_ty(), Ty::Never],
            vec![blk(
                vec![live(2)],
                call(
                    intrinsic(IntrinsicOp::PanicUnwind),
                    vec![],
                    2,
                    None,
                    UnwindAction::Continue,
                ),
            )],
        );
        let table = table.with_callee("boom", 1, lower(&boom, pw));
        assert_eq!(
            eval_lowered_body_cfg_with_call_table(
                &lower(&body("boom"), pw),
                &[iv(&u32_ty(), 1, pw)],
                8,
                &table
            ),
            Ok(CfgEvalOutcome::Terminated {
                bb: 2,
                msg: PanicMessage::Intrinsic(IntrinsicOp::PanicUnwind)
            })
        );
    }
}
