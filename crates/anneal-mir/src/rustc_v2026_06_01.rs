//! Thin, version-tagged adapter from the callee `DefPath`s of `rustc` `V2026_06_01`
//! (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`) to Anneal's version-independent call
//! targets ([`IntrinsicOp`], [`CallTarget`]).
//!
//! This module is the only place in `anneal-mir` that recognizes `rustc` paths: the core IR
//! and its evaluator never inspect a callee's spelling, so supporting another `rustc` version
//! means adding another adapter, not touching the semantics. The tables mirror
//! `Trusted.Rustc.V2026_06_01.MirSemantics`:
//! - [`RUST_INTRINSIC_DEF_PATHS_V2026_06_01`] (27 paths, each mapped to the [`IntrinsicOp`] of
//!   the same name) is `isDirectExactDivTarget` (`core::intrinsics::exact_div`) together with
//!   26 of the 34 `core::intrinsics::*` paths of `classifyRustIntrinsic?`: its 24 value
//!   intrinsics and the call forms of the memory intrinsics,
//!   `core::intrinsics::copy_nonoverlapping` / `core::intrinsics::write_bytes` (which
//!   `Trusted` evaluates with `evalCopyNonOverlappingCall` / `evalWriteBytesCall`). The other
//!   8 paths of `classifyRustIntrinsic?` are deliberately not listed:
//!   - `core::intrinsics::const_eval_select`, which `rustc` removes before `optimized_mir`
//!     and Anneal does not model;
//!   - the 7 volatile memory intrinsics (`isVolatileMemIntrinsicKind`), which are
//!     `Trusted`-only (see below): `core::intrinsics::unaligned_volatile_load`,
//!     `core::intrinsics::unaligned_volatile_store`, `core::intrinsics::volatile_load`,
//!     `core::intrinsics::volatile_store`,
//!     `core::intrinsics::volatile_copy_nonoverlapping_memory`,
//!     `core::intrinsics::volatile_copy_memory`, and `core::intrinsics::volatile_set_memory`;
//! - `isUnreachableCallTarget` is [`UNREACHABLE_DEF_PATHS_V2026_06_01`];
//! - `isAbortingPanicDefPath` is [`ABORTING_PANIC_DEF_PATHS_V2026_06_01`];
//! - `isUnwindingPanicDefPath` is [`UNWINDING_PANIC_DEF_PATHS_V2026_06_01`];
//! - the `CastKind::PointerCoercion` tags that `MirSemantics.Places` matches with
//!   `stringEq coercionKind "…"` (`evalReifyFnPointer`, `reifyCoercionSafetyCompatible`, ...)
//!   are [`POINTER_COERCION_SPELLINGS_V2026_06_01`], each mapped to its typed
//!   [`PointerCoercionKind`] (so `ir` and `lower` never match a coercion's spelling).
//!
//! The diverging entry points are classified whatever the call's `target`, and Anneal executes
//! a call of one as `Trusted` executes a call without a return target (`rustc` never gives a
//! call of these `-> !` functions a target; for a hand-built call with one, `Trusted` instead
//! defers to the environment through `extCall`).
//!
//! Like `Trusted`'s `evalTerminator` (which consults `lookupCallee` before any intrinsic
//! or panic classification), [`classify_linked_call_target_v2026_06_01`] prefers a body linked
//! in a [`CallTable`] over these tables.
//!
//! # `Trusted`-only paths
//!
//! Besides `const_eval_select`, `Trusted` evaluates a direct call of 11 paths inline that
//! Anneal deliberately does not: the 7 volatile memory intrinsics above
//! (`evalVolatileMemIntrinsicCall`), for which Anneal has no [`IntrinsicOp`], and the 4
//! `core::ptr` raw-pointer access functions that `Trusted` evaluates when no body is linked
//! for them (`evalUnlinkedPtrAccessCall?`: `core::ptr::read_unaligned`,
//! `core::ptr::write_unaligned`, `core::ptr::read_volatile`, and `core::ptr::write_volatile`),
//! for which this module has no table. [`lower_intrinsic_kind_v2026_06_01`] is `None` for
//! each of them, so a direct call of one is a call of an ordinary function
//! ([`CallTarget::Fn`]): Anneal runs a body linked for it in a [`CallTable`], and otherwise
//! leaves the call to the caller's call handler or, without one, fails the evaluation
//! ([`CfgEvalError::UnsupportedCall`], or [`CfgEvalError::UnknownCallee`] under a call
//! table). It never executes such a call inline. For the 7 volatile memory intrinsics, this
//! is the Rust counterpart of the Lean theorem
//! `MiniRustSpec.Correspondence.lintrinsicOp_volatile_lowered_fail_closed`
//! (`minirust/lean/MiniRustSpec/Correspondence/IntrinsicBoundary.lean`), by which Anneal's
//! lowered evaluator takes no step on a volatile memory intrinsic.
//!
//! [`CfgEvalError::UnsupportedCall`]: crate::lower::cfg::CfgEvalError::UnsupportedCall
//! [`CfgEvalError::UnknownCallee`]: crate::lower::cfg::CfgEvalError::UnknownCallee

use crate::ir::{CallTarget, CalleeSymbol, IntrinsicOp, PointerCoercionKind, Safety};
use crate::lower::cfg::CallTable;

/// The `CastKind::PointerCoercion` tags of `rustc` `V2026_06_01` (the `Debug` spellings of
/// `rustc_middle::ty::adjustment::PointerCoercion` that `MirSemantics.Places` matches with
/// `stringEq coercionKind "…"`) and the [`PointerCoercionKind`] each denotes. The
/// unparameterized `ReifyFnPointer` / `ClosureFnPointer` tags accept a function pointer of
/// either safety (`reifyCoercionSafetyCompatible`); the `(Safe)` / `(Unsafe)` forms require
/// that safety of the target function pointer.
pub const POINTER_COERCION_SPELLINGS_V2026_06_01: &[(&str, PointerCoercionKind)] = &[
    ("Unsize", PointerCoercionKind::Unsize),
    ("MutToConstPointer", PointerCoercionKind::MutToConstPointer),
    ("ArrayToPointer", PointerCoercionKind::ArrayToPointer),
    ("ReifyFnPointer", PointerCoercionKind::ReifyFnPointer),
    (
        "ReifyFnPointer(Safe)",
        PointerCoercionKind::ReifyFnPointerWithSafety(Safety::Safe),
    ),
    (
        "ReifyFnPointer(Unsafe)",
        PointerCoercionKind::ReifyFnPointerWithSafety(Safety::Unsafe),
    ),
    (
        "ClosureFnPointer",
        PointerCoercionKind::ClosureFnPointerAnySafety,
    ),
    (
        "ClosureFnPointer(Safe)",
        PointerCoercionKind::ClosureFnPointer(Safety::Safe),
    ),
    (
        "ClosureFnPointer(Unsafe)",
        PointerCoercionKind::ClosureFnPointer(Safety::Unsafe),
    ),
    ("UnsafeFnPointer", PointerCoercionKind::UnsafeFnPointer),
];

/// The [`PointerCoercionKind`] that the `CastKind::PointerCoercion` tag `spelling` (compared
/// exactly, as `Trusted`'s `stringEq`) denotes in `rustc` `V2026_06_01`, or `None` for a tag
/// this version does not have.
pub fn lower_pointer_coercion_kind_v2026_06_01(spelling: &str) -> Option<PointerCoercionKind> {
    POINTER_COERCION_SPELLINGS_V2026_06_01
        .iter()
        .find(|(tag, _)| *tag == spelling)
        .map(|(_, kind)| *kind)
}

/// The `rustc` `V2026_06_01` tag of the [`PointerCoercionKind`] `kind` (the inverse of
/// [`lower_pointer_coercion_kind_v2026_06_01`]).
pub fn pointer_coercion_spelling_v2026_06_01(kind: PointerCoercionKind) -> &'static str {
    POINTER_COERCION_SPELLINGS_V2026_06_01
        .iter()
        .find(|(_, k)| *k == kind)
        .map_or("", |(tag, _)| tag)
}

/// `core::intrinsics::*` paths of the inline intrinsics, each with the [`IntrinsicOp`] of the
/// same name: `isDirectExactDivTarget` (`exact_div`) and the 26 entries of
/// `classifyRustIntrinsic?` that Anneal executes inline (its 24 value intrinsics and the call
/// forms of the memory intrinsics, `copy_nonoverlapping` and `write_bytes`).
///
/// `classifyRustIntrinsic?` has 34 entries. The other 8 are deliberately absent:
/// `const_eval_select` (not modeled: `rustc` removes it before `optimized_mir`) and the 7
/// `Trusted`-only volatile memory intrinsics (`unaligned_volatile_load`,
/// `unaligned_volatile_store`, `volatile_load`, `volatile_store`,
/// `volatile_copy_nonoverlapping_memory`, `volatile_copy_memory`, and `volatile_set_memory`).
pub const RUST_INTRINSIC_DEF_PATHS_V2026_06_01: &[(&str, IntrinsicOp)] = &[
    ("core::intrinsics::ub_checks", IntrinsicOp::UbChecks),
    ("core::intrinsics::arith_offset", IntrinsicOp::ArithOffset),
    ("core::intrinsics::ctlz", IntrinsicOp::Ctlz),
    ("core::intrinsics::ctlz_nonzero", IntrinsicOp::CtlzNonzero),
    ("core::intrinsics::cttz", IntrinsicOp::Cttz),
    ("core::intrinsics::cttz_nonzero", IntrinsicOp::CttzNonzero),
    ("core::intrinsics::ctpop", IntrinsicOp::Ctpop),
    ("core::intrinsics::bswap", IntrinsicOp::Bswap),
    ("core::intrinsics::bitreverse", IntrinsicOp::Bitreverse),
    ("core::intrinsics::wrapping_add", IntrinsicOp::WrappingAdd),
    ("core::intrinsics::wrapping_sub", IntrinsicOp::WrappingSub),
    ("core::intrinsics::wrapping_mul", IntrinsicOp::WrappingMul),
    (
        "core::intrinsics::saturating_add",
        IntrinsicOp::SaturatingAdd,
    ),
    (
        "core::intrinsics::saturating_sub",
        IntrinsicOp::SaturatingSub,
    ),
    ("core::intrinsics::unchecked_shl", IntrinsicOp::UncheckedShl),
    ("core::intrinsics::unchecked_shr", IntrinsicOp::UncheckedShr),
    ("core::intrinsics::unchecked_add", IntrinsicOp::UncheckedAdd),
    ("core::intrinsics::unchecked_sub", IntrinsicOp::UncheckedSub),
    ("core::intrinsics::unchecked_mul", IntrinsicOp::UncheckedMul),
    ("core::intrinsics::unchecked_div", IntrinsicOp::UncheckedDiv),
    ("core::intrinsics::unchecked_rem", IntrinsicOp::UncheckedRem),
    (
        "core::intrinsics::three_way_compare",
        IntrinsicOp::ThreeWayCompare,
    ),
    ("core::intrinsics::size_of_val", IntrinsicOp::SizeOfVal),
    ("core::intrinsics::align_of_val", IntrinsicOp::AlignOfVal),
    ("core::intrinsics::exact_div", IntrinsicOp::ExactDiv),
    (
        "core::intrinsics::copy_nonoverlapping",
        IntrinsicOp::CopyNonOverlapping,
    ),
    ("core::intrinsics::write_bytes", IntrinsicOp::WriteBytes),
];

/// Unreachable hints and intrinsics (`isUnreachableCallTarget`), all
/// [`IntrinsicOp::UnreachableUnchecked`].
pub const UNREACHABLE_DEF_PATHS_V2026_06_01: &[&str] = &[
    "core::hint::unreachable_unchecked",
    "std::hint::unreachable_unchecked",
    "core::intrinsics::unreachable",
];

/// Non-unwinding panic and abort entry points (`isAbortingPanicDefPath`), all
/// [`IntrinsicOp::Abort`].
pub const ABORTING_PANIC_DEF_PATHS_V2026_06_01: &[&str] = &[
    "core::panicking::panic_nounwind",
    "core::panicking::panic_nounwind_fmt",
    "core::panicking::panic_nounwind_fmt::panic_impl",
    "core::panicking::panic_nounwind_nobacktrace",
    "core::panicking::panic_in_cleanup",
    "core::panicking::panic_cannot_unwind",
    "core::panicking::panic_misaligned_pointer_dereference",
    "core::panicking::panic_null_pointer_dereference",
    "core::panicking::panic_invalid_enum_construction",
    "core::intrinsics::abort",
];

/// Unwinding panic entry points (`isUnwindingPanicDefPath`), all
/// [`IntrinsicOp::PanicUnwind`].
pub const UNWINDING_PANIC_DEF_PATHS_V2026_06_01: &[&str] = &[
    "core::panicking::panic",
    "core::panicking::panic_fmt",
    "core::panicking::panic_fmt::panic_impl",
    "core::panicking::const_panic_fmt",
    "core::panicking::assert_failed",
    "core::panicking::assert_failed_inner",
    "core::panicking::assert_matches_failed",
    "core::slice::index::slice_index_fail",
    "core::panicking::panic_bounds_check",
    "core::panicking::panic_explicit",
    "core::panicking::panic_display",
    "core::panicking::panic_str_2015",
    "core::panicking::unreachable_display",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::result::unwrap_failed",
    "core::panicking::panic_const::panic_const_add_overflow",
    "core::panicking::panic_const::panic_const_sub_overflow",
    "core::panicking::panic_const::panic_const_mul_overflow",
    "core::panicking::panic_const::panic_const_div_overflow",
    "core::panicking::panic_const::panic_const_rem_overflow",
    "core::panicking::panic_const::panic_const_neg_overflow",
    "core::panicking::panic_const::panic_const_shr_overflow",
    "core::panicking::panic_const::panic_const_shl_overflow",
    "core::panicking::panic_const::panic_const_div_by_zero",
    "core::panicking::panic_const::panic_const_rem_by_zero",
];

/// The inline intrinsic or diverging entry point that `def_path` (a direct callee's canonical
/// `DefPath`, compared exactly as `Trusted`'s `stringEq`) names in `rustc` `V2026_06_01`, or
/// `None` for an ordinary function.
///
/// It is also `None` for the paths that `Trusted` classifies or evaluates inline and Anneal
/// deliberately does not: `core::intrinsics::const_eval_select`, the 7 volatile memory
/// intrinsics of `classifyRustIntrinsic?`, and the 4 `core::ptr` raw-pointer access functions
/// of `evalUnlinkedPtrAccessCall?` (see the module documentation's `Trusted`-only paths).
pub fn lower_intrinsic_kind_v2026_06_01(def_path: &str) -> Option<IntrinsicOp> {
    if let Some((_, op)) = RUST_INTRINSIC_DEF_PATHS_V2026_06_01
        .iter()
        .find(|(path, _)| *path == def_path)
    {
        return Some(*op);
    }
    if UNREACHABLE_DEF_PATHS_V2026_06_01.contains(&def_path) {
        return Some(IntrinsicOp::UnreachableUnchecked);
    }
    if ABORTING_PANIC_DEF_PATHS_V2026_06_01.contains(&def_path) {
        return Some(IntrinsicOp::Abort);
    }
    if UNWINDING_PANIC_DEF_PATHS_V2026_06_01.contains(&def_path) {
        return Some(IntrinsicOp::PanicUnwind);
    }
    None
}

/// [`CallTarget::Intrinsic`] of [`lower_intrinsic_kind_v2026_06_01`], or `None` for an
/// ordinary function.
pub fn lower_call_target_v2026_06_01(def_path: &str) -> Option<CallTarget> {
    lower_intrinsic_kind_v2026_06_01(def_path).map(CallTarget::Intrinsic)
}

/// The call target of a direct call of `def_path`: its inline intrinsic, or else the ordinary
/// function [`CallTarget::Fn`] whose [`CalleeSymbol`] is `def_path`.
pub fn classify_call_target_v2026_06_01(def_path: &str) -> CallTarget {
    lower_call_target_v2026_06_01(def_path)
        .unwrap_or_else(|| CallTarget::Fn(CalleeSymbol::new(def_path)))
}

/// [`classify_call_target_v2026_06_01`] with `Trusted`'s precedence of linked bodies: a
/// `def_path` linked in `table` is the ordinary function [`CallTarget::Fn`] even when it also
/// names an intrinsic or panic entry point (`evalTerminator` runs a callee found by
/// `lookupCallee` before classifying the path).
pub fn classify_linked_call_target_v2026_06_01(def_path: &str, table: &CallTable) -> CallTarget {
    let symbol = CalleeSymbol::new(def_path);
    if table.contains(&symbol) {
        return CallTarget::Fn(symbol);
    }
    classify_call_target_v2026_06_01(def_path)
}
