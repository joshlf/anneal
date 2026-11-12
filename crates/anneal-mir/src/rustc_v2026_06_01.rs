//! Thin, version-tagged adapter from the callee `DefPath`s of `rustc` `V2026_06_01`
//! (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`) to Anneal's version-independent call
//! targets ([`IntrinsicOp`], [`CallTarget`]).
//!
//! This module is the only place in `anneal-mir` that recognizes `rustc` paths: the core IR
//! and its evaluator never inspect a callee's spelling, so supporting another `rustc` version
//! means adding another adapter, not touching the semantics. The tables mirror
//! `Trusted.Rustc.V2026_06_01.MirSemantics`:
//! - `classifyRustIntrinsic?` (every modeled `core::intrinsics::*` value intrinsic except
//!   `const_eval_select`, which `rustc` removes before `optimized_mir` and Anneal does not
//!   model), `isDirectExactDivTarget` (`core::intrinsics::exact_div`), and the memory
//!   intrinsics `core::intrinsics::copy_nonoverlapping` / `core::intrinsics::write_bytes`
//!   (which `Trusted` models as statements and leaves as external calls in call form; Anneal
//!   executes them inline with the statement's semantics) are
//!   [`RUST_INTRINSIC_DEF_PATHS_V2026_06_01`];
//! - `isUnreachableCallTarget` is [`UNREACHABLE_DEF_PATHS_V2026_06_01`];
//! - `isAbortingPanicDefPath` is [`ABORTING_PANIC_DEF_PATHS_V2026_06_01`];
//! - `isUnwindingPanicDefPath` is [`UNWINDING_PANIC_DEF_PATHS_V2026_06_01`].
//!
//! The diverging entry points are classified whatever the call's `target`, and Anneal executes
//! a call of one as `Trusted` executes a call without a return target (`rustc` never gives a
//! call of these `-> !` functions a target; for a hand-built call with one, `Trusted` instead
//! defers to the environment through `extCall`).
//!
//! Like `Trusted`'s `evalTerminator` (which consults `lookupCallee` before any intrinsic
//! or panic classification), [`classify_linked_call_target_v2026_06_01`] prefers a body linked
//! in a [`CallTable`] over these tables.

use crate::ir::{CallTarget, CalleeSymbol, IntrinsicOp};
use crate::lower::cfg::CallTable;

/// `core::intrinsics::*` paths of the inline intrinsics (`classifyRustIntrinsic?`,
/// `isDirectExactDivTarget`, and the call forms of the memory intrinsics).
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
