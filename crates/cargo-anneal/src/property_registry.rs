//! Unified 12-class `PropertyRegistry`, independent MIR `FaultSiteCensus`, and
//! fail-closed `FaultSiteCoverageReconciler` for `cargo-anneal`.
//!
//! This module is self-contained and `#![forbid(unsafe_code)]`-clean so it can
//! be extracted directly into `google/zerocopy:anneal/trusted/cargo-anneal/`.
//!
//! 1. **[`PropertyClass`] & [`PropertyRegistry`] (12 Canonical Classes)**:
//!    Tracks verification disposition across arithmetic overflow, shift bounds,
//!    division/remainder UB, pointer alignment/provenance/dangling dereference,
//!    slice/array bounds, union/enum discriminant validity, call argument and
//!    precondition contracts, loop termination/variant, switch/branch
//!    exhaustiveness, memory copy/set overlap, uninitialized reads, and the
//!    non-waivable unsupported-construct fallback.
//! 2. **[`FaultSiteCensus`]**:
//!    Independently enumerates every potential fault site `(block_idx, stmt_idx,
//!    is_terminator, class)` across reachable MIR blocks (plus whole-body
//!    [`PropertyClass::UnsupportedFallback`] hygiene), statements, rvalues,
//!    places, projections, operands, terminators, static allocations, and CFG /
//!    direct-recursion cycles without consulting `obligations.rs`. Includes a
//!    strict recursive-descent `Mir/<Item>.lean` parser failing closed on
//!    non-inline, malformed, or unknown syntax.
//! 3. **[`FaultSiteCoverageReconciler`]**:
//!    Enforces `census_sites ⊆ discharged_or_explicitly_waived_sites`,
//!    [`PropertyRegistry`] dispositions, exact `Obligations.<Item>` /
//!    `Verify.<Item>` token-level claim-surface pins, and `MirSemantics`-exact
//!    callee-closure invariants, returning structured
//!    [`UncoveredSiteDiagnostic`] records on any gap.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::str::FromStr;

use anneal_rustc_capture::lean_emit::{
    IrAbiPassMode, IrAggregateKind, IrAlign, IrArgAbi, IrBackendRepr, IrBasicBlockData, IrBinOp,
    IrBorrowKind, IrCallConv, IrCapturedAllocation, IrCapturedMir, IrCastKind, IrConstOperand,
    IrConstScalar, IrConstValue, IrContractRole, IrFieldsShape, IrFloatTy, IrFnAbi,
    IrGenericParamDef, IrIntTy, IrLayoutTable, IrLocalDecl, IrMirPhaseTag, IrMutability,
    IrNonDivergingIntrinsic, IrNullOp, IrOperand, IrPlace, IrPrimitiveKind, IrProjectionElem,
    IrProvenancePtr, IrRetagKind, IrRigidTy, IrRvalue, IrSafety, IrScalarInt, IrScalarLayout,
    IrSize, IrStatement, IrStatementKind, IrSwitchTargets, IrTerminator, IrTerminatorKind,
    IrTraitImplEntry, IrTraitRef, IrTy, IrTypeLayout, IrUintTy, IrUnOp, IrUnwindAction,
    IrVariantsShape, IrWrappingRange,
};

use crate::obligations::{AuthoredItemModules, SubjectObligationBundle};

// ============================================================================
// 1. Canonical 12-Class Property Taxonomy & PropertyRegistry
// ============================================================================

/// The 12 canonical MIR verification property classes tracked by
/// [`PropertyRegistry`], [`FaultSiteCensus`], and [`FaultSiteCoverageReconciler`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PropertyClass {
    /// Rank 0: Signed/unsigned integer addition, subtraction, multiplication,
    /// negation, or float-to-int overflow.
    ArithmeticOverflow,
    /// Rank 1: Bit-shift distance out of bounds (`< 0` or `>= bit_width`).
    ShiftBounds,
    /// Rank 2: Integer division or remainder by zero, or signed `MIN / -1` / `MIN % -1`.
    DivRemUb,
    /// Rank 3: Pointer alignment, provenance, Tree Borrows aliasing permission,
    /// or dangling/out-of-bounds dereference.
    PointerDereference,
    /// Rank 4: Array, slice, subslice, or runtime `Assert` index bounds check.
    SliceArrayBounds,
    /// Rank 5: Union/enum discriminant validity, scalar niche validity
    /// (`bool`, `char`, `transmute`, `assume`), or reaching `unreachable`.
    DiscriminantValidity,
    /// Rank 6: Call argument ABI compatibility, callee precondition contracts,
    /// drop glue, and unwind ABI obligations.
    CallContract,
    /// Rank 7: Loop termination / variant decrease across CFG cycle back-edges
    /// or recursive call cycles.
    LoopTermination,
    /// Rank 8: `SwitchInt` branch / `otherwise` exhaustiveness and in-bounds
    /// CFG basic-block target indices.
    SwitchExhaustiveness,
    /// Rank 9: Memory copy/set disjointness (`copy_nonoverlapping`), byte
    /// count validity, and region bounds (`copy`, `write_bytes`).
    MemoryCopyOverlap,
    /// Rank 10: Reading uninitialized or storage-dead locals, union padding,
    /// or uninitialized static allocation bytes.
    UninitRead,
    /// Rank 11: Non-waivable fail-closed fallback for unsupported or
    /// unscannable MIR constructs (e.g., `inlineAsm`, `threadLocalRef`,
    /// coroutine aggregates, `NullOp::ContractChecks`, or non-inline
    /// `CapturedMir` definitions).
    UnsupportedFallback,
}

impl PropertyClass {
    /// Total number of canonical property classes.
    pub const COUNT: usize = 12;

    /// Duplicate-free array of all 12 [`PropertyClass`] variants in canonical
    /// rank order `0..12`.
    pub const ALL: [PropertyClass; Self::COUNT] = [
        PropertyClass::ArithmeticOverflow,
        PropertyClass::ShiftBounds,
        PropertyClass::DivRemUb,
        PropertyClass::PointerDereference,
        PropertyClass::SliceArrayBounds,
        PropertyClass::DiscriminantValidity,
        PropertyClass::CallContract,
        PropertyClass::LoopTermination,
        PropertyClass::SwitchExhaustiveness,
        PropertyClass::MemoryCopyOverlap,
        PropertyClass::UninitRead,
        PropertyClass::UnsupportedFallback,
    ];

    /// 0-based canonical rank (`0..12`).
    pub const fn rank(self) -> usize {
        match self {
            Self::ArithmeticOverflow => 0,
            Self::ShiftBounds => 1,
            Self::DivRemUb => 2,
            Self::PointerDereference => 3,
            Self::SliceArrayBounds => 4,
            Self::DiscriminantValidity => 5,
            Self::CallContract => 6,
            Self::LoopTermination => 7,
            Self::SwitchExhaustiveness => 8,
            Self::MemoryCopyOverlap => 9,
            Self::UninitRead => 10,
            Self::UnsupportedFallback => 11,
        }
    }

    /// Reconstruct a [`PropertyClass`] from its canonical rank `0..12`.
    pub const fn from_rank(rank: usize) -> Option<Self> {
        match rank {
            0 => Some(Self::ArithmeticOverflow),
            1 => Some(Self::ShiftBounds),
            2 => Some(Self::DivRemUb),
            3 => Some(Self::PointerDereference),
            4 => Some(Self::SliceArrayBounds),
            5 => Some(Self::DiscriminantValidity),
            6 => Some(Self::CallContract),
            7 => Some(Self::LoopTermination),
            8 => Some(Self::SwitchExhaustiveness),
            9 => Some(Self::MemoryCopyOverlap),
            10 => Some(Self::UninitRead),
            11 => Some(Self::UnsupportedFallback),
            _ => None,
        }
    }

    /// Canonical `snake_case` wire identifier for this property class.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ArithmeticOverflow => "arithmetic_overflow",
            Self::ShiftBounds => "shift_bounds",
            Self::DivRemUb => "div_rem_ub",
            Self::PointerDereference => "pointer_deref",
            Self::SliceArrayBounds => "slice_array_bounds",
            Self::DiscriminantValidity => "discriminant_validity",
            Self::CallContract => "call_contract",
            Self::LoopTermination => "loop_termination",
            Self::SwitchExhaustiveness => "switch_exhaustiveness",
            Self::MemoryCopyOverlap => "memory_copy_overlap",
            Self::UninitRead => "uninit_read",
            Self::UnsupportedFallback => "unsupported_fallback",
        }
    }

    /// Concise human-readable description of the property class.
    pub const fn description(self) -> &'static str {
        match self {
            Self::ArithmeticOverflow => {
                "signed/unsigned arithmetic and float-to-int conversion overflow"
            }
            Self::ShiftBounds => "bit-shift distance within target integer bit width",
            Self::DivRemUb => "non-zero divisor and non-overflowing signed MIN / -1 division",
            Self::PointerDereference => {
                "pointer alignment, provenance, Tree Borrows permissions, and live dereference"
            }
            Self::SliceArrayBounds => "array, slice, subslice, and runtime assert index bounds",
            Self::DiscriminantValidity => {
                "union/enum discriminant, scalar niche validity, assume, and unreachability"
            }
            Self::CallContract => {
                "call argument ABI compatibility, callee preconditions, and unwind contracts"
            }
            Self::LoopTermination => {
                "CFG cycle back-edge and recursive-call termination / decreasing variant"
            }
            Self::SwitchExhaustiveness => {
                "SwitchInt branch / otherwise exhaustiveness and in-bounds CFG targets"
            }
            Self::MemoryCopyOverlap => {
                "copy_nonoverlapping disjointness, byte-count validity, and copy/set bounds"
            }
            Self::UninitRead => "initialized local slot and memory byte reads",
            Self::UnsupportedFallback => {
                "fail-closed fallback for unsupported or unscannable MIR constructs"
            }
        }
    }

    /// Whether explicit contract or registry waivers may ever cover sites of
    /// this class. [`PropertyClass::UnsupportedFallback`] is unconditionally
    /// non-waivable.
    pub const fn is_waivable(self) -> bool {
        !matches!(self, Self::UnsupportedFallback)
    }
}

impl fmt::Display for PropertyClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for PropertyClass {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::ALL
            .into_iter()
            .find(|c| c.as_str() == s)
            .ok_or_else(|| format!("unknown PropertyClass identifier `{s}`"))
    }
}

/// Per-class verification disposition in a [`PropertyRegistry`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PropertyDisposition {
    /// Obligation generation emits this property class into the target Lean
    /// verification claim; every censused site must appear in `discharged_sites`
    /// (or carry a validated per-site [`ExplicitSiteWaiver`]).
    Discharged,
    /// Class-wide explicit waiver with a mandatory non-empty justification
    /// (for example, waiving [`PropertyClass::LoopTermination`] under a
    /// partial-correctness `MirNoUB` specification). Forbidden on
    /// [`PropertyClass::UnsupportedFallback`].
    ExplicitlyWaived {
        /// Human- and machine-auditable reason for the class waiver.
        reason: String,
    },
    /// Obligation emission does not cover this property class; any censused
    /// site in this class fails closed even if listed in `discharged_sites`.
    UnemittedGap,
    /// Non-waivable fail-closed disposition (mandatory for
    /// [`PropertyClass::UnsupportedFallback`]).
    UnsupportedFailClosed,
}

impl PropertyDisposition {
    /// Short wire tag summarizing the disposition.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::Discharged => "discharged",
            Self::ExplicitlyWaived { .. } => "explicitly_waived",
            Self::UnemittedGap => "unemitted_gap",
            Self::UnsupportedFailClosed => "unsupported_fail_closed",
        }
    }
}

/// Single entry inside a [`PropertyRegistry`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyEntry {
    /// Canonical property class.
    pub class: PropertyClass,
    /// Active verification disposition for `class`.
    pub disposition: PropertyDisposition,
    /// Canonical summary of what `class` checks.
    pub description: &'static str,
}

/// Complete 12-class verification property registry indexed by
/// [`PropertyClass::rank`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyRegistry {
    entries: [PropertyEntry; PropertyClass::COUNT],
}

impl Default for PropertyRegistry {
    fn default() -> Self {
        Self::strict()
    }
}

impl PropertyRegistry {
    /// Construct the strict total-correctness registry: classes `0..=10`
    /// require [`PropertyDisposition::Discharged`] and
    /// [`PropertyClass::UnsupportedFallback`] is
    /// [`PropertyDisposition::UnsupportedFailClosed`].
    pub fn strict() -> Self {
        Self {
            entries: PropertyClass::ALL.map(|class| PropertyEntry {
                class,
                disposition: if class == PropertyClass::UnsupportedFallback {
                    PropertyDisposition::UnsupportedFailClosed
                } else {
                    PropertyDisposition::Discharged
                },
                description: class.description(),
            }),
        }
    }

    /// Construct the partial-correctness (`MirNoUB`) registry: identical to
    /// [`Self::strict`], except [`PropertyClass::LoopTermination`] carries an
    /// explicit partial-correctness divergence waiver.
    pub fn for_partial_correctness() -> Self {
        let mut reg = Self::strict();
        reg.entries[PropertyClass::LoopTermination.rank()].disposition =
            PropertyDisposition::ExplicitlyWaived {
                reason: String::from(
                    "partial-correctness MirNoUB claim permits safe non-termination; \
                     use TotalItemSpec / #[spec(safe_total)] to require termination",
                ),
            };
        reg
    }

    /// Select the canonical [`PropertyRegistry`] matching a subject bundle and
    /// its active authored contract surface.
    pub fn for_bundle(bundle: &SubjectObligationBundle, authored: AuthoredItemModules) -> Self {
        if authored.is_total || authored.is_equiv || bundle.has_rust_safe_total_attr() {
            Self::strict()
        } else {
            Self::for_partial_correctness()
        }
    }

    /// Construct a fail-closed registry in which all 11 waivable classes are
    /// marked [`PropertyDisposition::UnemittedGap`] and
    /// [`PropertyClass::UnsupportedFallback`] is
    /// [`PropertyDisposition::UnsupportedFailClosed`].
    pub fn all_unemitted() -> Self {
        Self {
            entries: PropertyClass::ALL.map(|class| PropertyEntry {
                class,
                disposition: if class == PropertyClass::UnsupportedFallback {
                    PropertyDisposition::UnsupportedFailClosed
                } else {
                    PropertyDisposition::UnemittedGap
                },
                description: class.description(),
            }),
        }
    }

    /// Update the disposition of `class`, rejecting attempts to mark
    /// [`PropertyClass::UnsupportedFallback`] as discharged or waived, or to
    /// supply an empty waiver reason.
    pub fn try_set_disposition(
        &mut self,
        class: PropertyClass,
        disposition: PropertyDisposition,
    ) -> Result<(), String> {
        validate_disposition_for_class(class, &disposition)?;
        self.entries[class.rank()].disposition = disposition;
        Ok(())
    }

    /// Builder-style wrapper around [`Self::try_set_disposition`].
    pub fn try_with_disposition(
        mut self,
        class: PropertyClass,
        disposition: PropertyDisposition,
    ) -> Result<Self, String> {
        self.try_set_disposition(class, disposition)?;
        Ok(self)
    }

    /// Look up the [`PropertyDisposition`] for `class`.
    pub fn disposition(&self, class: PropertyClass) -> &PropertyDisposition {
        &self.entries[class.rank()].disposition
    }

    /// Look up the full [`PropertyEntry`] for `class`.
    pub fn entry(&self, class: PropertyClass) -> &PropertyEntry {
        &self.entries[class.rank()]
    }

    /// Return all 12 [`PropertyEntry`] records in canonical rank order.
    pub fn entries(&self) -> &[PropertyEntry; PropertyClass::COUNT] {
        &self.entries
    }

    /// Render a deterministic single-line summary of the registry's
    /// dispositions.
    pub fn summary_line(&self) -> String {
        let mut discharged = 0usize;
        let mut waived = 0usize;
        let mut unemitted = 0usize;
        let mut unsupported = 0usize;
        for entry in &self.entries {
            match entry.disposition {
                PropertyDisposition::Discharged => discharged += 1,
                PropertyDisposition::ExplicitlyWaived { .. } => waived += 1,
                PropertyDisposition::UnemittedGap => unemitted += 1,
                PropertyDisposition::UnsupportedFailClosed => unsupported += 1,
            }
        }
        format!(
            "PropertyRegistry(total=12, discharged={discharged}, waived={waived}, \
             unemitted_gap={unemitted}, unsupported_fail_closed={unsupported})"
        )
    }
}

fn validate_disposition_for_class(
    class: PropertyClass,
    disposition: &PropertyDisposition,
) -> Result<(), String> {
    if !class.is_waivable() {
        match disposition {
            PropertyDisposition::Discharged | PropertyDisposition::ExplicitlyWaived { .. } => {
                return Err(format!(
                    "property class `{class}` is non-waivable and cannot be set to `{}`",
                    disposition.tag()
                ));
            }
            PropertyDisposition::UnemittedGap | PropertyDisposition::UnsupportedFailClosed => {}
        }
    }
    if let PropertyDisposition::ExplicitlyWaived { reason } = disposition
        && reason.trim().is_empty()
    {
        return Err(format!(
            "explicit waiver for property class `{class}` requires a non-empty justification"
        ));
    }
    Ok(())
}

// ============================================================================
// 2. Exact `MirSemantics` Native Call Target Tables
// ============================================================================

/// Returns `true` when `def_path` is a `core::intrinsics::*` or
/// `unreachable_unchecked` target evaluated inline on converging (or diverging
/// unreachable) calls by `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator`
/// (`isDirectExactDivTarget`, `classifyRustIntrinsic?`, and
/// `isUnreachableCallTarget` in `Terminators.lean`).
pub fn is_natively_modeled_converging_mir_callee(def_path: &str) -> bool {
    matches!(
        def_path,
        "core::intrinsics::exact_div"
            | "core::intrinsics::ub_checks"
            | "core::intrinsics::const_eval_select"
            | "core::intrinsics::arith_offset"
            | "core::intrinsics::ctlz"
            | "core::intrinsics::ctlz_nonzero"
            | "core::intrinsics::cttz"
            | "core::intrinsics::cttz_nonzero"
            | "core::intrinsics::ctpop"
            | "core::intrinsics::bswap"
            | "core::intrinsics::bitreverse"
            | "core::intrinsics::wrapping_add"
            | "core::intrinsics::wrapping_sub"
            | "core::intrinsics::wrapping_mul"
            | "core::intrinsics::saturating_add"
            | "core::intrinsics::saturating_sub"
            | "core::intrinsics::unchecked_shl"
            | "core::intrinsics::unchecked_shr"
            | "core::intrinsics::unchecked_add"
            | "core::intrinsics::unchecked_sub"
            | "core::intrinsics::unchecked_mul"
            | "core::intrinsics::unchecked_div"
            | "core::intrinsics::unchecked_rem"
            | "core::intrinsics::three_way_compare"
            | "core::intrinsics::size_of_val"
            | "core::intrinsics::align_of_val"
            | "core::intrinsics::copy_nonoverlapping"
            | "core::intrinsics::write_bytes"
            | "core::intrinsics::unreachable"
            | "core::hint::unreachable_unchecked"
            | "std::hint::unreachable_unchecked"
    )
}

/// Returns `true` when `def_path` is a diverging (`target == None`) panic,
/// abort, or unreachable entrypoint evaluated inline by
/// `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator`
/// (`isUnreachableCallTarget`, `isAbortingPanicDefPath`, and
/// `isUnwindingPanicDefPath` in `Terminators.lean`).
pub fn is_natively_modeled_diverging_mir_callee(def_path: &str) -> bool {
    matches!(
        def_path,
        "core::hint::unreachable_unchecked"
            | "std::hint::unreachable_unchecked"
            | "core::intrinsics::unreachable"
            | "core::panicking::panic_nounwind"
            | "core::panicking::panic_nounwind_fmt"
            | "core::panicking::panic_nounwind_fmt::panic_impl"
            | "core::panicking::panic_nounwind_nobacktrace"
            | "core::panicking::panic_in_cleanup"
            | "core::panicking::panic_cannot_unwind"
            | "core::panicking::panic_misaligned_pointer_dereference"
            | "core::panicking::panic_null_pointer_dereference"
            | "core::panicking::panic_invalid_enum_construction"
            | "core::intrinsics::abort"
            | "core::panicking::panic"
            | "core::panicking::panic_fmt"
            | "core::panicking::panic_fmt::panic_impl"
            | "core::panicking::const_panic_fmt"
            | "core::panicking::assert_failed"
            | "core::panicking::assert_failed_inner"
            | "core::panicking::assert_matches_failed"
            | "core::slice::index::slice_index_fail"
            | "core::panicking::panic_bounds_check"
            | "core::panicking::panic_explicit"
            | "core::panicking::panic_display"
            | "core::panicking::panic_str_2015"
            | "core::panicking::unreachable_display"
            | "core::option::unwrap_failed"
            | "core::option::expect_failed"
            | "core::result::unwrap_failed"
            | "core::panicking::panic_const::panic_const_add_overflow"
            | "core::panicking::panic_const::panic_const_sub_overflow"
            | "core::panicking::panic_const::panic_const_mul_overflow"
            | "core::panicking::panic_const::panic_const_div_overflow"
            | "core::panicking::panic_const::panic_const_rem_overflow"
            | "core::panicking::panic_const::panic_const_neg_overflow"
            | "core::panicking::panic_const::panic_const_shr_overflow"
            | "core::panicking::panic_const::panic_const_shl_overflow"
            | "core::panicking::panic_const::panic_const_div_by_zero"
            | "core::panicking::panic_const::panic_const_rem_by_zero"
    )
}

/// Returns `true` when a direct call to `def_path` with `is_diverging`
/// (`target == None`) is modeled natively by `MirSemantics` without requiring
/// `defaultCallees` or `ModularItemSpec.envAssumed`.
pub fn is_natively_modeled_mir_call(def_path: &str, is_diverging: bool) -> bool {
    if is_diverging {
        is_natively_modeled_diverging_mir_callee(def_path)
            || is_natively_modeled_converging_mir_callee(def_path)
    } else {
        is_natively_modeled_converging_mir_callee(def_path)
    }
}

/// Convenience check returning `true` when `def_path` is natively modeled in
/// converging position (`is_natively_modeled_converging_mir_callee`).
pub fn is_natively_modeled_mir_callee(def_path: &str) -> bool {
    is_natively_modeled_converging_mir_callee(def_path)
}

// ============================================================================
// 3. FaultSite & Independent MIR FaultSiteCensus
// ============================================================================

/// Single potential runtime fault or contract obligation site inside a MIR body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FaultSite {
    /// 0-based index into `basic_blocks`.
    pub block_idx: usize,
    /// 0-based statement index (`0..statements.len()`) for straight-line
    /// statements, or `statements.len()` for the block's terminator.
    pub stmt_idx: usize,
    /// `true` when this site originates from the block's terminator rather than
    /// `statements[stmt_idx]`.
    pub is_terminator: bool,
    /// Canonical [`PropertyClass`] triggered at this location.
    pub class: PropertyClass,
}

impl FaultSite {
    /// Construct a fault site on straight-line statement `stmt_idx` of `block_idx`.
    pub const fn statement(block_idx: usize, stmt_idx: usize, class: PropertyClass) -> Self {
        Self {
            block_idx,
            stmt_idx,
            is_terminator: false,
            class,
        }
    }

    /// Construct a fault site on the terminator of `block_idx` (at `stmt_idx ==
    /// statements.len()`).
    pub const fn terminator(block_idx: usize, stmt_idx: usize, class: PropertyClass) -> Self {
        Self {
            block_idx,
            stmt_idx,
            is_terminator: true,
            class,
        }
    }
}

impl fmt::Display for FaultSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = if self.is_terminator { "term" } else { "stmt" };
        write!(
            f,
            "(bb{}, {}[{}], {})",
            self.block_idx, kind, self.stmt_idx, self.class
        )
    }
}

/// Resolved call-site descriptor recorded in [`FaultSiteCensus::call_site_targets`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallSiteTarget {
    /// `Some(def_path)` for direct function-item calls; `None` for indirect
    /// runtime function-pointer calls.
    pub callee: Option<String>,
    /// `true` iff `TerminatorKind::Call { target: None, .. }`.
    pub is_diverging: bool,
}

/// Error returned when a `Mir/<Item>.lean` source file violates module hygiene
/// or cannot be parsed as an inline `CapturedMir` definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusError {
    /// Detailed explanation of why strict MIR parsing failed.
    pub message: String,
}

impl CensusError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for CensusError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CensusError {}

/// Independent fault-site census of a single `CapturedMir` body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaultSiteCensus {
    /// Canonical Rust `DefPath` of the inspected body.
    pub def_path: String,
    /// Total number of basic blocks in `basic_blocks`.
    pub basic_block_count: usize,
    /// Deterministically ordered set of all censused [`FaultSite`] entries.
    pub sites: BTreeSet<FaultSite>,
    /// Direct function-item callees (`DefPath`) invoked by reachable `Call` /
    /// `TailCall` terminators.
    pub direct_callees: BTreeSet<String>,
    /// Map from `(block_idx, term_stmt_idx)` of each reachable `Call` /
    /// `TailCall` terminator to its [`CallSiteTarget`].
    pub call_site_targets: BTreeMap<(usize, usize), CallSiteTarget>,
    /// Function items reified into function pointers or referenced via
    /// `traitImpls` inside the body (informational metadata).
    pub reified_fn_defs: BTreeSet<String>,
    /// Directed CFG edges `(latch_bb, header_bb)` closing a reachable cycle in
    /// `basic_blocks`.
    pub loop_back_edges: Vec<(usize, usize)>,
    /// Non-empty when unscannable, malformed, or unsupported syntax forced a
    /// fail-closed [`PropertyClass::UnsupportedFallback`] site.
    pub unscannable_reasons: Vec<String>,
}

impl FaultSiteCensus {
    /// Compute the [`FaultSiteCensus`] of an [`IrCapturedMir`], filtering
    /// `IrStatementKind::Retag` to match `emit_mir_lean_module`'s `basicBlocks`
    /// indexing 1-to-1.
    pub fn from_ir_captured_mir(mir: &IrCapturedMir) -> Self {
        Self::from_ir_captured_mir_with_options(mir, false)
    }

    /// Compute the [`FaultSiteCensus`] of an [`IrCapturedMir`], optionally
    /// preserving `IrStatementKind::Retag` statements (used when inspecting a
    /// parsed `Mir/<Item>.lean` module whose `basicBlocks` list already
    /// reflects the exact statements seen by Lean).
    pub fn from_ir_captured_mir_with_options(mir: &IrCapturedMir, preserve_retags: bool) -> Self {
        let mut sites = BTreeSet::new();
        let mut direct_callees = BTreeSet::new();
        let mut call_site_targets = BTreeMap::new();
        let mut reified_fn_defs = BTreeSet::new();
        let mut unscannable_reasons = Vec::new();

        for impl_entry in &mir.trait_impls {
            if !impl_entry.impl_path.is_empty() {
                reified_fn_defs.insert(impl_entry.impl_path.clone());
            }
        }

        if !matches!(
            mir.phase,
            IrMirPhaseTag::RuntimePostCleanup | IrMirPhaseTag::RuntimeOptimized
        ) {
            sites.insert(FaultSite::terminator(
                0,
                0,
                PropertyClass::UnsupportedFallback,
            ));
            unscannable_reasons.push(format!(
                "unsupported MIR phase `{:?}` on `{}`",
                mir.phase, mir.def_path
            ));
        }

        let num_blocks = mir.basic_blocks.len();
        if num_blocks == 0 {
            sites.insert(FaultSite::terminator(
                0,
                0,
                PropertyClass::UnsupportedFallback,
            ));
            unscannable_reasons.push(format!(
                "CapturedMir `{}` has zero basic blocks (missing entry block bb0)",
                mir.def_path
            ));
            return Self {
                def_path: mir.def_path.clone(),
                basic_block_count: 0,
                sites,
                direct_callees,
                call_site_targets,
                reified_fn_defs,
                loop_back_edges: Vec::new(),
                unscannable_reasons,
            };
        }

        let ctx = MirBodyTypingCtx {
            local_decls: &mir.local_decls,
            layouts: &mir.layouts,
            allocations: &mir.allocations,
        };

        let reachable = compute_cfg_reachable_blocks(&mir.basic_blocks);
        let loop_back_edges: Vec<(usize, usize)> = detect_cfg_cycle_back_edges(&mir.basic_blocks)
            .into_iter()
            .filter(|&(latch, _)| reachable[latch])
            .collect();
        let back_edge_latches: BTreeSet<usize> =
            loop_back_edges.iter().map(|&(latch, _)| latch).collect();

        for (bb_idx, bb) in mir.basic_blocks.iter().enumerate() {
            let is_reachable = reachable[bb_idx];
            let effective_stmts: Vec<&IrStatement> = bb
                .statements
                .iter()
                .filter(|s| preserve_retags || !matches!(s.kind, IrStatementKind::Retag(_, _)))
                .collect();

            for (stmt_idx, stmt) in effective_stmts.iter().enumerate() {
                let mut stmt_classes = Vec::new();
                census_statement_kind(
                    &ctx,
                    &stmt.kind,
                    &mut stmt_classes,
                    &mut reified_fn_defs,
                    &mut unscannable_reasons,
                );
                for class in stmt_classes {
                    // Runtime UB sites apply to blocks reachable from entry
                    // `bb0`, whereas `UnsupportedFallback` fails closed across
                    // the entire module even inside dead blocks.
                    if is_reachable || class == PropertyClass::UnsupportedFallback {
                        sites.insert(FaultSite::statement(bb_idx, stmt_idx, class));
                    }
                }
            }

            let term_idx = effective_stmts.len();
            let mut term_classes = Vec::new();
            if is_reachable && back_edge_latches.contains(&bb_idx) {
                term_classes.push(PropertyClass::LoopTermination);
            }
            for succ in terminator_all_targets(&bb.terminator.kind) {
                if succ >= num_blocks && is_reachable {
                    term_classes.push(PropertyClass::SwitchExhaustiveness);
                }
            }
            let mut local_callees = BTreeSet::new();
            let mut local_call_targets = BTreeMap::new();
            census_terminator_kind(
                &ctx,
                &mir.def_path,
                bb_idx,
                term_idx,
                &bb.terminator.kind,
                &mut term_classes,
                &mut local_callees,
                &mut local_call_targets,
                &mut reified_fn_defs,
                &mut unscannable_reasons,
            );
            if is_reachable {
                direct_callees.extend(local_callees);
                call_site_targets.extend(local_call_targets);
            }
            for class in term_classes {
                if is_reachable || class == PropertyClass::UnsupportedFallback {
                    sites.insert(FaultSite::terminator(bb_idx, term_idx, class));
                }
            }
        }

        Self {
            def_path: mir.def_path.clone(),
            basic_block_count: num_blocks,
            sites,
            direct_callees,
            call_site_targets,
            reified_fn_defs,
            loop_back_edges,
            unscannable_reasons,
        }
    }

    /// Parse a `Mir/<Item>.lean` source module strictly into an
    /// [`IrCapturedMir`] and compute its [`FaultSiteCensus`], preserving all
    /// statements present in `basicBlocks` (including any explicit
    /// `StatementKind.retag`) at their exact Lean statement indices.
    pub fn from_lean_mir_module(lean_src: &str) -> Result<Self, CensusError> {
        let parsed = parse_lean_mir_module_strict(lean_src)?;
        Ok(Self::from_ir_captured_mir_with_options(&parsed, true))
    }

    /// Parse a `Mir/<Item>.lean` source module, converting any [`CensusError`]
    /// into a fail-closed [`FaultSiteCensus`] containing a non-waivable
    /// [`PropertyClass::UnsupportedFallback`] site so malformed or non-inline
    /// MIR modules never fail open.
    pub fn from_lean_mir_fail_closed(fallback_def_path: &str, lean_src: &str) -> Self {
        match Self::from_lean_mir_module(lean_src) {
            Ok(census) => census,
            Err(err) => Self::fail_closed_with_reason(fallback_def_path, err.message),
        }
    }

    /// Construct a single-site fail-closed [`PropertyClass::UnsupportedFallback`]
    /// census carrying `reason`.
    pub fn fail_closed_with_reason(def_path: &str, reason: impl Into<String>) -> Self {
        let mut sites = BTreeSet::new();
        sites.insert(FaultSite::terminator(
            0,
            0,
            PropertyClass::UnsupportedFallback,
        ));
        Self {
            def_path: def_path.to_string(),
            basic_block_count: 0,
            sites,
            direct_callees: BTreeSet::new(),
            call_site_targets: BTreeMap::new(),
            reified_fn_defs: BTreeSet::new(),
            loop_back_edges: Vec::new(),
            unscannable_reasons: vec![reason.into()],
        }
    }

    /// Augment this census with [`PropertyClass::LoopTermination`] sites on
    /// every reachable call terminator whose target `DefPath` belongs to
    /// `recursive_callees` (used for mutual/transitive recursion across a
    /// `defaultCallees` call graph; direct self-recursion is already recorded
    /// during [`Self::from_ir_captured_mir`]).
    pub fn add_recursive_call_termination_sites(&mut self, recursive_callees: &BTreeSet<String>) {
        for (&(bb_idx, term_idx), target) in &self.call_site_targets {
            if let Some(ref callee) = target.callee
                && recursive_callees.contains(callee)
            {
                self.sites.insert(FaultSite::terminator(
                    bb_idx,
                    term_idx,
                    PropertyClass::LoopTermination,
                ));
            }
        }
    }

    /// Count censused fault sites grouped by [`PropertyClass`].
    pub fn counts_by_class(&self) -> BTreeMap<PropertyClass, usize> {
        let mut counts = BTreeMap::new();
        for site in &self.sites {
            *counts.entry(site.class).or_insert(0) += 1;
        }
        counts
    }

    /// Whether any reachable call site invokes an indirect function pointer.
    pub fn has_indirect_call(&self) -> bool {
        self.call_site_targets.values().any(|t| t.callee.is_none())
    }

    /// Render a deterministic one-line summary for `cargo anneal agent-context`
    /// and diagnostics.
    pub fn summary_line(&self) -> String {
        let counts = self.counts_by_class();
        if counts.is_empty() {
            return format!("0 sites across {} basic block(s)", self.basic_block_count);
        }
        let parts: Vec<String> = counts
            .iter()
            .map(|(cls, n)| format!("{cls}:{n}"))
            .collect();
        format!(
            "{} site(s) across {} basic block(s) [{}]",
            self.sites.len(),
            self.basic_block_count,
            parts.join(", ")
        )
    }
}

fn compute_cfg_reachable_blocks(basic_blocks: &[IrBasicBlockData]) -> Vec<bool> {
    let n = basic_blocks.len();
    let mut reachable = vec![false; n];
    if n == 0 {
        return reachable;
    }
    let mut stack = vec![0usize];
    while let Some(bb) = stack.pop() {
        if bb >= n || reachable[bb] {
            continue;
        }
        reachable[bb] = true;
        for succ in terminator_all_targets(&basic_blocks[bb].terminator.kind) {
            if succ < n && !reachable[succ] {
                stack.push(succ);
            }
        }
    }
    reachable
}

struct MirBodyTypingCtx<'a> {
    local_decls: &'a [IrLocalDecl],
    layouts: &'a IrLayoutTable,
    allocations: &'a [IrCapturedAllocation],
}

impl<'a> MirBodyTypingCtx<'a> {
    fn check_local_in_bounds(
        &self,
        local_idx: usize,
        out: &mut Vec<PropertyClass>,
        reasons: &mut Vec<String>,
    ) {
        if !self.local_decls.is_empty() && local_idx >= self.local_decls.len() {
            out.push(PropertyClass::UnsupportedFallback);
            reasons.push(format!(
                "out-of-bounds local index _{local_idx} (local_decls.len() == {})",
                self.local_decls.len()
            ));
        }
    }

    fn layout_is_union(&self, layout_idx: usize) -> bool {
        self.layouts
            .entries
            .get(layout_idx)
            .is_some_and(|l| matches!(l.fields, IrFieldsShape::Union { .. }))
    }

    fn place_reads_union_field(&self, place: &IrPlace) -> bool {
        let mut cur_ty_opt: Option<IrTy> = self.local_decls.get(place.local_).map(|d| d.ty.clone());
        for proj in &place.projection {
            match proj {
                IrProjectionElem::Field(_, fty) => {
                    if let Some(ref container_ty) = cur_ty_opt
                        && self.layout_is_union(container_ty.layout_idx)
                    {
                        return true;
                    }
                    cur_ty_opt = Some(fty.clone());
                }
                IrProjectionElem::Deref => {
                    cur_ty_opt = cur_ty_opt.and_then(|t| self.pointee_ty(&t));
                }
                IrProjectionElem::Index(_) | IrProjectionElem::ConstantIndex { .. } => {
                    cur_ty_opt = cur_ty_opt.and_then(|t| self.elem_ty(&t));
                }
                IrProjectionElem::OpaqueCast(ty) | IrProjectionElem::UnwrapUnsafeBinder(ty) => {
                    cur_ty_opt = Some(ty.clone());
                }
                IrProjectionElem::Subslice { .. } | IrProjectionElem::Downcast(_, _) => {}
            }
        }
        false
    }

    fn pointee_ty(&self, ptr_ty: &IrTy) -> Option<IrTy> {
        let inner_kind = match &ptr_ty.kind {
            IrRigidTy::Ref(_, inner) | IrRigidTy::RawPtr(_, inner) => (**inner).clone(),
            _ => return None,
        };
        let pointee_layout_idx = self
            .layouts
            .entries
            .get(ptr_ty.layout_idx)
            .and_then(|l| l.field_layouts.first().copied())
            .unwrap_or(0);
        Some(IrTy {
            kind: inner_kind,
            layout_idx: pointee_layout_idx,
        })
    }

    fn elem_ty(&self, container_ty: &IrTy) -> Option<IrTy> {
        match &container_ty.kind {
            IrRigidTy::Array(elem, _) | IrRigidTy::Slice(elem) => Some(IrTy {
                kind: (**elem).clone(),
                layout_idx: 0,
            }),
            _ => None,
        }
    }

    fn resolve_place_ty(&self, place: &IrPlace) -> Option<IrTy> {
        let mut cur = self.local_decls.get(place.local_)?.ty.clone();
        for proj in &place.projection {
            match proj {
                IrProjectionElem::Field(_, fty)
                | IrProjectionElem::OpaqueCast(fty)
                | IrProjectionElem::UnwrapUnsafeBinder(fty) => cur = fty.clone(),
                IrProjectionElem::Deref => cur = self.pointee_ty(&cur)?,
                IrProjectionElem::Index(_) | IrProjectionElem::ConstantIndex { .. } => {
                    cur = self.elem_ty(&cur)?;
                }
                IrProjectionElem::Subslice { .. } | IrProjectionElem::Downcast(_, _) => {}
            }
        }
        Some(cur)
    }

    fn operand_is_ptr_like(&self, op: &IrOperand) -> bool {
        let ty_opt = match op {
            IrOperand::Constant(co) => Some(co.ty.kind.clone()),
            IrOperand::Copy(p) | IrOperand::Move(p) => self.resolve_place_ty(p).map(|t| t.kind),
        };
        matches!(
            ty_opt,
            Some(IrRigidTy::RawPtr(_, _) | IrRigidTy::Ref(_, _) | IrRigidTy::FnPtr(_, _, _, _))
        )
    }

    fn body_has_any_ref_or_ptr_local(&self) -> bool {
        self.local_decls.iter().any(|d| {
            matches!(
                d.ty.kind,
                IrRigidTy::Ref(_, _) | IrRigidTy::RawPtr(_, _)
            )
        })
    }

    fn lookup_allocation(&self, alloc_id: u64) -> Option<&'a IrCapturedAllocation> {
        self.allocations.iter().find(|a| a.alloc_id == alloc_id)
    }
}

fn collect_rigid_ty_fn_defs(ty: &IrRigidTy, reified: &mut BTreeSet<String>) {
    match ty {
        IrRigidTy::FnDef(def_path, args) => {
            if !def_path.is_empty() {
                reified.insert(def_path.clone());
            }
            for arg in args {
                collect_rigid_ty_fn_defs(arg, reified);
            }
        }
        IrRigidTy::Tuple(elems)
        | IrRigidTy::Adt(_, elems)
        | IrRigidTy::Closure(_, elems)
        | IrRigidTy::Alias { args: elems, .. } => {
            for elem in elems {
                collect_rigid_ty_fn_defs(elem, reified);
            }
        }
        IrRigidTy::Array(inner, _)
        | IrRigidTy::Slice(inner)
        | IrRigidTy::Ref(_, inner)
        | IrRigidTy::RawPtr(_, inner) => collect_rigid_ty_fn_defs(inner, reified),
        IrRigidTy::FnPtr(inputs, output, _, _) => {
            for inp in inputs {
                collect_rigid_ty_fn_defs(inp, reified);
            }
            collect_rigid_ty_fn_defs(output, reified);
        }
        IrRigidTy::Bool
        | IrRigidTy::Char
        | IrRigidTy::Int(_)
        | IrRigidTy::Uint(_)
        | IrRigidTy::Float(_)
        | IrRigidTy::Never
        | IrRigidTy::Str
        | IrRigidTy::Dynamic(_)
        | IrRigidTy::Foreign(_)
        | IrRigidTy::Other(_)
        | IrRigidTy::Param { .. } => {}
    }
}

fn census_place_projections(
    ctx: &MirBodyTypingCtx<'_>,
    place: &IrPlace,
    out: &mut Vec<PropertyClass>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    ctx.check_local_in_bounds(place.local_, out, reasons);
    for proj in &place.projection {
        match proj {
            IrProjectionElem::Deref => {
                out.push(PropertyClass::UninitRead);
                out.push(PropertyClass::PointerDereference);
            }
            IrProjectionElem::Field(_, fty) => {
                collect_rigid_ty_fn_defs(&fty.kind, reified);
                if matches!(fty.kind, IrRigidTy::Other(_)) {
                    out.push(PropertyClass::UnsupportedFallback);
                    reasons.push(String::from("unlowered RigidTy.other in field projection"));
                }
            }
            IrProjectionElem::Index(idx_local) => {
                ctx.check_local_in_bounds(*idx_local, out, reasons);
                out.push(PropertyClass::UninitRead);
                out.push(PropertyClass::SliceArrayBounds);
            }
            IrProjectionElem::ConstantIndex { .. } | IrProjectionElem::Subslice { .. } => {
                out.push(PropertyClass::SliceArrayBounds);
            }
            IrProjectionElem::Downcast(_, _) => {
                out.push(PropertyClass::DiscriminantValidity);
            }
            IrProjectionElem::OpaqueCast(ty) | IrProjectionElem::UnwrapUnsafeBinder(ty) => {
                collect_rigid_ty_fn_defs(&ty.kind, reified);
                if matches!(ty.kind, IrRigidTy::Other(_)) {
                    out.push(PropertyClass::UnsupportedFallback);
                    reasons.push(String::from("unlowered RigidTy.other in cast/binder projection"));
                }
            }
        }
    }
}

fn census_place_read(
    ctx: &MirBodyTypingCtx<'_>,
    place: &IrPlace,
    out: &mut Vec<PropertyClass>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    out.push(PropertyClass::UninitRead);
    if ctx.place_reads_union_field(place) {
        out.push(PropertyClass::DiscriminantValidity);
    }
    census_place_projections(ctx, place, out, reified, reasons);
}

fn census_place_write(
    ctx: &MirBodyTypingCtx<'_>,
    place: &IrPlace,
    out: &mut Vec<PropertyClass>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    if !place.projection.is_empty() {
        out.push(PropertyClass::UninitRead);
    }
    census_place_projections(ctx, place, out, reified, reasons);
}

fn census_alloc_tree(
    ctx: &MirBodyTypingCtx<'_>,
    alloc_id: u64,
    offset_bytes: u64,
    visited: &mut BTreeSet<u64>,
    out: &mut Vec<PropertyClass>,
) {
    out.push(PropertyClass::PointerDereference);
    let Some(alloc) = ctx.lookup_allocation(alloc_id) else {
        out.push(PropertyClass::UninitRead);
        return;
    };
    if usize::try_from(offset_bytes).map_or(true, |off| off > alloc.bytes.len()) {
        out.push(PropertyClass::SliceArrayBounds);
    }
    if alloc.bytes.iter().any(Option::is_none) {
        out.push(PropertyClass::UninitRead);
    }
    if visited.insert(alloc_id) {
        for &(_, reloc_ptr) in &alloc.relocations {
            census_alloc_tree(ctx, reloc_ptr.alloc_id, reloc_ptr.offset_bytes, visited, out);
        }
    }
}

fn census_const_operand(
    ctx: &MirBodyTypingCtx<'_>,
    co: &IrConstOperand,
    is_direct_call_func: bool,
    out: &mut Vec<PropertyClass>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    if !is_direct_call_func {
        collect_rigid_ty_fn_defs(&co.ty.kind, reified);
    }
    if matches!(co.ty.kind, IrRigidTy::Never) {
        out.push(PropertyClass::DiscriminantValidity);
    }
    if matches!(co.ty.kind, IrRigidTy::Other(_)) {
        out.push(PropertyClass::UnsupportedFallback);
        reasons.push(String::from("unlowered RigidTy.other in constant operand"));
    }

    match &co.val {
        IrConstValue::ZeroSized => {}
        IrConstValue::Scalar(IrConstScalar::Int(si)) => match co.ty.kind {
            IrRigidTy::Bool if si.bits > 1 => out.push(PropertyClass::DiscriminantValidity),
            IrRigidTy::Char
                if si.bits > 0x10FFFF || (0xD800..=0xDFFF).contains(&si.bits) =>
            {
                out.push(PropertyClass::DiscriminantValidity);
            }
            _ => {}
        },
        IrConstValue::Scalar(IrConstScalar::Ptr(ptr, _)) => {
            let mut visited = BTreeSet::new();
            census_alloc_tree(ctx, ptr.alloc_id, ptr.offset_bytes, &mut visited, out);
        }
        IrConstValue::Slice { data, .. } => {
            if let IrConstScalar::Ptr(ptr, _) = data {
                let mut visited = BTreeSet::new();
                census_alloc_tree(ctx, ptr.alloc_id, ptr.offset_bytes, &mut visited, out);
            }
        }
        IrConstValue::Indirect {
            alloc_id,
            offset_bytes,
        } => {
            let mut visited = BTreeSet::new();
            census_alloc_tree(ctx, *alloc_id, *offset_bytes, &mut visited, out);
        }
        IrConstValue::Unevaluated(def_path) => {
            if !is_direct_call_func {
                out.push(PropertyClass::UnsupportedFallback);
                reasons.push(format!(
                    "unevaluated constant `{def_path}` in value position"
                ));
            }
        }
    }
}

fn census_operand(
    ctx: &MirBodyTypingCtx<'_>,
    op: &IrOperand,
    out: &mut Vec<PropertyClass>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    match op {
        IrOperand::Copy(place) | IrOperand::Move(place) => {
            census_place_read(ctx, place, out, reified, reasons);
        }
        IrOperand::Constant(co) => {
            census_const_operand(ctx, co, false, out, reified, reasons);
        }
    }
}

fn census_rvalue(
    ctx: &MirBodyTypingCtx<'_>,
    rv: &IrRvalue,
    out: &mut Vec<PropertyClass>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    match rv {
        IrRvalue::Use(op) | IrRvalue::Repeat(op, _) => {
            census_operand(ctx, op, out, reified, reasons);
        }
        IrRvalue::WrapUnsafeBinder(op, ty) => {
            collect_rigid_ty_fn_defs(&ty.kind, reified);
            census_operand(ctx, op, out, reified, reasons);
        }
        IrRvalue::ShallowInitBox(op, ty) => {
            collect_rigid_ty_fn_defs(&ty.kind, reified);
            census_operand(ctx, op, out, reified, reasons);
            out.push(PropertyClass::PointerDereference);
        }
        IrRvalue::Ref(_, place) | IrRvalue::RawPtr(_, place) => {
            out.push(PropertyClass::PointerDereference);
            census_place_projections(ctx, place, out, reified, reasons);
        }
        IrRvalue::ThreadLocalRef(path) => {
            out.push(PropertyClass::UnsupportedFallback);
            reasons.push(format!("unsupported Rvalue.threadLocalRef `{path}`"));
        }
        IrRvalue::Len(place) => {
            census_place_read(ctx, place, out, reified, reasons);
            out.push(PropertyClass::SliceArrayBounds);
        }
        IrRvalue::CopyForDeref(place) => {
            census_place_read(ctx, place, out, reified, reasons);
            out.push(PropertyClass::PointerDereference);
        }
        IrRvalue::Discriminant(place) => {
            census_place_read(ctx, place, out, reified, reasons);
            out.push(PropertyClass::DiscriminantValidity);
        }
        IrRvalue::Cast(ck, op, target_ty) => {
            collect_rigid_ty_fn_defs(&target_ty.kind, reified);
            census_operand(ctx, op, out, reified, reasons);
            if matches!(target_ty.kind, IrRigidTy::Other(_)) {
                out.push(PropertyClass::UnsupportedFallback);
                reasons.push(String::from("unlowered RigidTy.other in cast target"));
            }
            match ck {
                IrCastKind::FloatToInt => out.push(PropertyClass::ArithmeticOverflow),
                IrCastKind::PointerExposeProvenance
                | IrCastKind::PointerWithExposedProvenance
                | IrCastKind::PointerCoercion(_)
                | IrCastKind::PtrToPtr
                | IrCastKind::FnPtrToPtr => out.push(PropertyClass::PointerDereference),
                IrCastKind::Transmute => {
                    out.push(PropertyClass::DiscriminantValidity);
                    out.push(PropertyClass::UninitRead);
                }
                IrCastKind::IntToInt
                | IrCastKind::FloatToFloat
                | IrCastKind::IntToFloat
                | IrCastKind::Subtype => {
                    if matches!(
                        target_ty.kind,
                        IrRigidTy::Bool | IrRigidTy::Char | IrRigidTy::Adt(_, _) | IrRigidTy::Never
                    ) {
                        out.push(PropertyClass::DiscriminantValidity);
                    }
                }
            }
        }
        IrRvalue::BinaryOp(bin_op, lhs, rhs) => {
            census_operand(ctx, lhs, out, reified, reasons);
            census_operand(ctx, rhs, out, reified, reasons);
            match bin_op {
                IrBinOp::Add
                | IrBinOp::AddUnchecked
                | IrBinOp::AddWithOverflow
                | IrBinOp::Sub
                | IrBinOp::SubUnchecked
                | IrBinOp::SubWithOverflow
                | IrBinOp::Mul
                | IrBinOp::MulUnchecked
                | IrBinOp::MulWithOverflow => out.push(PropertyClass::ArithmeticOverflow),
                IrBinOp::Shl | IrBinOp::ShlUnchecked | IrBinOp::Shr | IrBinOp::ShrUnchecked => {
                    out.push(PropertyClass::ShiftBounds);
                }
                IrBinOp::Div | IrBinOp::Rem => out.push(PropertyClass::DivRemUb),
                IrBinOp::Offset => {
                    out.push(PropertyClass::PointerDereference);
                    out.push(PropertyClass::SliceArrayBounds);
                }
                IrBinOp::Eq
                | IrBinOp::Ne
                | IrBinOp::Lt
                | IrBinOp::Le
                | IrBinOp::Gt
                | IrBinOp::Ge
                | IrBinOp::Cmp => {
                    if ctx.operand_is_ptr_like(lhs) || ctx.operand_is_ptr_like(rhs) {
                        out.push(PropertyClass::PointerDereference);
                    }
                }
                IrBinOp::BitXor | IrBinOp::BitAnd | IrBinOp::BitOr => {}
            }
        }
        IrRvalue::UnaryOp(un_op, arg) => {
            census_operand(ctx, arg, out, reified, reasons);
            match un_op {
                IrUnOp::Neg => out.push(PropertyClass::ArithmeticOverflow),
                IrUnOp::PtrMetadata => {
                    out.push(PropertyClass::PointerDereference);
                    out.push(PropertyClass::SliceArrayBounds);
                }
                IrUnOp::Not => {}
            }
        }
        IrRvalue::NullaryOp(null_op, ty) => {
            collect_rigid_ty_fn_defs(&ty.kind, reified);
            if matches!(ty.kind, IrRigidTy::Other(_)) {
                out.push(PropertyClass::UnsupportedFallback);
                reasons.push(String::from("unlowered RigidTy.other in nullaryOp"));
            }
            match null_op {
                IrNullOp::ContractChecks => {
                    out.push(PropertyClass::UnsupportedFallback);
                    reasons.push(String::from(
                        "NullOp.contractChecks evaluates to .unsupported in MirSemantics",
                    ));
                }
                IrNullOp::UbChecks if !matches!(ty.kind, IrRigidTy::Bool) => {
                    out.push(PropertyClass::UnsupportedFallback);
                    reasons.push(String::from("NullOp.ubChecks requires RigidTy.bool"));
                }
                IrNullOp::SizeOf
                | IrNullOp::AlignOf
                | IrNullOp::OffsetOf(_)
                | IrNullOp::UbChecks => {}
            }
        }
        IrRvalue::Aggregate(ak, ops) => {
            for op in ops {
                census_operand(ctx, op, out, reified, reasons);
            }
            match ak {
                IrAggregateKind::Array(ty) => collect_rigid_ty_fn_defs(&ty.kind, reified),
                IrAggregateKind::Tuple | IrAggregateKind::Closure(_) => {}
                IrAggregateKind::Adt(_, _, _) => out.push(PropertyClass::DiscriminantValidity),
                IrAggregateKind::RawPtr(ty, _) => {
                    collect_rigid_ty_fn_defs(&ty.kind, reified);
                    out.push(PropertyClass::PointerDereference);
                }
                IrAggregateKind::Coroutine(path) => {
                    out.push(PropertyClass::UnsupportedFallback);
                    reasons.push(format!("unsupported AggregateKind.coroutine `{path}`"));
                }
            }
        }
    }
}

fn census_statement_kind(
    ctx: &MirBodyTypingCtx<'_>,
    kind: &IrStatementKind,
    out: &mut Vec<PropertyClass>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    match kind {
        IrStatementKind::Assign(dst, rv) => {
            census_place_write(ctx, dst, out, reified, reasons);
            census_rvalue(ctx, rv, out, reified, reasons);
        }
        IrStatementKind::SetDiscriminant(dst, _) => {
            census_place_write(ctx, dst, out, reified, reasons);
            out.push(PropertyClass::DiscriminantValidity);
        }
        IrStatementKind::Deinit(dst) => {
            census_place_write(ctx, dst, out, reified, reasons);
        }
        IrStatementKind::StorageLive(local) | IrStatementKind::StorageDead(local) => {
            ctx.check_local_in_bounds(*local, out, reasons);
        }
        IrStatementKind::Retag(_, place) => {
            out.push(PropertyClass::PointerDereference);
            census_place_projections(ctx, place, out, reified, reasons);
        }
        IrStatementKind::PlaceMention(place)
        | IrStatementKind::BackwardIncompatibleDropHint(place) => {
            census_place_projections(ctx, place, out, reified, reasons);
        }
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(op)) => {
            census_operand(ctx, op, out, reified, reasons);
            out.push(PropertyClass::DiscriminantValidity);
        }
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
            src,
            dst,
            count,
        }) => {
            census_operand(ctx, src, out, reified, reasons);
            census_operand(ctx, dst, out, reified, reasons);
            census_operand(ctx, count, out, reified, reasons);
            out.push(PropertyClass::PointerDereference);
            out.push(PropertyClass::MemoryCopyOverlap);
            out.push(PropertyClass::ArithmeticOverflow);
        }
        IrStatementKind::Coverage | IrStatementKind::ConstEvalCounter | IrStatementKind::Nop => {}
    }
}

fn extract_direct_callee_def_path(op: &IrOperand) -> Option<&str> {
    let IrOperand::Constant(co) = op else {
        return None;
    };
    if let IrRigidTy::FnDef(def_path, _) = &co.ty.kind {
        return Some(def_path.as_str());
    }
    if let IrConstValue::Unevaluated(def_path) = &co.val {
        return Some(def_path.as_str());
    }
    None
}

fn classify_callee_intrinsic_classes(def_path: &str, out: &mut Vec<PropertyClass>) {
    let leaf = def_path.rsplit("::").next().unwrap_or(def_path);
    let is_core_or_std = def_path.starts_with("core::intrinsics::")
        || def_path.starts_with("std::intrinsics::")
        || def_path.starts_with("core::hint::")
        || def_path.starts_with("std::hint::")
        || def_path.starts_with("core::ptr::")
        || def_path.starts_with("std::ptr::")
        || def_path.starts_with("core::mem::")
        || def_path.starts_with("std::mem::");
    if !is_core_or_std {
        return;
    }
    match leaf {
        "unchecked_add" | "unchecked_sub" | "unchecked_mul" | "float_to_int_unchecked" => {
            out.push(PropertyClass::ArithmeticOverflow);
        }
        "unchecked_shl" | "unchecked_shr" => {
            out.push(PropertyClass::ShiftBounds);
        }
        "unchecked_div" | "unchecked_rem" | "exact_div" => {
            out.push(PropertyClass::DivRemUb);
        }
        "unreachable" | "unreachable_unchecked" | "assume" | "ctlz_nonzero" | "cttz_nonzero" => {
            out.push(PropertyClass::DiscriminantValidity);
        }
        "copy"
        | "copy_nonoverlapping"
        | "write_bytes"
        | "swap"
        | "swap_nonoverlapping"
        | "typed_swap_nonoverlapping"
        | "replace" => {
            out.push(PropertyClass::PointerDereference);
            out.push(PropertyClass::MemoryCopyOverlap);
            out.push(PropertyClass::ArithmeticOverflow);
        }
        "read"
        | "read_unaligned"
        | "read_volatile"
        | "volatile_load"
        | "unaligned_volatile_load" => {
            out.push(PropertyClass::PointerDereference);
            out.push(PropertyClass::UninitRead);
        }
        "write"
        | "write_unaligned"
        | "write_volatile"
        | "volatile_store"
        | "unaligned_volatile_store"
        | "drop_in_place" => {
            out.push(PropertyClass::PointerDereference);
        }
        "offset"
        | "arith_offset"
        | "ptr_offset_from"
        | "ptr_offset_from_unsigned" => {
            out.push(PropertyClass::PointerDereference);
            out.push(PropertyClass::SliceArrayBounds);
        }
        "transmute" | "transmute_copy" => {
            out.push(PropertyClass::DiscriminantValidity);
            out.push(PropertyClass::UninitRead);
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn census_terminator_kind(
    ctx: &MirBodyTypingCtx<'_>,
    owner_def_path: &str,
    bb_idx: usize,
    term_idx: usize,
    kind: &IrTerminatorKind,
    out: &mut Vec<PropertyClass>,
    direct_callees: &mut BTreeSet<String>,
    call_site_targets: &mut BTreeMap<(usize, usize), CallSiteTarget>,
    reified: &mut BTreeSet<String>,
    reasons: &mut Vec<String>,
) {
    match kind {
        IrTerminatorKind::Goto(_) | IrTerminatorKind::UnwindTerminate => {}
        IrTerminatorKind::SwitchInt(discr, _) => {
            census_operand(ctx, discr, out, reified, reasons);
            out.push(PropertyClass::SwitchExhaustiveness);
        }
        IrTerminatorKind::UnwindResume => {
            out.push(PropertyClass::CallContract);
        }
        IrTerminatorKind::Return => {
            ctx.check_local_in_bounds(0, out, reasons);
            out.push(PropertyClass::UninitRead);
            if ctx.body_has_any_ref_or_ptr_local() {
                out.push(PropertyClass::PointerDereference);
            }
        }
        IrTerminatorKind::Unreachable => {
            out.push(PropertyClass::DiscriminantValidity);
        }
        IrTerminatorKind::Drop {
            place,
            unwind,
            ..
        } => {
            census_place_write(ctx, place, out, reified, reasons);
            out.push(PropertyClass::CallContract);
            if matches!(unwind, IrUnwindAction::Unreachable) {
                out.push(PropertyClass::DiscriminantValidity);
            }
        }
        IrTerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
        } => {
            out.push(PropertyClass::CallContract);
            let is_diverging = target.is_none();
            if let Some(def_path) = extract_direct_callee_def_path(func) {
                if let IrOperand::Constant(co) = func {
                    census_const_operand(ctx, co, true, out, reified, reasons);
                    if let IrRigidTy::FnDef(_, type_args) = &co.ty.kind {
                        for arg_ty in type_args {
                            collect_rigid_ty_fn_defs(arg_ty, reified);
                        }
                    }
                }
                if !def_path.is_empty() {
                    direct_callees.insert(def_path.to_string());
                    classify_callee_intrinsic_classes(def_path, out);
                    if def_path == owner_def_path {
                        out.push(PropertyClass::LoopTermination);
                    }
                }
                call_site_targets.insert(
                    (bb_idx, term_idx),
                    CallSiteTarget {
                        callee: Some(def_path.to_string()),
                        is_diverging,
                    },
                );
            } else {
                census_operand(ctx, func, out, reified, reasons);
                out.push(PropertyClass::PointerDereference);
                call_site_targets.insert(
                    (bb_idx, term_idx),
                    CallSiteTarget {
                        callee: None,
                        is_diverging,
                    },
                );
            }
            for arg in args {
                census_operand(ctx, arg, out, reified, reasons);
            }
            census_place_write(ctx, destination, out, reified, reasons);
            if matches!(unwind, IrUnwindAction::Unreachable) {
                out.push(PropertyClass::DiscriminantValidity);
            }
        }
        IrTerminatorKind::TailCall { func, args } => {
            out.push(PropertyClass::CallContract);
            if let Some(def_path) = extract_direct_callee_def_path(func) {
                if let IrOperand::Constant(co) = func {
                    census_const_operand(ctx, co, true, out, reified, reasons);
                    if let IrRigidTy::FnDef(_, type_args) = &co.ty.kind {
                        for arg_ty in type_args {
                            collect_rigid_ty_fn_defs(arg_ty, reified);
                        }
                    }
                }
                if !def_path.is_empty() {
                    direct_callees.insert(def_path.to_string());
                    classify_callee_intrinsic_classes(def_path, out);
                    if def_path == owner_def_path {
                        out.push(PropertyClass::LoopTermination);
                    }
                }
                call_site_targets.insert(
                    (bb_idx, term_idx),
                    CallSiteTarget {
                        callee: Some(def_path.to_string()),
                        is_diverging: false,
                    },
                );
            } else {
                census_operand(ctx, func, out, reified, reasons);
                out.push(PropertyClass::PointerDereference);
                call_site_targets.insert(
                    (bb_idx, term_idx),
                    CallSiteTarget {
                        callee: None,
                        is_diverging: false,
                    },
                );
            }
            for arg in args {
                census_operand(ctx, arg, out, reified, reasons);
            }
        }
        IrTerminatorKind::Assert { cond, unwind, .. } => {
            census_operand(ctx, cond, out, reified, reasons);
            out.push(PropertyClass::SliceArrayBounds);
            if matches!(unwind, IrUnwindAction::Unreachable) {
                out.push(PropertyClass::DiscriminantValidity);
            }
        }
        IrTerminatorKind::InlineAsm { template, .. } => {
            out.push(PropertyClass::UnsupportedFallback);
            reasons.push(format!("unsupported TerminatorKind.inlineAsm `{template}`"));
        }
    }
}

/// Enumerate all successor basic-block indices referenced by `kind`, including
/// `UnwindAction::Cleanup` edges.
pub fn terminator_all_targets(kind: &IrTerminatorKind) -> Vec<usize> {
    let mut targets = Vec::new();
    match kind {
        IrTerminatorKind::Goto(bb) => targets.push(*bb),
        IrTerminatorKind::SwitchInt(_, st) => {
            for &(_, bb) in &st.branches {
                targets.push(bb);
            }
            targets.push(st.otherwise);
        }
        IrTerminatorKind::Drop {
            target, unwind, ..
        }
        | IrTerminatorKind::Assert {
            target, unwind, ..
        } => {
            targets.push(*target);
            if let IrUnwindAction::Cleanup(cleanup_bb) = unwind {
                targets.push(*cleanup_bb);
            }
        }
        IrTerminatorKind::Call {
            target, unwind, ..
        } => {
            if let Some(bb) = target {
                targets.push(*bb);
            }
            if let IrUnwindAction::Cleanup(cleanup_bb) = unwind {
                targets.push(*cleanup_bb);
            }
        }
        IrTerminatorKind::InlineAsm {
            targets: asm_targets,
            unwind,
            ..
        } => {
            targets.extend(asm_targets.iter().copied());
            if let IrUnwindAction::Cleanup(cleanup_bb) = unwind {
                targets.push(*cleanup_bb);
            }
        }
        IrTerminatorKind::UnwindResume
        | IrTerminatorKind::UnwindTerminate
        | IrTerminatorKind::Return
        | IrTerminatorKind::Unreachable
        | IrTerminatorKind::TailCall { .. } => {}
    }
    targets
}

/// Detect all directed cycle back-edges `(u, v)` across `basic_blocks` using a
/// deterministic three-color depth-first search rooted first at `bb0` and then
/// at any remaining unvisited components.
pub fn detect_cfg_cycle_back_edges(basic_blocks: &[IrBasicBlockData]) -> Vec<(usize, usize)> {
    let n = basic_blocks.len();
    let mut color = vec![0u8; n]; // 0 = unvisited, 1 = on stack, 2 = finished
    let mut back_edges = BTreeSet::new();

    for root in 0..n {
        if color[root] != 0 {
            continue;
        }
        let root_succs: Vec<usize> = terminator_all_targets(&basic_blocks[root].terminator.kind)
            .into_iter()
            .filter(|&t| t < n)
            .collect();
        color[root] = 1;
        let mut stack: Vec<(usize, usize, Vec<usize>)> = vec![(root, 0, root_succs)];
        while let Some((u, idx, succs)) = stack.last_mut() {
            if *idx < succs.len() {
                let v = succs[*idx];
                *idx += 1;
                match color[v] {
                    0 => {
                        color[v] = 1;
                        let v_succs: Vec<usize> =
                            terminator_all_targets(&basic_blocks[v].terminator.kind)
                                .into_iter()
                                .filter(|&t| t < n)
                                .collect();
                        stack.push((v, 0, v_succs));
                    }
                    1 => {
                        back_edges.insert((*u, v));
                    }
                    _ => {}
                }
            } else {
                let finished = *u;
                color[finished] = 2;
                stack.pop();
            }
        }
    }

    back_edges.into_iter().collect()
}

// ============================================================================
// 4. Fail-Closed FaultSiteCoverageReconciler & Structured Diagnostics
// ============================================================================

/// Category of an explicit per-site or registry-derived obligation waiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WaiverKind {
    /// Partial-correctness (`MirNoUB`) contract permits non-termination; valid
    /// strictly on [`PropertyClass::LoopTermination`].
    PartialCorrectnessDivergence,
    /// Scoped UB-exception certificate (`UbExceptionItemSpec`) explicitly
    /// carves out a documented safety precondition.
    ScopedUbException,
    /// Explicit assumption boundary (`#[spec(trusted)]` or `Assumptions.<Item>`).
    TrustedAssumptionBoundary,
    /// Class-level [`PropertyDisposition::ExplicitlyWaived`] configured on
    /// [`PropertyRegistry`].
    RegistryClassWaiver,
}

impl WaiverKind {
    /// Canonical wire tag for the waiver category.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::PartialCorrectnessDivergence => "partial_correctness_divergence",
            Self::ScopedUbException => "scoped_ub_exception",
            Self::TrustedAssumptionBoundary => "trusted_assumption_boundary",
            Self::RegistryClassWaiver => "registry_class_waiver",
        }
    }
}

/// Explicit, auditable waiver covering a single [`FaultSite`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExplicitSiteWaiver {
    /// Waived fault site.
    pub site: FaultSite,
    /// Waiver category constraining which property classes it may cover.
    pub kind: WaiverKind,
    /// Non-empty human-readable justification.
    pub reason: String,
}

impl ExplicitSiteWaiver {
    /// Construct a new [`ExplicitSiteWaiver`].
    pub fn new(site: FaultSite, kind: WaiverKind, reason: impl Into<String>) -> Self {
        Self {
            site,
            kind,
            reason: reason.into(),
        }
    }

    fn validate(&self) -> Result<(), String> {
        if !self.site.class.is_waivable() {
            return Err(format!(
                "cannot waive non-waivable fault class `{}` at {}",
                self.site.class, self.site
            ));
        }
        if self.reason.trim().is_empty() {
            return Err(format!(
                "waiver `{}` at {} has an empty justification",
                self.kind.as_str(),
                self.site
            ));
        }
        if self.kind == WaiverKind::PartialCorrectnessDivergence
            && self.site.class != PropertyClass::LoopTermination
        {
            return Err(format!(
                "PartialCorrectnessDivergence waiver may cover only `loop_termination`, not `{}` at {}",
                self.site.class, self.site
            ));
        }
        Ok(())
    }
}

/// Why a censused [`FaultSite`] failed reconciliation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UncoveredReason {
    /// `site` is in `census.sites`, its class is `Discharged` in
    /// [`PropertyRegistry`], and `site` was omitted from both `discharged_sites`
    /// and `explicit_waivers`.
    OmittedObligation,
    /// [`PropertyRegistry`] marks `site.class` as
    /// [`PropertyDisposition::UnemittedGap`].
    RegistryUnemittedGap,
    /// `site` lies in [`PropertyClass::UnsupportedFallback`] or a class marked
    /// [`PropertyDisposition::UnsupportedFailClosed`].
    UnsupportedConstruct {
        /// Optional unscannable/unsupported syntax detail from [`FaultSiteCensus`].
        detail: Option<String>,
    },
    /// An [`ExplicitSiteWaiver`] or [`PropertyRegistry`] waiver for `site` was
    /// invalid (e.g. blank reason, wrong waiver kind, or targeting a
    /// non-waivable class).
    InvalidWaiver {
        /// Validation error message.
        detail: String,
    },
    /// A [`PropertyClass::CallContract`] site invokes a direct or indirect
    /// callee that is neither natively modeled in `MirSemantics`, linked in
    /// `defaultCallees`, nor covered by an active modular call contract.
    UnresolvedCallContract {
        /// Uncovered callee `DefPath` (or `"<indirect fn_ptr>"`).
        callee: String,
    },
}

impl fmt::Display for UncoveredReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OmittedObligation => {
                f.write_str("obligation check omitted from discharged and waived sets")
            }
            Self::RegistryUnemittedGap => {
                f.write_str("property class is marked UnemittedGap in PropertyRegistry")
            }
            Self::UnsupportedConstruct { detail: Some(d) } => {
                write!(f, "unsupported or unscannable MIR construct ({d})")
            }
            Self::UnsupportedConstruct { detail: None } => {
                f.write_str("unsupported or unscannable MIR construct (fail-closed)")
            }
            Self::InvalidWaiver { detail } => write!(f, "invalid waiver ({detail})"),
            Self::UnresolvedCallContract { callee } => write!(
                f,
                "call target `{callee}` is neither natively modeled in MirSemantics, linked in defaultCallees, nor covered by ModularItemSpec.envAssumed"
            ),
        }
    }
}

/// Structured diagnostic describing one uncovered [`FaultSite`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UncoveredSiteDiagnostic {
    /// Canonical `DefPath` of the MIR body containing `site`.
    pub def_path: String,
    /// Exact uncovered [`FaultSite`].
    pub site: FaultSite,
    /// Root cause of the coverage failure.
    pub reason: UncoveredReason,
    /// Actionable remediation hint.
    pub remediation_hint: String,
}

impl fmt::Display for UncoveredSiteDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[UNCOVERED_FAULT_SITE] `{}` at {}: {} (hint: {})",
            self.def_path, self.site, self.reason, self.remediation_hint
        )
    }
}

/// Callee-resolution context supplied alongside obligation coverage so
/// [`FaultSiteCoverageReconciler`] can independently verify call-contract
/// coverage at every `Call` / `TailCall` terminator.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CallCoverageContext {
    /// Whether call-contract target resolution should be enforced against
    /// `linked_callees` and `modular_contract_callees`.
    pub enforce_callee_closure: bool,
    /// Callee `DefPath`s linked concretely in `defaultCallees` (`s.memory.callees`).
    pub linked_callees: BTreeSet<String>,
    /// Callee `DefPath`s abstracted via `ModularItemSpec.envAssumed`
    /// (`#[external_spec]` or verified sibling `defaultCallContract`) when the
    /// active verification certificate is `ModularVerificationResult`.
    pub modular_contract_callees: BTreeSet<String>,
    /// Whether indirect function-pointer calls (`RigidTy::FnPtr`) are covered
    /// by an explicit authored `ModularItemSpec.envAssumed` assumption.
    pub allow_modular_indirect_calls: bool,
}

/// Result of reconciling a [`FaultSiteCensus`] against discharged and
/// explicitly waived obligation sites.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverageReconciliationReport {
    /// Canonical `DefPath` of the reconciled MIR item.
    pub def_path: String,
    /// All fault sites discovered by [`FaultSiteCensus`].
    pub census_sites: BTreeSet<FaultSite>,
    /// Census sites verified via `discharged_sites`.
    pub verified_discharged_sites: BTreeSet<FaultSite>,
    /// Validated waivers applied to census sites.
    pub applied_waivers: Vec<ExplicitSiteWaiver>,
    /// Sites supplied in `discharged_sites` that did not correspond to any
    /// censused site (tracked for precision auditing).
    pub extra_discharged_sites: BTreeSet<FaultSite>,
    /// Structured diagnostics for every uncovered or invalidly waived site
    /// (`is_empty()` iff reconciliation passed).
    pub uncovered_diagnostics: Vec<UncoveredSiteDiagnostic>,
}

impl CoverageReconciliationReport {
    /// Returns `true` iff `census_sites ⊆ (verified_discharged_sites ∪ applied_waivers)`
    /// with zero uncovered diagnostics.
    pub fn is_covered(&self) -> bool {
        self.uncovered_diagnostics.is_empty()
    }

    /// Convert this report into `Ok(self)` when [`Self::is_covered`] holds, or
    /// `Err(CoverageReconciliationError)` when any site failed reconciliation.
    pub fn into_result(self) -> Result<Self, CoverageReconciliationError> {
        if self.is_covered() {
            Ok(self)
        } else {
            Err(CoverageReconciliationError { report: self })
        }
    }

    /// Render a deterministic multi-line diagnostic report.
    pub fn render_diagnostic_report(&self) -> String {
        if self.is_covered() {
            return format!(
                "FAULT_COVERAGE_OK `{}`: {} census site(s) covered ({} discharged, {} waived)",
                self.def_path,
                self.census_sites.len(),
                self.verified_discharged_sites.len(),
                self.applied_waivers.len(),
            );
        }
        let mut out = format!(
            "FAULT_COVERAGE_FAILED `{}`: {} uncovered diagnostic(s) out of {} census site(s):\n",
            self.def_path,
            self.uncovered_diagnostics.len(),
            self.census_sites.len(),
        );
        for diag in &self.uncovered_diagnostics {
            out.push_str("  - ");
            out.push_str(&diag.to_string());
            out.push('\n');
        }
        out
    }
}

/// Fail-closed error returned when [`FaultSiteCoverageReconciler`] finds one or
/// more uncovered fault sites.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverageReconciliationError {
    /// Underlying reconciliation report containing all structured diagnostics.
    pub report: CoverageReconciliationReport,
}

impl fmt::Display for CoverageReconciliationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.report.render_diagnostic_report())
    }
}

impl std::error::Error for CoverageReconciliationError {}

/// Fail-closed reconciler checking that every [`FaultSite`] in a
/// [`FaultSiteCensus`] is legitimately discharged or explicitly waived under a
/// [`PropertyRegistry`].
#[derive(Clone, Debug)]
pub struct FaultSiteCoverageReconciler {
    registry: PropertyRegistry,
}

impl Default for FaultSiteCoverageReconciler {
    fn default() -> Self {
        Self::new(PropertyRegistry::strict())
    }
}

impl FaultSiteCoverageReconciler {
    /// Construct a new reconciler backed by `registry`.
    pub fn new(registry: PropertyRegistry) -> Self {
        Self { registry }
    }

    /// Borrow the underlying [`PropertyRegistry`].
    pub fn registry(&self) -> &PropertyRegistry {
        &self.registry
    }

    /// Reconcile `census` against `discharged_sites` and `explicit_waivers`,
    /// returning a structured [`CoverageReconciliationReport`].
    pub fn reconcile<D, W>(
        &self,
        census: &FaultSiteCensus,
        discharged_sites: D,
        explicit_waivers: W,
    ) -> CoverageReconciliationReport
    where
        D: IntoIterator<Item = FaultSite>,
        W: IntoIterator<Item = ExplicitSiteWaiver>,
    {
        self.reconcile_with_call_context(
            census,
            discharged_sites,
            explicit_waivers,
            &CallCoverageContext::default(),
        )
    }

    /// Reconcile `census` against `discharged_sites`, `explicit_waivers`, and
    /// `call_ctx`, enforcing `census_sites ⊆ discharged_or_explicitly_waived`
    /// plus registry disposition and callee-closure invariants.
    pub fn reconcile_with_call_context<D, W>(
        &self,
        census: &FaultSiteCensus,
        discharged_sites: D,
        explicit_waivers: W,
        call_ctx: &CallCoverageContext,
    ) -> CoverageReconciliationReport
    where
        D: IntoIterator<Item = FaultSite>,
        W: IntoIterator<Item = ExplicitSiteWaiver>,
    {
        let discharged_set: BTreeSet<FaultSite> = discharged_sites.into_iter().collect();
        let mut waivers_by_site: BTreeMap<FaultSite, Vec<ExplicitSiteWaiver>> = BTreeMap::new();
        for waiver in explicit_waivers {
            waivers_by_site.entry(waiver.site).or_default().push(waiver);
        }

        let mut verified_discharged_sites = BTreeSet::new();
        let mut applied_waivers = Vec::new();
        let mut uncovered_diagnostics = Vec::new();

        for (site, site_waivers) in &waivers_by_site {
            if !census.sites.contains(site) {
                for w in site_waivers {
                    if let Err(detail) = w.validate() {
                        uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                            def_path: census.def_path.clone(),
                            site: *site,
                            reason: UncoveredReason::InvalidWaiver { detail },
                            remediation_hint: remediation_hint_for_class(site.class),
                        });
                    }
                }
            }
        }

        let unsupported_detail = (!census.unscannable_reasons.is_empty())
            .then(|| census.unscannable_reasons.join("; "));

        for &site in &census.sites {
            // Hard invariant 1: `UnsupportedFallback` is never coverable or waivable.
            if !site.class.is_waivable() {
                uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                    def_path: census.def_path.clone(),
                    site,
                    reason: UncoveredReason::UnsupportedConstruct {
                        detail: unsupported_detail.clone(),
                    },
                    remediation_hint: remediation_hint_for_class(site.class),
                });
                continue;
            }

            // Hard invariant 2: Validate any explicit waivers attached to `site`
            // regardless of the registry disposition for `site.class`.
            if let Some(site_waivers) = waivers_by_site.get(&site) {
                let mut bad_detail = None;
                for w in site_waivers {
                    if let Err(detail) = w.validate() {
                        bad_detail = Some(detail);
                        break;
                    }
                }
                if let Some(detail) = bad_detail {
                    uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                        def_path: census.def_path.clone(),
                        site,
                        reason: UncoveredReason::InvalidWaiver { detail },
                        remediation_hint: remediation_hint_for_class(site.class),
                    });
                    continue;
                }
            }

            // Hard invariant 3: Check callee-closure resolution on `Call` /
            // `TailCall` terminators when `enforce_callee_closure` is enabled.
            if site.class == PropertyClass::CallContract
                && site.is_terminator
                && call_ctx.enforce_callee_closure
                && let Some(target_desc) = census.call_site_targets.get(&(site.block_idx, site.stmt_idx))
            {
                let unresolved_callee = match &target_desc.callee {
                    Some(def_path) => {
                        let covered =
                            is_natively_modeled_mir_call(def_path, target_desc.is_diverging)
                                || call_ctx.linked_callees.contains(def_path)
                                || call_ctx.modular_contract_callees.contains(def_path);
                        (!covered).then(|| def_path.clone())
                    }
                    None => (!call_ctx.allow_modular_indirect_calls)
                        .then(|| String::from("<indirect fn_ptr>")),
                };
                if let Some(callee) = unresolved_callee {
                    let has_valid_trusted_waiver =
                        waivers_by_site.get(&site).is_some_and(|ws| {
                            ws.iter()
                                .any(|w| w.kind == WaiverKind::TrustedAssumptionBoundary)
                        });
                    if !has_valid_trusted_waiver {
                        uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                            def_path: census.def_path.clone(),
                            site,
                            reason: UncoveredReason::UnresolvedCallContract { callee },
                            remediation_hint: String::from(
                                "link callee MIR in `defaultCallees`, add an `#[external_spec]` \
                                 sidecar on `ModularItemSpec`, or mark the boundary `#[spec(trusted)]`",
                            ),
                        });
                        continue;
                    }
                }
            }

            // Hard invariant 4: Enforce `PropertyRegistry` disposition for `site.class`.
            match self.registry.disposition(site.class) {
                PropertyDisposition::UnsupportedFailClosed => {
                    uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                        def_path: census.def_path.clone(),
                        site,
                        reason: UncoveredReason::UnsupportedConstruct {
                            detail: unsupported_detail.clone(),
                        },
                        remediation_hint: remediation_hint_for_class(site.class),
                    });
                }
                PropertyDisposition::UnemittedGap => {
                    uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                        def_path: census.def_path.clone(),
                        site,
                        reason: UncoveredReason::RegistryUnemittedGap,
                        remediation_hint: remediation_hint_for_class(site.class),
                    });
                }
                PropertyDisposition::ExplicitlyWaived { reason } => {
                    if reason.trim().is_empty() {
                        uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                            def_path: census.def_path.clone(),
                            site,
                            reason: UncoveredReason::InvalidWaiver {
                                detail: format!(
                                    "PropertyRegistry waiver for `{}` has an empty reason",
                                    site.class
                                ),
                            },
                            remediation_hint: remediation_hint_for_class(site.class),
                        });
                    } else if discharged_set.contains(&site) {
                        verified_discharged_sites.insert(site);
                    } else if let Some(site_waivers) = waivers_by_site.get(&site)
                        && let Some(explicit_w) = site_waivers.first()
                    {
                        applied_waivers.push(explicit_w.clone());
                    } else {
                        applied_waivers.push(ExplicitSiteWaiver::new(
                            site,
                            WaiverKind::RegistryClassWaiver,
                            reason.clone(),
                        ));
                    }
                }
                PropertyDisposition::Discharged => {
                    if discharged_set.contains(&site) {
                        verified_discharged_sites.insert(site);
                    } else if let Some(site_waivers) = waivers_by_site.get(&site)
                        && let Some(valid_waiver) = site_waivers.first()
                    {
                        applied_waivers.push(valid_waiver.clone());
                    } else {
                        uncovered_diagnostics.push(UncoveredSiteDiagnostic {
                            def_path: census.def_path.clone(),
                            site,
                            reason: UncoveredReason::OmittedObligation,
                            remediation_hint: remediation_hint_for_class(site.class),
                        });
                    }
                }
            }
        }

        let extra_discharged_sites: BTreeSet<FaultSite> = discharged_set
            .difference(&census.sites)
            .copied()
            .collect();

        CoverageReconciliationReport {
            def_path: census.def_path.clone(),
            census_sites: census.sites.clone(),
            verified_discharged_sites,
            applied_waivers,
            extra_discharged_sites,
            uncovered_diagnostics,
        }
    }

    /// Strict fail-closed wrapper returning `Err(CoverageReconciliationError)`
    /// whenever any site in `census` is uncovered.
    pub fn require_covered<D, W>(
        &self,
        census: &FaultSiteCensus,
        discharged_sites: D,
        explicit_waivers: W,
    ) -> Result<CoverageReconciliationReport, CoverageReconciliationError>
    where
        D: IntoIterator<Item = FaultSite>,
        W: IntoIterator<Item = ExplicitSiteWaiver>,
    {
        self.reconcile(census, discharged_sites, explicit_waivers)
            .into_result()
    }
}

fn remediation_hint_for_class(class: PropertyClass) -> String {
    let msg = match class {
        PropertyClass::ArithmeticOverflow => {
            "prove integer arithmetic bounds in `requires` / loop invariants so operations cannot overflow"
        }
        PropertyClass::ShiftBounds => {
            "constrain shift distance `< bit_width` and `>= 0` in `requires` or branch guards"
        }
        PropertyClass::DivRemUb => {
            "prove divisor `!= 0` (and exclude `MIN / -1` on signed division) before `Div` / `Rem`"
        }
        PropertyClass::PointerDereference => {
            "discharge pointer alignment, provenance, live allocation bounds, and Tree Borrows permissions (`StatefulItemSpec` / `SepLogicLenses`)"
        }
        PropertyClass::SliceArrayBounds => {
            "prove index/subslice `< len` and runtime `Assert` condition holds on all reachable paths"
        }
        PropertyClass::DiscriminantValidity => {
            "prove active union/enum discriminant and scalar niche validity (`Anneal.BitValidity`) and unreachability of `unreachable` arms"
        }
        PropertyClass::CallContract => {
            "evaluate all call argument operands, link callee MIR in `defaultCallees`, or discharge `ModularItemSpec` call preconditions"
        }
        PropertyClass::LoopTermination => {
            "prove a strictly decreasing loop/recursion variant (`TotalItemSpec` / `forRangeUp`) or explicitly scope partial correctness (`ItemSpec`)"
        }
        PropertyClass::SwitchExhaustiveness => {
            "explore all `SwitchInt` branch targets plus `otherwise` and ensure CFG target indices are in bounds"
        }
        PropertyClass::MemoryCopyOverlap => {
            "prove `src` and `dst` intervals are disjoint, aligned, and in-bounds (`evalCopyNonOverlappingPermOk`)"
        }
        PropertyClass::UninitRead => {
            "prove every read local slot and memory byte range is initialized and storage-live"
        }
        PropertyClass::UnsupportedFallback => {
            "replace unsupported inline assembly / thread-local / non-inline MIR constructs or isolate behind an audited FFI boundary"
        }
    };
    String::from(msg)
}

// ============================================================================
// 5. Independent Obligation Explorer & Token-Level Claim/Verify Pinning
// ============================================================================

/// Extracted obligation coverage for a single MIR body, pairing the reachable
/// discharged fault sites with any explicit contract waivers and call-closure
/// metadata.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EmittedObligationCoverage {
    /// Fault sites discharged along explored CFG paths from entry `bb0`.
    pub discharged_sites: BTreeSet<FaultSite>,
    /// Explicit waivers derived from the active contract surface (e.g.
    /// partial-correctness loop divergence or `#[spec(trusted)]`).
    pub explicit_waivers: Vec<ExplicitSiteWaiver>,
    /// Callee-closure resolution context derived from `bundle` and verified
    /// against `Obligations.<Item>` and `Verify.<Item>`.
    pub call_context: CallCoverageContext,
}

/// Configuration for the independent MIR obligation explorer
/// ([`explore_mir_obligations`]), supporting optional mutation modes for the
/// 4 canonical false-proof negative probes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ObligationExplorerOptions {
    /// Whether the active contract proves total termination (`TotalItemSpec`,
    /// `StatefulEquivItemSpec`, or `#[spec(safe_total)]`).
    pub proves_total_termination: bool,
    /// Whether the item's body is explicitly waived via an audited
    /// `#[spec(trusted)]` or `Assumptions.<Item>` boundary.
    pub is_trusted_assumption: bool,
    /// Whether `StatementKind::Retag` statements are preserved in `basic_blocks`
    /// (`true` when `mir` was parsed from `Mir/<Item>.lean`, `false` when
    /// inspecting raw pre-emission `IrCapturedMir`).
    pub preserve_retags: bool,
    /// Callee-closure context.
    pub call_context: CallCoverageContext,
    /// Additional callee `DefPath`s participating in a mutual recursion cycle
    /// with `mir.def_path`.
    pub recursive_callees: BTreeSet<String>,
    /// Optional defective-emitter mutation injected by a negative probe.
    pub injected_mutation: Option<FalseProofMutationProbe>,
}

/// Explore `mir` from entry block `bb0` using an independent obligation-emission
/// pass (distinct from [`FaultSiteCensus`]) to compute the set of discharged
/// fault sites and explicit contract waivers.
pub fn explore_mir_obligations(
    mir: &IrCapturedMir,
    opts: &ObligationExplorerOptions,
) -> EmittedObligationCoverage {
    let mut discharged_sites = BTreeSet::new();
    let mut explicit_waivers = Vec::new();

    let num_blocks = mir.basic_blocks.len();
    if num_blocks == 0
        || !matches!(
            mir.phase,
            IrMirPhaseTag::RuntimePostCleanup | IrMirPhaseTag::RuntimeOptimized
        )
    {
        return EmittedObligationCoverage {
            discharged_sites,
            explicit_waivers,
            call_context: opts.call_context.clone(),
        };
    }

    // Independent CFG worklist explorer (affected by `SwitchBreakStripProbe`
    // when simulating a defective explorer that drops `SwitchInt.otherwise`).
    let mut visited = vec![false; num_blocks];
    let mut queue = vec![0usize];
    while let Some(b) = queue.pop() {
        if b >= num_blocks || visited[b] {
            continue;
        }
        visited[b] = true;
        let term = &mir.basic_blocks[b].terminator.kind;
        let succs: Vec<usize> = match (term, opts.injected_mutation) {
            (
                IrTerminatorKind::SwitchInt(_, st),
                Some(FalseProofMutationProbe::SwitchBreakStripProbe),
            ) => st.branches.iter().map(|&(_, target_bb)| target_bb).collect(),
            _ => terminator_all_targets(term),
        };
        for succ in succs {
            if succ < num_blocks && !visited[succ] {
                queue.push(succ);
            }
        }
    }

    let back_edges = detect_cfg_cycle_back_edges(&mir.basic_blocks);
    let latch_blocks: BTreeSet<usize> = back_edges.into_iter().map(|(u, _)| u).collect();

    for (bb_idx, bb) in mir.basic_blocks.iter().enumerate() {
        if !visited[bb_idx] {
            continue;
        }
        let is_latch = latch_blocks.contains(&bb_idx);
        let stmts: Vec<&IrStatement> = bb
            .statements
            .iter()
            .filter(|s| opts.preserve_retags || !matches!(s.kind, IrStatementKind::Retag(_, _)))
            .collect();

        for (stmt_idx, stmt) in stmts.iter().enumerate() {
            let emitted = explore_stmt_obligations(
                mir,
                &stmt.kind,
                is_latch,
                opts.injected_mutation,
            );
            for class in emitted {
                let site = FaultSite::statement(bb_idx, stmt_idx, class);
                if opts.is_trusted_assumption {
                    explicit_waivers.push(ExplicitSiteWaiver::new(
                        site,
                        WaiverKind::TrustedAssumptionBoundary,
                        format!("assumed via explicit trusted contract on `{}`", mir.def_path),
                    ));
                } else {
                    discharged_sites.insert(site);
                }
            }
        }

        let term_idx = stmts.len();
        let term_emitted = explore_terminator_obligations(
            mir,
            bb_idx,
            &bb.terminator.kind,
            is_latch,
            opts,
        );
        for class in term_emitted {
            let site = FaultSite::terminator(bb_idx, term_idx, class);
            if class == PropertyClass::LoopTermination && !opts.proves_total_termination {
                explicit_waivers.push(ExplicitSiteWaiver::new(
                    site,
                    WaiverKind::PartialCorrectnessDivergence,
                    format!(
                        "partial-correctness MirNoUB contract on `{}` waives loop/recursion termination",
                        mir.def_path
                    ),
                ));
            } else if opts.is_trusted_assumption {
                explicit_waivers.push(ExplicitSiteWaiver::new(
                    site,
                    WaiverKind::TrustedAssumptionBoundary,
                    format!("assumed via explicit trusted contract on `{}`", mir.def_path),
                ));
            } else {
                discharged_sites.insert(site);
            }
        }
    }

    EmittedObligationCoverage {
        discharged_sites,
        explicit_waivers,
        call_context: opts.call_context.clone(),
    }
}

/// Backwards-compatible wrapper around [`explore_mir_obligations`] for raw
/// `IrCapturedMir` values (`preserve_retags = false`).
pub fn collect_reachable_body_obligations(
    mir: &IrCapturedMir,
    proves_total_termination: bool,
    is_trusted_assumption: bool,
    call_context: CallCoverageContext,
) -> EmittedObligationCoverage {
    explore_mir_obligations(
        mir,
        &ObligationExplorerOptions {
            proves_total_termination,
            is_trusted_assumption,
            preserve_retags: false,
            call_context,
            recursive_callees: BTreeSet::new(),
            injected_mutation: None,
        },
    )
}

fn explore_place_access(
    mir: &IrCapturedMir,
    place: &IrPlace,
    is_read: bool,
    ignore_deref: bool,
    out: &mut BTreeSet<PropertyClass>,
) {
    if !mir.local_decls.is_empty() && place.local_ >= mir.local_decls.len() {
        return;
    }
    if is_read || !place.projection.is_empty() {
        out.insert(PropertyClass::UninitRead);
    }
    if is_read {
        let ctx = MirBodyTypingCtx {
            local_decls: &mir.local_decls,
            layouts: &mir.layouts,
            allocations: &mir.allocations,
        };
        if ctx.place_reads_union_field(place) {
            out.insert(PropertyClass::DiscriminantValidity);
        }
    }
    for proj in &place.projection {
        match proj {
            IrProjectionElem::Deref => {
                out.insert(PropertyClass::UninitRead);
                if !ignore_deref {
                    out.insert(PropertyClass::PointerDereference);
                }
            }
            IrProjectionElem::Index(idx_local) => {
                if mir.local_decls.is_empty() || *idx_local < mir.local_decls.len() {
                    out.insert(PropertyClass::UninitRead);
                    out.insert(PropertyClass::SliceArrayBounds);
                }
            }
            IrProjectionElem::ConstantIndex { .. } | IrProjectionElem::Subslice { .. } => {
                out.insert(PropertyClass::SliceArrayBounds);
            }
            IrProjectionElem::Downcast(_, _) => {
                out.insert(PropertyClass::DiscriminantValidity);
            }
            IrProjectionElem::Field(_, _)
            | IrProjectionElem::OpaqueCast(_)
            | IrProjectionElem::UnwrapUnsafeBinder(_) => {}
        }
    }
}

fn explore_operand(
    mir: &IrCapturedMir,
    op: &IrOperand,
    ignore_deref: bool,
    out: &mut BTreeSet<PropertyClass>,
) {
    match op {
        IrOperand::Copy(p) | IrOperand::Move(p) => {
            explore_place_access(mir, p, true, ignore_deref, out);
        }
        IrOperand::Constant(co) => {
            if matches!(co.ty.kind, IrRigidTy::Never) {
                out.insert(PropertyClass::DiscriminantValidity);
            }
            let mut walk_alloc = |alloc_id: u64, off: u64| {
                let ctx = MirBodyTypingCtx {
                    local_decls: &mir.local_decls,
                    layouts: &mir.layouts,
                    allocations: &mir.allocations,
                };
                let mut tmp = Vec::new();
                let mut vis = BTreeSet::new();
                census_alloc_tree(&ctx, alloc_id, off, &mut vis, &mut tmp);
                for c in tmp {
                    if !ignore_deref || c != PropertyClass::PointerDereference {
                        out.insert(c);
                    }
                }
            };
            match &co.val {
                IrConstValue::ZeroSized | IrConstValue::Unevaluated(_) => {}
                IrConstValue::Scalar(IrConstScalar::Int(si)) => match co.ty.kind {
                    IrRigidTy::Bool if si.bits > 1 => {
                        out.insert(PropertyClass::DiscriminantValidity);
                    }
                    IrRigidTy::Char
                        if si.bits > 0x10FFFF || (0xD800..=0xDFFF).contains(&si.bits) =>
                    {
                        out.insert(PropertyClass::DiscriminantValidity);
                    }
                    _ => {}
                },
                IrConstValue::Scalar(IrConstScalar::Ptr(ptr, _)) => {
                    walk_alloc(ptr.alloc_id, ptr.offset_bytes);
                }
                IrConstValue::Slice {
                    data: IrConstScalar::Ptr(ptr, _),
                    ..
                } => {
                    walk_alloc(ptr.alloc_id, ptr.offset_bytes);
                }
                IrConstValue::Slice { .. } => {}
                IrConstValue::Indirect {
                    alloc_id,
                    offset_bytes,
                } => {
                    walk_alloc(*alloc_id, *offset_bytes);
                }
            }
        }
    }
}

fn explore_stmt_obligations(
    mir: &IrCapturedMir,
    kind: &IrStatementKind,
    is_latch_block: bool,
    mutation: Option<FalseProofMutationProbe>,
) -> BTreeSet<PropertyClass> {
    let mut out = BTreeSet::new();
    let ignore_deref = mutation == Some(FalseProofMutationProbe::DerefAliasProbe);
    let skip_latch_arith =
        is_latch_block && mutation == Some(FalseProofMutationProbe::LoopUpdateOverflowProbe);

    match kind {
        IrStatementKind::Assign(dst, rv) => {
            explore_place_access(mir, dst, false, ignore_deref, &mut out);
            match rv {
                IrRvalue::Use(op)
                | IrRvalue::Repeat(op, _)
                | IrRvalue::WrapUnsafeBinder(op, _) => {
                    explore_operand(mir, op, ignore_deref, &mut out);
                }
                IrRvalue::ShallowInitBox(op, _) => {
                    explore_operand(mir, op, ignore_deref, &mut out);
                    if !ignore_deref {
                        out.insert(PropertyClass::PointerDereference);
                    }
                }
                IrRvalue::Ref(_, p) | IrRvalue::RawPtr(_, p) => {
                    if !ignore_deref {
                        out.insert(PropertyClass::PointerDereference);
                    }
                    for proj in &p.projection {
                        match proj {
                            IrProjectionElem::Deref => {
                                out.insert(PropertyClass::UninitRead);
                                if !ignore_deref {
                                    out.insert(PropertyClass::PointerDereference);
                                }
                            }
                            IrProjectionElem::Index(_) => {
                                out.insert(PropertyClass::UninitRead);
                                out.insert(PropertyClass::SliceArrayBounds);
                            }
                            IrProjectionElem::ConstantIndex { .. }
                            | IrProjectionElem::Subslice { .. } => {
                                out.insert(PropertyClass::SliceArrayBounds);
                            }
                            IrProjectionElem::Downcast(_, _) => {
                                out.insert(PropertyClass::DiscriminantValidity);
                            }
                            IrProjectionElem::Field(_, _)
                            | IrProjectionElem::OpaqueCast(_)
                            | IrProjectionElem::UnwrapUnsafeBinder(_) => {}
                        }
                    }
                }
                IrRvalue::Len(p) => {
                    explore_place_access(mir, p, true, ignore_deref, &mut out);
                    out.insert(PropertyClass::SliceArrayBounds);
                }
                IrRvalue::CopyForDeref(p) => {
                    explore_place_access(mir, p, true, ignore_deref, &mut out);
                    if !ignore_deref {
                        out.insert(PropertyClass::PointerDereference);
                    }
                }
                IrRvalue::Discriminant(p) => {
                    explore_place_access(mir, p, true, ignore_deref, &mut out);
                    out.insert(PropertyClass::DiscriminantValidity);
                }
                IrRvalue::Cast(ck, op, target_ty) => {
                    explore_operand(mir, op, ignore_deref, &mut out);
                    match ck {
                        IrCastKind::FloatToInt if !skip_latch_arith => {
                            out.insert(PropertyClass::ArithmeticOverflow);
                        }
                        IrCastKind::FloatToInt => {}
                        IrCastKind::PointerExposeProvenance
                        | IrCastKind::PointerWithExposedProvenance
                        | IrCastKind::PointerCoercion(_)
                        | IrCastKind::PtrToPtr
                        | IrCastKind::FnPtrToPtr => {
                            if !ignore_deref {
                                out.insert(PropertyClass::PointerDereference);
                            }
                        }
                        IrCastKind::Transmute => {
                            out.insert(PropertyClass::DiscriminantValidity);
                            out.insert(PropertyClass::UninitRead);
                        }
                        IrCastKind::IntToInt
                        | IrCastKind::FloatToFloat
                        | IrCastKind::IntToFloat
                        | IrCastKind::Subtype => {
                            if matches!(
                                target_ty.kind,
                                IrRigidTy::Bool
                                    | IrRigidTy::Char
                                    | IrRigidTy::Adt(_, _)
                                    | IrRigidTy::Never
                            ) {
                                out.insert(PropertyClass::DiscriminantValidity);
                            }
                        }
                    }
                }
                IrRvalue::BinaryOp(bin_op, lhs, rhs) => {
                    explore_operand(mir, lhs, ignore_deref, &mut out);
                    explore_operand(mir, rhs, ignore_deref, &mut out);
                    match bin_op {
                        IrBinOp::Add
                        | IrBinOp::AddUnchecked
                        | IrBinOp::AddWithOverflow
                        | IrBinOp::Sub
                        | IrBinOp::SubUnchecked
                        | IrBinOp::SubWithOverflow
                        | IrBinOp::Mul
                        | IrBinOp::MulUnchecked
                        | IrBinOp::MulWithOverflow => {
                            if !skip_latch_arith {
                                out.insert(PropertyClass::ArithmeticOverflow);
                            }
                        }
                        IrBinOp::Shl
                        | IrBinOp::ShlUnchecked
                        | IrBinOp::Shr
                        | IrBinOp::ShrUnchecked => {
                            out.insert(PropertyClass::ShiftBounds);
                        }
                        IrBinOp::Div | IrBinOp::Rem => {
                            out.insert(PropertyClass::DivRemUb);
                        }
                        IrBinOp::Offset => {
                            if !ignore_deref {
                                out.insert(PropertyClass::PointerDereference);
                            }
                            out.insert(PropertyClass::SliceArrayBounds);
                        }
                        IrBinOp::Eq
                        | IrBinOp::Ne
                        | IrBinOp::Lt
                        | IrBinOp::Le
                        | IrBinOp::Gt
                        | IrBinOp::Ge
                        | IrBinOp::Cmp => {
                            let ctx = MirBodyTypingCtx {
                                local_decls: &mir.local_decls,
                                layouts: &mir.layouts,
                                allocations: &mir.allocations,
                            };
                            if !ignore_deref
                                && (ctx.operand_is_ptr_like(lhs) || ctx.operand_is_ptr_like(rhs))
                            {
                                out.insert(PropertyClass::PointerDereference);
                            }
                        }
                        IrBinOp::BitXor | IrBinOp::BitAnd | IrBinOp::BitOr => {}
                    }
                }
                IrRvalue::UnaryOp(un_op, arg) => {
                    explore_operand(mir, arg, ignore_deref, &mut out);
                    match un_op {
                        IrUnOp::Neg if !skip_latch_arith => {
                            out.insert(PropertyClass::ArithmeticOverflow);
                        }
                        IrUnOp::PtrMetadata => {
                            if !ignore_deref {
                                out.insert(PropertyClass::PointerDereference);
                            }
                            out.insert(PropertyClass::SliceArrayBounds);
                        }
                        IrUnOp::Neg | IrUnOp::Not => {}
                    }
                }
                IrRvalue::Aggregate(ak, ops) => {
                    for op in ops {
                        explore_operand(mir, op, ignore_deref, &mut out);
                    }
                    match ak {
                        IrAggregateKind::Adt(_, _, _) => {
                            out.insert(PropertyClass::DiscriminantValidity);
                        }
                        IrAggregateKind::RawPtr(_, _) if !ignore_deref => {
                            out.insert(PropertyClass::PointerDereference);
                        }
                        IrAggregateKind::Array(_)
                        | IrAggregateKind::Tuple
                        | IrAggregateKind::Closure(_)
                        | IrAggregateKind::Coroutine(_)
                        | IrAggregateKind::RawPtr(_, _) => {}
                    }
                }
                IrRvalue::ThreadLocalRef(_) | IrRvalue::NullaryOp(_, _) => {}
            }
        }
        IrStatementKind::SetDiscriminant(dst, _) => {
            explore_place_access(mir, dst, false, ignore_deref, &mut out);
            out.insert(PropertyClass::DiscriminantValidity);
        }
        IrStatementKind::Deinit(dst) => {
            explore_place_access(mir, dst, false, ignore_deref, &mut out);
        }
        IrStatementKind::Retag(_, p) => {
            if !ignore_deref {
                out.insert(PropertyClass::PointerDereference);
            }
            explore_place_access(mir, p, false, ignore_deref, &mut out);
        }
        IrStatementKind::PlaceMention(p) | IrStatementKind::BackwardIncompatibleDropHint(p) => {
            for proj in &p.projection {
                match proj {
                    IrProjectionElem::Deref => {
                        out.insert(PropertyClass::UninitRead);
                        if !ignore_deref {
                            out.insert(PropertyClass::PointerDereference);
                        }
                    }
                    IrProjectionElem::Index(_) => {
                        out.insert(PropertyClass::UninitRead);
                        out.insert(PropertyClass::SliceArrayBounds);
                    }
                    IrProjectionElem::ConstantIndex { .. } | IrProjectionElem::Subslice { .. } => {
                        out.insert(PropertyClass::SliceArrayBounds);
                    }
                    IrProjectionElem::Downcast(_, _) => {
                        out.insert(PropertyClass::DiscriminantValidity);
                    }
                    _ => {}
                }
            }
        }
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::Assume(op)) => {
            explore_operand(mir, op, ignore_deref, &mut out);
            out.insert(PropertyClass::DiscriminantValidity);
        }
        IrStatementKind::Intrinsic(IrNonDivergingIntrinsic::CopyNonOverlapping {
            src,
            dst,
            count,
        }) => {
            explore_operand(mir, src, ignore_deref, &mut out);
            explore_operand(mir, dst, ignore_deref, &mut out);
            explore_operand(mir, count, ignore_deref, &mut out);
            if !ignore_deref {
                out.insert(PropertyClass::PointerDereference);
            }
            out.insert(PropertyClass::MemoryCopyOverlap);
            if !skip_latch_arith {
                out.insert(PropertyClass::ArithmeticOverflow);
            }
        }
        IrStatementKind::StorageLive(_)
        | IrStatementKind::StorageDead(_)
        | IrStatementKind::Coverage
        | IrStatementKind::ConstEvalCounter
        | IrStatementKind::Nop => {}
    }

    out
}

fn explore_terminator_obligations(
    mir: &IrCapturedMir,
    _bb_idx: usize,
    kind: &IrTerminatorKind,
    is_latch_block: bool,
    opts: &ObligationExplorerOptions,
) -> BTreeSet<PropertyClass> {
    let mut out = BTreeSet::new();
    let num_blocks = mir.basic_blocks.len();
    let has_oob_succ = terminator_all_targets(kind).iter().any(|&s| s >= num_blocks);

    if is_latch_block {
        out.insert(PropertyClass::LoopTermination);
    }

    match kind {
        IrTerminatorKind::Goto(_) | IrTerminatorKind::UnwindTerminate => {}
        IrTerminatorKind::SwitchInt(discr, _) => {
            explore_operand(mir, discr, false, &mut out);
            if !has_oob_succ {
                out.insert(PropertyClass::SwitchExhaustiveness);
            }
        }
        IrTerminatorKind::UnwindResume => {
            out.insert(PropertyClass::CallContract);
        }
        IrTerminatorKind::Return => {
            out.insert(PropertyClass::UninitRead);
            let ctx = MirBodyTypingCtx {
                local_decls: &mir.local_decls,
                layouts: &mir.layouts,
                allocations: &mir.allocations,
            };
            if ctx.body_has_any_ref_or_ptr_local() {
                out.insert(PropertyClass::PointerDereference);
            }
        }
        IrTerminatorKind::Unreachable => {
            out.insert(PropertyClass::DiscriminantValidity);
        }
        IrTerminatorKind::Drop { place, unwind, .. } => {
            explore_place_access(mir, place, false, false, &mut out);
            out.insert(PropertyClass::CallContract);
            if matches!(unwind, IrUnwindAction::Unreachable) {
                out.insert(PropertyClass::DiscriminantValidity);
            }
        }
        IrTerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
        } => {
            let is_diverging = target.is_none();
            explore_call_common(
                mir,
                func,
                args,
                is_diverging,
                opts,
                &mut out,
            );
            explore_place_access(mir, destination, false, false, &mut out);
            if matches!(unwind, IrUnwindAction::Unreachable) {
                out.insert(PropertyClass::DiscriminantValidity);
            }
        }
        IrTerminatorKind::TailCall { func, args } => {
            explore_call_common(mir, func, args, false, opts, &mut out);
        }
        IrTerminatorKind::Assert { cond, unwind, .. } => {
            explore_operand(mir, cond, false, &mut out);
            if !has_oob_succ {
                out.insert(PropertyClass::SliceArrayBounds);
            }
            if matches!(unwind, IrUnwindAction::Unreachable) {
                out.insert(PropertyClass::DiscriminantValidity);
            }
        }
        IrTerminatorKind::InlineAsm { .. } => {}
    }

    out
}

fn explore_call_common(
    mir: &IrCapturedMir,
    func: &IrOperand,
    args: &[IrOperand],
    is_diverging: bool,
    opts: &ObligationExplorerOptions,
    out: &mut BTreeSet<PropertyClass>,
) {
    let blind_call_args =
        opts.injected_mutation == Some(FalseProofMutationProbe::CallArgBlindProbe);

    let call_covered = if let Some(def_path) = extract_direct_callee_def_path(func) {
        let mut intrinsic_classes = Vec::new();
        classify_callee_intrinsic_classes(def_path, &mut intrinsic_classes);
        for c in intrinsic_classes {
            out.insert(c);
        }
        if def_path == mir.def_path || opts.recursive_callees.contains(def_path) {
            out.insert(PropertyClass::LoopTermination);
        }
        !opts.call_context.enforce_callee_closure
            || is_natively_modeled_mir_call(def_path, is_diverging)
            || opts.call_context.linked_callees.contains(def_path)
            || opts.call_context.modular_contract_callees.contains(def_path)
    } else {
        explore_operand(mir, func, false, out);
        out.insert(PropertyClass::PointerDereference);
        !opts.call_context.enforce_callee_closure || opts.call_context.allow_modular_indirect_calls
    };

    if call_covered {
        out.insert(PropertyClass::CallContract);
    }

    for arg in args {
        explore_operand(mir, arg, blind_call_args, out);
    }
}

/// Explore reachable CFG blocks of `mir` from entry `bb0` and derive the
/// [`EmittedObligationCoverage`] discharged by `bundle` + `authored`, enforcing
/// exact token-level pinning against `obligations_lean_src` and
/// `verify_lean_src` whenever provided.
pub fn derive_bundle_obligation_coverage(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
    mir: &IrCapturedMir,
    obligations_lean_src: Option<&str>,
    verify_lean_src: Option<&str>,
) -> EmittedObligationCoverage {
    derive_bundle_obligation_coverage_with_recursion(
        bundle,
        authored,
        mir,
        obligations_lean_src,
        verify_lean_src,
        &BTreeSet::new(),
        true,
    )
}

/// Extended variant of [`derive_bundle_obligation_coverage`] accepting
/// mutual-recursion callee `DefPath`s and explicit `preserve_retags` control.
pub fn derive_bundle_obligation_coverage_with_recursion(
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
    mir: &IrCapturedMir,
    obligations_lean_src: Option<&str>,
    verify_lean_src: Option<&str>,
    recursive_callees: &BTreeSet<String>,
    preserve_retags: bool,
) -> EmittedObligationCoverage {
    let item = &bundle.item_module_suffix;
    let empty_fail_closed = || EmittedObligationCoverage {
        discharged_sites: BTreeSet::new(),
        explicit_waivers: Vec::new(),
        call_context: CallCoverageContext {
            enforce_callee_closure: true,
            ..CallCoverageContext::default()
        },
    };

    let uses_rust_trusted_contract = !authored.has_proof
        && !authored.has_assumptions
        && (bundle.has_rust_trusted_attr() || authored.has_generated_assumptions);
    let is_trusted_assumption =
        bundle.has_rust_trusted_attr() || authored.has_assumptions || authored.has_generated_assumptions;

    let parsed_ob = if let Some(ob_src) = obligations_lean_src {
        let Some(pin) = verify_obligations_module_pin(ob_src, item, authored) else {
            return empty_fail_closed();
        };
        Some(pin)
    } else {
        None
    };

    if let Some(ver_src) = verify_lean_src {
        if !verify_module_pins_expected_surface(
            ver_src,
            item,
            bundle,
            authored,
            uses_rust_trusted_contract,
        ) {
            return empty_fail_closed();
        }
    }

    let mut linked_callees: BTreeSet<String> = bundle
        .transitive_callees
        .iter()
        .map(|c| c.def_id.clone())
        .collect();
    if let Some(ref ob_pin) = parsed_ob {
        for callee in &bundle.transitive_callees {
            if !ob_pin
                .default_callees_suffixes
                .contains(&callee.item_module_suffix)
            {
                linked_callees.remove(&callee.def_id);
            }
        }
    }

    let is_modular_surface = authored.is_modular
        || (!authored.has_proof
            && !authored.has_specs
            && !uses_rust_trusted_contract
            && (!bundle.external_spec_callees.is_empty() || !bundle.called_callees.is_empty()));
    let mut modular_contract_callees = BTreeSet::new();
    if is_modular_surface {
        for ext in &bundle.external_spec_callees {
            let ident = crate::obligations::external_call_contract_ident(ext);
            let present = parsed_ob
                .as_ref()
                .is_none_or(|p| p.env_assumed_idents.contains(&ident));
            if present {
                modular_contract_callees.insert(ext.target_def_id.clone());
            }
        }
        for callee in &bundle.called_callees {
            let ident = format!("Obligations.{}.defaultCallContract", callee.item_module_suffix);
            let present = parsed_ob
                .as_ref()
                .is_none_or(|p| p.env_assumed_idents.contains(&ident));
            if present {
                modular_contract_callees.insert(callee.def_id.clone());
            }
        }
    }

    let is_total_surface =
        authored.is_total || authored.is_equiv || bundle.has_rust_safe_total_attr();

    let call_context = CallCoverageContext {
        enforce_callee_closure: true,
        linked_callees,
        modular_contract_callees,
        allow_modular_indirect_calls: is_modular_surface && authored.has_specs,
    };

    explore_mir_obligations(
        mir,
        &ObligationExplorerOptions {
            proves_total_termination: is_total_surface,
            is_trusted_assumption,
            preserve_retags,
            call_context,
            recursive_callees: recursive_callees.clone(),
            injected_mutation: None,
        },
    )
}

#[derive(Debug, Default)]
pub(crate) struct VerifiedObligationsPin {
    pub(crate) default_callees_suffixes: BTreeSet<String>,
    pub(crate) env_assumed_idents: BTreeSet<String>,
}

/// Tokenize Lean source after stripping all `--` line comments, nested
/// `/- ... -/` block comments, and `"..."` / `'...'` literals (replacing string
/// literals with an opaque `""` token so string contents can never impersonate
/// Lean keywords, declarations, or `Mir.<Item>.body` identifiers).
fn tokenize_lean_code_words_and_punct(src: &str) -> Option<Vec<String>> {
    let mut toks = Vec::new();
    let mut chars = src.char_indices().peekable();
    let mut block_depth = 0usize;

    while let Some((idx, ch)) = chars.next() {
        if block_depth > 0 {
            if ch == '/' && chars.peek().is_some_and(|&(_, n)| n == '-') {
                chars.next();
                block_depth += 1;
            } else if ch == '-' && chars.peek().is_some_and(|&(_, n)| n == '/') {
                chars.next();
                block_depth -= 1;
            }
            continue;
        }
        if ch.is_whitespace() {
            continue;
        }
        if ch == '/' && chars.peek().is_some_and(|&(_, n)| n == '-') {
            chars.next();
            block_depth = 1;
            continue;
        }
        if ch == '-' && chars.peek().is_some_and(|&(_, n)| n == '-') {
            for (_, c) in chars.by_ref() {
                if c == '\n' {
                    break;
                }
            }
            continue;
        }
        if ch == '"' {
            let mut closed = false;
            let mut escaped = false;
            for (_, sc) in chars.by_ref() {
                if escaped {
                    escaped = false;
                } else if sc == '\\' {
                    escaped = true;
                } else if sc == '"' {
                    closed = true;
                    break;
                }
            }
            if !closed {
                return None;
            }
            toks.push(String::from("\"\""));
            continue;
        }
        if ch == '\''
            && let Some(lit_len) = lean_char_literal_len_local(
                src,
                idx,
                src[..idx].chars().next_back(),
            )
        {
            while chars.peek().is_some_and(|&(ni, _)| ni < idx + lit_len) {
                chars.next();
            }
            toks.push(String::from("''"));
            continue;
        }
        if ch == '«' || ch == '»' {
            return None;
        }
        if ch == ':' && chars.peek().is_some_and(|&(_, n)| n == '=') {
            chars.next();
            toks.push(String::from(":="));
            continue;
        }
        if matches!(ch, '(' | ')' | '{' | '}' | '[' | ']' | ',' | ':') {
            toks.push(ch.to_string());
            continue;
        }
        if is_lean_ident_char_local(ch)
            || (ch == '.'
                && chars
                    .peek()
                    .is_some_and(|&(_, n)| is_lean_ident_char_local(n)))
        {
            let start = idx;
            let mut end = idx + ch.len_utf8();
            while let Some(&(ni, nc)) = chars.peek() {
                if is_lean_ident_char_local(nc) || nc == '.' {
                    end = ni + nc.len_utf8();
                    chars.next();
                } else {
                    break;
                }
            }
            toks.push(src[start..end].to_string());
            continue;
        }
        toks.push(ch.to_string());
    }

    if block_depth != 0 {
        return None;
    }
    Some(toks)
}

/// Extract all `Mir.<Suffix>.body` module suffixes referenced in non-comment,
/// non-string Lean code tokens of `src`.
pub(crate) fn extract_lean_mir_body_refs(src: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let Some(toks) = tokenize_lean_code_words_and_punct(src) else {
        return out;
    };
    for tok in toks {
        if let Some(mid) = tok
            .strip_prefix("Mir.")
            .and_then(|s| s.strip_suffix(".body"))
            && !mid.is_empty()
        {
            out.insert(mid.to_string());
        }
    }
    out
}

fn split_top_level_decl_slices(toks: &[String]) -> Vec<&[String]> {
    let mut decls = Vec::new();
    let mut depth = 0usize;
    let mut cur_start: Option<usize> = None;

    for (i, tok) in toks.iter().enumerate() {
        match tok.as_str() {
            "(" | "[" | "{" => depth += 1,
            ")" | "]" | "}" => depth = depth.saturating_sub(1),
            _ if depth == 0 && is_lean_decl_boundary_tok(tok) => {
                if let Some(s) = cur_start.take() {
                    decls.push(&toks[s..i]);
                }
                if matches!(
                    tok.as_str(),
                    "def" | "abbrev" | "instance" | "theorem" | "lemma" | "axiom"
                ) {
                    cur_start = Some(i);
                }
            }
            _ => {}
        }
    }
    if let Some(s) = cur_start {
        decls.push(&toks[s..]);
    }
    decls
}

fn is_lean_decl_boundary_tok(tok: &str) -> bool {
    matches!(
        tok,
        "def"
            | "abbrev"
            | "instance"
            | "theorem"
            | "lemma"
            | "axiom"
            | "opaque"
            | "structure"
            | "inductive"
            | "class"
            | "namespace"
            | "end"
            | "section"
            | "@"
    )
}

fn tokens_contain_subslice(haystack: &[String], needle: &[&str]) -> bool {
    if needle.is_empty() || haystack.len() < needle.len() {
        return false;
    }
    haystack
        .windows(needle.len())
        .any(|w| w.iter().zip(needle).all(|(a, b)| a == b))
}

pub(crate) fn verify_obligations_module_pin(
    obligations_src: &str,
    item_suffix: &str,
    authored: AuthoredItemModules,
) -> Option<VerifiedObligationsPin> {
    let toks = tokenize_lean_code_words_and_punct(obligations_src)?;
    let expected_ns = format!("Obligations.{item_suffix}");
    if !tokens_contain_subslice(&toks, &["namespace", &expected_ns])
        || !tokens_contain_subslice(&toks, &["end", &expected_ns])
    {
        return None;
    }

    let decls = split_top_level_decl_slices(&toks);
    let find_unique_def = |target_name: &str| -> Option<&[String]> {
        let matches: Vec<&[String]> = decls
            .iter()
            .copied()
            .filter(|d| d.len() >= 2 && matches!(d[0].as_str(), "def" | "abbrev") && d[1] == target_name)
            .collect();
        match matches.as_slice() {
            [only] => Some(*only),
            _ => None,
        }
    };

    // 1. Parse `def defaultCallees : List CapturedMir := ...` inside its own declaration.
    let mut default_callees_suffixes = BTreeSet::new();
    if let Some(callees_decl) = find_unique_def("defaultCallees") {
        let eq_pos = callees_decl.iter().position(|t| t == ":=")?;
        let rhs = &callees_decl[eq_pos + 1..];
        for tok in rhs {
            if let Some(mid) = tok
                .strip_prefix("Mir.")
                .and_then(|s| s.strip_suffix(".body"))
                && !mid.is_empty()
            {
                default_callees_suffixes.insert(mid.to_string());
            }
        }
    } else {
        return None;
    }

    // 2. Parse `defaultModularSpec` `envAssumed` contracts inside its own instance declaration.
    let mut env_assumed_idents = BTreeSet::new();
    for d in &decls {
        if d.first().map(String::as_str) == Some("instance")
            && d.iter().any(|t| t == "defaultModularSpec")
        {
            for tok in *d {
                if let Some(contract_id) = tok.strip_suffix(".holdsOn") {
                    env_assumed_idents.insert(contract_id.to_string());
                }
            }
        }
    }

    // 3. Verify the exact active claim definition's body and callees fields!
    let mir_body_tok = format!("Mir.{item_suffix}.body");
    let mir_inst_tok = format!("Mir.{item_suffix}.body.instantiate");

    if authored.is_polymorphic {
        let (for_name, poly_name, result_ctor) = if authored.is_ub_exception {
            (
                "ubExceptionClaimFor",
                "polyUbExceptionClaim",
                "UbExceptionVerificationResult",
            )
        } else if authored.is_modular {
            (
                "modularClaimFor",
                "polyModularClaim",
                "ModularVerificationResult",
            )
        } else if authored.is_total {
            ("totalClaimFor", "polyTotalClaim", "TotalVerificationResult")
        } else if authored.is_stateful {
            (
                "statefulClaimFor",
                "polyStatefulClaim",
                "StatefulVerificationResult",
            )
        } else {
            ("claimFor", "polyClaim", "VerificationResult")
        };

        let for_decl = find_unique_def(for_name)?;
        if !tokens_contain_subslice(for_decl, &["body", ":=", &mir_inst_tok, "typeArgs"])
            || !tokens_contain_subslice(for_decl, &["callees", ":=", "defaultCallees"])
        {
            return None;
        }
        if authored.is_modular
            && !tokens_contain_subslice(for_decl, &["envAssumed", ":=", "spec.envAssumed"])
        {
            return None;
        }
        let poly_decl = find_unique_def(poly_name)?;
        if !tokens_contain_subslice(poly_decl, &[result_ctor, "(", for_name, "typeArgs", ")"]) {
            return None;
        }
    } else if authored.is_equiv {
        let equiv_decl = find_unique_def("equivClaim")?;
        if !tokens_contain_subslice(equiv_decl, &["implBody", ":=", &mir_body_tok])
            || !tokens_contain_subslice(equiv_decl, &["specBody", ":=", "spec.specBody"])
            || !tokens_contain_subslice(equiv_decl, &["implCallees", ":=", "defaultCallees"])
            || !tokens_contain_subslice(equiv_decl, &["specCallees", ":=", "defaultCallees"])
        {
            return None;
        }
    } else {
        let claim_name = if authored.is_ub_exception {
            "ubExceptionClaim"
        } else if authored.is_modular {
            "modularClaim"
        } else if authored.is_total {
            "totalClaim"
        } else if authored.is_stateful {
            "statefulClaim"
        } else {
            "claim"
        };
        let claim_decl = find_unique_def(claim_name)?;
        if !tokens_contain_subslice(claim_decl, &["body", ":=", &mir_body_tok])
            || !tokens_contain_subslice(claim_decl, &["callees", ":=", "defaultCallees"])
        {
            return None;
        }
        if authored.is_modular
            && !tokens_contain_subslice(claim_decl, &["envAssumed", ":=", "spec.envAssumed"])
        {
            return None;
        }
    }

    Some(VerifiedObligationsPin {
        default_callees_suffixes,
        env_assumed_idents,
    })
}

pub(crate) fn verify_module_pins_expected_surface(
    verify_src: &str,
    item_suffix: &str,
    bundle: &SubjectObligationBundle,
    authored: AuthoredItemModules,
    uses_rust_trusted_contract: bool,
) -> bool {
    let Some(toks) = tokenize_lean_code_words_and_punct(verify_src) else {
        return false;
    };
    let expected_ns = format!("Verify.{item_suffix}");
    if !tokens_contain_subslice(&toks, &["namespace", &expected_ns])
        || !tokens_contain_subslice(&toks, &["end", &expected_ns])
    {
        return false;
    }

    // Require matching imports for authored Specs / Proof / Assumptions modules.
    if authored.has_specs
        && !tokens_contain_subslice(&toks, &["import", &format!("Specs.{item_suffix}")])
    {
        return false;
    }
    if authored.has_proof
        && !tokens_contain_subslice(&toks, &["import", &format!("Proof.{item_suffix}")])
    {
        return false;
    }
    if (authored.has_assumptions || uses_rust_trusted_contract)
        && !tokens_contain_subslice(&toks, &["import", &format!("Assumptions.{item_suffix}")])
    {
        return false;
    }

    let decls = split_top_level_decl_slices(&toks);
    let verified_theorems: Vec<&[String]> = decls
        .iter()
        .copied()
        .filter(|d| d.len() >= 4 && d[0] == "theorem" && d[1] == "verified" && d[2] == ":")
        .collect();
    let [verified_decl] = verified_theorems.as_slice() else {
        return false;
    };
    let Some(assign_idx) = verified_decl.iter().position(|t| t == ":=") else {
        return false;
    };
    let sig_tokens: Vec<&str> = verified_decl[3..assign_idx]
        .iter()
        .map(String::as_str)
        .collect();

    let is_modular_default = !authored.has_proof
        && !uses_rust_trusted_contract
        && !authored.has_specs
        && (!bundle.external_spec_callees.is_empty() || !bundle.called_callees.is_empty());
    let is_total_trusted =
        uses_rust_trusted_contract && (bundle.has_rust_safe_total_attr() || authored.is_total);

    let expected_sig: Vec<String> = if authored.is_polymorphic {
        let poly_claim = if authored.is_ub_exception {
            format!("Obligations.{item_suffix}.polyUbExceptionClaim")
        } else if authored.is_modular || is_modular_default {
            format!("Obligations.{item_suffix}.polyModularClaim")
        } else if authored.is_total {
            format!("Obligations.{item_suffix}.polyTotalClaim")
        } else if authored.is_stateful {
            format!("Obligations.{item_suffix}.polyStatefulClaim")
        } else {
            format!("Obligations.{item_suffix}.polyClaim")
        };
        vec![
            String::from("CrateVerificationResult"),
            String::from("("),
            format!("Obligations.{item_suffix}.polyCertificate"),
            poly_claim,
            String::from(")"),
        ]
    } else if authored.is_ub_exception {
        vec![
            String::from("UbExceptionVerificationResult"),
            format!("Obligations.{item_suffix}.ubExceptionClaim"),
        ]
    } else if authored.is_modular || is_modular_default {
        vec![
            String::from("ModularVerificationResult"),
            format!("Obligations.{item_suffix}.modularClaim"),
        ]
    } else if authored.is_equiv {
        vec![
            String::from("StatefulEquivVerificationResult"),
            format!("Obligations.{item_suffix}.equivClaim"),
        ]
    } else if authored.is_total || is_total_trusted {
        vec![
            String::from("TotalVerificationResult"),
            format!("Obligations.{item_suffix}.totalClaim"),
        ]
    } else if authored.is_stateful {
        vec![
            String::from("StatefulVerificationResult"),
            format!("Obligations.{item_suffix}.statefulClaim"),
        ]
    } else {
        vec![
            String::from("VerificationResult"),
            format!("Obligations.{item_suffix}.claim"),
        ]
    };

    let expected_refs: Vec<&str> = expected_sig.iter().map(String::as_str).collect();
    if sig_tokens != expected_refs {
        return false;
    }

    // Require `signatureMonomorphic` guard on monomorphic signature-typed authored proofs.
    if authored.has_proof
        && !authored.is_polymorphic
        && (authored.is_ub_exception
            || authored.is_modular
            || authored.is_total
            || authored.is_stateful)
    {
        let has_mono_guard = decls
            .iter()
            .any(|d| d.len() >= 3 && d[0] == "theorem" && d[1] == "signatureMonomorphic");
        if !has_mono_guard {
            return false;
        }
    }

    true
}

// ============================================================================
// 6. Self-Contained Strict Recursive-Descent Parser for `Mir/<Item>.lean`
// ============================================================================

fn is_lean_ident_char_local(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\''
}

fn lean_char_literal_len_local(src: &str, i: usize, prev_ch: Option<char>) -> Option<usize> {
    if src.as_bytes().get(i).copied() != Some(b'\'') {
        return None;
    }
    if prev_ch.is_some_and(is_lean_ident_char_local) {
        return None;
    }
    let after_open = src.get(i + 1..)?;
    let first = after_open.chars().next()?;
    if first == '\'' || first == '\n' || first == '\r' {
        return None;
    }
    if first != '\\' {
        let rest = &after_open[first.len_utf8()..];
        return rest.starts_with('\'').then_some(1 + first.len_utf8() + 1);
    }
    let after_slash = &after_open[1..];
    if let Some(hex_rest) = after_slash.strip_prefix('x') {
        let hex = hex_rest.get(..2)?;
        if hex.bytes().all(|b| b.is_ascii_hexdigit()) && hex_rest[2..].starts_with('\'') {
            return Some(6);
        }
        return None;
    }
    if let Some(uni_rest) = after_slash.strip_prefix('u') {
        let hex = uni_rest.get(..4)?;
        if hex.bytes().all(|b| b.is_ascii_hexdigit()) && uni_rest[4..].starts_with('\'') {
            return Some(8);
        }
        return None;
    }
    let esc = after_slash.chars().next()?;
    if esc == '\n' || esc == '\r' {
        return None;
    }
    let rest = &after_slash[esc.len_utf8()..];
    rest.starts_with('\'').then_some(2 + esc.len_utf8() + 1)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum MirTok {
    Ident(String),
    Nat(u128),
    Str(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    ColonEq,
    FatArrow,
}

fn tokenize_lean_mir(src: &str) -> Result<Vec<MirTok>, CensusError> {
    let mut out = Vec::new();
    let mut chars = src.char_indices().peekable();
    let mut block_depth = 0usize;

    while let Some((idx, ch)) = chars.next() {
        if block_depth > 0 {
            if ch == '/' && chars.peek().is_some_and(|&(_, n)| n == '-') {
                chars.next();
                block_depth += 1;
            } else if ch == '-' && chars.peek().is_some_and(|&(_, n)| n == '/') {
                chars.next();
                block_depth -= 1;
            }
            continue;
        }

        if ch.is_whitespace() {
            continue;
        }
        if ch == '/' && chars.peek().is_some_and(|&(_, n)| n == '-') {
            chars.next();
            block_depth = 1;
            continue;
        }
        if ch == '-' && chars.peek().is_some_and(|&(_, n)| n == '-') {
            for (_, c) in chars.by_ref() {
                if c == '\n' {
                    break;
                }
            }
            continue;
        }

        match ch {
            '«' | '»' => {
                return Err(CensusError::new(
                    "guillemet-quoted identifiers (`«...»`) are forbidden in captured MIR code",
                ));
            }
            '(' => out.push(MirTok::LParen),
            ')' => out.push(MirTok::RParen),
            '{' => out.push(MirTok::LBrace),
            '}' => out.push(MirTok::RBrace),
            '[' => out.push(MirTok::LBracket),
            ']' => out.push(MirTok::RBracket),
            ',' => out.push(MirTok::Comma),
            ':' => {
                if chars.peek().is_some_and(|&(_, n)| n == '=') {
                    chars.next();
                    out.push(MirTok::ColonEq);
                } else {
                    out.push(MirTok::Colon);
                }
            }
            '=' if chars.peek().is_some_and(|&(_, n)| n == '>') => {
                chars.next();
                out.push(MirTok::FatArrow);
            }
            '"' => {
                let mut raw_bytes: Vec<u8> = Vec::new();
                let mut closed = false;
                while let Some((_, sc)) = chars.next() {
                    if sc == '"' {
                        closed = true;
                        break;
                    }
                    if sc == '\\' {
                        let Some((_, esc)) = chars.next() else {
                            return Err(CensusError::new("unterminated string escape in MIR module"));
                        };
                        match esc {
                            '"' => raw_bytes.push(b'"'),
                            '\\' => raw_bytes.push(b'\\'),
                            '\'' => raw_bytes.push(b'\''),
                            'n' => raw_bytes.push(b'\n'),
                            'r' => raw_bytes.push(b'\r'),
                            't' => raw_bytes.push(b'\t'),
                            '0' => raw_bytes.push(0),
                            'x' => {
                                let Some((_, h1)) = chars.next() else {
                                    return Err(CensusError::new("truncated \\x escape in MIR string"));
                                };
                                let Some((_, h2)) = chars.next() else {
                                    return Err(CensusError::new("truncated \\x escape in MIR string"));
                                };
                                let hex = format!("{h1}{h2}");
                                let byte = u8::from_str_radix(&hex, 16).map_err(|_| {
                                    CensusError::new(format!("invalid \\x{hex} escape in MIR string"))
                                })?;
                                raw_bytes.push(byte);
                            }
                            'u' => {
                                let mut hex = String::with_capacity(4);
                                for _ in 0..4 {
                                    let Some((_, hc)) = chars.next() else {
                                        return Err(CensusError::new(
                                            "truncated \\uXXXX escape in MIR string",
                                        ));
                                    };
                                    hex.push(hc);
                                }
                                let code = u32::from_str_radix(&hex, 16).map_err(|_| {
                                    CensusError::new(format!(
                                        "invalid \\u{hex} escape in MIR string"
                                    ))
                                })?;
                                let ch_u = char::from_u32(code).ok_or_else(|| {
                                    CensusError::new(format!(
                                        "invalid Unicode scalar \\u{hex} in MIR string"
                                    ))
                                })?;
                                let mut utf8_buf = [0u8; 4];
                                raw_bytes.extend_from_slice(ch_u.encode_utf8(&mut utf8_buf).as_bytes());
                            }
                            other => {
                                return Err(CensusError::new(format!(
                                    "unsupported escape sequence `\\{other}` in MIR string literal"
                                )));
                            }
                        }
                    } else {
                        let mut utf8_buf = [0u8; 4];
                        raw_bytes.extend_from_slice(sc.encode_utf8(&mut utf8_buf).as_bytes());
                    }
                }
                if !closed {
                    return Err(CensusError::new(
                        "unterminated string literal in captured MIR module",
                    ));
                }
                let decoded = String::from_utf8(raw_bytes).map_err(|err| {
                    CensusError::new(format!(
                        "invalid UTF-8 byte sequence in MIR string literal: {err}"
                    ))
                })?;
                out.push(MirTok::Str(decoded));
            }
            c if c.is_ascii_digit() => {
                let start = idx;
                let mut end = idx + c.len_utf8();
                while let Some(&(ni, nc)) = chars.peek() {
                    if nc.is_ascii_digit() || nc == '_' {
                        end = ni + nc.len_utf8();
                        chars.next();
                    } else if is_lean_ident_char_local(nc) {
                        return Err(CensusError::new(format!(
                            "malformed numeric token near `{}` in MIR module",
                            &src[start..=ni]
                        )));
                    } else {
                        break;
                    }
                }
                let clean_digits: String = src[start..end].chars().filter(|&d| d != '_').collect();
                let val = clean_digits.parse::<u128>().map_err(|err| {
                    CensusError::new(format!("integer literal `{clean_digits}` overflow: {err}"))
                })?;
                out.push(MirTok::Nat(val));
            }
            c if is_lean_ident_char_local(c)
                || (c == '.'
                    && chars
                        .peek()
                        .is_some_and(|&(_, n)| is_lean_ident_char_local(n))) =>
            {
                let start = idx;
                let mut end = idx + c.len_utf8();
                while let Some(&(ni, nc)) = chars.peek() {
                    if is_lean_ident_char_local(nc) || nc == '.' {
                        end = ni + nc.len_utf8();
                        chars.next();
                    } else {
                        break;
                    }
                }
                out.push(MirTok::Ident(src[start..end].to_string()));
            }
            other => {
                return Err(CensusError::new(format!(
                    "unsupported token `{other}` in captured MIR module (non-inline or metaprogram syntax)"
                )));
            }
        }
    }

    if block_depth != 0 {
        return Err(CensusError::new(
            "unclosed `/- ... -/` block comment in captured MIR module",
        ));
    }

    Ok(out)
}

/// Parse a `Mir/<Item>.lean` module strictly into an [`IrCapturedMir`],
/// enforcing module-level import, balanced-namespace, and declaration hygiene
/// and rejecting any non-inline helper calls, `let`/`match`/`fun`/`with`
/// expressions, or unknown constructors.
pub fn parse_lean_mir_module_strict(lean_src: &str) -> Result<IrCapturedMir, CensusError> {
    let toks = tokenize_lean_mir(lean_src)?;
    let mut parser = LeanMirParser { toks: &toks, pos: 0 };
    parser.parse_module()
}

struct LeanMirParser<'a> {
    toks: &'a [MirTok],
    pos: usize,
}

impl<'a> LeanMirParser<'a> {
    fn peek(&self) -> Option<&'a MirTok> {
        self.toks.get(self.pos)
    }

    fn next(&mut self) -> Result<&'a MirTok, CensusError> {
        let tok = self
            .toks
            .get(self.pos)
            .ok_or_else(|| CensusError::new("unexpected end of captured MIR module"))?;
        self.pos += 1;
        Ok(tok)
    }

    fn eat_comma(&mut self) -> bool {
        if matches!(self.peek(), Some(MirTok::Comma)) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_tok(&mut self, expected: &MirTok, ctx: &str) -> Result<(), CensusError> {
        let actual = self.next()?;
        if actual == expected {
            Ok(())
        } else {
            Err(CensusError::new(format!(
                "expected `{expected:?}` in {ctx}, found `{actual:?}`"
            )))
        }
    }

    fn expect_ident(&mut self, ctx: &str) -> Result<&'a str, CensusError> {
        match self.next()? {
            MirTok::Ident(s) => Ok(s.as_str()),
            other => Err(CensusError::new(format!(
                "expected identifier in {ctx}, found `{other:?}`"
            ))),
        }
    }

    fn expect_str(&mut self, ctx: &str) -> Result<String, CensusError> {
        match self.next()? {
            MirTok::Str(s) => Ok(s.clone()),
            other => Err(CensusError::new(format!(
                "expected string literal in {ctx}, found `{other:?}`"
            ))),
        }
    }

    fn expect_u128(&mut self, ctx: &str) -> Result<u128, CensusError> {
        match self.next()? {
            MirTok::Nat(n) => Ok(*n),
            other => Err(CensusError::new(format!(
                "expected natural literal in {ctx}, found `{other:?}`"
            ))),
        }
    }

    fn expect_u64(&mut self, ctx: &str) -> Result<u64, CensusError> {
        let n = self.expect_u128(ctx)?;
        u64::try_from(n)
            .map_err(|_| CensusError::new(format!("u64 overflow ({n}) in {ctx}")))
    }

    fn expect_u32(&mut self, ctx: &str) -> Result<u32, CensusError> {
        let n = self.expect_u128(ctx)?;
        u32::try_from(n)
            .map_err(|_| CensusError::new(format!("u32 overflow ({n}) in {ctx}")))
    }

    fn expect_usize(&mut self, ctx: &str) -> Result<usize, CensusError> {
        let n = self.expect_u128(ctx)?;
        usize::try_from(n)
            .map_err(|_| CensusError::new(format!("usize overflow ({n}) in {ctx}")))
    }

    fn parse_bool(&mut self, ctx: &str) -> Result<bool, CensusError> {
        let id = self.expect_ident(ctx)?;
        match ctor_leaf(id, Some("Bool"))? {
            "true" => Ok(true),
            "false" => Ok(false),
            other => Err(CensusError::new(format!(
                "expected `true` or `false` in {ctx}, found `{other}`"
            ))),
        }
    }

    fn parse_paren_or_bare<T, F>(&mut self, mut f: F) -> Result<T, CensusError>
    where
        F: FnMut(&mut Self) -> Result<T, CensusError>,
    {
        if matches!(self.peek(), Some(MirTok::LParen)) {
            self.pos += 1;
            let val = f(self)?;
            self.expect_tok(&MirTok::RParen, "parenthesized constructor")?;
            Ok(val)
        } else {
            f(self)
        }
    }

    fn parse_list<T, F>(&mut self, ctx: &str, mut elem_parser: F) -> Result<Vec<T>, CensusError>
    where
        F: FnMut(&mut Self) -> Result<T, CensusError>,
    {
        let mut items = Vec::new();
        self.parse_list_into(ctx, &mut elem_parser, &mut items)?;
        Ok(items)
    }

    fn parse_list_into<T, F>(
        &mut self,
        ctx: &str,
        elem_parser: &mut F,
        out: &mut Vec<T>,
    ) -> Result<(), CensusError>
    where
        F: FnMut(&mut Self) -> Result<T, CensusError>,
    {
        match self.peek() {
            Some(MirTok::LBracket) => {
                self.pos += 1;
                while !matches!(self.peek(), Some(MirTok::RBracket)) {
                    out.push(elem_parser(self)?);
                    if !self.eat_comma() {
                        break;
                    }
                }
                self.expect_tok(&MirTok::RBracket, ctx)?;
                Ok(())
            }
            Some(MirTok::LParen) => {
                self.pos += 1;
                let head = self.expect_ident(ctx)?;
                match ctor_leaf(head, Some("List"))? {
                    "nil" => {
                        self.expect_tok(&MirTok::RParen, ctx)?;
                        Ok(())
                    }
                    "cons" => {
                        out.push(elem_parser(self)?);
                        self.parse_list_into(ctx, elem_parser, out)?;
                        self.expect_tok(&MirTok::RParen, ctx)?;
                        Ok(())
                    }
                    other => Err(CensusError::new(format!(
                        "unexpected List constructor `{other}` in {ctx}"
                    ))),
                }
            }
            Some(MirTok::Ident(id)) => {
                let id_str = id.as_str();
                self.pos += 1;
                match ctor_leaf(id_str, Some("List"))? {
                    "nil" => Ok(()),
                    "cons" => {
                        out.push(elem_parser(self)?);
                        self.parse_list_into(ctx, elem_parser, out)
                    }
                    other => Err(CensusError::new(format!(
                        "non-inline or unknown list identifier `{other}` in {ctx}"
                    ))),
                }
            }
            other => Err(CensusError::new(format!(
                "expected list literal in {ctx}, found `{other:?}`"
            ))),
        }
    }

    fn parse_option<T, F>(&mut self, ctx: &str, mut inner: F) -> Result<Option<T>, CensusError>
    where
        F: FnMut(&mut Self) -> Result<T, CensusError>,
    {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident(ctx)?;
            match ctor_leaf(head, Some("Option"))? {
                "none" => Ok(None),
                "some" => Ok(Some(inner(p)?)),
                other => Err(CensusError::new(format!(
                    "expected `Option.some` or `Option.none` in {ctx}, found `{other}`"
                ))),
            }
        })
    }

    fn parse_module(&mut self) -> Result<IrCapturedMir, CensusError> {
        const FORBIDDEN_MODULE_KW: &[&str] = &[
            "where",
            "rec",
            "export",
            "run_cmd",
            "run_elab",
            "run_meta",
            "elab",
            "elab_rules",
            "macro",
            "macro_rules",
            "syntax",
            "notation",
            "infix",
            "infixl",
            "infixr",
            "prefix",
            "postfix",
            "initialize",
            "builtin_initialize",
            "axiom",
            "opaque",
            "section",
            "in",
        ];
        for tok in self.toks {
            if let MirTok::Ident(w) = tok
                && (FORBIDDEN_MODULE_KW.contains(&w.as_str()) || w.starts_with("builtin_"))
            {
                return Err(CensusError::new(format!(
                    "forbidden declaration/metaprogram keyword `{w}` in captured MIR module"
                )));
            }
        }

        let mut layouts_def: Option<IrLayoutTable> = None;
        let mut body_def: Option<IrCapturedMir> = None;
        let mut namespace_stack: Vec<String> = Vec::new();

        while let Some(tok) = self.peek() {
            let MirTok::Ident(kw) = tok else {
                return Err(CensusError::new(format!(
                    "unexpected top-level token `{tok:?}` in captured MIR module"
                )));
            };
            match kw.as_str() {
                "prelude" => {
                    self.pos += 1;
                }
                "import" => {
                    self.pos += 1;
                    let mod_name = self.expect_ident("import")?;
                    let allowed = ["Init", "Trusted"].iter().any(|root| {
                        mod_name == *root
                            || mod_name
                                .strip_prefix(root)
                                .is_some_and(|rest| rest.starts_with('.'))
                    });
                    if !allowed {
                        return Err(CensusError::new(format!(
                            "forbidden `import {mod_name}` in captured MIR module (only `Init` and `Trusted` are allowed)"
                        )));
                    }
                }
                "namespace" => {
                    self.pos += 1;
                    let ns = self.expect_ident("namespace")?;
                    namespace_stack.push(ns.to_string());
                }
                "end" => {
                    self.pos += 1;
                    let ended = self.expect_ident("end namespace")?;
                    let Some(expected) = namespace_stack.pop() else {
                        return Err(CensusError::new(format!(
                            "unmatched `end {ended}` without an open `namespace`"
                        )));
                    };
                    if ended != expected {
                        return Err(CensusError::new(format!(
                            "mismatched `end {ended}` for `namespace {expected}`"
                        )));
                    }
                }
                "open" => {
                    self.pos += 1;
                    let mut count = 0usize;
                    while let Some(MirTok::Ident(next_w)) = self.peek() {
                        if is_top_level_mir_module_kw(next_w) {
                            break;
                        }
                        self.pos += 1;
                        count += 1;
                        if matches!(self.peek(), Some(MirTok::LParen)) {
                            self.skip_balanced_group()?;
                        }
                    }
                    if count == 0 {
                        return Err(CensusError::new("empty `open` command in MIR module"));
                    }
                }
                "set_option" => {
                    self.pos += 1;
                    let _opt_name = self.expect_ident("set_option")?;
                    let _opt_val = self.next()?;
                }
                "def" | "abbrev" => {
                    self.pos += 1;
                    let decl_name = self.expect_ident("def name")?;
                    if decl_name == "layouts" {
                        if layouts_def.is_some() {
                            return Err(CensusError::new(
                                "duplicate `layouts` declaration in captured MIR module",
                            ));
                        }
                        self.expect_tok(&MirTok::Colon, "layouts type")?;
                        let ty_ident = self.expect_ident("layouts type")?;
                        if ctor_leaf(ty_ident, None)? != "LayoutTable" {
                            return Err(CensusError::new(format!(
                                "`layouts` must have type `LayoutTable`, found `{ty_ident}`"
                            )));
                        }
                        self.expect_tok(&MirTok::ColonEq, "layouts :=")?;
                        layouts_def = Some(self.parse_layout_table()?);
                    } else if decl_name == "body" {
                        if body_def.is_some() {
                            return Err(CensusError::new(
                                "duplicate `body` declaration in captured MIR module",
                            ));
                        }
                        self.expect_tok(&MirTok::Colon, "body type")?;
                        let ty_ident = self.expect_ident("body type")?;
                        if ctor_leaf(ty_ident, None)? != "CapturedMir" {
                            return Err(CensusError::new(format!(
                                "`body` must have type `CapturedMir`, found `{ty_ident}`"
                            )));
                        }
                        self.expect_tok(&MirTok::ColonEq, "body :=")?;
                        body_def = Some(self.parse_captured_mir(layouts_def.as_ref())?);
                    } else if decl_name == "defaultClaim" {
                        self.expect_tok(&MirTok::Colon, "defaultClaim type")?;
                        let _ = self.expect_ident("defaultClaim type")?;
                        self.expect_tok(&MirTok::ColonEq, "defaultClaim :=")?;
                        if !matches!(self.peek(), Some(MirTok::LBrace)) {
                            return Err(CensusError::new(
                                "`defaultClaim` must be an inline structure literal",
                            ));
                        }
                        self.skip_balanced_group()?;
                    } else {
                        return Err(CensusError::new(format!(
                            "unexpected declaration `def {decl_name}` in captured MIR module"
                        )));
                    }
                }
                other => {
                    return Err(CensusError::new(format!(
                        "unsupported top-level command `{other}` in captured MIR module"
                    )));
                }
            }
        }

        if let Some(unclosed) = namespace_stack.last() {
            return Err(CensusError::new(format!(
                "unclosed `namespace {unclosed}` at end of captured MIR module"
            )));
        }

        body_def.ok_or_else(|| {
            CensusError::new("captured MIR module is missing `def body : CapturedMir := ...`")
        })
    }

    fn skip_balanced_group(&mut self) -> Result<(), CensusError> {
        let open = self.next()?;
        let close = match open {
            MirTok::LParen => MirTok::RParen,
            MirTok::LBrace => MirTok::RBrace,
            MirTok::LBracket => MirTok::RBracket,
            other => {
                return Err(CensusError::new(format!(
                    "expected bracket group, found `{other:?}`"
                )));
            }
        };
        let mut stack = vec![close];
        while let Some(expected_close) = stack.last() {
            let tok = self.next()?;
            match tok {
                MirTok::LParen => stack.push(MirTok::RParen),
                MirTok::LBrace => stack.push(MirTok::RBrace),
                MirTok::LBracket => stack.push(MirTok::RBracket),
                t if t == expected_close => {
                    stack.pop();
                }
                MirTok::RParen | MirTok::RBrace | MirTok::RBracket => {
                    return Err(CensusError::new("mismatched closing bracket in MIR module"));
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn parse_struct_fields<F>(&mut self, ctx: &str, mut field_fn: F) -> Result<(), CensusError>
    where
        F: FnMut(&mut Self, &str) -> Result<(), CensusError>,
    {
        self.expect_tok(&MirTok::LBrace, ctx)?;
        let mut seen = BTreeSet::new();
        while !matches!(self.peek(), Some(MirTok::RBrace)) {
            let field_name = self.expect_ident(ctx)?;
            if field_name == "with" || matches!(self.peek(), Some(MirTok::Ident(w)) if w == "with")
            {
                return Err(CensusError::new(format!(
                    "structure-update `with` syntax is forbidden in {ctx} (fail-closed)"
                )));
            }
            if !seen.insert(field_name.to_string()) {
                return Err(CensusError::new(format!(
                    "duplicate structure field `{field_name}` in {ctx}"
                )));
            }
            self.expect_tok(&MirTok::ColonEq, ctx)?;
            field_fn(self, field_name)?;
            let _ = self.eat_comma();
        }
        self.expect_tok(&MirTok::RBrace, ctx)?;
        Ok(())
    }

    fn parse_size(&mut self) -> Result<IrSize, CensusError> {
        let mut bytes = None;
        self.parse_struct_fields("Size", |p, f| match f {
            "bytes" => {
                bytes = Some(p.expect_u64("Size.bytes")?);
                Ok(())
            }
            other => Err(CensusError::new(format!("unknown Size field `{other}`"))),
        })?;
        Ok(IrSize {
            bytes: bytes.ok_or_else(|| CensusError::new("Size is missing `bytes` field"))?,
        })
    }

    fn parse_align(&mut self) -> Result<IrAlign, CensusError> {
        let mut bytes = None;
        self.parse_struct_fields("Align", |p, f| match f {
            "bytes" => {
                bytes = Some(p.expect_u64("Align.bytes")?);
                Ok(())
            }
            other => Err(CensusError::new(format!("unknown Align field `{other}`"))),
        })?;
        Ok(IrAlign {
            bytes: bytes.ok_or_else(|| CensusError::new("Align is missing `bytes` field"))?,
        })
    }

    fn parse_wrapping_range(&mut self) -> Result<IrWrappingRange, CensusError> {
        let mut start = None;
        let mut end_ = None;
        self.parse_struct_fields("WrappingRange", |p, f| match f {
            "start" => {
                start = Some(p.expect_u128("WrappingRange.start")?);
                Ok(())
            }
            "end_" => {
                end_ = Some(p.expect_u128("WrappingRange.end_")?);
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown WrappingRange field `{other}`"
            ))),
        })?;
        Ok(IrWrappingRange {
            start: start
                .ok_or_else(|| CensusError::new("WrappingRange is missing `start` field"))?,
            end_: end_.ok_or_else(|| CensusError::new("WrappingRange is missing `end_` field"))?,
        })
    }

    fn parse_primitive_kind(&mut self) -> Result<IrPrimitiveKind, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("PrimitiveKind")?;
            match ctor_leaf(head, Some("PrimitiveKind"))? {
                "int" => {
                    let bits = p.expect_u64("PrimitiveKind.int bits")?;
                    let signed = p.parse_bool("PrimitiveKind.int signed")?;
                    Ok(IrPrimitiveKind::Int { bits, signed })
                }
                "float" => Ok(IrPrimitiveKind::Float {
                    bits: p.expect_u64("PrimitiveKind.float bits")?,
                }),
                "pointer" => Ok(IrPrimitiveKind::Pointer {
                    address_space: p.expect_u32("PrimitiveKind.pointer address_space")?,
                }),
                other => Err(CensusError::new(format!(
                    "unknown PrimitiveKind `{other}`"
                ))),
            }
        })
    }

    fn parse_scalar_layout(&mut self) -> Result<IrScalarLayout, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("ScalarLayout")?;
            match ctor_leaf(head, Some("ScalarLayout"))? {
                "initialized" => {
                    let value = p.parse_primitive_kind()?;
                    let valid_range = p.parse_wrapping_range()?;
                    Ok(IrScalarLayout::Initialized { value, valid_range })
                }
                "union" => Ok(IrScalarLayout::Union {
                    value: p.parse_primitive_kind()?,
                }),
                other => Err(CensusError::new(format!("unknown ScalarLayout `{other}`"))),
            }
        })
    }

    fn parse_fields_shape(&mut self) -> Result<IrFieldsShape, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("FieldsShape")?;
            match ctor_leaf(head, Some("FieldsShape"))? {
                "primitive" => Ok(IrFieldsShape::Primitive),
                "union" => Ok(IrFieldsShape::Union {
                    count: p.expect_usize("FieldsShape.union")?,
                }),
                "array" => {
                    let stride = p.parse_size()?;
                    let count = p.expect_u64("FieldsShape.array count")?;
                    Ok(IrFieldsShape::Array { stride, count })
                }
                "arbitrary" => {
                    let offsets = p.parse_list("FieldsShape.arbitrary offsets", Self::parse_size)?;
                    let memory_index = p.parse_list("FieldsShape.arbitrary memory_index", |q| {
                        q.expect_usize("memory_index")
                    })?;
                    Ok(IrFieldsShape::Arbitrary {
                        offsets,
                        memory_index,
                    })
                }
                other => Err(CensusError::new(format!("unknown FieldsShape `{other}`"))),
            }
        })
    }

    fn parse_variants_shape(&mut self) -> Result<IrVariantsShape, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("VariantsShape")?;
            match ctor_leaf(head, Some("VariantsShape"))? {
                "empty" => Ok(IrVariantsShape::Empty),
                "single" => Ok(IrVariantsShape::Single {
                    index: p.expect_usize("VariantsShape.single")?,
                }),
                "multiple" => {
                    let tag = p.parse_scalar_layout()?;
                    let tag_field = p.expect_usize("VariantsShape.multiple tag_field")?;
                    let variants = p.parse_list(
                        "VariantsShape.multiple variants",
                        Self::parse_fields_shape,
                    )?;
                    Ok(IrVariantsShape::Multiple {
                        tag,
                        tag_field,
                        variants,
                    })
                }
                other => Err(CensusError::new(format!(
                    "unknown VariantsShape `{other}`"
                ))),
            }
        })
    }

    fn parse_backend_repr(&mut self) -> Result<IrBackendRepr, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("BackendRepr")?;
            match ctor_leaf(head, Some("BackendRepr"))? {
                "scalar" => Ok(IrBackendRepr::Scalar(p.parse_scalar_layout()?)),
                "scalarPair" => {
                    let a = p.parse_scalar_layout()?;
                    let b = p.parse_scalar_layout()?;
                    Ok(IrBackendRepr::ScalarPair(a, b))
                }
                "memory" => Ok(IrBackendRepr::Memory),
                other => Err(CensusError::new(format!("unknown BackendRepr `{other}`"))),
            }
        })
    }

    fn parse_type_layout(&mut self) -> Result<IrTypeLayout, CensusError> {
        let mut size = IrSize { bytes: 0 };
        let mut align = IrAlign { bytes: 1 };
        let mut backend_repr = IrBackendRepr::Memory;
        let mut fields = IrFieldsShape::Primitive;
        let mut variants = IrVariantsShape::Single { index: 0 };
        let mut is_uninhabited = false;
        let mut field_layouts = Vec::new();

        self.parse_struct_fields("TypeLayout", |p, f| match f {
            "size" => {
                size = p.parse_size()?;
                Ok(())
            }
            "align" => {
                align = p.parse_align()?;
                Ok(())
            }
            "backendRepr" => {
                backend_repr = p.parse_backend_repr()?;
                Ok(())
            }
            "fields" => {
                fields = p.parse_fields_shape()?;
                Ok(())
            }
            "variants" => {
                variants = p.parse_variants_shape()?;
                Ok(())
            }
            "isUninhabited" => {
                is_uninhabited = p.parse_bool("TypeLayout.isUninhabited")?;
                Ok(())
            }
            "fieldLayouts" => {
                field_layouts =
                    p.parse_list("TypeLayout.fieldLayouts", |q| q.expect_usize("fieldLayout"))?;
                Ok(())
            }
            "variantDiscriminants" => {
                let _ = p.parse_list("TypeLayout.variantDiscriminants", |q| {
                    q.expect_u128("variantDiscriminant")
                })?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown TypeLayout field `{other}`"
            ))),
        })?;

        Ok(IrTypeLayout {
            size,
            align,
            backend_repr,
            fields,
            variants,
            is_uninhabited,
            field_layouts,
        })
    }

    fn parse_layout_table(&mut self) -> Result<IrLayoutTable, CensusError> {
        let mut pointer_bits = 64u64;
        let mut is_little_endian = true;
        let mut entries = Vec::new();
        self.parse_struct_fields("LayoutTable", |p, f| match f {
            "pointerBits" => {
                pointer_bits = p.expect_u64("LayoutTable.pointerBits")?;
                Ok(())
            }
            "isLittleEndian" => {
                is_little_endian = p.parse_bool("LayoutTable.isLittleEndian")?;
                Ok(())
            }
            "entries" => {
                entries = p.parse_list("LayoutTable.entries", Self::parse_type_layout)?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown LayoutTable field `{other}`"
            ))),
        })?;
        Ok(IrLayoutTable {
            pointer_bits,
            is_little_endian,
            entries,
        })
    }

    fn parse_abi_pass_mode(&mut self) -> Result<IrAbiPassMode, CensusError> {
        let id = self.expect_ident("AbiPassMode")?;
        match ctor_leaf(id, Some("AbiPassMode"))? {
            "ignore" => Ok(IrAbiPassMode::Ignore),
            "direct" => Ok(IrAbiPassMode::Direct),
            "pair" => Ok(IrAbiPassMode::Pair),
            "indirect" => Ok(IrAbiPassMode::Indirect),
            other => Err(CensusError::new(format!("unknown AbiPassMode `{other}`"))),
        }
    }

    fn parse_arg_abi(&mut self) -> Result<IrArgAbi, CensusError> {
        let mut layout = None;
        let mut mode = None;
        self.parse_struct_fields("ArgAbi", |p, f| match f {
            "layout" => {
                layout = Some(p.parse_type_layout()?);
                Ok(())
            }
            "mode" => {
                mode = Some(p.parse_abi_pass_mode()?);
                Ok(())
            }
            other => Err(CensusError::new(format!("unknown ArgAbi field `{other}`"))),
        })?;
        Ok(IrArgAbi {
            layout: layout.ok_or_else(|| CensusError::new("ArgAbi is missing `layout` field"))?,
            mode: mode.ok_or_else(|| CensusError::new("ArgAbi is missing `mode` field"))?,
        })
    }

    fn parse_call_conv(&mut self) -> Result<IrCallConv, CensusError> {
        self.parse_paren_or_bare(|p| {
            let id = p.expect_ident("CallConv")?;
            match ctor_leaf(id, Some("CallConv"))? {
                "rust" => Ok(IrCallConv::Rust),
                "c" => Ok(IrCallConv::C),
                "rustIntrinsic" => Ok(IrCallConv::RustIntrinsic),
                "other" => Ok(IrCallConv::Other(p.expect_str("CallConv.other")?)),
                other => Err(CensusError::new(format!("unknown CallConv `{other}`"))),
            }
        })
    }

    fn parse_fn_abi(&mut self) -> Result<IrFnAbi, CensusError> {
        let mut args = Vec::new();
        let mut ret = None;
        let mut conv = IrCallConv::Rust;
        let mut can_unwind = true;
        self.parse_struct_fields("FnAbi", |p, f| match f {
            "args" => {
                args = p.parse_list("FnAbi.args", Self::parse_arg_abi)?;
                Ok(())
            }
            "ret" => {
                ret = Some(p.parse_arg_abi()?);
                Ok(())
            }
            "conv" => {
                conv = p.parse_call_conv()?;
                Ok(())
            }
            "canUnwind" => {
                can_unwind = p.parse_bool("FnAbi.canUnwind")?;
                Ok(())
            }
            other => Err(CensusError::new(format!("unknown FnAbi field `{other}`"))),
        })?;
        Ok(IrFnAbi {
            args,
            ret: ret.ok_or_else(|| CensusError::new("FnAbi is missing `ret` field"))?,
            conv,
            can_unwind,
        })
    }

    fn parse_mutability(&mut self) -> Result<IrMutability, CensusError> {
        let id = self.expect_ident("Mutability")?;
        match ctor_leaf(id, Some("Mutability"))? {
            "not" => Ok(IrMutability::Not),
            "mut" => Ok(IrMutability::Mut),
            other => Err(CensusError::new(format!("unknown Mutability `{other}`"))),
        }
    }

    fn parse_safety(&mut self) -> Result<IrSafety, CensusError> {
        let id = self.expect_ident("Safety")?;
        match ctor_leaf(id, Some("Safety"))? {
            "safe" => Ok(IrSafety::Safe),
            "unsafe_" => Ok(IrSafety::Unsafe),
            other => Err(CensusError::new(format!("unknown Safety `{other}`"))),
        }
    }

    fn parse_uint_ty(&mut self) -> Result<IrUintTy, CensusError> {
        let id = self.expect_ident("UintTy")?;
        match ctor_leaf(id, Some("UintTy"))? {
            "u8" => Ok(IrUintTy::U8),
            "u16" => Ok(IrUintTy::U16),
            "u32" => Ok(IrUintTy::U32),
            "u64" => Ok(IrUintTy::U64),
            "u128" => Ok(IrUintTy::U128),
            "usize" => Ok(IrUintTy::Usize),
            other => Err(CensusError::new(format!("unknown UintTy `{other}`"))),
        }
    }

    fn parse_int_ty(&mut self) -> Result<IrIntTy, CensusError> {
        let id = self.expect_ident("IntTy")?;
        match ctor_leaf(id, Some("IntTy"))? {
            "i8" => Ok(IrIntTy::I8),
            "i16" => Ok(IrIntTy::I16),
            "i32" => Ok(IrIntTy::I32),
            "i64" => Ok(IrIntTy::I64),
            "i128" => Ok(IrIntTy::I128),
            "isize" => Ok(IrIntTy::Isize),
            other => Err(CensusError::new(format!("unknown IntTy `{other}`"))),
        }
    }

    fn parse_float_ty(&mut self) -> Result<IrFloatTy, CensusError> {
        let id = self.expect_ident("FloatTy")?;
        match ctor_leaf(id, Some("FloatTy"))? {
            "f16" => Ok(IrFloatTy::F16),
            "f32" => Ok(IrFloatTy::F32),
            "f64" => Ok(IrFloatTy::F64),
            "f128" => Ok(IrFloatTy::F128),
            other => Err(CensusError::new(format!("unknown FloatTy `{other}`"))),
        }
    }

    fn parse_rigid_ty(&mut self) -> Result<IrRigidTy, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("RigidTy")?;
            match ctor_leaf(head, Some("RigidTy"))? {
                "bool" => Ok(IrRigidTy::Bool),
                "char" => Ok(IrRigidTy::Char),
                "int" => Ok(IrRigidTy::Int(p.parse_int_ty()?)),
                "uint" => Ok(IrRigidTy::Uint(p.parse_uint_ty()?)),
                "float" => Ok(IrRigidTy::Float(p.parse_float_ty()?)),
                "never" => Ok(IrRigidTy::Never),
                "str" => Ok(IrRigidTy::Str),
                "tuple" => Ok(IrRigidTy::Tuple(
                    p.parse_list("RigidTy.tuple", Self::parse_rigid_ty)?,
                )),
                "array" => {
                    let elem = p.parse_rigid_ty()?;
                    let len = p.expect_u64("RigidTy.array len")?;
                    Ok(IrRigidTy::Array(Box::new(elem), len))
                }
                "slice" => Ok(IrRigidTy::Slice(Box::new(p.parse_rigid_ty()?))),
                "ref" => {
                    let m = p.parse_mutability()?;
                    let inner = p.parse_rigid_ty()?;
                    Ok(IrRigidTy::Ref(m, Box::new(inner)))
                }
                "rawPtr" => {
                    let m = p.parse_mutability()?;
                    let inner = p.parse_rigid_ty()?;
                    Ok(IrRigidTy::RawPtr(m, Box::new(inner)))
                }
                "adt" => {
                    let path = p.expect_str("RigidTy.adt")?;
                    let args = p.parse_list("RigidTy.adt args", Self::parse_rigid_ty)?;
                    Ok(IrRigidTy::Adt(path, args))
                }
                "fnDef" => {
                    let path = p.expect_str("RigidTy.fnDef")?;
                    let args = p.parse_list("RigidTy.fnDef args", Self::parse_rigid_ty)?;
                    Ok(IrRigidTy::FnDef(path, args))
                }
                "fnPtr" => {
                    let inputs = p.parse_list("RigidTy.fnPtr inputs", Self::parse_rigid_ty)?;
                    let output = p.parse_rigid_ty()?;
                    let safety = p.parse_safety()?;
                    let conv = p.parse_call_conv()?;
                    Ok(IrRigidTy::FnPtr(inputs, Box::new(output), safety, conv))
                }
                "closure" => {
                    let path = p.expect_str("RigidTy.closure")?;
                    let upvars = p.parse_list("RigidTy.closure upvars", Self::parse_rigid_ty)?;
                    Ok(IrRigidTy::Closure(path, upvars))
                }
                "dynamic" => Ok(IrRigidTy::Dynamic(p.expect_str("RigidTy.dynamic")?)),
                "foreign" => Ok(IrRigidTy::Foreign(p.expect_str("RigidTy.foreign")?)),
                "param" => {
                    let index = p.expect_u32("RigidTy.param index")?;
                    let name = p.expect_str("RigidTy.param name")?;
                    Ok(IrRigidTy::Param { index, name })
                }
                "alias" => {
                    let def_path = p.expect_str("RigidTy.alias")?;
                    let args = p.parse_list("RigidTy.alias args", Self::parse_rigid_ty)?;
                    Ok(IrRigidTy::Alias { def_path, args })
                }
                "other" => Ok(IrRigidTy::Other(p.expect_str("RigidTy.other")?)),
                other => Err(CensusError::new(format!("unknown RigidTy `{other}`"))),
            }
        })
    }

    fn parse_ty(&mut self) -> Result<IrTy, CensusError> {
        let mut kind = None;
        let mut layout_idx = 0usize;
        self.parse_struct_fields("Ty", |p, f| match f {
            "kind" => {
                kind = Some(p.parse_rigid_ty()?);
                Ok(())
            }
            "layoutIdx" => {
                layout_idx = p.expect_usize("Ty.layoutIdx")?;
                Ok(())
            }
            other => Err(CensusError::new(format!("unknown Ty field `{other}`"))),
        })?;
        Ok(IrTy {
            kind: kind.ok_or_else(|| CensusError::new("Ty is missing `kind` field"))?,
            layout_idx,
        })
    }

    fn parse_projection_elem(&mut self) -> Result<IrProjectionElem, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("ProjectionElem")?;
            match ctor_leaf(head, Some("ProjectionElem"))? {
                "deref" => Ok(IrProjectionElem::Deref),
                "field" => {
                    let idx = p.expect_usize("ProjectionElem.field")?;
                    let ty = p.parse_ty()?;
                    Ok(IrProjectionElem::Field(idx, ty))
                }
                "index" => Ok(IrProjectionElem::Index(
                    p.expect_usize("ProjectionElem.index")?,
                )),
                "constantIndex" => {
                    let offset = p.expect_u64("ProjectionElem.constantIndex offset")?;
                    let min_length = p.expect_u64("ProjectionElem.constantIndex min_length")?;
                    let from_end = p.parse_bool("ProjectionElem.constantIndex from_end")?;
                    Ok(IrProjectionElem::ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    })
                }
                "subslice" => {
                    let from_idx = p.expect_u64("ProjectionElem.subslice from_idx")?;
                    let to_idx = p.expect_u64("ProjectionElem.subslice to_idx")?;
                    let from_end = p.parse_bool("ProjectionElem.subslice from_end")?;
                    Ok(IrProjectionElem::Subslice {
                        from_idx,
                        to_idx,
                        from_end,
                    })
                }
                "downcast" => {
                    let sym = p.parse_option("ProjectionElem.downcast", |q| {
                        q.expect_str("downcast symbol")
                    })?;
                    let idx = p.expect_usize("ProjectionElem.downcast idx")?;
                    Ok(IrProjectionElem::Downcast(sym, idx))
                }
                "opaqueCast" => Ok(IrProjectionElem::OpaqueCast(p.parse_ty()?)),
                "unwrapUnsafeBinder" => Ok(IrProjectionElem::UnwrapUnsafeBinder(p.parse_ty()?)),
                other => Err(CensusError::new(format!(
                    "unknown ProjectionElem `{other}`"
                ))),
            }
        })
    }

    fn parse_place(&mut self) -> Result<IrPlace, CensusError> {
        let mut local_ = None;
        let mut projection = Vec::new();
        self.parse_struct_fields("Place", |p, f| match f {
            "local_" => {
                local_ = Some(p.expect_usize("Place.local_")?);
                Ok(())
            }
            "projection" => {
                projection = p.parse_list("Place.projection", Self::parse_projection_elem)?;
                Ok(())
            }
            other => Err(CensusError::new(format!("unknown Place field `{other}`"))),
        })?;
        let local_ = local_.ok_or_else(|| CensusError::new("Place is missing `local_` field"))?;
        Ok(IrPlace { local_, projection })
    }

    fn parse_scalar_int(&mut self) -> Result<IrScalarInt, CensusError> {
        let mut bits = None;
        let mut size_bytes = None;
        self.parse_struct_fields("ScalarInt", |p, f| match f {
            "bits" => {
                bits = Some(p.expect_u128("ScalarInt.bits")?);
                Ok(())
            }
            "sizeBytes" => {
                size_bytes = Some(p.expect_u64("ScalarInt.sizeBytes")?);
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown ScalarInt field `{other}`"
            ))),
        })?;
        Ok(IrScalarInt {
            bits: bits.ok_or_else(|| CensusError::new("ScalarInt is missing `bits` field"))?,
            size_bytes: size_bytes
                .ok_or_else(|| CensusError::new("ScalarInt is missing `sizeBytes` field"))?,
        })
    }

    fn parse_provenance_ptr(&mut self) -> Result<IrProvenancePtr, CensusError> {
        let mut alloc_id = None;
        let mut offset_bytes = None;
        self.parse_struct_fields("ProvenancePtr", |p, f| match f {
            "allocId" => {
                alloc_id = Some(p.expect_u64("ProvenancePtr.allocId")?);
                Ok(())
            }
            "offsetBytes" => {
                offset_bytes = Some(p.expect_u64("ProvenancePtr.offsetBytes")?);
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown ProvenancePtr field `{other}`"
            ))),
        })?;
        Ok(IrProvenancePtr {
            alloc_id: alloc_id
                .ok_or_else(|| CensusError::new("ProvenancePtr is missing `allocId` field"))?,
            offset_bytes: offset_bytes
                .ok_or_else(|| CensusError::new("ProvenancePtr is missing `offsetBytes` field"))?,
        })
    }

    fn parse_const_scalar(&mut self) -> Result<IrConstScalar, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("ConstScalar")?;
            match ctor_leaf(head, Some("ConstScalar"))? {
                "int" => Ok(IrConstScalar::Int(p.parse_scalar_int()?)),
                "ptr" => {
                    let ptr = p.parse_provenance_ptr()?;
                    let sz = p.expect_u64("ConstScalar.ptr size")?;
                    Ok(IrConstScalar::Ptr(ptr, sz))
                }
                other => Err(CensusError::new(format!("unknown ConstScalar `{other}`"))),
            }
        })
    }

    fn parse_const_value(&mut self) -> Result<IrConstValue, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("ConstValue")?;
            match ctor_leaf(head, Some("ConstValue"))? {
                "zeroSized" => Ok(IrConstValue::ZeroSized),
                "scalar" => Ok(IrConstValue::Scalar(p.parse_const_scalar()?)),
                "slice" => {
                    let data = p.parse_const_scalar()?;
                    let meta = p.expect_u64("ConstValue.slice meta")?;
                    Ok(IrConstValue::Slice { data, meta })
                }
                "indirect" => {
                    let alloc_id = p.expect_u64("ConstValue.indirect alloc_id")?;
                    let offset_bytes = p.expect_u64("ConstValue.indirect offset_bytes")?;
                    Ok(IrConstValue::Indirect {
                        alloc_id,
                        offset_bytes,
                    })
                }
                "unevaluated" => Ok(IrConstValue::Unevaluated(
                    p.expect_str("ConstValue.unevaluated")?,
                )),
                other => Err(CensusError::new(format!("unknown ConstValue `{other}`"))),
            }
        })
    }

    fn parse_const_operand(&mut self) -> Result<IrConstOperand, CensusError> {
        let mut ty = None;
        let mut val = None;
        self.parse_struct_fields("ConstOperand", |p, f| match f {
            "ty" => {
                ty = Some(p.parse_ty()?);
                Ok(())
            }
            "val" => {
                val = Some(p.parse_const_value()?);
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown ConstOperand field `{other}`"
            ))),
        })?;
        Ok(IrConstOperand {
            ty: ty.ok_or_else(|| CensusError::new("ConstOperand is missing `ty` field"))?,
            val: val.ok_or_else(|| CensusError::new("ConstOperand is missing `val` field"))?,
        })
    }

    fn parse_operand(&mut self) -> Result<IrOperand, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("Operand")?;
            match ctor_leaf(head, Some("Operand"))? {
                "copy" => Ok(IrOperand::Copy(p.parse_place()?)),
                "move" => Ok(IrOperand::Move(p.parse_place()?)),
                "constant" => Ok(IrOperand::Constant(p.parse_const_operand()?)),
                other => Err(CensusError::new(format!("unknown Operand `{other}`"))),
            }
        })
    }

    fn parse_bin_op(&mut self) -> Result<IrBinOp, CensusError> {
        let id = self.expect_ident("BinOp")?;
        match ctor_leaf(id, Some("BinOp"))? {
            "add" => Ok(IrBinOp::Add),
            "addUnchecked" => Ok(IrBinOp::AddUnchecked),
            "addWithOverflow" => Ok(IrBinOp::AddWithOverflow),
            "sub" => Ok(IrBinOp::Sub),
            "subUnchecked" => Ok(IrBinOp::SubUnchecked),
            "subWithOverflow" => Ok(IrBinOp::SubWithOverflow),
            "mul" => Ok(IrBinOp::Mul),
            "mulUnchecked" => Ok(IrBinOp::MulUnchecked),
            "mulWithOverflow" => Ok(IrBinOp::MulWithOverflow),
            "div" => Ok(IrBinOp::Div),
            "rem" => Ok(IrBinOp::Rem),
            "bitXor" => Ok(IrBinOp::BitXor),
            "bitAnd" => Ok(IrBinOp::BitAnd),
            "bitOr" => Ok(IrBinOp::BitOr),
            "shl" => Ok(IrBinOp::Shl),
            "shlUnchecked" => Ok(IrBinOp::ShlUnchecked),
            "shr" => Ok(IrBinOp::Shr),
            "shrUnchecked" => Ok(IrBinOp::ShrUnchecked),
            "eq" => Ok(IrBinOp::Eq),
            "lt" => Ok(IrBinOp::Lt),
            "le" => Ok(IrBinOp::Le),
            "ne" => Ok(IrBinOp::Ne),
            "ge" => Ok(IrBinOp::Ge),
            "gt" => Ok(IrBinOp::Gt),
            "cmp" => Ok(IrBinOp::Cmp),
            "offset" => Ok(IrBinOp::Offset),
            other => Err(CensusError::new(format!("unknown BinOp `{other}`"))),
        }
    }

    fn parse_un_op(&mut self) -> Result<IrUnOp, CensusError> {
        let id = self.expect_ident("UnOp")?;
        match ctor_leaf(id, Some("UnOp"))? {
            "not" => Ok(IrUnOp::Not),
            "neg" => Ok(IrUnOp::Neg),
            "ptrMetadata" => Ok(IrUnOp::PtrMetadata),
            other => Err(CensusError::new(format!("unknown UnOp `{other}`"))),
        }
    }

    fn parse_null_op(&mut self) -> Result<IrNullOp, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("NullOp")?;
            match ctor_leaf(head, Some("NullOp"))? {
                "sizeOf" => Ok(IrNullOp::SizeOf),
                "alignOf" => Ok(IrNullOp::AlignOf),
                "offsetOf" => {
                    let fields = p.parse_list("NullOp.offsetOf", |q| {
                        q.expect_tok(&MirTok::LParen, "offsetOf pair")?;
                        let v = q.expect_usize("offsetOf variant")?;
                        q.expect_tok(&MirTok::Comma, "offsetOf comma")?;
                        let f = q.expect_usize("offsetOf field")?;
                        q.expect_tok(&MirTok::RParen, "offsetOf pair")?;
                        Ok((v, f))
                    })?;
                    Ok(IrNullOp::OffsetOf(fields))
                }
                "ubChecks" => Ok(IrNullOp::UbChecks),
                "contractChecks" => Ok(IrNullOp::ContractChecks),
                other => Err(CensusError::new(format!("unknown NullOp `{other}`"))),
            }
        })
    }

    fn parse_borrow_kind(&mut self) -> Result<IrBorrowKind, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("BorrowKind")?;
            match ctor_leaf(head, Some("BorrowKind"))? {
                "shared" => Ok(IrBorrowKind::Shared),
                "mut" => Ok(IrBorrowKind::Mut {
                    allow_two_phase: p.parse_bool("BorrowKind.mut")?,
                }),
                other => Err(CensusError::new(format!("unknown BorrowKind `{other}`"))),
            }
        })
    }

    fn parse_cast_kind(&mut self) -> Result<IrCastKind, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("CastKind")?;
            match ctor_leaf(head, Some("CastKind"))? {
                "pointerExposeProvenance" => Ok(IrCastKind::PointerExposeProvenance),
                "pointerWithExposedProvenance" => Ok(IrCastKind::PointerWithExposedProvenance),
                "pointerCoercion" => Ok(IrCastKind::PointerCoercion(
                    p.expect_str("CastKind.pointerCoercion")?,
                )),
                "intToInt" => Ok(IrCastKind::IntToInt),
                "floatToInt" => Ok(IrCastKind::FloatToInt),
                "floatToFloat" => Ok(IrCastKind::FloatToFloat),
                "intToFloat" => Ok(IrCastKind::IntToFloat),
                "ptrToPtr" => Ok(IrCastKind::PtrToPtr),
                "fnPtrToPtr" => Ok(IrCastKind::FnPtrToPtr),
                "transmute" => Ok(IrCastKind::Transmute),
                "subtype" => Ok(IrCastKind::Subtype),
                other => Err(CensusError::new(format!("unknown CastKind `{other}`"))),
            }
        })
    }

    fn parse_aggregate_kind(&mut self) -> Result<IrAggregateKind, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("AggregateKind")?;
            match ctor_leaf(head, Some("AggregateKind"))? {
                "array" => Ok(IrAggregateKind::Array(p.parse_ty()?)),
                "tuple" => Ok(IrAggregateKind::Tuple),
                "adt" => {
                    let path = p.expect_str("AggregateKind.adt")?;
                    let variant_idx = p.expect_usize("AggregateKind.adt variant")?;
                    let active_field =
                        p.parse_option("AggregateKind.adt active_field", |q| {
                            q.expect_usize("active_field")
                        })?;
                    Ok(IrAggregateKind::Adt(path, variant_idx, active_field))
                }
                "closure" => Ok(IrAggregateKind::Closure(
                    p.expect_str("AggregateKind.closure")?,
                )),
                "coroutine" => Ok(IrAggregateKind::Coroutine(
                    p.expect_str("AggregateKind.coroutine")?,
                )),
                "rawPtr" => {
                    let ty = p.parse_ty()?;
                    let m = p.parse_mutability()?;
                    Ok(IrAggregateKind::RawPtr(ty, m))
                }
                other => Err(CensusError::new(format!(
                    "unknown AggregateKind `{other}`"
                ))),
            }
        })
    }

    fn parse_rvalue(&mut self) -> Result<IrRvalue, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("Rvalue")?;
            match ctor_leaf(head, Some("Rvalue"))? {
                "use" => Ok(IrRvalue::Use(p.parse_operand()?)),
                "repeat" => {
                    let op = p.parse_operand()?;
                    let count = p.expect_u64("Rvalue.repeat count")?;
                    Ok(IrRvalue::Repeat(op, count))
                }
                "ref" => {
                    let bk = p.parse_borrow_kind()?;
                    let place = p.parse_place()?;
                    Ok(IrRvalue::Ref(bk, place))
                }
                "threadLocalRef" => Ok(IrRvalue::ThreadLocalRef(
                    p.expect_str("Rvalue.threadLocalRef")?,
                )),
                "rawPtr" => {
                    let m = p.parse_mutability()?;
                    let place = p.parse_place()?;
                    Ok(IrRvalue::RawPtr(m, place))
                }
                "len" => Ok(IrRvalue::Len(p.parse_place()?)),
                "cast" => {
                    let ck = p.parse_cast_kind()?;
                    let op = p.parse_operand()?;
                    let ty = p.parse_ty()?;
                    Ok(IrRvalue::Cast(ck, op, ty))
                }
                "binaryOp" => {
                    let op = p.parse_bin_op()?;
                    let lhs = p.parse_operand()?;
                    let rhs = p.parse_operand()?;
                    Ok(IrRvalue::BinaryOp(op, lhs, rhs))
                }
                "nullaryOp" => {
                    let op = p.parse_null_op()?;
                    let ty = p.parse_ty()?;
                    Ok(IrRvalue::NullaryOp(op, ty))
                }
                "unaryOp" => {
                    let op = p.parse_un_op()?;
                    let arg = p.parse_operand()?;
                    Ok(IrRvalue::UnaryOp(op, arg))
                }
                "discriminant" => Ok(IrRvalue::Discriminant(p.parse_place()?)),
                "aggregate" => {
                    let ak = p.parse_aggregate_kind()?;
                    let ops = p.parse_list("Rvalue.aggregate", Self::parse_operand)?;
                    Ok(IrRvalue::Aggregate(ak, ops))
                }
                "shallowInitBox" => {
                    let op = p.parse_operand()?;
                    let ty = p.parse_ty()?;
                    Ok(IrRvalue::ShallowInitBox(op, ty))
                }
                "copyForDeref" => Ok(IrRvalue::CopyForDeref(p.parse_place()?)),
                "wrapUnsafeBinder" => {
                    let op = p.parse_operand()?;
                    let ty = p.parse_ty()?;
                    Ok(IrRvalue::WrapUnsafeBinder(op, ty))
                }
                other => Err(CensusError::new(format!("unknown Rvalue `{other}`"))),
            }
        })
    }

    fn parse_non_diverging_intrinsic(&mut self) -> Result<IrNonDivergingIntrinsic, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("NonDivergingIntrinsic")?;
            match ctor_leaf(head, Some("NonDivergingIntrinsic"))? {
                "assume" => Ok(IrNonDivergingIntrinsic::Assume(p.parse_operand()?)),
                "copyNonOverlapping" => {
                    let src = p.parse_operand()?;
                    let dst = p.parse_operand()?;
                    let count = p.parse_operand()?;
                    Ok(IrNonDivergingIntrinsic::CopyNonOverlapping { src, dst, count })
                }
                other => Err(CensusError::new(format!(
                    "unknown NonDivergingIntrinsic `{other}`"
                ))),
            }
        })
    }

    fn parse_retag_kind(&mut self) -> Result<IrRetagKind, CensusError> {
        let id = self.expect_ident("RetagKind")?;
        match ctor_leaf(id, Some("RetagKind"))? {
            "fnEntry" => Ok(IrRetagKind::FnEntry),
            "twoPhase" => Ok(IrRetagKind::TwoPhase),
            "raw" => Ok(IrRetagKind::Raw),
            "default" => Ok(IrRetagKind::Default),
            other => Err(CensusError::new(format!("unknown RetagKind `{other}`"))),
        }
    }

    fn parse_statement_kind(&mut self) -> Result<IrStatementKind, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("StatementKind")?;
            match ctor_leaf(head, Some("StatementKind"))? {
                "assign" => {
                    let dst = p.parse_place()?;
                    let rv = p.parse_rvalue()?;
                    Ok(IrStatementKind::Assign(dst, rv))
                }
                "setDiscriminant" => {
                    let dst = p.parse_place()?;
                    let idx = p.expect_usize("StatementKind.setDiscriminant")?;
                    Ok(IrStatementKind::SetDiscriminant(dst, idx))
                }
                "deinit" => Ok(IrStatementKind::Deinit(p.parse_place()?)),
                "storageLive" => Ok(IrStatementKind::StorageLive(
                    p.expect_usize("StatementKind.storageLive")?,
                )),
                "storageDead" => Ok(IrStatementKind::StorageDead(
                    p.expect_usize("StatementKind.storageDead")?,
                )),
                "retag" => {
                    let rk = p.parse_retag_kind()?;
                    let place = p.parse_place()?;
                    Ok(IrStatementKind::Retag(rk, place))
                }
                "placeMention" => Ok(IrStatementKind::PlaceMention(p.parse_place()?)),
                "intrinsic" => Ok(IrStatementKind::Intrinsic(
                    p.parse_non_diverging_intrinsic()?,
                )),
                "coverage" => Ok(IrStatementKind::Coverage),
                "constEvalCounter" => Ok(IrStatementKind::ConstEvalCounter),
                "backwardIncompatibleDropHint" => Ok(
                    IrStatementKind::BackwardIncompatibleDropHint(p.parse_place()?),
                ),
                "nop" => Ok(IrStatementKind::Nop),
                other => Err(CensusError::new(format!(
                    "unknown StatementKind `{other}`"
                ))),
            }
        })
    }

    fn parse_statement(&mut self) -> Result<IrStatement, CensusError> {
        let mut kind = None;
        let mut span = String::new();
        self.parse_struct_fields("Statement", |p, f| match f {
            "kind" => {
                kind = Some(p.parse_statement_kind()?);
                Ok(())
            }
            "span" => {
                span = p.expect_str("Statement.span")?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown Statement field `{other}`"
            ))),
        })?;
        let kind = kind.ok_or_else(|| CensusError::new("Statement is missing `kind` field"))?;
        Ok(IrStatement {
            kind,
            span,
            comment: None,
        })
    }

    fn parse_switch_targets(&mut self) -> Result<IrSwitchTargets, CensusError> {
        let mut branches = Vec::new();
        let mut otherwise = None;
        self.parse_struct_fields("SwitchTargets", |p, f| match f {
            "branches" => {
                branches = p.parse_list("SwitchTargets.branches", |q| {
                    q.expect_tok(&MirTok::LParen, "SwitchTargets branch")?;
                    let val = q.expect_u128("SwitchTargets branch value")?;
                    q.expect_tok(&MirTok::Comma, "SwitchTargets branch comma")?;
                    let bb = q.expect_usize("SwitchTargets branch target")?;
                    q.expect_tok(&MirTok::RParen, "SwitchTargets branch")?;
                    Ok((val, bb))
                })?;
                Ok(())
            }
            "otherwise" => {
                otherwise = Some(p.expect_usize("SwitchTargets.otherwise")?);
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown SwitchTargets field `{other}`"
            ))),
        })?;
        let otherwise = otherwise
            .ok_or_else(|| CensusError::new("SwitchTargets is missing `otherwise` field"))?;
        Ok(IrSwitchTargets {
            branches,
            otherwise,
        })
    }

    fn parse_unwind_action(&mut self) -> Result<IrUnwindAction, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("UnwindAction")?;
            match ctor_leaf(head, Some("UnwindAction"))? {
                "cleanup" => Ok(IrUnwindAction::Cleanup(
                    p.expect_usize("UnwindAction.cleanup")?,
                )),
                "unreachable" => Ok(IrUnwindAction::Unreachable),
                "terminate" => Ok(IrUnwindAction::Terminate),
                "continue_" => Ok(IrUnwindAction::Continue),
                other => Err(CensusError::new(format!(
                    "unknown UnwindAction `{other}`"
                ))),
            }
        })
    }

    fn parse_terminator_kind(&mut self) -> Result<IrTerminatorKind, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("TerminatorKind")?;
            match ctor_leaf(head, Some("TerminatorKind"))? {
                "goto" => Ok(IrTerminatorKind::Goto(p.expect_usize("TerminatorKind.goto")?)),
                "switchInt" => {
                    let discr = p.parse_operand()?;
                    let targets = p.parse_switch_targets()?;
                    Ok(IrTerminatorKind::SwitchInt(discr, targets))
                }
                "unwindResume" => Ok(IrTerminatorKind::UnwindResume),
                "unwindTerminate" => Ok(IrTerminatorKind::UnwindTerminate),
                "return_" => Ok(IrTerminatorKind::Return),
                "unreachable" => Ok(IrTerminatorKind::Unreachable),
                "drop" => {
                    let place = p.parse_place()?;
                    let target = p.expect_usize("TerminatorKind.drop target")?;
                    let unwind = p.parse_unwind_action()?;
                    Ok(IrTerminatorKind::Drop {
                        place,
                        target,
                        unwind,
                    })
                }
                "call" => {
                    let func = p.parse_operand()?;
                    let args = p.parse_list("TerminatorKind.call args", Self::parse_operand)?;
                    let destination = p.parse_place()?;
                    let target = p.parse_option("TerminatorKind.call target", |q| {
                        q.expect_usize("call target")
                    })?;
                    let unwind = p.parse_unwind_action()?;
                    Ok(IrTerminatorKind::Call {
                        func,
                        args,
                        destination,
                        target,
                        unwind,
                    })
                }
                "tailCall" => {
                    let func = p.parse_operand()?;
                    let args =
                        p.parse_list("TerminatorKind.tailCall args", Self::parse_operand)?;
                    Ok(IrTerminatorKind::TailCall { func, args })
                }
                "assert" => {
                    let cond = p.parse_operand()?;
                    let expected = p.parse_bool("TerminatorKind.assert expected")?;
                    let target = p.expect_usize("TerminatorKind.assert target")?;
                    let unwind = p.parse_unwind_action()?;
                    Ok(IrTerminatorKind::Assert {
                        cond,
                        expected,
                        target,
                        unwind,
                    })
                }
                "inlineAsm" => {
                    let template = p.expect_str("TerminatorKind.inlineAsm template")?;
                    let targets = p.parse_list("TerminatorKind.inlineAsm targets", |q| {
                        q.expect_usize("inlineAsm target")
                    })?;
                    let unwind = p.parse_unwind_action()?;
                    Ok(IrTerminatorKind::InlineAsm {
                        template,
                        targets,
                        unwind,
                    })
                }
                other => Err(CensusError::new(format!(
                    "unknown TerminatorKind `{other}`"
                ))),
            }
        })
    }

    fn parse_terminator(&mut self) -> Result<IrTerminator, CensusError> {
        let mut kind = None;
        let mut span = String::new();
        self.parse_struct_fields("Terminator", |p, f| match f {
            "kind" => {
                kind = Some(p.parse_terminator_kind()?);
                Ok(())
            }
            "span" => {
                span = p.expect_str("Terminator.span")?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown Terminator field `{other}`"
            ))),
        })?;
        let kind = kind.ok_or_else(|| CensusError::new("Terminator is missing `kind` field"))?;
        Ok(IrTerminator {
            kind,
            span,
            comment: None,
        })
    }

    fn parse_basic_block_data(&mut self) -> Result<IrBasicBlockData, CensusError> {
        let mut statements = Vec::new();
        let mut terminator = None;
        let mut is_cleanup = false;
        self.parse_struct_fields("BasicBlockData", |p, f| match f {
            "statements" => {
                statements = p.parse_list("BasicBlockData.statements", Self::parse_statement)?;
                Ok(())
            }
            "terminator" => {
                terminator = Some(p.parse_terminator()?);
                Ok(())
            }
            "isCleanup" => {
                is_cleanup = p.parse_bool("BasicBlockData.isCleanup")?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown BasicBlockData field `{other}`"
            ))),
        })?;
        let terminator = terminator
            .ok_or_else(|| CensusError::new("BasicBlockData is missing `terminator` field"))?;
        Ok(IrBasicBlockData {
            statements,
            terminator,
            is_cleanup,
        })
    }

    fn parse_local_decl(&mut self) -> Result<IrLocalDecl, CensusError> {
        let mut mutability = IrMutability::Not;
        let mut ty = None;
        let mut debug_name = None;
        self.parse_struct_fields("LocalDecl", |p, f| match f {
            "mutability" => {
                mutability = p.parse_mutability()?;
                Ok(())
            }
            "ty" => {
                ty = Some(p.parse_ty()?);
                Ok(())
            }
            "debugName" => {
                debug_name =
                    p.parse_option("LocalDecl.debugName", |q| q.expect_str("debugName"))?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown LocalDecl field `{other}`"
            ))),
        })?;
        Ok(IrLocalDecl {
            mutability,
            ty: ty.ok_or_else(|| CensusError::new("LocalDecl is missing `ty` field"))?,
            debug_name,
        })
    }

    fn parse_mir_phase_tag(&mut self) -> Result<IrMirPhaseTag, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("MirPhaseTag")?;
            match ctor_leaf(head, Some("MirPhaseTag"))? {
                "runtimePostCleanup" => Ok(IrMirPhaseTag::RuntimePostCleanup),
                "runtimeOptimized" => Ok(IrMirPhaseTag::RuntimeOptimized),
                "other" => Ok(IrMirPhaseTag::Other(p.expect_str("MirPhaseTag.other")?)),
                other => Err(CensusError::new(format!("unknown MirPhaseTag `{other}`"))),
            }
        })
    }

    fn parse_contract_role(&mut self) -> Result<IrContractRole, CensusError> {
        self.parse_paren_or_bare(|p| {
            let head = p.expect_ident("ContractRole")?;
            match ctor_leaf(head, Some("ContractRole"))? {
                "subject" => Ok(IrContractRole::Subject),
                "requires" => Ok(IrContractRole::Requires(
                    p.expect_str("ContractRole.requires")?,
                )),
                "ensures" => Ok(IrContractRole::Ensures(
                    p.expect_str("ContractRole.ensures")?,
                )),
                "externalSpec" => Ok(IrContractRole::ExternalSpec(
                    p.expect_str("ContractRole.externalSpec")?,
                )),
                "model" => Ok(IrContractRole::Model),
                other => Err(CensusError::new(format!("unknown ContractRole `{other}`"))),
            }
        })
    }

    fn parse_captured_allocation(&mut self) -> Result<IrCapturedAllocation, CensusError> {
        let mut alloc_id = None;
        let mut bytes = Vec::new();
        let mut relocations = Vec::new();
        let mut align = IrAlign { bytes: 1 };
        let mut mutability = IrMutability::Not;
        self.parse_struct_fields("CapturedAllocation", |p, f| match f {
            "allocId" => {
                alloc_id = Some(p.expect_u64("CapturedAllocation.allocId")?);
                Ok(())
            }
            "bytes" => {
                bytes = p.parse_list("CapturedAllocation.bytes", |q| {
                    q.parse_option("CapturedAllocation byte", |r| r.parse_uint8_byte())
                })?;
                Ok(())
            }
            "relocations" => {
                relocations = p.parse_list("CapturedAllocation.relocations", |q| {
                    q.expect_tok(&MirTok::LParen, "relocation pair")?;
                    let off = q.expect_u64("relocation offset")?;
                    q.expect_tok(&MirTok::Comma, "relocation comma")?;
                    let ptr = q.parse_provenance_ptr()?;
                    q.expect_tok(&MirTok::RParen, "relocation pair")?;
                    Ok((off, ptr))
                })?;
                Ok(())
            }
            "align" => {
                align = p.parse_align()?;
                Ok(())
            }
            "mutability" => {
                mutability = p.parse_mutability()?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown CapturedAllocation field `{other}`"
            ))),
        })?;
        Ok(IrCapturedAllocation {
            alloc_id: alloc_id
                .ok_or_else(|| CensusError::new("CapturedAllocation is missing `allocId`"))?,
            bytes,
            relocations,
            align,
            mutability,
        })
    }

    fn parse_uint8_byte(&mut self) -> Result<u8, CensusError> {
        self.parse_paren_or_bare(|p| {
            if let Some(MirTok::Nat(_)) = p.peek() {
                let v = p.expect_u128("UInt8 byte")?;
                return u8::try_from(v)
                    .map_err(|_| CensusError::new(format!("byte value `{v}` out of u8 range")));
            }
            let head = p.expect_ident("UInt8.ofNat")?;
            if ctor_leaf(head, Some("UInt8"))? != "ofNat" {
                return Err(CensusError::new(format!(
                    "expected `UInt8.ofNat` in allocation byte, found `{head}`"
                )));
            }
            let v = p.expect_u128("UInt8.ofNat")?;
            u8::try_from(v)
                .map_err(|_| CensusError::new(format!("byte value `{v}` out of u8 range")))
        })
    }

    fn parse_generic_param_def(&mut self) -> Result<IrGenericParamDef, CensusError> {
        let mut index = None;
        let mut name = None;
        self.parse_struct_fields("GenericParamDef", |p, f| match f {
            "idx" => {
                index = Some(p.expect_u32("GenericParamDef.idx")?);
                Ok(())
            }
            "name" => {
                name = Some(p.expect_str("GenericParamDef.name")?);
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown GenericParamDef field `{other}`"
            ))),
        })?;
        Ok(IrGenericParamDef {
            index: index.ok_or_else(|| CensusError::new("GenericParamDef missing `idx`"))?,
            name: name.ok_or_else(|| CensusError::new("GenericParamDef missing `name`"))?,
        })
    }

    fn parse_trait_ref(&mut self) -> Result<IrTraitRef, CensusError> {
        let mut def_path = None;
        let mut args = Vec::new();
        self.parse_struct_fields("TraitRef", |p, f| match f {
            "defPath" => {
                def_path = Some(p.expect_str("TraitRef.defPath")?);
                Ok(())
            }
            "args" => {
                args = p.parse_list("TraitRef.args", Self::parse_rigid_ty)?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown TraitRef field `{other}`"
            ))),
        })?;
        Ok(IrTraitRef {
            def_path: def_path.ok_or_else(|| CensusError::new("TraitRef missing `defPath`"))?,
            args,
        })
    }

    fn parse_trait_impl_entry(&mut self) -> Result<IrTraitImplEntry, CensusError> {
        let mut trait_ref = None;
        let mut impl_path = None;
        self.parse_struct_fields("TraitImplEntry", |p, f| match f {
            "traitRef" => {
                trait_ref = Some(p.parse_trait_ref()?);
                Ok(())
            }
            "implPath" => {
                impl_path = Some(p.expect_str("TraitImplEntry.implPath")?);
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown TraitImplEntry field `{other}`"
            ))),
        })?;
        Ok(IrTraitImplEntry {
            trait_ref: trait_ref
                .ok_or_else(|| CensusError::new("TraitImplEntry missing `traitRef`"))?,
            impl_path: impl_path
                .ok_or_else(|| CensusError::new("TraitImplEntry missing `implPath`"))?,
        })
    }

    fn parse_captured_mir(
        &mut self,
        module_layouts: Option<&IrLayoutTable>,
    ) -> Result<IrCapturedMir, CensusError> {
        let mut def_path = None;
        let mut phase = IrMirPhaseTag::RuntimePostCleanup;
        let mut role = IrContractRole::Subject;
        let mut type_param_count = 0usize;
        let mut generic_params = Vec::new();
        let mut trait_impls = Vec::new();
        let mut arg_count = 0usize;
        let mut local_decls = Vec::new();
        let mut basic_blocks = None;
        let mut fn_abi = IrFnAbi {
            args: Vec::new(),
            ret: IrArgAbi {
                layout: IrTypeLayout {
                    size: IrSize { bytes: 0 },
                    align: IrAlign { bytes: 1 },
                    backend_repr: IrBackendRepr::Memory,
                    fields: IrFieldsShape::Primitive,
                    variants: IrVariantsShape::Single { index: 0 },
                    is_uninhabited: false,
                    field_layouts: Vec::new(),
                },
                mode: IrAbiPassMode::Ignore,
            },
            conv: IrCallConv::Rust,
            can_unwind: true,
        };
        let mut layouts = module_layouts.cloned().unwrap_or(IrLayoutTable {
            pointer_bits: 64,
            is_little_endian: true,
            entries: Vec::new(),
        });
        let mut allocations = Vec::new();

        self.parse_struct_fields("CapturedMir", |p, f| match f {
            "defPath" => {
                def_path = Some(p.expect_str("CapturedMir.defPath")?);
                Ok(())
            }
            "phase" => {
                phase = p.parse_mir_phase_tag()?;
                Ok(())
            }
            "role" => {
                role = p.parse_contract_role()?;
                Ok(())
            }
            "typeParamCount" => {
                type_param_count = p.expect_usize("CapturedMir.typeParamCount")?;
                Ok(())
            }
            "genericParams" => {
                generic_params =
                    p.parse_list("CapturedMir.genericParams", Self::parse_generic_param_def)?;
                Ok(())
            }
            "traitImpls" => {
                trait_impls =
                    p.parse_list("CapturedMir.traitImpls", Self::parse_trait_impl_entry)?;
                Ok(())
            }
            "argCount" => {
                arg_count = p.expect_usize("CapturedMir.argCount")?;
                Ok(())
            }
            "localDecls" => {
                local_decls = p.parse_list("CapturedMir.localDecls", Self::parse_local_decl)?;
                Ok(())
            }
            "basicBlocks" => {
                basic_blocks =
                    Some(p.parse_list("CapturedMir.basicBlocks", Self::parse_basic_block_data)?);
                Ok(())
            }
            "fnAbi" => {
                fn_abi = p.parse_fn_abi()?;
                Ok(())
            }
            "layouts" => {
                if matches!(p.peek(), Some(MirTok::LBrace)) {
                    layouts = p.parse_layout_table()?;
                } else {
                    let id = p.expect_ident("CapturedMir.layouts")?;
                    if id == "layouts" {
                        layouts = module_layouts.cloned().ok_or_else(|| {
                            CensusError::new(
                                "CapturedMir references `layouts`, but no preceding `def layouts : LayoutTable` exists",
                            )
                        })?;
                    } else {
                        return Err(CensusError::new(format!(
                            "non-inline layouts reference `{id}` in CapturedMir"
                        )));
                    }
                }
                Ok(())
            }
            "allocations" => {
                allocations = p.parse_list(
                    "CapturedMir.allocations",
                    Self::parse_captured_allocation,
                )?;
                Ok(())
            }
            other => Err(CensusError::new(format!(
                "unknown CapturedMir field `{other}`"
            ))),
        })?;

        let def_path = def_path
            .ok_or_else(|| CensusError::new("CapturedMir is missing `defPath` field"))?;
        let basic_blocks = basic_blocks
            .ok_or_else(|| CensusError::new("CapturedMir is missing inline `basicBlocks` field"))?;

        Ok(IrCapturedMir {
            def_path,
            phase,
            role,
            type_param_count,
            generic_params,
            trait_impls,
            arg_count,
            local_decls,
            basic_blocks,
            fn_abi,
            layouts,
            allocations,
        })
    }
}

fn is_top_level_mir_module_kw(word: &str) -> bool {
    matches!(
        word,
        "prelude"
            | "import"
            | "namespace"
            | "end"
            | "open"
            | "set_option"
            | "def"
            | "abbrev"
            | "theorem"
            | "lemma"
            | "instance"
            | "axiom"
            | "opaque"
            | "structure"
            | "inductive"
            | "class"
    )
}

fn ctor_leaf<'a>(raw: &'a str, expected_ty: Option<&str>) -> Result<&'a str, CensusError> {
    if let Some(stripped) = raw.strip_prefix('.') {
        if stripped.is_empty() || stripped.contains('.') {
            return Err(CensusError::new(format!(
                "malformed dot-shorthand constructor `{raw}`"
            )));
        }
        return Ok(stripped);
    }
    let parts: Vec<&str> = raw.split('.').collect();
    let Some(&leaf) = parts.last() else {
        return Err(CensusError::new("empty constructor identifier"));
    };
    if parts.len() == 1 {
        return Ok(leaf);
    }
    let prefix = &parts[..parts.len() - 1];
    if let Some(exp_ty) = expected_ty {
        let valid = match prefix {
            [ty] => *ty == exp_ty,
            ["Trusted", "MirAst", ty] | ["Trusted", "Layout", ty] => *ty == exp_ty,
            ["Trusted", "Rustc", dialect, "MirAst", ty]
            | ["Trusted", "Rustc", dialect, "Layout", ty] => {
                dialect.starts_with("V202") && *ty == exp_ty
            }
            _ => false,
        };
        if !valid {
            return Err(CensusError::new(format!(
                "invalid constructor qualifier `{raw}` (expected `{exp_ty}`)"
            )));
        }
    }
    Ok(leaf)
}

// ============================================================================
// 7. Canonical False-Proof Mutation Probes (Genuine Mutated Explorer Passes)
// ============================================================================

/// The 4 canonical false-proof negative mutation probes ensuring omitted
/// obligation checks are caught fail-closed by [`FaultSiteCoverageReconciler`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FalseProofMutationProbe {
    /// Probe 1 (`CallArgBlindProbe`): `TerminatorKind::Call` passing a
    /// dereferenced pointer argument (`copy (*_1)`); the mutated obligation
    /// explorer checks the call contract while omitting pointer-dereference
    /// evaluation on `Call` arguments.
    CallArgBlindProbe,
    /// Probe 2 (`SwitchBreakStripProbe`): `TerminatorKind::SwitchInt` branching
    /// to `bb1` on `0` and `otherwise -> bb2` (where `bb2` executes integer
    /// division `BinOp::Div`); the mutated obligation explorer drops
    /// `SwitchInt.otherwise` from CFG exploration and never visits `bb2`.
    SwitchBreakStripProbe,
    /// Probe 3 (`LoopUpdateOverflowProbe`): CFG loop `bb0 -> bb1 (SwitchInt) ->
    /// bb2 (latch: _1 = AddUnchecked(_1, 1); goto bb1)` with exit `bb3: return`;
    /// the mutated obligation explorer omits arithmetic overflow obligations on
    /// loop-latch statements.
    LoopUpdateOverflowProbe,
    /// Probe 4 (`DerefAliasProbe`): Dereference read/write `*_1 = copy (*_2)`
    /// at `(bb0, stmt[0])`; the mutated obligation explorer treats dereference
    /// projections as plain local copies and omits `PointerDereference`.
    DerefAliasProbe,
}

impl FalseProofMutationProbe {
    /// All 4 canonical false-proof mutation probes in deterministic order.
    pub const ALL: [FalseProofMutationProbe; 4] = [
        Self::CallArgBlindProbe,
        Self::SwitchBreakStripProbe,
        Self::LoopUpdateOverflowProbe,
        Self::DerefAliasProbe,
    ];

    /// Canonical identifier of the probe.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CallArgBlindProbe => "CallArgBlindProbe",
            Self::SwitchBreakStripProbe => "SwitchBreakStripProbe",
            Self::LoopUpdateOverflowProbe => "LoopUpdateOverflowProbe",
            Self::DerefAliasProbe => "DerefAliasProbe",
        }
    }
}

impl fmt::Display for FalseProofMutationProbe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Complete scenario and verification outcome for a [`FalseProofMutationProbe`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MutationProbeScenario {
    /// Probe kind.
    pub probe: FalseProofMutationProbe,
    /// Canonical `IrCapturedMir` witness body for `probe`.
    pub mir: IrCapturedMir,
    /// Independent [`FaultSiteCensus`] of `mir`.
    pub census: FaultSiteCensus,
    /// Complete unmutated obligation coverage produced by
    /// [`explore_mir_obligations`] with `injected_mutation: None`.
    pub baseline_coverage: EmittedObligationCoverage,
    /// Defective obligation coverage produced organically by running
    /// [`explore_mir_obligations`] with `injected_mutation: Some(probe)` (no
    /// post-hoc set surgery).
    pub mutated_coverage: EmittedObligationCoverage,
    /// Exact [`FaultSite`]s that [`FaultSiteCoverageReconciler`] must report as
    /// uncovered on `mutated_coverage`.
    pub expected_uncovered_sites: BTreeSet<FaultSite>,
}

impl MutationProbeScenario {
    /// Build the canonical [`MutationProbeScenario`] for `probe` without
    /// panicking assertions.
    pub fn build(probe: FalseProofMutationProbe) -> Self {
        let mir = build_probe_mir_body(probe);
        let census = FaultSiteCensus::from_ir_captured_mir(&mir);
        let mut call_ctx = CallCoverageContext {
            enforce_callee_closure: true,
            ..CallCoverageContext::default()
        };
        if probe == FalseProofMutationProbe::CallArgBlindProbe {
            call_ctx
                .linked_callees
                .insert(String::from("probes::callee_u32"));
        }

        let base_opts = ObligationExplorerOptions {
            proves_total_termination: true,
            is_trusted_assumption: false,
            preserve_retags: false,
            call_context: call_ctx,
            recursive_callees: BTreeSet::new(),
            injected_mutation: None,
        };
        let baseline_coverage = explore_mir_obligations(&mir, &base_opts);

        let mut mut_opts = base_opts;
        mut_opts.injected_mutation = Some(probe);
        let mutated_coverage = explore_mir_obligations(&mir, &mut_opts);

        let expected_uncovered_sites = match probe {
            FalseProofMutationProbe::CallArgBlindProbe => BTreeSet::from([FaultSite::terminator(
                0,
                0,
                PropertyClass::PointerDereference,
            )]),
            FalseProofMutationProbe::SwitchBreakStripProbe => BTreeSet::from([
                FaultSite::statement(2, 0, PropertyClass::DivRemUb),
                FaultSite::statement(2, 0, PropertyClass::UninitRead),
                FaultSite::terminator(2, 1, PropertyClass::UninitRead),
            ]),
            FalseProofMutationProbe::LoopUpdateOverflowProbe => BTreeSet::from([
                FaultSite::statement(2, 0, PropertyClass::ArithmeticOverflow),
            ]),
            FalseProofMutationProbe::DerefAliasProbe => BTreeSet::from([FaultSite::statement(
                0,
                0,
                PropertyClass::PointerDereference,
            )]),
        };

        Self {
            probe,
            mir,
            census,
            baseline_coverage,
            mutated_coverage,
            expected_uncovered_sites,
        }
    }

    /// Execute both the positive baseline check and the negative mutated check
    /// against `reconciler`, returning `(baseline_report, mutant_report)`.
    pub fn execute(
        &self,
        reconciler: &FaultSiteCoverageReconciler,
    ) -> (CoverageReconciliationReport, CoverageReconciliationReport) {
        let baseline_report = reconciler.reconcile_with_call_context(
            &self.census,
            self.baseline_coverage.discharged_sites.iter().copied(),
            self.baseline_coverage.explicit_waivers.iter().cloned(),
            &self.baseline_coverage.call_context,
        );
        let mutant_report = reconciler.reconcile_with_call_context(
            &self.census,
            self.mutated_coverage.discharged_sites.iter().copied(),
            self.mutated_coverage.explicit_waivers.iter().cloned(),
            &self.mutated_coverage.call_context,
        );
        (baseline_report, mutant_report)
    }
}

fn scalar_u32_layout() -> IrTypeLayout {
    IrTypeLayout {
        size: IrSize { bytes: 4 },
        align: IrAlign { bytes: 4 },
        backend_repr: IrBackendRepr::Scalar(IrScalarLayout::Initialized {
            value: IrPrimitiveKind::Int {
                bits: 32,
                signed: false,
            },
            valid_range: IrWrappingRange {
                start: 0,
                end_: u32::MAX as u128,
            },
        }),
        fields: IrFieldsShape::Primitive,
        variants: IrVariantsShape::Single { index: 0 },
        is_uninhabited: false,
        field_layouts: Vec::new(),
    }
}

fn ptr_layout() -> IrTypeLayout {
    IrTypeLayout {
        size: IrSize { bytes: 8 },
        align: IrAlign { bytes: 8 },
        backend_repr: IrBackendRepr::Scalar(IrScalarLayout::Initialized {
            value: IrPrimitiveKind::Pointer { address_space: 0 },
            valid_range: IrWrappingRange {
                start: 1,
                end_: u64::MAX as u128,
            },
        }),
        fields: IrFieldsShape::Primitive,
        variants: IrVariantsShape::Single { index: 0 },
        is_uninhabited: false,
        field_layouts: vec![0],
    }
}

fn unit_layout() -> IrTypeLayout {
    IrTypeLayout {
        size: IrSize { bytes: 0 },
        align: IrAlign { bytes: 1 },
        backend_repr: IrBackendRepr::Memory,
        fields: IrFieldsShape::Arbitrary {
            offsets: Vec::new(),
            memory_index: Vec::new(),
        },
        variants: IrVariantsShape::Single { index: 0 },
        is_uninhabited: false,
        field_layouts: Vec::new(),
    }
}

fn const_u32_operand(bits: u128) -> IrOperand {
    IrOperand::Constant(IrConstOperand {
        ty: IrTy {
            kind: IrRigidTy::Uint(IrUintTy::U32),
            layout_idx: 0,
        },
        val: IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
            bits,
            size_bytes: 4,
        })),
    })
}

fn build_probe_mir_body(probe: FalseProofMutationProbe) -> IrCapturedMir {
    let u32_ty = IrTy {
        kind: IrRigidTy::Uint(IrUintTy::U32),
        layout_idx: 0,
    };
    let ref_u32_ty = IrTy {
        kind: IrRigidTy::Ref(IrMutability::Not, Box::new(IrRigidTy::Uint(IrUintTy::U32))),
        layout_idx: 1,
    };
    let mut_ref_u32_ty = IrTy {
        kind: IrRigidTy::Ref(IrMutability::Mut, Box::new(IrRigidTy::Uint(IrUintTy::U32))),
        layout_idx: 1,
    };
    let unit_ty = IrTy {
        kind: IrRigidTy::Tuple(Vec::new()),
        layout_idx: 2,
    };
    let layouts = IrLayoutTable {
        pointer_bits: 64,
        is_little_endian: true,
        entries: vec![scalar_u32_layout(), ptr_layout(), unit_layout()],
    };

    match probe {
        FalseProofMutationProbe::CallArgBlindProbe => IrCapturedMir {
            def_path: String::from("probes::call_arg_blind"),
            phase: IrMirPhaseTag::RuntimePostCleanup,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: Vec::new(),
            trait_impls: Vec::new(),
            arg_count: 1,
            local_decls: vec![
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: u32_ty.clone(),
                    debug_name: None,
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: ref_u32_ty.clone(),
                    debug_name: Some(String::from("ptr_arg")),
                },
            ],
            basic_blocks: vec![
                IrBasicBlockData {
                    statements: Vec::new(),
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Call {
                            func: IrOperand::Constant(IrConstOperand {
                                ty: IrTy {
                                    kind: IrRigidTy::FnDef(
                                        String::from("probes::callee_u32"),
                                        Vec::new(),
                                    ),
                                    layout_idx: 2,
                                },
                                val: IrConstValue::ZeroSized,
                            }),
                            args: vec![IrOperand::Copy(IrPlace {
                                local_: 1,
                                projection: vec![IrProjectionElem::Deref],
                            })],
                            destination: IrPlace {
                                local_: 0,
                                projection: Vec::new(),
                            },
                            target: Some(1),
                            unwind: IrUnwindAction::Continue,
                        },
                        span: String::from("probes.rs:10:5"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: Vec::new(),
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Return,
                        span: String::from("probes.rs:11:5"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
            ],
            fn_abi: IrFnAbi {
                args: vec![IrArgAbi {
                    layout: ptr_layout(),
                    mode: IrAbiPassMode::Direct,
                }],
                ret: IrArgAbi {
                    layout: scalar_u32_layout(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts,
            allocations: Vec::new(),
        },
        FalseProofMutationProbe::SwitchBreakStripProbe => IrCapturedMir {
            def_path: String::from("probes::switch_break_strip"),
            phase: IrMirPhaseTag::RuntimePostCleanup,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: Vec::new(),
            trait_impls: Vec::new(),
            arg_count: 2,
            local_decls: vec![
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: u32_ty.clone(),
                    debug_name: None,
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: u32_ty.clone(),
                    debug_name: Some(String::from("tag")),
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: u32_ty.clone(),
                    debug_name: Some(String::from("denom")),
                },
            ],
            basic_blocks: vec![
                IrBasicBlockData {
                    statements: Vec::new(),
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::SwitchInt(
                            IrOperand::Copy(IrPlace {
                                local_: 1,
                                projection: Vec::new(),
                            }),
                            IrSwitchTargets {
                                branches: vec![(0, 1)],
                                otherwise: 2,
                            },
                        ),
                        span: String::from("probes.rs:20:5"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: vec![IrStatement {
                        kind: IrStatementKind::Assign(
                            IrPlace {
                                local_: 0,
                                projection: Vec::new(),
                            },
                            IrRvalue::Use(const_u32_operand(42)),
                        ),
                        span: String::from("probes.rs:21:9"),
                        comment: None,
                    }],
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Return,
                        span: String::from("probes.rs:21:17"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: vec![IrStatement {
                        kind: IrStatementKind::Assign(
                            IrPlace {
                                local_: 0,
                                projection: Vec::new(),
                            },
                            IrRvalue::BinaryOp(
                                IrBinOp::Div,
                                const_u32_operand(100),
                                IrOperand::Copy(IrPlace {
                                    local_: 2,
                                    projection: Vec::new(),
                                }),
                            ),
                        ),
                        span: String::from("probes.rs:23:9"),
                        comment: None,
                    }],
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Return,
                        span: String::from("probes.rs:23:25"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
            ],
            fn_abi: IrFnAbi {
                args: vec![
                    IrArgAbi {
                        layout: scalar_u32_layout(),
                        mode: IrAbiPassMode::Direct,
                    },
                    IrArgAbi {
                        layout: scalar_u32_layout(),
                        mode: IrAbiPassMode::Direct,
                    },
                ],
                ret: IrArgAbi {
                    layout: scalar_u32_layout(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts,
            allocations: Vec::new(),
        },
        FalseProofMutationProbe::LoopUpdateOverflowProbe => IrCapturedMir {
            def_path: String::from("probes::loop_update_overflow"),
            phase: IrMirPhaseTag::RuntimePostCleanup,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: Vec::new(),
            trait_impls: Vec::new(),
            arg_count: 1,
            local_decls: vec![
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: u32_ty.clone(),
                    debug_name: None,
                },
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: u32_ty.clone(),
                    debug_name: Some(String::from("idx")),
                },
            ],
            basic_blocks: vec![
                IrBasicBlockData {
                    statements: Vec::new(),
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Goto(1),
                        span: String::from("probes.rs:30:5"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: Vec::new(),
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::SwitchInt(
                            IrOperand::Copy(IrPlace {
                                local_: 1,
                                projection: Vec::new(),
                            }),
                            IrSwitchTargets {
                                branches: vec![(10, 3)],
                                otherwise: 2,
                            },
                        ),
                        span: String::from("probes.rs:31:5"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: vec![IrStatement {
                        kind: IrStatementKind::Assign(
                            IrPlace {
                                local_: 1,
                                projection: Vec::new(),
                            },
                            IrRvalue::BinaryOp(
                                IrBinOp::AddUnchecked,
                                IrOperand::Copy(IrPlace {
                                    local_: 1,
                                    projection: Vec::new(),
                                }),
                                const_u32_operand(1),
                            ),
                        ),
                        span: String::from("probes.rs:32:9"),
                        comment: None,
                    }],
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Goto(1),
                        span: String::from("probes.rs:32:25"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: vec![IrStatement {
                        kind: IrStatementKind::Assign(
                            IrPlace {
                                local_: 0,
                                projection: Vec::new(),
                            },
                            IrRvalue::Use(IrOperand::Copy(IrPlace {
                                local_: 1,
                                projection: Vec::new(),
                            })),
                        ),
                        span: String::from("probes.rs:34:5"),
                        comment: None,
                    }],
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Return,
                        span: String::from("probes.rs:34:13"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
            ],
            fn_abi: IrFnAbi {
                args: vec![IrArgAbi {
                    layout: scalar_u32_layout(),
                    mode: IrAbiPassMode::Direct,
                }],
                ret: IrArgAbi {
                    layout: scalar_u32_layout(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts,
            allocations: Vec::new(),
        },
        FalseProofMutationProbe::DerefAliasProbe => IrCapturedMir {
            def_path: String::from("probes::deref_alias"),
            phase: IrMirPhaseTag::RuntimePostCleanup,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: Vec::new(),
            trait_impls: Vec::new(),
            arg_count: 2,
            local_decls: vec![
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: unit_ty,
                    debug_name: None,
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: mut_ref_u32_ty,
                    debug_name: Some(String::from("dst")),
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: ref_u32_ty,
                    debug_name: Some(String::from("src")),
                },
            ],
            basic_blocks: vec![IrBasicBlockData {
                statements: vec![IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace {
                            local_: 1,
                            projection: vec![IrProjectionElem::Deref],
                        },
                        IrRvalue::Use(IrOperand::Copy(IrPlace {
                            local_: 2,
                            projection: vec![IrProjectionElem::Deref],
                        })),
                    ),
                    span: String::from("probes.rs:40:5"),
                    comment: None,
                }],
                terminator: IrTerminator {
                    kind: IrTerminatorKind::Return,
                    span: String::from("probes.rs:41:5"),
                    comment: None,
                },
                is_cleanup: false,
            }],
            fn_abi: IrFnAbi {
                args: vec![
                    IrArgAbi {
                        layout: ptr_layout(),
                        mode: IrAbiPassMode::Direct,
                    },
                    IrArgAbi {
                        layout: ptr_layout(),
                        mode: IrAbiPassMode::Direct,
                    },
                ],
                ret: IrArgAbi {
                    layout: unit_layout(),
                    mode: IrAbiPassMode::Ignore,
                },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts,
            allocations: Vec::new(),
        },
    }
}

// ============================================================================
// Spec-Boundary Guard Taxonomy, Canonical Taxonomy Manifest & Static Audit
// ============================================================================
//
// The 12 property classes above classify faults *inside* a MIR body. The three
// guards below reject specifications whose *boundary* makes a kernel-checked
// proof worthless:
//
// - `entry_point_requires` (`verus#3606`): a binary entry point carries a
//   non-trivial precondition that no verified caller discharges.
// - `fixed_width_ghost_length` (`Slate` soundness bug 121): a ghost collection
//   length is typed at a machine width and wraps at `2^64`.
// - `error_branch_wildcard` (`awsm2`): a postcondition arm such as
//   `Err(_) => true` accepts every error escape.
//
// The identifiers are frozen across `Anneal.SpecBoundaryGuards` (Lean),
// `anneal_spec::spec_check::SpecBoundaryGuardClass`, and this module.

/// The 3 specification-boundary guards in canonical rank order `0..3`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecBoundaryGuardId {
    /// Rank 0 (`verus#3606`): a binary entry point (`main`, `#![no_main]`
    /// `_start`) carries a non-trivial `requires`.
    EntryPointRequires,
    /// Rank 1 (`Slate` soundness bug 121): a ghost collection length or
    /// cardinality has a fixed machine width instead of `Nat` / `Int`.
    FixedWidthGhostLength,
    /// Rank 2 (`awsm2`): a postcondition arm accepts every error, `ub`, or
    /// `unsupported` outcome.
    ErrorBranchWildcard,
}

impl SpecBoundaryGuardId {
    /// Total number of specification-boundary guards.
    pub const COUNT: usize = 3;

    /// All 3 guards in canonical rank order.
    pub const ALL: [SpecBoundaryGuardId; Self::COUNT] = [
        SpecBoundaryGuardId::EntryPointRequires,
        SpecBoundaryGuardId::FixedWidthGhostLength,
        SpecBoundaryGuardId::ErrorBranchWildcard,
    ];

    /// 0-based canonical rank (`0..3`).
    pub const fn rank(self) -> usize {
        match self {
            Self::EntryPointRequires => 0,
            Self::FixedWidthGhostLength => 1,
            Self::ErrorBranchWildcard => 2,
        }
    }

    /// Reconstruct a guard from its canonical rank `0..3`.
    pub const fn from_rank(rank: usize) -> Option<Self> {
        match rank {
            0 => Some(Self::EntryPointRequires),
            1 => Some(Self::FixedWidthGhostLength),
            2 => Some(Self::ErrorBranchWildcard),
            _ => None,
        }
    }

    /// Canonical `snake_case` guard identifier
    /// (`SpecBoundaryGuardClass::guard_id` in `anneal-spec`, `guardId` in Lean).
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::EntryPointRequires => "entry_point_requires",
            Self::FixedWidthGhostLength => "fixed_width_ghost_length",
            Self::ErrorBranchWildcard => "error_branch_wildcard",
        }
    }

    /// Canonical diagnostic name (`canonical_name` / `canonicalName`).
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::EntryPointRequires => "EntryPointPrecondition",
            Self::FixedWidthGhostLength => "FixedWidthGhostLength",
            Self::ErrorBranchWildcard => "ErrorBranchWildcard",
        }
    }

    /// Canonical name of the frozen vacuity class a violation is reported
    /// under (`to_vacuity_class` / `toVacuityClass`).
    pub const fn vacuity_class(self) -> &'static str {
        match self {
            Self::EntryPointRequires => "DeadPrecondition",
            Self::FixedWidthGhostLength => "SpecViolation",
            Self::ErrorBranchWildcard => "SurvivedAllMutants",
        }
    }

    /// Concise human-readable description of the guard.
    pub const fn description(self) -> &'static str {
        match self {
            Self::EntryPointRequires => {
                "binary entry point (main, #![no_main] _start, #[entry]) carries a non-trivial \
                 requires that no verified caller discharges"
            }
            Self::FixedWidthGhostLength => {
                "ghost collection length or cardinality typed at a fixed machine width wraps at \
                 2^64 instead of using Nat or Int"
            }
            Self::ErrorBranchWildcard => {
                "postcondition arm accepts every error payload, ub, or unsupported outcome"
            }
        }
    }
}

impl fmt::Display for SpecBoundaryGuardId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for SpecBoundaryGuardId {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::ALL
            .into_iter()
            .find(|guard| guard.as_str() == s)
            .ok_or_else(|| format!("unknown SpecBoundaryGuardId identifier `{s}`"))
    }
}

impl PropertyClass {
    /// Rust enum variant name of the class, as exported in the taxonomy
    /// manifest (`PropertyClassTag.variantName` in Lean).
    pub const fn variant_name(self) -> &'static str {
        match self {
            Self::ArithmeticOverflow => "ArithmeticOverflow",
            Self::ShiftBounds => "ShiftBounds",
            Self::DivRemUb => "DivRemUb",
            Self::PointerDereference => "PointerDereference",
            Self::SliceArrayBounds => "SliceArrayBounds",
            Self::DiscriminantValidity => "DiscriminantValidity",
            Self::CallContract => "CallContract",
            Self::LoopTermination => "LoopTermination",
            Self::SwitchExhaustiveness => "SwitchExhaustiveness",
            Self::MemoryCopyOverlap => "MemoryCopyOverlap",
            Self::UninitRead => "UninitRead",
            Self::UnsupportedFallback => "UnsupportedFallback",
        }
    }
}

// ----------------------------------------------------------------------------
// Canonical taxonomy manifest (JSON)
// ----------------------------------------------------------------------------

/// Schema version of the canonical property taxonomy manifest.
pub const PROPERTY_TAXONOMY_SCHEMA_VERSION: u32 = 1;

/// One of the 12 property classes as exported in the taxonomy manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyClassManifestEntry {
    /// 0-based canonical rank.
    pub rank: usize,
    /// Canonical `snake_case` wire identifier ([`PropertyClass::as_str`]).
    pub id: String,
    /// Rust enum variant name ([`PropertyClass::variant_name`]).
    pub variant: String,
    /// Whether a contract or registry waiver may cover the class.
    pub is_waivable: bool,
    /// Disposition tag under [`PropertyRegistry::strict`].
    pub strict_disposition: String,
    /// Disposition tag under [`PropertyRegistry::for_partial_correctness`].
    pub partial_disposition: String,
    /// Disposition tag of the exporting registry. Present only in
    /// [`PropertyRegistry::to_taxonomy_json`] exports.
    pub disposition: Option<String>,
    /// Canonical summary of what the class checks.
    pub description: String,
}

/// One of the 3 spec-boundary guards as exported in the taxonomy manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecBoundaryGuardManifestEntry {
    /// 0-based canonical rank.
    pub rank: usize,
    /// Canonical `snake_case` guard identifier.
    pub id: String,
    /// Canonical diagnostic name.
    pub canonical_name: String,
    /// Canonical name of the vacuity class a violation is reported under.
    pub vacuity_class: String,
    /// Canonical summary of what the guard rejects.
    pub description: String,
}

/// The cross-language property taxonomy: 12 property classes and 3
/// spec-boundary guards.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyTaxonomyManifest {
    /// Manifest schema version ([`PROPERTY_TAXONOMY_SCHEMA_VERSION`]).
    pub schema_version: u32,
    /// The property classes in rank order.
    pub property_classes: Vec<PropertyClassManifestEntry>,
    /// The spec-boundary guards in rank order.
    pub spec_boundary_guards: Vec<SpecBoundaryGuardManifestEntry>,
}

impl PropertyTaxonomyManifest {
    /// The canonical manifest of the taxonomy compiled into this module.
    pub fn canonical() -> Self {
        let strict = PropertyRegistry::strict();
        let partial = PropertyRegistry::for_partial_correctness();
        Self {
            schema_version: PROPERTY_TAXONOMY_SCHEMA_VERSION,
            property_classes: PropertyClass::ALL
                .into_iter()
                .map(|class| PropertyClassManifestEntry {
                    rank: class.rank(),
                    id: String::from(class.as_str()),
                    variant: String::from(class.variant_name()),
                    is_waivable: class.is_waivable(),
                    strict_disposition: String::from(strict.disposition(class).tag()),
                    partial_disposition: String::from(partial.disposition(class).tag()),
                    disposition: None,
                    description: String::from(class.description()),
                })
                .collect(),
            spec_boundary_guards: SpecBoundaryGuardId::ALL
                .into_iter()
                .map(|guard| SpecBoundaryGuardManifestEntry {
                    rank: guard.rank(),
                    id: String::from(guard.as_str()),
                    canonical_name: String::from(guard.canonical_name()),
                    vacuity_class: String::from(guard.vacuity_class()),
                    description: String::from(guard.description()),
                })
                .collect(),
        }
    }

    /// The canonical manifest annotated with the dispositions of `registry`.
    pub fn for_registry(registry: &PropertyRegistry) -> Self {
        let mut manifest = Self::canonical();
        for (entry, class) in manifest.property_classes.iter_mut().zip(PropertyClass::ALL) {
            entry.disposition = Some(String::from(registry.disposition(class).tag()));
        }
        manifest
    }

    /// Render the manifest as deterministic canonical JSON: fixed key order,
    /// two-space indentation, one entry per line, and a trailing newline.
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        out.push_str("{\n");
        out.push_str(&format!("  \"schema_version\": {},\n", self.schema_version));
        out.push_str("  \"property_classes\": [\n");
        for (idx, entry) in self.property_classes.iter().enumerate() {
            out.push_str("    {");
            out.push_str(&format!("\"rank\": {}, ", entry.rank));
            push_json_field(&mut out, "id", &entry.id);
            out.push_str(", ");
            push_json_field(&mut out, "variant", &entry.variant);
            out.push_str(&format!(", \"is_waivable\": {}, ", entry.is_waivable));
            push_json_field(&mut out, "strict_disposition", &entry.strict_disposition);
            out.push_str(", ");
            push_json_field(&mut out, "partial_disposition", &entry.partial_disposition);
            out.push_str(", ");
            if let Some(disposition) = &entry.disposition {
                push_json_field(&mut out, "disposition", disposition);
                out.push_str(", ");
            }
            push_json_field(&mut out, "description", &entry.description);
            out.push('}');
            out.push_str(if idx + 1 < self.property_classes.len() {
                ",\n"
            } else {
                "\n"
            });
        }
        out.push_str("  ],\n");
        out.push_str("  \"spec_boundary_guards\": [\n");
        for (idx, entry) in self.spec_boundary_guards.iter().enumerate() {
            out.push_str("    {");
            out.push_str(&format!("\"rank\": {}, ", entry.rank));
            push_json_field(&mut out, "id", &entry.id);
            out.push_str(", ");
            push_json_field(&mut out, "canonical_name", &entry.canonical_name);
            out.push_str(", ");
            push_json_field(&mut out, "vacuity_class", &entry.vacuity_class);
            out.push_str(", ");
            push_json_field(&mut out, "description", &entry.description);
            out.push('}');
            out.push_str(if idx + 1 < self.spec_boundary_guards.len() {
                ",\n"
            } else {
                "\n"
            });
        }
        out.push_str("  ]\n");
        out.push_str("}\n");
        out
    }

    /// Check that the manifest describes exactly the taxonomy compiled into
    /// this module, ignoring registry-specific `disposition` annotations.
    /// Returns a description of the first drift found.
    pub fn check_canonical(&self) -> Result<(), String> {
        let canonical = Self::canonical();
        if self.schema_version != canonical.schema_version {
            return Err(format!(
                "taxonomy schema_version drift: manifest has {}, expected {}",
                self.schema_version, canonical.schema_version
            ));
        }
        if self.property_classes.len() != canonical.property_classes.len() {
            return Err(format!(
                "taxonomy drift: manifest has {} property classes, expected {}",
                self.property_classes.len(),
                canonical.property_classes.len()
            ));
        }
        for (entry, expected) in self
            .property_classes
            .iter()
            .zip(&canonical.property_classes)
        {
            let comparable = PropertyClassManifestEntry {
                disposition: None,
                ..entry.clone()
            };
            if &comparable != expected {
                return Err(format!(
                    "taxonomy drift at property class rank {}: manifest has {comparable:?}, \
                     expected {expected:?}",
                    expected.rank
                ));
            }
            if let Some(disposition) = &entry.disposition {
                if !PROPERTY_DISPOSITION_TAGS.contains(&disposition.as_str()) {
                    return Err(format!(
                        "taxonomy drift at property class rank {}: unknown disposition tag \
                         `{disposition}`",
                        expected.rank
                    ));
                }
                if !expected.is_waivable
                    && matches!(disposition.as_str(), "discharged" | "explicitly_waived")
                {
                    return Err(format!(
                        "taxonomy drift at property class rank {}: non-waivable class `{}` \
                         cannot carry disposition `{disposition}`",
                        expected.rank, expected.id
                    ));
                }
            }
        }
        if self.spec_boundary_guards.len() != canonical.spec_boundary_guards.len() {
            return Err(format!(
                "taxonomy drift: manifest has {} spec-boundary guards, expected {}",
                self.spec_boundary_guards.len(),
                canonical.spec_boundary_guards.len()
            ));
        }
        for (entry, expected) in self
            .spec_boundary_guards
            .iter()
            .zip(&canonical.spec_boundary_guards)
        {
            if entry != expected {
                return Err(format!(
                    "taxonomy drift at spec-boundary guard rank {}: manifest has {entry:?}, \
                     expected {expected:?}",
                    expected.rank
                ));
            }
        }
        Ok(())
    }
}

/// Every [`PropertyDisposition::tag`] value.
const PROPERTY_DISPOSITION_TAGS: [&str; 4] = [
    "discharged",
    "explicitly_waived",
    "unemitted_gap",
    "unsupported_fail_closed",
];

/// Render the canonical taxonomy manifest (12 property classes and 3
/// spec-boundary guards) as deterministic JSON.
pub fn render_property_taxonomy_json() -> String {
    PropertyTaxonomyManifest::canonical().to_json()
}

impl PropertyRegistry {
    /// Render the canonical taxonomy manifest annotated with this registry's
    /// per-class `disposition` tags.
    pub fn to_taxonomy_json(&self) -> String {
        PropertyTaxonomyManifest::for_registry(self).to_json()
    }
}

fn push_json_string(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if (ch as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
}

fn push_json_field(out: &mut String, key: &str, value: &str) {
    push_json_string(out, key);
    out.push_str(": ");
    push_json_string(out, value);
}

/// JSON value subset used by the taxonomy manifest: objects, arrays, strings,
/// unsigned integers, and booleans.
#[derive(Clone, Debug, PartialEq, Eq)]
enum TaxonomyJson {
    Bool(bool),
    Number(u64),
    String(String),
    Array(Vec<TaxonomyJson>),
    Object(Vec<(String, TaxonomyJson)>),
}

/// Maximum nesting depth accepted by the taxonomy JSON parser.
const TAXONOMY_JSON_MAX_DEPTH: usize = 8;

struct TaxonomyJsonParser<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> TaxonomyJsonParser<'a> {
    fn error(&self, message: &str) -> String {
        format!("taxonomy JSON error at byte {}: {message}", self.pos)
    }

    fn skip_ws(&mut self) {
        let bytes = self.src.as_bytes();
        while self.pos < bytes.len() && matches!(bytes[self.pos], b' ' | b'\n' | b'\r' | b'\t') {
            self.pos += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.src.as_bytes().get(self.pos).copied()
    }

    fn expect(&mut self, byte: u8) -> Result<(), String> {
        if self.peek() == Some(byte) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.error(&format!("expected `{}`", byte as char)))
        }
    }

    fn parse_value(&mut self, depth: usize) -> Result<TaxonomyJson, String> {
        if depth > TAXONOMY_JSON_MAX_DEPTH {
            return Err(self.error("nesting too deep"));
        }
        self.skip_ws();
        match self.peek() {
            Some(b'{') => self.parse_object(depth),
            Some(b'[') => self.parse_array(depth),
            Some(b'"') => self.parse_string().map(TaxonomyJson::String),
            Some(b't') if self.src[self.pos..].starts_with("true") => {
                self.pos += 4;
                Ok(TaxonomyJson::Bool(true))
            }
            Some(b'f') if self.src[self.pos..].starts_with("false") => {
                self.pos += 5;
                Ok(TaxonomyJson::Bool(false))
            }
            Some(b'0'..=b'9') => self.parse_number(),
            Some(_) => Err(self.error("unexpected character")),
            None => Err(self.error("unexpected end of input")),
        }
    }

    fn parse_number(&mut self) -> Result<TaxonomyJson, String> {
        let bytes = self.src.as_bytes();
        let start = self.pos;
        while self.pos < bytes.len() && bytes[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        let digits = &self.src[start..self.pos];
        if digits.len() > 1 && digits.starts_with('0') {
            return Err(self.error("number has a leading zero"));
        }
        if matches!(self.peek(), Some(b'.' | b'e' | b'E' | b'-' | b'+')) {
            return Err(self.error("only unsigned integers are allowed"));
        }
        digits
            .parse::<u64>()
            .map(TaxonomyJson::Number)
            .map_err(|_| self.error("integer out of range"))
    }

    fn parse_string(&mut self) -> Result<String, String> {
        self.expect(b'"')?;
        let mut out = String::new();
        loop {
            let Some(ch) = self.src[self.pos..].chars().next() else {
                return Err(self.error("unterminated string"));
            };
            self.pos += ch.len_utf8();
            match ch {
                '"' => return Ok(out),
                '\\' => {
                    let Some(escape) = self.src[self.pos..].chars().next() else {
                        return Err(self.error("unterminated escape"));
                    };
                    self.pos += escape.len_utf8();
                    match escape {
                        '"' => out.push('"'),
                        '\\' => out.push('\\'),
                        '/' => out.push('/'),
                        'b' => out.push('\u{0008}'),
                        'f' => out.push('\u{000c}'),
                        'n' => out.push('\n'),
                        'r' => out.push('\r'),
                        't' => out.push('\t'),
                        'u' => {
                            let hex = self
                                .src
                                .get(self.pos..self.pos + 4)
                                .ok_or_else(|| self.error("truncated \\u escape"))?;
                            if !hex.bytes().all(|b| b.is_ascii_hexdigit()) {
                                return Err(self.error("invalid \\u escape"));
                            }
                            let code = u32::from_str_radix(hex, 16)
                                .map_err(|_| self.error("invalid \\u escape"))?;
                            let decoded = char::from_u32(code)
                                .ok_or_else(|| self.error("invalid \\u code point"))?;
                            out.push(decoded);
                            self.pos += 4;
                        }
                        _ => return Err(self.error("unknown escape")),
                    }
                }
                ch if (ch as u32) < 0x20 => {
                    return Err(self.error("unescaped control character in string"));
                }
                ch => out.push(ch),
            }
        }
    }

    fn parse_array(&mut self, depth: usize) -> Result<TaxonomyJson, String> {
        self.expect(b'[')?;
        let mut items = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(TaxonomyJson::Array(items));
        }
        loop {
            items.push(self.parse_value(depth + 1)?);
            self.skip_ws();
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(TaxonomyJson::Array(items));
                }
                _ => return Err(self.error("expected `,` or `]`")),
            }
        }
    }

    fn parse_object(&mut self, depth: usize) -> Result<TaxonomyJson, String> {
        self.expect(b'{')?;
        let mut fields: Vec<(String, TaxonomyJson)> = Vec::new();
        self.skip_ws();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(TaxonomyJson::Object(fields));
        }
        loop {
            self.skip_ws();
            let key = self.parse_string()?;
            if fields.iter().any(|(existing, _)| existing == &key) {
                return Err(self.error(&format!("duplicate key `{key}`")));
            }
            self.skip_ws();
            self.expect(b':')?;
            let value = self.parse_value(depth + 1)?;
            fields.push((key, value));
            self.skip_ws();
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(TaxonomyJson::Object(fields));
                }
                _ => return Err(self.error("expected `,` or `}`")),
            }
        }
    }
}

/// Typed access to the fields of one manifest object, rejecting unknown keys.
struct TaxonomyObject<'a> {
    context: &'a str,
    fields: Vec<(String, TaxonomyJson)>,
}

impl<'a> TaxonomyObject<'a> {
    fn new(context: &'a str, value: TaxonomyJson) -> Result<Self, String> {
        match value {
            TaxonomyJson::Object(fields) => Ok(Self { context, fields }),
            _ => Err(format!(
                "taxonomy manifest: {context} must be a JSON object"
            )),
        }
    }

    fn take(&mut self, key: &str) -> Option<TaxonomyJson> {
        let idx = self.fields.iter().position(|(name, _)| name == key)?;
        Some(self.fields.remove(idx).1)
    }

    fn require(&mut self, key: &str) -> Result<TaxonomyJson, String> {
        self.take(key)
            .ok_or_else(|| format!("taxonomy manifest: {} is missing key `{key}`", self.context))
    }

    fn string(&mut self, key: &str) -> Result<String, String> {
        match self.require(key)? {
            TaxonomyJson::String(value) => Ok(value),
            _ => Err(format!(
                "taxonomy manifest: {} key `{key}` must be a string",
                self.context
            )),
        }
    }

    fn optional_string(&mut self, key: &str) -> Result<Option<String>, String> {
        match self.take(key) {
            None => Ok(None),
            Some(TaxonomyJson::String(value)) => Ok(Some(value)),
            Some(_) => Err(format!(
                "taxonomy manifest: {} key `{key}` must be a string",
                self.context
            )),
        }
    }

    fn number(&mut self, key: &str) -> Result<u64, String> {
        match self.require(key)? {
            TaxonomyJson::Number(value) => Ok(value),
            _ => Err(format!(
                "taxonomy manifest: {} key `{key}` must be an unsigned integer",
                self.context
            )),
        }
    }

    fn boolean(&mut self, key: &str) -> Result<bool, String> {
        match self.require(key)? {
            TaxonomyJson::Bool(value) => Ok(value),
            _ => Err(format!(
                "taxonomy manifest: {} key `{key}` must be a boolean",
                self.context
            )),
        }
    }

    fn array(&mut self, key: &str) -> Result<Vec<TaxonomyJson>, String> {
        match self.require(key)? {
            TaxonomyJson::Array(items) => Ok(items),
            _ => Err(format!(
                "taxonomy manifest: {} key `{key}` must be an array",
                self.context
            )),
        }
    }

    fn finish(self) -> Result<(), String> {
        match self.fields.first() {
            None => Ok(()),
            Some((key, _)) => Err(format!(
                "taxonomy manifest: {} has unknown key `{key}`",
                self.context
            )),
        }
    }
}

fn manifest_rank(value: u64, expected: usize, context: &str) -> Result<usize, String> {
    let rank = usize::try_from(value)
        .map_err(|_| format!("taxonomy manifest: {context} rank {value} is out of range"))?;
    if rank != expected {
        return Err(format!(
            "taxonomy manifest: {context} entry {expected} has rank {rank} (entries must be in \
             rank order)"
        ));
    }
    Ok(rank)
}

/// Parse a taxonomy manifest produced by [`render_property_taxonomy_json`] or
/// [`PropertyRegistry::to_taxonomy_json`].
///
/// Parsing is strict: unknown, missing, or duplicate keys, entries out of rank
/// order, an unsupported `schema_version`, and trailing input are errors. The
/// result is not compared against the compiled taxonomy; call
/// [`PropertyTaxonomyManifest::check_canonical`] (or use
/// [`parse_canonical_property_taxonomy_json`]) to detect drift.
pub fn parse_property_taxonomy_json(json: &str) -> Result<PropertyTaxonomyManifest, String> {
    let mut parser = TaxonomyJsonParser { src: json, pos: 0 };
    let root = parser.parse_value(0)?;
    parser.skip_ws();
    if parser.pos != json.len() {
        return Err(parser.error("trailing input after the manifest"));
    }

    let mut root = TaxonomyObject::new("root", root)?;
    let schema_version = root.number("schema_version")?;
    if schema_version != u64::from(PROPERTY_TAXONOMY_SCHEMA_VERSION) {
        return Err(format!(
            "taxonomy manifest: unsupported schema_version {schema_version} (expected \
             {PROPERTY_TAXONOMY_SCHEMA_VERSION})"
        ));
    }

    let mut property_classes = Vec::new();
    for (idx, item) in root.array("property_classes")?.into_iter().enumerate() {
        let mut entry = TaxonomyObject::new("property class", item)?;
        let parsed = PropertyClassManifestEntry {
            rank: manifest_rank(entry.number("rank")?, idx, "property class")?,
            id: entry.string("id")?,
            variant: entry.string("variant")?,
            is_waivable: entry.boolean("is_waivable")?,
            strict_disposition: entry.string("strict_disposition")?,
            partial_disposition: entry.string("partial_disposition")?,
            disposition: entry.optional_string("disposition")?,
            description: entry.string("description")?,
        };
        entry.finish()?;
        property_classes.push(parsed);
    }

    let mut spec_boundary_guards = Vec::new();
    for (idx, item) in root.array("spec_boundary_guards")?.into_iter().enumerate() {
        let mut entry = TaxonomyObject::new("spec-boundary guard", item)?;
        let parsed = SpecBoundaryGuardManifestEntry {
            rank: manifest_rank(entry.number("rank")?, idx, "spec-boundary guard")?,
            id: entry.string("id")?,
            canonical_name: entry.string("canonical_name")?,
            vacuity_class: entry.string("vacuity_class")?,
            description: entry.string("description")?,
        };
        entry.finish()?;
        spec_boundary_guards.push(parsed);
    }
    root.finish()?;

    Ok(PropertyTaxonomyManifest {
        schema_version: PROPERTY_TAXONOMY_SCHEMA_VERSION,
        property_classes,
        spec_boundary_guards,
    })
}

/// Parse a taxonomy manifest and require it to describe exactly the taxonomy
/// compiled into this module ([`PropertyTaxonomyManifest::check_canonical`]).
pub fn parse_canonical_property_taxonomy_json(
    json: &str,
) -> Result<PropertyTaxonomyManifest, String> {
    let manifest = parse_property_taxonomy_json(json)?;
    manifest.check_canonical()?;
    Ok(manifest)
}

// ----------------------------------------------------------------------------
// Comment- and literal-aware specification tokenizer
// ----------------------------------------------------------------------------

/// Source dialect of a scanned specification file, which decides what a
/// comment is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SpecSourceDialect {
    /// Rust: `//` line comments and nested `/* */` block comments.
    Rust,
    /// Lean 4: `--` line comments and nested `/- -/` block comments.
    Lean,
    /// Unknown: both comment families are recognized.
    Unknown,
}

impl SpecSourceDialect {
    /// Infer the dialect from a source label: `*.rs` is Rust, `*.lean` is
    /// Lean, and anything else is [`Self::Unknown`].
    pub fn from_source_label(source_label: &str) -> Self {
        if source_label.ends_with(".rs") {
            Self::Rust
        } else if source_label.ends_with(".lean") {
            Self::Lean
        } else {
            Self::Unknown
        }
    }

    fn rust_comments(self) -> bool {
        self != Self::Lean
    }

    fn lean_comments(self) -> bool {
        self != Self::Rust
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GuardTokKind {
    /// Identifier, keyword, or numeric literal.
    Word,
    /// String, raw-string, byte-string, or character literal.
    Literal,
    /// `=>`
    FatArrow,
    /// `::`
    PathSep,
    /// `..`, `..=`, or `...`
    DotDot,
    /// Any other operator or punctuation.
    Sym,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GuardTok<'a> {
    kind: GuardTokKind,
    text: &'a str,
    /// 1-based source line of the token's first character.
    line: usize,
}

impl GuardTok<'_> {
    fn is_word(&self, word: &str) -> bool {
        self.kind == GuardTokKind::Word && self.text == word
    }

    fn is_sym(&self, sym: &str) -> bool {
        self.kind == GuardTokKind::Sym && self.text == sym
    }
}

/// A block comment, string literal, or character literal left unclosed,
/// starting at 1-based source line `line`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct UnclosedSpecSource {
    line: usize,
}

fn is_guard_word_char(ch: char) -> bool {
    ch == '_' || ch.is_alphanumeric()
}

/// Tokenize Rust or Lean specification source, skipping comments and never
/// looking inside literals. Mirrors `SpecLexer` in `anneal_spec::spec_check`.
fn tokenize_spec_source(
    src: &str,
    dialect: SpecSourceDialect,
) -> Result<Vec<GuardTok<'_>>, UnclosedSpecSource> {
    let bytes = src.as_bytes();
    let mut toks = Vec::new();
    let mut pos = 0usize;
    let mut line = 1usize;
    let mut line_pos = 0usize;
    // Advance the line counter to byte offset `upto`.
    let line_at = |upto: usize, line: &mut usize, line_pos: &mut usize| {
        *line += bytes[*line_pos..upto]
            .iter()
            .filter(|b| **b == b'\n')
            .count();
        *line_pos = upto;
        *line
    };

    while pos < bytes.len() {
        let here = bytes[pos];
        if here.is_ascii_whitespace() {
            pos += 1;
            continue;
        }
        // Lean identifier quotes (`«pre»` is the identifier `pre`).
        if dialect != SpecSourceDialect::Rust
            && (src[pos..].starts_with('«') || src[pos..].starts_with('»'))
        {
            pos += '«'.len_utf8();
            continue;
        }
        let next = bytes.get(pos + 1).copied();
        let start_line = line_at(pos, &mut line, &mut line_pos);

        // Comments.
        let line_comment = (dialect.rust_comments() && here == b'/' && next == Some(b'/'))
            || (dialect.lean_comments() && here == b'-' && next == Some(b'-'));
        if line_comment {
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        let block_marker = if dialect.rust_comments() && here == b'/' && next == Some(b'*') {
            Some(b'*')
        } else if dialect.lean_comments() && here == b'/' && next == Some(b'-') {
            Some(b'-')
        } else {
            None
        };
        if let Some(marker) = block_marker {
            pos += 2;
            let mut depth = 1usize;
            while pos < bytes.len() && depth > 0 {
                let after = bytes.get(pos + 1).copied();
                if bytes[pos] == b'/' && after == Some(marker) {
                    depth += 1;
                    pos += 2;
                } else if bytes[pos] == marker && after == Some(b'/') {
                    depth -= 1;
                    pos += 2;
                } else {
                    pos += 1;
                }
            }
            if depth > 0 {
                return Err(UnclosedSpecSource { line: start_line });
            }
            continue;
        }

        // String literals.
        if here == b'"' {
            pos = skip_guard_string(bytes, pos).ok_or(UnclosedSpecSource { line: start_line })?;
            toks.push(GuardTok {
                kind: GuardTokKind::Literal,
                text: &src[pos..pos],
                line: start_line,
            });
            continue;
        }
        // Character literals and lone quotes (Rust lifetimes).
        if here == b'\'' {
            match lex_guard_quote(src, pos) {
                Some((end, is_literal)) => {
                    toks.push(GuardTok {
                        kind: if is_literal {
                            GuardTokKind::Literal
                        } else {
                            GuardTokKind::Sym
                        },
                        text: if is_literal {
                            &src[pos..pos]
                        } else {
                            &src[pos..end]
                        },
                        line: start_line,
                    });
                    pos = end;
                }
                None => return Err(UnclosedSpecSource { line: start_line }),
            }
            continue;
        }

        let first = src[pos..]
            .chars()
            .next()
            .expect("`pos` is a character boundary inside the source");
        if is_guard_word_char(first) {
            let mut end = pos;
            for (offset, ch) in src[pos..].char_indices() {
                if !is_guard_word_char(ch) {
                    break;
                }
                end = pos + offset + ch.len_utf8();
            }
            let word = &src[pos..end];
            // Raw strings exist in both languages (`r"…"`, `r#"…"#`): a
            // backslash inside one is not an escape. The Rust-only byte and
            // C-string prefixes (`br"…"`, `cr#"…"#`, `b"…"`, `c"…"`, `b'…'`)
            // never apply in Lean mode, where `b'` is a primed identifier.
            if word == "r" || (dialect != SpecSourceDialect::Lean && matches!(word, "br" | "cr")) {
                match skip_guard_raw_string(bytes, end) {
                    Ok(Some(after)) => {
                        toks.push(GuardTok {
                            kind: GuardTokKind::Literal,
                            text: &src[pos..pos],
                            line: start_line,
                        });
                        pos = after;
                        continue;
                    }
                    Ok(None) => {}
                    Err(()) => return Err(UnclosedSpecSource { line: start_line }),
                }
            }
            if dialect != SpecSourceDialect::Lean {
                if matches!(word, "b" | "c") && bytes.get(end) == Some(&b'"') {
                    pos = skip_guard_string(bytes, end)
                        .ok_or(UnclosedSpecSource { line: start_line })?;
                    toks.push(GuardTok {
                        kind: GuardTokKind::Literal,
                        text: &src[pos..pos],
                        line: start_line,
                    });
                    continue;
                }
                if word == "b" && bytes.get(end) == Some(&b'\'') {
                    match lex_guard_quote(src, end) {
                        Some((after, true)) => {
                            toks.push(GuardTok {
                                kind: GuardTokKind::Literal,
                                text: &src[pos..pos],
                                line: start_line,
                            });
                            pos = after;
                            continue;
                        }
                        None => return Err(UnclosedSpecSource { line: start_line }),
                        Some((_, false)) if dialect == SpecSourceDialect::Rust => {
                            return Err(UnclosedSpecSource { line: start_line });
                        }
                        // In `SpecSourceDialect::Unknown`, fall through so Lean's
                        // primed identifier `b'` lexes cleanly as `Word("b'")`.
                        Some((_, false)) => {}
                    }
                }
            }
            // Lean identifiers may end in primes (`x'`, `b'`).
            if dialect != SpecSourceDialect::Rust {
                while bytes.get(end) == Some(&b'\'') {
                    end += 1;
                }
            }
            toks.push(GuardTok {
                kind: GuardTokKind::Word,
                text: &src[pos..end],
                line: start_line,
            });
            pos = end;
            continue;
        }

        let rest = &src[pos..];
        let (kind, len) = if rest.starts_with("==>") {
            (GuardTokKind::Sym, 3)
        } else if rest.starts_with("=>") {
            (GuardTokKind::FatArrow, 2)
        } else if rest.starts_with("...") || rest.starts_with("..=") {
            (GuardTokKind::DotDot, 3)
        } else if rest.starts_with("..") {
            (GuardTokKind::DotDot, 2)
        } else if rest.starts_with("::") {
            (GuardTokKind::PathSep, 2)
        } else if rest.starts_with("<->") {
            (GuardTokKind::Sym, 3)
        } else if [
            "==", "!=", "<=", ">=", "&&", "||", "->", "<-", ":=", "/\\", "\\/",
        ]
        .iter()
        .any(|op| rest.starts_with(op))
        {
            (GuardTokKind::Sym, 2)
        } else {
            (GuardTokKind::Sym, first.len_utf8())
        };
        toks.push(GuardTok {
            kind,
            text: &rest[..len],
            line: start_line,
        });
        pos += len;
    }
    Ok(toks)
}

/// Skip a `"…"` string starting at the opening quote; returns the offset
/// after the closing quote, or `None` when the string is unclosed.
fn skip_guard_string(bytes: &[u8], start: usize) -> Option<usize> {
    let mut pos = start + 1;
    while pos < bytes.len() {
        match bytes[pos] {
            b'\\' => pos += 2,
            b'"' => return Some(pos + 1),
            _ => pos += 1,
        }
    }
    None
}

/// Skip a raw string whose hashes start at `start`. `Ok(None)` when no raw
/// string starts there, `Err(())` when it is unclosed.
fn skip_guard_raw_string(bytes: &[u8], start: usize) -> Result<Option<usize>, ()> {
    let mut idx = start;
    let mut hashes = 0usize;
    while bytes.get(idx) == Some(&b'#') {
        hashes += 1;
        idx += 1;
    }
    if bytes.get(idx) != Some(&b'"') {
        return Ok(None);
    }
    idx += 1;
    while idx < bytes.len() {
        if bytes[idx] == b'"' {
            let mut closing = 0usize;
            while closing < hashes && bytes.get(idx + 1 + closing) == Some(&b'#') {
                closing += 1;
            }
            if closing == hashes {
                return Ok(Some(idx + 1 + hashes));
            }
        }
        idx += 1;
    }
    Err(())
}

/// Lex the token starting at a `'`. Returns `(end, true)` for a character
/// literal, `(end, false)` for a lone quote, and `None` for an unclosed
/// escaped character literal.
fn lex_guard_quote(src: &str, start: usize) -> Option<(usize, bool)> {
    const MAX_CHAR_ESCAPE_BYTES: usize = 12;
    let bytes = src.as_bytes();
    let rest = &src[start + 1..];
    if let Some(escape_body) = rest.strip_prefix('\\') {
        let escaped = escape_body.chars().next()?;
        if escaped == '\n' || escaped == '\r' {
            return None;
        }
        let body_start = start + 2 + escaped.len_utf8();
        let window_end = (body_start + MAX_CHAR_ESCAPE_BYTES).min(bytes.len());
        for idx in body_start..window_end {
            match bytes[idx] {
                b'\'' => return Some((idx + 1, true)),
                b'\n' | b'\r' => return None,
                _ => {}
            }
        }
        return None;
    }
    if let Some(ch) = rest.chars().next() {
        let after = start + 1 + ch.len_utf8();
        if ch != '\'' && ch != '\n' && ch != '\r' && bytes.get(after) == Some(&b'\'') {
            return Some((after + 1, true));
        }
    }
    Some((start + 1, false))
}

// ----------------------------------------------------------------------------
// Guard 2: fixed-width ghost length scanner (`Slate` soundness bug 121)
// ----------------------------------------------------------------------------

/// Fixed-width machine integer type names flagged on ghost lengths
/// (`fixedWidthGhostTypeNames` in Lean). `BitVec <N>` is flagged as well.
pub const FIXED_WIDTH_GHOST_INT_TYPE_NAMES: [&str; 22] = [
    "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64", "ISize",
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

/// Unbounded integer type names accepted on ghost lengths
/// (`unboundedGhostTypeNames` in Lean).
pub const UNBOUNDED_GHOST_INT_TYPE_NAMES: [&str; 2] = ["Nat", "Int"];

/// Ghost (mathematical) collection type names.
pub const GHOST_COLLECTION_TYPE_NAMES: [&str; 7] = [
    "GhostList",
    "GhostSet",
    "GhostMap",
    "GhostSeq",
    "Seq",
    "Multiset",
    "Finset",
];

/// Name segments that mark a declaration as a length or cardinality.
const GHOST_LENGTH_NAME_SEGMENTS: [&str; 9] = [
    "len",
    "length",
    "card",
    "cardinality",
    "size",
    "count",
    "cap",
    "capacity",
    "bound",
];

/// Projections whose value is a collection length or cardinality.
const GHOST_LENGTH_PROJECTIONS: [&str; 5] = ["length", "len", "card", "size", "count"];

/// Lean conversions from `Nat` into a fixed-width machine integer.
const LEAN_TO_FIXED_WIDTH_CASTS: [&str; 10] = [
    "toUInt8", "toUInt16", "toUInt32", "toUInt64", "toUSize", "toInt8", "toInt16", "toInt32",
    "toInt64", "toISize",
];

/// Lean declaration keywords that introduce a named constant with a type.
const LEAN_TYPED_DECL_KEYWORDS: [&str; 6] =
    ["def", "axiom", "opaque", "abbrev", "theorem", "lemma"];

/// Lean keywords that start a new top-level command.
const LEAN_COMMAND_KEYWORDS: [&str; 22] = [
    "def",
    "axiom",
    "opaque",
    "abbrev",
    "theorem",
    "lemma",
    "instance",
    "structure",
    "inductive",
    "class",
    "namespace",
    "section",
    "end",
    "open",
    "import",
    "variable",
    "universe",
    "example",
    "noncomputable",
    "private",
    "protected",
    "set_option",
];

/// What the fixed-width ghost length scanner found.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GhostLengthWidthKind {
    /// A ghost length or cardinality declaration returns a fixed-width type.
    FixedWidthReturnType,
    /// A collection length is cast into a fixed-width type
    /// (`UInt64.ofNat xs.length`, `xs.length.toUSize`, `s.len() as u64`).
    WraparoundCast,
    /// The source has an unclosed comment or literal and cannot be scanned.
    MalformedSource,
}

impl GhostLengthWidthKind {
    /// Short wire tag of the finding.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FixedWidthReturnType => "fixed_width_return_type",
            Self::WraparoundCast => "wraparound_cast",
            Self::MalformedSource => "malformed_source",
        }
    }
}

/// A `fixed_width_ghost_length` finding (`Slate` soundness bug 121,
/// `cl/1028783918`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct GhostLengthWidthDiagnostic {
    /// Label of the scanned source (usually its path).
    pub source_label: String,
    /// 1-based line of the offending type or cast.
    pub line: usize,
    /// Name of the ghost declaration (empty for a cast outside a declaration
    /// and for malformed source).
    pub declaration: String,
    /// The fixed-width type as written (`u64`, `USize`, `BitVec 64`).
    pub fixed_width_type: String,
    /// What was found.
    pub kind: GhostLengthWidthKind,
}

impl GhostLengthWidthDiagnostic {
    /// The guard every diagnostic of this type reports under.
    pub const GUARD: SpecBoundaryGuardId = SpecBoundaryGuardId::FixedWidthGhostLength;
}

impl fmt::Display for GhostLengthWidthDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}: ", self.source_label, self.line, Self::GUARD)?;
        match self.kind {
            GhostLengthWidthKind::FixedWidthReturnType => write!(
                f,
                "ghost length `{}` has fixed-width type `{}`, which wraps at its bit width; use \
                 Nat or Int",
                self.declaration, self.fixed_width_type
            ),
            GhostLengthWidthKind::WraparoundCast => write!(
                f,
                "collection length is cast into fixed-width type `{}`{}, which wraps at its bit \
                 width; keep the length in Nat or Int",
                self.fixed_width_type,
                if self.declaration.is_empty() {
                    String::new()
                } else {
                    format!(" in `{}`", self.declaration)
                }
            ),
            GhostLengthWidthKind::MalformedSource => f.write_str(
                "unclosed comment or literal; the source cannot be scanned (fail-closed)",
            ),
        }
    }
}

/// Split an identifier into lowercase `snake_case` / `camelCase` segments
/// (`ghostLen` and `ghost_len` both yield `["ghost", "len"]`).
fn identifier_segments(name: &str) -> Vec<String> {
    let mut segments = Vec::new();
    let mut current = String::new();
    let mut prev_lower = false;
    for ch in name.chars() {
        if !ch.is_alphanumeric() {
            if !current.is_empty() {
                segments.push(std::mem::take(&mut current));
            }
            prev_lower = false;
            continue;
        }
        if ch.is_uppercase() && prev_lower && !current.is_empty() {
            segments.push(std::mem::take(&mut current));
        }
        prev_lower = ch.is_lowercase() || ch.is_numeric();
        current.extend(ch.to_lowercase());
    }
    if !current.is_empty() {
        segments.push(current);
    }
    segments
}

/// The last `.`- or `::`-separated component of a declaration name.
fn declaration_leaf(name: &str) -> &str {
    let after_dot = name.rsplit('.').next().unwrap_or(name);
    after_dot.rsplit("::").next().unwrap_or(after_dot)
}

/// Whether the declaration's own name marks it as a length or cardinality.
fn is_ghost_length_name(name: &str) -> bool {
    identifier_segments(declaration_leaf(name))
        .iter()
        .any(|segment| GHOST_LENGTH_NAME_SEGMENTS.contains(&segment.as_str()))
}

/// Whether any component of the declaration name carries a `ghost` segment
/// (`ghostLen`, `ghost_len`, `GhostList.len`).
fn has_ghost_name_marker(name: &str) -> bool {
    identifier_segments(name)
        .iter()
        .any(|segment| segment == "ghost")
}

fn is_fixed_width_int_type_name(word: &str) -> bool {
    FIXED_WIDTH_GHOST_INT_TYPE_NAMES.contains(&word)
}

/// The fixed-width type a type expression denotes, if it is exactly one:
/// a fixed-width integer name (optionally path-qualified such as `Std.UInt64`
/// or `core::primitive::u64`) or `BitVec <N>`, optionally wrapped in matched
/// parentheses.
fn fixed_width_type_of(toks: &[GuardTok<'_>]) -> Option<(String, usize)> {
    let mut toks = toks;
    while toks.len() >= 2 && matching_close(toks, 0) == Some(toks.len() - 1) && toks[0].is_sym("(")
    {
        toks = &toks[1..toks.len() - 1];
    }
    let first = toks.first()?;
    if first.kind != GuardTokKind::Word {
        return None;
    }
    if is_fixed_width_int_type_name(first.text) && toks.len() == 1 {
        return Some((String::from(first.text), first.line));
    }
    // Path-qualified fixed-width type (`Std.UInt64`, `core::primitive::u64`).
    if toks.len() >= 3 && toks.len() % 2 == 1 {
        let valid_path = toks.iter().enumerate().all(|(i, t)| {
            if i % 2 == 0 {
                t.kind == GuardTokKind::Word
            } else {
                t.kind == GuardTokKind::PathSep || t.is_sym(".")
            }
        });
        if valid_path
            && let Some(last) = toks.last()
            && is_fixed_width_int_type_name(last.text)
        {
            return Some((String::from(last.text), last.line));
        }
    }
    if first.text == "BitVec" && toks.len() >= 2 {
        let mut width_toks = &toks[1..];
        while width_toks.len() >= 2
            && matching_close(width_toks, 0) == Some(width_toks.len() - 1)
            && width_toks[0].is_sym("(")
        {
            width_toks = &width_toks[1..width_toks.len() - 1];
        }
        let width: Vec<&str> = width_toks.iter().map(|tok| tok.text).collect();
        return Some((format!("BitVec {}", width.join(" ")), first.line));
    }
    None
}

/// Fixed-width integer types beyond the primitive names that a Rust ghost
/// length may be typed at: the `NonZero*` wrappers and the C integer aliases.
pub const RUST_FIXED_WIDTH_WRAPPER_TYPE_NAMES: [&str; 22] = [
    "NonZeroU8",
    "NonZeroU16",
    "NonZeroU32",
    "NonZeroU64",
    "NonZeroU128",
    "NonZeroUsize",
    "NonZeroI8",
    "NonZeroI16",
    "NonZeroI32",
    "NonZeroI64",
    "NonZeroI128",
    "NonZeroIsize",
    "size_t",
    "ssize_t",
    "uintptr_t",
    "intptr_t",
    "c_int",
    "c_uint",
    "c_long",
    "c_ulong",
    "c_longlong",
    "c_ulonglong",
];

/// Text of the first argument of a type constructor (`64`, or the inside of
/// `(2 ^ 64)`), and its tokens.
fn type_argument<'t, 'a>(after: &'t [GuardTok<'a>]) -> Option<(String, &'t [GuardTok<'a>])> {
    let first = after.first()?;
    let arg = if first.is_sym("(") {
        let close = matching_close(after, 0)?;
        &after[1..close]
    } else if first.kind == GuardTokKind::Word {
        &after[..1]
    } else {
        return None;
    };
    let text: Vec<&str> = arg.iter().map(|tok| tok.text).collect();
    Some((text.join(" "), arg))
}

/// Whether a `Fin` bound is a closed machine-width expression (`256`,
/// `2 ^ 64`, `UInt64.size`) rather than a bound that depends on the
/// collection (`Fin (s.cap + 1)`).
fn is_closed_width_bound(bound: &[GuardTok<'_>]) -> bool {
    !bound.is_empty()
        && bound.iter().all(|tok| match tok.kind {
            GuardTokKind::Word => {
                tok.text.starts_with(|first: char| first.is_ascii_digit())
                    || is_fixed_width_int_type_name(tok.text)
                    || tok.text == "size"
            }
            GuardTokKind::Sym => {
                matches!(tok.text, "^" | "*" | "+" | "-" | "/" | "%" | "(" | ")" | ".")
            }
            _ => false,
        })
}

/// Split a token slice on depth-0 occurrences of `sep` (outside `()`, `[]`,
/// `{}`, `<>`, `⟨⟩`).
fn split_top_level_toks<'t, 'a>(
    toks: &'t [GuardTok<'a>],
    is_sep: impl Fn(&GuardTok<'_>) -> bool,
) -> Vec<&'t [GuardTok<'a>]> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut angle = 0i32;
    let mut start = 0usize;
    for (idx, tok) in toks.iter().enumerate() {
        if depth == 0 && angle == 0 && is_sep(tok) {
            parts.push(&toks[start..idx]);
            start = idx + 1;
            continue;
        }
        let delta = bracket_delta(tok);
        if delta != 0 {
            depth += delta;
        } else if depth == 0 {
            if tok.is_sym("<") {
                angle += 1;
            } else if tok.is_sym(">") && angle > 0 {
                angle -= 1;
            }
        }
    }
    parts.push(&toks[start..]);
    parts
}

/// Strip leading Rust field attributes (`#[…]`) and visibility (`pub`,
/// `pub(crate)`, …) from a tuple-struct field type slice.
fn strip_rust_field_prefix<'t, 'a>(mut toks: &'t [GuardTok<'a>]) -> &'t [GuardTok<'a>] {
    loop {
        if toks.first().is_some_and(|t| t.is_sym("#"))
            && toks.get(1).is_some_and(|t| t.is_sym("["))
            && let Some(close) = matching_close(toks, 1)
        {
            toks = &toks[close + 1..];
            continue;
        }
        if toks.first().is_some_and(|t| t.is_word("pub")) {
            toks = &toks[1..];
            if toks.first().is_some_and(|t| t.is_sym("("))
                && let Some(close) = matching_close(toks, 0)
            {
                toks = &toks[close + 1..];
            }
            continue;
        }
        break;
    }
    toks
}

/// Read a leading Rust or Lean path (`A::B::C` or `A.B.C`, optionally with a
/// leading `::`) starting at `start`, returning `(leaf_tok, next_idx)`.
fn read_type_path<'t, 'a>(
    toks: &'t [GuardTok<'a>],
    start: usize,
) -> Option<(&'t GuardTok<'a>, usize)> {
    let mut cursor = start;
    if toks
        .get(cursor)
        .is_some_and(|t| t.kind == GuardTokKind::PathSep)
    {
        cursor += 1;
    }
    let mut leaf = toks.get(cursor).filter(|t| t.kind == GuardTokKind::Word)?;
    cursor += 1;
    while toks
        .get(cursor)
        .is_some_and(|sep| sep.kind == GuardTokKind::PathSep || sep.is_sym("."))
        && let Some(next) = toks
            .get(cursor + 1)
            .filter(|t| t.kind == GuardTokKind::Word)
    {
        leaf = next;
        cursor += 2;
    }
    Some((leaf, cursor))
}

/// Split Lean type arguments (`Arg1 (Arg2 ...) Arg3`) into bracket-balanced
/// slices.
fn split_lean_type_args<'t, 'a>(toks: &'t [GuardTok<'a>]) -> Vec<&'t [GuardTok<'a>]> {
    let mut args = Vec::new();
    let mut idx = 0usize;
    while idx < toks.len() {
        let start = idx;
        if bracket_delta(&toks[idx]) > 0 {
            let mut depth = 0i32;
            while idx < toks.len() {
                depth += bracket_delta(&toks[idx]);
                idx += 1;
                if depth == 0 {
                    break;
                }
            }
            args.push(&toks[start..idx]);
        } else if toks[idx].kind == GuardTokKind::Word {
            idx += 1;
            while toks.get(idx).is_some_and(|sep| sep.is_sym("."))
                && toks
                    .get(idx + 1)
                    .is_some_and(|part| part.kind == GuardTokKind::Word)
            {
                idx += 2;
            }
            args.push(&toks[start..idx]);
        } else {
            idx += 1;
        }
    }
    args
}

/// Resolve a bare or path-qualified fixed-width scalar integer name, Rust
/// wrapper (`NonZeroU64`, `size_t`, …), or module-local alias.
fn resolve_fixed_width_leaf(
    leaf: &GuardTok<'_>,
    aliases: &[(String, String)],
) -> Option<(String, usize)> {
    if is_fixed_width_int_type_name(leaf.text)
        || RUST_FIXED_WIDTH_WRAPPER_TYPE_NAMES.contains(&leaf.text)
    {
        return Some((String::from(leaf.text), leaf.line));
    }
    aliases
        .iter()
        .find(|(alias, _)| alias == leaf.text)
        .map(|(_, underlying)| (underlying.clone(), leaf.line))
}

/// Type constructors whose arguments are element, key, marker, or parameter
/// types rather than the value itself (in addition to
/// [`GHOST_COLLECTION_TYPE_NAMES`]): a fixed-width integer below one of them
/// is not the length.
const ELEMENT_CONTAINER_TYPE_NAMES: [&str; 27] = [
    "Vec",
    "VecDeque",
    "LinkedList",
    "BinaryHeap",
    "HashMap",
    "HashSet",
    "BTreeMap",
    "BTreeSet",
    "IndexMap",
    "IndexSet",
    "List",
    "Array",
    "Set",
    "Map",
    "Vector",
    "Subarray",
    "RBMap",
    "RBTree",
    "AssocList",
    "Stream",
    "Iterator",
    "IntoIterator",
    "PhantomData",
    "fn",
    "Fn",
    "FnMut",
    "FnOnce",
];

fn is_element_container_type_name(name: &str) -> bool {
    GHOST_COLLECTION_TYPE_NAMES.contains(&name) || ELEMENT_CONTAINER_TYPE_NAMES.contains(&name)
}

/// Structurally inspect a type expression for a fixed-width scalar integer
/// length type. Every type constructor is looked through (a wrapper the
/// scanner has never heard of, `Tracked<u64>` or `WithTop UInt64`, is still a
/// machine integer) except the element containers
/// ([`GHOST_COLLECTION_TYPE_NAMES`], [`ELEMENT_CONTAINER_TYPE_NAMES`], slices,
/// arrays) and the error slot of `Result` / `Except`.
///
/// A wrapper does not make a machine integer unbounded, so `Option<u64>`,
/// `Wrapping<u64>`, `NonZero<u64>`, `&u64`, `(u64, bool)`, `Result<u64, E>`,
/// `Option UInt64`, `UInt64 × Bool`, `Except String UInt64`, and
/// `{ n : UInt64 // n < 10 }` are fixed-width, as are `NonZeroU64`, `size_t`,
/// `Std.BitVec 64`, `Fin (2 ^ 64)`, and every name in `aliases`
/// (`abbrev GhostLen := UInt64`, `type GhostLen = u64;`). Conversely,
/// collections and error slots (`GhostSeq<u8>`, `List UInt8`, `&[u8]`,
/// `Result<Nat, u8>`, `Except UInt32 Nat`) are not flagged.
fn fixed_width_type_within(
    toks: &[GuardTok<'_>],
    aliases: &[(String, String)],
) -> Option<(String, usize)> {
    const MAX_TYPE_DEPTH: u32 = 12;
    fn inspect(
        toks: &[GuardTok<'_>],
        aliases: &[(String, String)],
        depth: u32,
    ) -> Option<(String, usize)> {
        if depth == 0 || toks.is_empty() {
            return None;
        }
        let mut toks = toks;
        while toks.len() >= 2
            && toks[0].is_sym("(")
            && matching_close(toks, 0) == Some(toks.len() - 1)
        {
            toks = &toks[1..toks.len() - 1];
        }
        if toks.is_empty() {
            return None;
        }
        if let Some(found) = fixed_width_type_of(toks) {
            return Some(found);
        }
        // Rust slice / array types (`[u8]`, `[u8; 64]`) are collections, not
        // scalar lengths.
        if toks[0].is_sym("[") && matching_close(toks, 0) == Some(toks.len() - 1) {
            return None;
        }
        // Lean subtype `{ n : T // P }` or `{ n : T | P }`.
        if toks[0].is_sym("{") && matching_close(toks, 0) == Some(toks.len() - 1) {
            let inner = &toks[1..toks.len() - 1];
            let mut d = 0i32;
            let mut colon = None;
            let mut pred_sep = None;
            for idx in 0..inner.len() {
                if d == 0 {
                    if colon.is_none() && inner[idx].is_sym(":") {
                        colon = Some(idx);
                    } else if colon.is_some()
                        && (inner[idx].is_sym("|")
                            || (inner[idx].is_sym("/")
                                && inner.get(idx + 1).is_some_and(|n| n.is_sym("/"))))
                    {
                        pred_sep = Some(idx);
                        break;
                    }
                }
                d += bracket_delta(&inner[idx]);
            }
            if let (Some(c), Some(sep)) = (colon, pred_sep) {
                return inspect(&inner[c + 1..sep], aliases, depth - 1);
            }
            return None;
        }
        // Tuples / products at depth 0 (`(u64, bool)`, `UInt64 × Bool`).
        let tuple_parts =
            split_top_level_toks(toks, |t| t.is_sym(",") || t.is_sym("×") || t.is_sym("⊕"));
        if tuple_parts.len() > 1 {
            for part in tuple_parts {
                if let Some(found) = inspect(part, aliases, depth - 1) {
                    return Some(found);
                }
            }
            return None;
        }
        // `impl Trait<…> + …` / `dyn Trait<…> + …`.
        if toks[0].is_word("impl") || toks[0].is_word("dyn") {
            return split_top_level_toks(&toks[1..], |t| t.is_sym("+"))
                .into_iter()
                .find_map(|bound| inspect(bound, aliases, depth - 1));
        }
        // Qualified path `<T as Trait>::Assoc`: judged by its self type.
        if toks[0].is_sym("<") {
            let close = skip_rust_generics(toks, 0);
            if close > 1 && close <= toks.len() {
                let inner = &toks[1..close - 1];
                let self_end = inner
                    .iter()
                    .position(|t| t.is_word("as"))
                    .unwrap_or(inner.len());
                return inspect(&inner[..self_end], aliases, depth - 1);
            }
            return None;
        }
        // Rust reference (`&'a mut T`, `&T`) or raw pointer (`*const T`, `*mut T`).
        if toks[0].is_sym("&") {
            let mut cursor = 1usize;
            if toks.get(cursor).is_some_and(|t| t.is_sym("'"))
                && toks
                    .get(cursor + 1)
                    .is_some_and(|t| t.kind == GuardTokKind::Word)
            {
                cursor += 2;
            }
            if toks.get(cursor).is_some_and(|t| t.is_word("mut")) {
                cursor += 1;
            }
            return inspect(&toks[cursor..], aliases, depth - 1);
        }
        if toks[0].is_sym("*")
            && toks
                .get(1)
                .is_some_and(|t| t.is_word("const") || t.is_word("mut"))
        {
            return inspect(&toks[2..], aliases, depth - 1);
        }
        // Path-headed type (`u64`, `core::num::NonZeroU64`, `Std.BitVec 64`,
        // `Fin (2 ^ 64)`, `Option<u64>`, `Result<u64, E>`, `Option UInt64`,
        // `Except String UInt64`, `GhostSeq<u8>`, `List UInt8`, …).
        let (head, after_head) = read_type_path(toks, 0)?;
        if after_head == toks.len() {
            return resolve_fixed_width_leaf(head, aliases);
        }
        if head.text == "BitVec"
            && let Some((width, _)) = type_argument(&toks[after_head..])
        {
            return Some((format!("BitVec {width}"), head.line));
        }
        if head.text == "Fin"
            && let Some((bound, bound_toks)) = type_argument(&toks[after_head..])
            && is_closed_width_bound(bound_toks)
        {
            return Some((format!("Fin {bound}"), head.line));
        }
        // Rust generic wrapper `Head<Arg1, Arg2, …>`.
        if toks.get(after_head).is_some_and(|t| t.is_sym("<")) {
            let close = skip_rust_generics(toks, after_head);
            if close > after_head + 1 && close == toks.len() {
                let raw_args =
                    split_top_level_toks(&toks[after_head + 1..close - 1], |t| t.is_sym(","));
                let type_args: Vec<&[GuardTok<'_>]> = raw_args
                    .into_iter()
                    .filter(|arg| !arg.is_empty() && !arg.first().is_some_and(|t| t.is_sym("'")))
                    .collect();
                if is_element_container_type_name(head.text) {
                    return None;
                }
                // The error slot of a `Result` does not carry the length.
                let value_args = if head.text == "Result" {
                    &type_args[..type_args.len().min(1)]
                } else {
                    &type_args[..]
                };
                return value_args
                    .iter()
                    .find_map(|arg| inspect(arg, aliases, depth - 1));
            }
            return None;
        }
        // Lean type application `Head Arg1 Arg2 …`.
        let lean_args = split_lean_type_args(&toks[after_head..]);
        if is_element_container_type_name(head.text) {
            return None;
        }
        // The error slot of `Except ε α` / `ExceptT ε m α` is not the length.
        let value_args = if matches!(head.text, "Except" | "ExceptT") {
            lean_args.get(1..).unwrap_or(&[])
        } else {
            &lean_args[..]
        };
        value_args
            .iter()
            .find_map(|arg| inspect(arg, aliases, depth - 1))
    }
    inspect(toks, aliases, MAX_TYPE_DEPTH)
}

/// Whether a Lean expression is a type (applications, products, arrows,
/// numerals, or subtypes `{ x : T // P }`) rather than a proposition or a
/// term: no top-level relation, connective, binder, or literal occurs in it.
fn is_lean_type_expression(toks: &[GuardTok<'_>]) -> bool {
    if toks.is_empty() {
        return false;
    }
    let mut idx = 0usize;
    while idx < toks.len() {
        let tok = &toks[idx];
        if tok.is_sym("{")
            && let Some(close) = matching_close(toks, idx)
        {
            // Lean subtype `{ x : T // P }` or `{ x : T | P }`: validate `T`
            // as a type expression and skip over the predicate `P`.
            let inner = &toks[idx + 1..close];
            let mut d = 0i32;
            let mut colon = None;
            let mut pred_sep = None;
            for pos in 0..inner.len() {
                if d == 0 {
                    if colon.is_none() && inner[pos].is_sym(":") {
                        colon = Some(pos);
                    } else if colon.is_some()
                        && (inner[pos].is_sym("|")
                            || (inner[pos].is_sym("/")
                                && inner.get(pos + 1).is_some_and(|n| n.is_sym("/"))))
                    {
                        pred_sep = Some(pos);
                        break;
                    }
                }
                d += bracket_delta(&inner[pos]);
            }
            let Some((c, sep)) = colon.zip(pred_sep) else {
                return false;
            };
            if !is_lean_type_expression(&inner[c + 1..sep]) {
                return false;
            }
            idx = close + 1;
            continue;
        }
        let ok = match tok.kind {
            GuardTokKind::Word => !matches!(
                tok.text,
                "fun" | "λ" | "match" | "if" | "then" | "else" | "let" | "by" | "do" | "forall"
            ),
            GuardTokKind::Sym => {
                matches!(
                    tok.text,
                    "." | "(" | ")" | "×" | "→" | "->" | "^" | "*" | "+" | "-" | "/" | "%" | "⊕"
                )
            }
            _ => false,
        };
        if !ok {
            return false;
        }
        idx += 1;
    }
    true
}

/// The result type of a Lean type: what follows its last depth-0 arrow
/// (`A → B → R`) or universal binder (`∀ x, R` / `Π x, R`).
fn lean_result_type<'t, 'a>(ty: &'t [GuardTok<'a>]) -> &'t [GuardTok<'a>] {
    let mut depth = 0i32;
    let mut result_start = 0usize;
    let mut saw_quantifier = false;
    for (offset, ty_tok) in ty.iter().enumerate() {
        if depth == 0 {
            if ty_tok.is_sym("∀") || ty_tok.is_sym("Π") || ty_tok.is_word("forall") {
                saw_quantifier = true;
            } else if ty_tok.is_sym("→") || ty_tok.is_sym("->") {
                result_start = offset + 1;
                saw_quantifier = false;
            } else if saw_quantifier && ty_tok.is_sym(",") {
                result_start = offset + 1;
                saw_quantifier = false;
            }
        }
        depth += bracket_delta(ty_tok);
    }
    &ty[result_start..]
}

/// The fixed-width type of a Lean result or field type. A type expression is
/// searched for a fixed-width type anywhere inside it; anything else (the
/// statement of a `theorem`, a proposition such as `s.len < UInt64.size`)
/// must be exactly one.
fn lean_fixed_width_result(
    result: &[GuardTok<'_>],
    is_statement: bool,
    aliases: &[(String, String)],
) -> Option<(String, usize)> {
    if !is_statement && is_lean_type_expression(result) {
        fixed_width_type_within(result, aliases)
    } else {
        fixed_width_type_of(result)
    }
}

/// Module-local names of fixed-width types and the type each stands for:
/// Lean `abbrev GhostLen := UInt64` / `def GhostLen : Type := BitVec 64`,
/// Rust `type GhostLen = u64;` and the newtype `struct GhostLen(u64);`.
/// Aliases of aliases are resolved.
fn collect_fixed_width_type_aliases(
    toks: &[GuardTok<'_>],
    dialect: SpecSourceDialect,
) -> Vec<(String, String)> {
    let mut aliases: Vec<(String, String)> = Vec::new();
    loop {
        let known = aliases.len();
        for idx in 0..toks.len() {
            let tok = &toks[idx];
            let mut candidate: Option<(String, &[GuardTok<'_>])> = None;
            if dialect != SpecSourceDialect::Lean
                && tok.is_word("type")
                && let Some(name) = toks.get(idx + 1).filter(|t| t.kind == GuardTokKind::Word)
            {
                let assign = skip_rust_generics(toks, idx + 2);
                if toks.get(assign).is_some_and(|eq| eq.is_sym("=")) {
                    let mut end = assign + 1;
                    while end < toks.len() && !toks[end].is_sym(";") {
                        end += 1;
                    }
                    candidate = Some((String::from(name.text), &toks[assign + 1..end]));
                }
            } else if dialect != SpecSourceDialect::Lean && tok.is_word("use") {
                // `use core::primitive::u64 as Len;`
                let mut end = idx + 1;
                while end < toks.len() && !toks[end].is_sym(";") {
                    end += 1;
                }
                if end >= idx + 4
                    && end <= toks.len()
                    && toks[end - 2].is_word("as")
                    && toks[end - 1].kind == GuardTokKind::Word
                {
                    candidate = Some((String::from(toks[end - 1].text), &toks[idx + 1..end - 2]));
                }
            } else if dialect != SpecSourceDialect::Lean
                && tok.is_word("struct")
                && let Some(name) = toks.get(idx + 1).filter(|t| t.kind == GuardTokKind::Word)
            {
                let open = skip_rust_generics(toks, idx + 2);
                if toks.get(open).is_some_and(|brace| brace.is_sym("{"))
                    && let Some(close) = matching_close(toks, open)
                {
                    // A struct with a single named field (`struct Len { n: u64 }`)
                    // is a newtype as well.
                    let fields = split_top_level_toks(&toks[open + 1..close], |t| t.is_sym(","));
                    let non_empty: Vec<&[GuardTok<'_>]> =
                        fields.into_iter().filter(|f| !f.is_empty()).collect();
                    if non_empty.len() == 1 {
                        let field = strip_rust_field_prefix(non_empty[0]);
                        if field.len() > 2
                            && field[0].kind == GuardTokKind::Word
                            && field[1].is_sym(":")
                        {
                            candidate = Some((String::from(name.text), &field[2..]));
                        }
                    }
                } else if toks.get(open).is_some_and(|paren| paren.is_sym("("))
                    && let Some(close) = matching_close(toks, open)
                {
                    let fields = split_top_level_toks(&toks[open + 1..close], |t| t.is_sym(","));
                    let non_empty: Vec<&[GuardTok<'_>]> =
                        fields.into_iter().filter(|f| !f.is_empty()).collect();
                    if non_empty.len() == 1 {
                        candidate = Some((
                            String::from(name.text),
                            strip_rust_field_prefix(non_empty[0]),
                        ));
                    }
                }
            }
            if candidate.is_none()
                && dialect != SpecSourceDialect::Rust
                && (tok.is_word("abbrev") || tok.is_word("def"))
            {
                let (name, after_name) = read_lean_dotted_name(toks, idx + 1);
                let end = lean_command_end(toks, after_name);
                let header_ok = |header: &[GuardTok<'_>]| {
                    header.is_empty()
                        || (header.len() >= 2 && header[0].is_sym(":") && header[1].is_word("Type"))
                };
                if !name.is_empty()
                    && let Some(assign) =
                        (after_name..end).find(|cursor| toks[*cursor].is_sym(":="))
                    && header_ok(&toks[after_name..assign])
                    && is_lean_type_expression(&toks[assign + 1..end])
                {
                    candidate = Some((
                        String::from(declaration_leaf(&name)),
                        &toks[assign + 1..end],
                    ));
                }
            }
            if let Some((name, body)) = candidate
                && !aliases.iter().any(|(alias, _)| *alias == name)
                && let Some((underlying, _)) = fixed_width_type_within(body, &aliases)
            {
                aliases.push((name, underlying));
            }
        }
        if aliases.len() == known {
            return aliases;
        }
    }
}

/// Index of the opening `(` matching the `)` at `close_idx`.
fn matching_open_paren(toks: &[GuardTok<'_>], close_idx: usize) -> Option<usize> {
    if !toks.get(close_idx).is_some_and(|t| t.is_sym(")")) {
        return None;
    }
    let mut depth = 0usize;
    for idx in (0..=close_idx).rev() {
        if toks[idx].is_sym(")") {
            depth += 1;
        } else if toks[idx].is_sym("(") {
            depth -= 1;
            if depth == 0 {
                return Some(idx);
            }
        }
    }
    None
}

/// Whether `tok` terminates an unparenthesized Lean function argument
/// (relational/logical/arithmetic operator or delimiter).
fn is_lean_unparen_arg_stop(tok: &GuardTok<'_>) -> bool {
    if tok.kind == GuardTokKind::Word && LEAN_COMMAND_KEYWORDS.contains(&tok.text) {
        return true;
    }
    tok.kind == GuardTokKind::Sym
        && matches!(
            tok.text,
            "=" | "≠"
                | "!="
                | "<"
                | ">"
                | "<="
                | ">="
                | "≤"
                | "≥"
                | "∧"
                | "∨"
                | "/\\"
                | "\\/"
                | "&&"
                | "||"
                | "→"
                | "->"
                | "↔"
                | "<->"
                | "+"
                | "-"
                | "*"
                | "/"
                | "%"
                | ","
                | ")"
                | "]"
                | "}"
                | ":="
                | "|"
                | ";"
        )
}

fn mentions_ghost_collection(toks: &[GuardTok<'_>]) -> bool {
    toks.iter().any(|tok| {
        tok.kind == GuardTokKind::Word && GHOST_COLLECTION_TYPE_NAMES.contains(&tok.text)
    })
}

/// Index of the token closing the bracket opened at `open_idx`.
fn matching_close(toks: &[GuardTok<'_>], open_idx: usize) -> Option<usize> {
    let (open, close) = match toks.get(open_idx)?.text {
        "(" => ("(", ")"),
        "[" => ("[", "]"),
        "{" => ("{", "}"),
        _ => return None,
    };
    let mut depth = 0usize;
    for (idx, tok) in toks.iter().enumerate().skip(open_idx) {
        if tok.kind != GuardTokKind::Sym {
            continue;
        }
        if tok.text == open {
            depth += 1;
        } else if tok.text == close {
            depth -= 1;
            if depth == 0 {
                return Some(idx);
            }
        }
    }
    None
}

fn bracket_delta(tok: &GuardTok<'_>) -> i32 {
    if tok.kind != GuardTokKind::Sym {
        return 0;
    }
    match tok.text {
        "(" | "[" | "{" | "⟨" => 1,
        ")" | "]" | "}" | "⟩" => -1,
        _ => 0,
    }
}

/// Consume a dotted Lean identifier starting at `start`, returning
/// `(name, next_idx)`.
fn read_lean_dotted_name(toks: &[GuardTok<'_>], start: usize) -> (String, usize) {
    let mut cursor = start;
    let mut name = String::new();
    while let Some(part) = toks.get(cursor) {
        if part.kind != GuardTokKind::Word {
            break;
        }
        name.push_str(part.text);
        cursor += 1;
        if toks.get(cursor).is_some_and(|dot| dot.is_sym("."))
            && toks
                .get(cursor + 1)
                .is_some_and(|next| next.kind == GuardTokKind::Word)
        {
            name.push('.');
            cursor += 1;
        } else {
            break;
        }
    }
    (name, cursor)
}

/// An open Lean `namespace` or `section` block.
#[derive(Clone, Debug)]
enum LeanScope {
    Namespace(String),
    Section(Option<String>),
}

/// Qualify `name` with the active Lean `namespace` scopes (ignoring `section`
/// scopes).
fn qualify_lean_name(scopes: &[LeanScope], name: &str) -> String {
    let namespaces: Vec<&str> = scopes
        .iter()
        .filter_map(|scope| match scope {
            LeanScope::Namespace(ns) => Some(ns.as_str()),
            LeanScope::Section(_) => None,
        })
        .collect();
    if namespaces.is_empty() {
        String::from(name)
    } else {
        format!("{}.{name}", namespaces.join("."))
    }
}

/// Scan Lean declarations (`def`, `axiom`, `opaque`, `abbrev`, `theorem`,
/// `lemma`) and ghost `structure` / `class` fields for ghost length specs with
/// a fixed-width result or field type, tracking enclosing `namespace` and
/// `section` scopes.
fn scan_lean_ghost_length_decls(
    source_label: &str,
    toks: &[GuardTok<'_>],
    aliases: &[(String, String)],
    out: &mut Vec<GhostLengthWidthDiagnostic>,
) {
    let mut scopes: Vec<LeanScope> = Vec::new();
    let mut idx = 0usize;
    while idx < toks.len() {
        let tok = &toks[idx];
        if tok.is_word("namespace") {
            let (ns, next) = read_lean_dotted_name(toks, idx + 1);
            if !ns.is_empty() {
                for part in ns.split('.') {
                    scopes.push(LeanScope::Namespace(String::from(part)));
                }
            }
            idx = next.max(idx + 1);
            continue;
        }
        if tok.is_word("section") {
            let has_same_line_name = toks.get(idx + 1).is_some_and(|next| {
                next.line == tok.line
                    && next.kind == GuardTokKind::Word
                    && !LEAN_COMMAND_KEYWORDS.contains(&next.text)
            });
            if has_same_line_name {
                let (name, next) = read_lean_dotted_name(toks, idx + 1);
                scopes.push(LeanScope::Section(Some(name)));
                idx = next.max(idx + 1);
            } else {
                scopes.push(LeanScope::Section(None));
                idx += 1;
            }
            continue;
        }
        if tok.is_word("end") {
            let has_same_line_name = toks.get(idx + 1).is_some_and(|next| {
                next.line == tok.line
                    && next.kind == GuardTokKind::Word
                    && !LEAN_COMMAND_KEYWORDS.contains(&next.text)
            });
            if !has_same_line_name {
                scopes.pop();
                idx += 1;
            } else {
                let (ns, next) = read_lean_dotted_name(toks, idx + 1);
                if matches!(scopes.last(), Some(LeanScope::Section(Some(sec))) if *sec == ns) {
                    scopes.pop();
                } else {
                    let parts: Vec<&str> = ns.split('.').collect();
                    for _ in 0..parts.len() {
                        if scopes.pop().is_none() {
                            break;
                        }
                    }
                }
                idx = next.max(idx + 1);
            }
            continue;
        }
        // Lean ghost `structure` / `class` fields
        // (`structure GhostBuf where len : UInt64`,
        // `class HasGhostLen (α : Type) where ghostLen : α → UInt64`).
        if tok.is_word("structure") || tok.is_word("class") {
            let (raw_name, mut cursor) = read_lean_dotted_name(toks, idx + 1);
            if raw_name.is_empty() {
                idx += 1;
                continue;
            }
            let struct_name = qualify_lean_name(&scopes, &raw_name);
            let header_start = cursor;
            while let Some(t) = toks.get(cursor) {
                if t.is_word("where")
                    || (t.kind == GuardTokKind::Word && LEAN_COMMAND_KEYWORDS.contains(&t.text))
                {
                    break;
                }
                cursor += 1;
            }
            let header = &toks[header_start..cursor];
            if !toks.get(cursor).is_some_and(|t| t.is_word("where")) {
                idx = cursor.max(idx + 1);
                continue;
            }
            let fields_start = cursor + 1;
            let mut fields_end = fields_start;
            let mut depth = 0i32;
            while let Some(t) = toks.get(fields_end) {
                if depth == 0
                    && (t.is_word("deriving")
                        || (t.kind == GuardTokKind::Word
                            && LEAN_COMMAND_KEYWORDS.contains(&t.text)))
                {
                    break;
                }
                depth += bracket_delta(t);
                fields_end += 1;
            }
            let fields = &toks[fields_start..fields_end];
            let ghost_struct = has_ghost_name_marker(&struct_name)
                || struct_name
                    .split('.')
                    .any(|part| GHOST_COLLECTION_TYPE_NAMES.contains(&part))
                || mentions_ghost_collection(header)
                || mentions_ghost_collection(fields);
            if ghost_struct {
                let mut f = 0usize;
                while f < fields.len() {
                    if fields[f].kind == GuardTokKind::Word
                        && fields.get(f + 1).is_some_and(|c| c.is_sym(":"))
                    {
                        let field_name = fields[f].text;
                        let ty_start = f + 2;
                        let mut ty_end = ty_start;
                        let mut d = 0i32;
                        while let Some(ft) = fields.get(ty_end) {
                            if d == 0 {
                                if ft.is_sym(":=") {
                                    break;
                                }
                                // Next field starts on a new line with `<ident> :`.
                                if ty_end > ty_start
                                    && ft.line > fields[f].line
                                    && ft.kind == GuardTokKind::Word
                                    && fields.get(ty_end + 1).is_some_and(|c| c.is_sym(":"))
                                {
                                    break;
                                }
                            }
                            d += bracket_delta(ft);
                            ty_end += 1;
                        }
                        if is_ghost_length_name(field_name)
                            && let Some((fixed_width_type, line)) = lean_fixed_width_result(
                                lean_result_type(&fields[ty_start..ty_end]),
                                false,
                                aliases,
                            )
                        {
                            out.push(GhostLengthWidthDiagnostic {
                                source_label: String::from(source_label),
                                line,
                                declaration: format!("{struct_name}.{field_name}"),
                                fixed_width_type,
                                kind: GhostLengthWidthKind::FixedWidthReturnType,
                            });
                        }
                        f = ty_end.max(f + 1);
                    } else {
                        f += 1;
                    }
                }
            }
            idx = fields_end.max(idx + 1);
            continue;
        }
        if !(tok.kind == GuardTokKind::Word && LEAN_TYPED_DECL_KEYWORDS.contains(&tok.text)) {
            idx += 1;
            continue;
        }
        let (raw_name, cursor) = read_lean_dotted_name(toks, idx + 1);
        if raw_name.is_empty() {
            idx += 1;
            continue;
        }
        let name = qualify_lean_name(&scopes, &raw_name);
        // Signature: up to `:=`, `where`, a match-arm `|`, or the next command.
        let sig_start = cursor;
        let mut depth = 0i32;
        let mut sig_end = cursor;
        while let Some(sig_tok) = toks.get(sig_end) {
            if depth == 0
                && (sig_tok.is_sym(":=")
                    || sig_tok.is_sym("|")
                    || sig_tok.is_word("where")
                    || (sig_tok.kind == GuardTokKind::Word
                        && LEAN_COMMAND_KEYWORDS.contains(&sig_tok.text)))
            {
                break;
            }
            depth += bracket_delta(sig_tok);
            sig_end += 1;
        }
        let signature = &toks[sig_start..sig_end];
        idx = sig_end.max(idx + 1);

        // The first depth-0 `:` separates the binders from the result type.
        let mut depth = 0i32;
        let mut colon = None;
        for (offset, sig_tok) in signature.iter().enumerate() {
            if depth == 0 && sig_tok.is_sym(":") {
                colon = Some(offset);
                break;
            }
            depth += bracket_delta(sig_tok);
        }
        let Some(colon) = colon else { continue };
        let ty = &signature[colon + 1..];
        // The result type follows the last depth-0 arrow (`→`, `->`) or
        // universal quantifier binder separator (`∀ …, T` / `Π …, T`).
        let is_statement = matches!(tok.text, "theorem" | "lemma");
        let Some((fixed_width_type, line)) =
            lean_fixed_width_result(lean_result_type(ty), is_statement, aliases)
        else {
            continue;
        };
        let ghost_context = has_ghost_name_marker(&name)
            || mentions_ghost_collection(signature)
            || name
                .split('.')
                .any(|part| GHOST_COLLECTION_TYPE_NAMES.contains(&part));
        if ghost_context && is_ghost_length_name(&name) {
            out.push(GhostLengthWidthDiagnostic {
                source_label: String::from(source_label),
                line,
                declaration: name,
                fixed_width_type,
                kind: GhostLengthWidthKind::FixedWidthReturnType,
            });
        }
    }
}

/// Scan Lean source for casts of a collection length into a fixed-width type:
/// `UInt64.ofNat xs.length`, `USize.ofNat (xs.length + 1)`,
/// `BitVec.ofNat 64 xs.length`, `Nat.toUInt64 xs.length`,
/// `xs.length.toUInt64`, `(xs.length).toUSize`, `(List.length xs).toUInt64`,
/// `(xs.length + 1).toUInt64`.
fn scan_lean_wraparound_casts(
    source_label: &str,
    toks: &[GuardTok<'_>],
    aliases: &[(String, String)],
    out: &mut Vec<GhostLengthWidthDiagnostic>,
) {
    /// Maximum tokens inspected after an unparenthesized cast function.
    const OF_NAT_WINDOW: usize = 8;
    let is_length_projection = |at: usize| {
        toks.get(at).is_some_and(|dot| dot.is_sym("."))
            && toks.get(at + 1).is_some_and(|proj| {
                proj.kind == GuardTokKind::Word && GHOST_LENGTH_PROJECTIONS.contains(&proj.text)
            })
    };
    let arg_span = |mut arg_start: usize, cast_line: usize| -> (usize, usize) {
        // Skip Lean low-precedence application operators (`<|`, lexed as
        // `<` `|`, and `$`).
        if toks.get(arg_start).is_some_and(|t| t.is_sym("<"))
            && toks.get(arg_start + 1).is_some_and(|t| t.is_sym("|"))
        {
            arg_start += 2;
        } else if toks.get(arg_start).is_some_and(|t| t.is_sym("$")) {
            arg_start += 1;
        }
        if toks.get(arg_start).is_some_and(|open| open.is_sym("(")) {
            let end = matching_close(toks, arg_start).unwrap_or(toks.len());
            (arg_start, end)
        } else {
            let line = toks.get(arg_start).map_or(cast_line, |arg| arg.line);
            let mut end = arg_start;
            while end < toks.len()
                && end < arg_start + OF_NAT_WINDOW
                && toks[end].line == line
                && !is_lean_unparen_arg_stop(&toks[end])
            {
                end += 1;
            }
            (arg_start, end)
        }
    };

    for idx in 0..toks.len() {
        let tok = &toks[idx];
        // Type ascription `(<expr containing .length> : <Fixed>)`, which
        // coerces the length into the machine type. Reject control-flow or
        // relational expressions on the LHS (`(if xs.length == 0 then 0 else 1 : UInt64)`).
        if tok.is_sym("(")
            && let Some(close) = matching_close(toks, idx)
        {
            let mut depth = 0i32;
            let mut colon = None;
            for pos in idx + 1..close {
                if depth == 0 && toks[pos].is_sym(":") {
                    colon = Some(pos);
                    break;
                }
                depth += bracket_delta(&toks[pos]);
            }
            if let Some(colon) = colon {
                let lhs = &toks[idx + 1..colon];
                let mut lhs_depth = 0i32;
                let mut lhs_is_control_or_rel = false;
                for lt in lhs {
                    if lhs_depth == 0
                        && ((lt.kind == GuardTokKind::Word
                            && matches!(
                                lt.text,
                                "if" | "then" | "else" | "match" | "with" | "fun" | "λ" | "forall"
                            ))
                            || (lt.kind == GuardTokKind::Sym
                                && matches!(
                                    lt.text,
                                    "=" | "=="
                                        | "!="
                                        | "≠"
                                        | "<"
                                        | ">"
                                        | "<="
                                        | ">="
                                        | "≤"
                                        | "≥"
                                        | "∧"
                                        | "∨"
                                        | "/\\"
                                        | "\\/"
                                        | "&&"
                                        | "||"
                                        | "→"
                                        | "->"
                                        | "↔"
                                        | "<->"
                                        | "∀"
                                        | "∃"
                                        | ","
                                        | ";"
                                )))
                    {
                        lhs_is_control_or_rel = true;
                        break;
                    }
                    lhs_depth += bracket_delta(lt);
                }
                if !lhs_is_control_or_rel
                    && (idx + 1..colon).any(is_length_projection)
                    && let Some((fixed_width_type, _)) =
                        fixed_width_type_within(&toks[colon + 1..close], aliases)
                            .filter(|_| is_lean_type_expression(&toks[colon + 1..close]))
                {
                    out.push(GhostLengthWidthDiagnostic {
                        source_label: String::from(source_label),
                        line: tok.line,
                        declaration: String::new(),
                        fixed_width_type,
                        kind: GhostLengthWidthKind::WraparoundCast,
                    });
                }
            }
        }
        // `<Fixed>.ofNat <expr>`, `<Fixed>.ofNatTruncate <expr>`, `<Fixed>.ofInt <expr>`
        if tok.kind == GuardTokKind::Word
            && is_fixed_width_int_type_name(tok.text)
            && toks.get(idx + 1).is_some_and(|dot| dot.is_sym("."))
            && toks.get(idx + 2).is_some_and(|ctor| {
                ctor.kind == GuardTokKind::Word
                    && matches!(ctor.text, "ofNat" | "ofNatTruncate" | "ofInt")
            })
        {
            let (arg_start, arg_end) = arg_span(idx + 3, tok.line);
            if (arg_start..arg_end).any(is_length_projection) {
                out.push(GhostLengthWidthDiagnostic {
                    source_label: String::from(source_label),
                    line: tok.line,
                    declaration: String::new(),
                    fixed_width_type: String::from(tok.text),
                    kind: GhostLengthWidthKind::WraparoundCast,
                });
            }
        }
        // `BitVec.ofNat <width> <expr>` / `BitVec.ofInt <width> <expr>`
        if tok.is_word("BitVec")
            && toks.get(idx + 1).is_some_and(|dot| dot.is_sym("."))
            && toks.get(idx + 2).is_some_and(|ctor| {
                ctor.kind == GuardTokKind::Word && matches!(ctor.text, "ofNat" | "ofInt")
            })
            && let Some(width_tok) = toks.get(idx + 3)
        {
            let (width_label, val_start) = if width_tok.is_sym("(")
                && let Some(close) = matching_close(toks, idx + 3)
            {
                let inner: Vec<&str> = toks[idx + 4..close].iter().map(|t| t.text).collect();
                (format!("BitVec {}", inner.join(" ")), close + 1)
            } else {
                (format!("BitVec {}", width_tok.text), idx + 4)
            };
            let (arg_start, arg_end) = arg_span(val_start, tok.line);
            if (arg_start..arg_end).any(is_length_projection) {
                out.push(GhostLengthWidthDiagnostic {
                    source_label: String::from(source_label),
                    line: tok.line,
                    declaration: String::new(),
                    fixed_width_type: width_label,
                    kind: GhostLengthWidthKind::WraparoundCast,
                });
            }
        }
        // `Nat.toUInt64 <expr>` / `Int.toInt64 <expr>` / `Nat.toUSize …`
        if (tok.is_word("Nat") || tok.is_word("Int"))
            && toks.get(idx + 1).is_some_and(|dot| dot.is_sym("."))
            && let Some(cast) = toks.get(idx + 2)
            && cast.kind == GuardTokKind::Word
            && LEAN_TO_FIXED_WIDTH_CASTS.contains(&cast.text)
        {
            let (arg_start, arg_end) = arg_span(idx + 3, cast.line);
            if (arg_start..arg_end).any(is_length_projection) {
                out.push(GhostLengthWidthDiagnostic {
                    source_label: String::from(source_label),
                    line: cast.line,
                    declaration: String::new(),
                    fixed_width_type: String::from(&cast.text[2..]),
                    kind: GhostLengthWidthKind::WraparoundCast,
                });
            }
        }
        // Dot-projected `…toUInt64` / `…toUSize`: catches `xs.length.toUSize`,
        // `(xs.length).toUInt64`, `(List.length xs).toUInt64`, and
        // `(xs.length + 1).toUInt64`.
        if tok.is_sym(".")
            && let Some(cast) = toks.get(idx + 1)
            && cast.kind == GuardTokKind::Word
            && LEAN_TO_FIXED_WIDTH_CASTS.contains(&cast.text)
            && idx >= 2
        {
            // `xs.length |>.toUInt64`: the receiver precedes the pipeline
            // operator (lexed as `|` `>`).
            let base = if toks[idx - 1].is_sym(">") && toks[idx - 2].is_sym("|") {
                idx - 2
            } else {
                idx
            };
            let has_len = base >= 2
                && if toks[base - 1].is_sym(")")
                    && let Some(open) = matching_open_paren(toks, base - 1)
                {
                    (open..base).any(is_length_projection)
                } else {
                    is_length_projection(base - 2)
                };
            if has_len {
                out.push(GhostLengthWidthDiagnostic {
                    source_label: String::from(source_label),
                    line: cast.line,
                    declaration: String::new(),
                    fixed_width_type: String::from(&cast.text[2..]),
                    kind: GhostLengthWidthKind::WraparoundCast,
                });
            }
        }
    }
}

/// Ghost context an attribute places the following Rust item in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RustGhostAttr {
    /// `#[model]`: the item itself is ghost code.
    Model,
    /// `#[spec]`, `#[embed_spec]`, `#[external_spec]`, `#[invariant]`: a
    /// runtime item carrying a specification.
    Spec,
}

/// Classify the attribute whose `[` is at `open_idx` by the last segment of
/// its path (`#[model]`, `#[anneal_spec::model]`, `#[spec(…)]`). A
/// `#[cfg_attr(predicate, attr, …)]` is classified by its conditional
/// attributes, since the predicate may hold in the verified configuration.
fn rust_ghost_attr(toks: &[GuardTok<'_>], open_idx: usize) -> Option<RustGhostAttr> {
    /// Maximum nesting of `cfg_attr` followed.
    const MAX_CFG_ATTR_DEPTH: usize = 8;
    let close = matching_close(toks, open_idx).unwrap_or(toks.len());
    rust_ghost_attr_body(&toks[open_idx + 1..close], MAX_CFG_ATTR_DEPTH)
}

/// Classify an attribute body (the tokens inside `#[…]`).
fn rust_ghost_attr_body(attr: &[GuardTok<'_>], fuel: usize) -> Option<RustGhostAttr> {
    let mut cursor = 0usize;
    let mut leaf = None;
    while let Some(tok) = attr.get(cursor) {
        match tok.kind {
            GuardTokKind::Word => leaf = Some(tok.text),
            GuardTokKind::PathSep => {}
            _ => break,
        }
        cursor += 1;
    }
    match leaf? {
        "model" => Some(RustGhostAttr::Model),
        "spec" | "embed_spec" | "external_spec" | "invariant" => Some(RustGhostAttr::Spec),
        "cfg_attr" if fuel > 0 && attr.get(cursor).is_some_and(|open| open.is_sym("(")) => {
            let close = matching_close(attr, cursor)?;
            let args = &attr[cursor + 1..close];
            let mut found = None;
            let mut depth = 0i32;
            let mut start = 0usize;
            let mut index = 0usize;
            for pos in 0..=args.len() {
                let at_end = pos == args.len();
                if at_end || (depth == 0 && args[pos].is_sym(",")) {
                    // The first argument is the predicate.
                    if index > 0 {
                        match rust_ghost_attr_body(&args[start..pos], fuel - 1) {
                            Some(RustGhostAttr::Model) => return Some(RustGhostAttr::Model),
                            Some(RustGhostAttr::Spec) => found = Some(RustGhostAttr::Spec),
                            None => {}
                        }
                    }
                    start = pos + 1;
                    index += 1;
                } else {
                    depth += bracket_delta(&args[pos]);
                }
            }
            found
        }
        _ => None,
    }
}

/// Scan a Rust token slice for `.len() as <fixed>`, `(<expr with .len()>) as <fixed>`,
/// or `<fixed>::{from,try_from,new}(<expr with .len()>)` wraparound casts (including
/// path-qualified types, C aliases, and module-local aliases).
fn scan_rust_slice_wraparound_casts(
    source_label: &str,
    declaration: &str,
    toks: &[GuardTok<'_>],
    aliases: &[(String, String)],
    require_ghost_receiver: bool,
    out: &mut Vec<GhostLengthWidthDiagnostic>,
) {
    let is_len_call_at = |at: usize| -> bool {
        toks.get(at).is_some_and(|dot| dot.is_sym("."))
            && toks.get(at + 1).is_some_and(|proj| {
                proj.kind == GuardTokKind::Word && GHOST_LENGTH_PROJECTIONS.contains(&proj.text)
            })
            && toks.get(at + 2).is_some_and(|o| o.is_sym("("))
            && toks.get(at + 3).is_some_and(|c| c.is_sym(")"))
    };
    let receiver_is_ghost = |dot_idx: usize| -> bool {
        if !require_ghost_receiver {
            return true;
        }
        toks.get(dot_idx.saturating_sub(1)).is_some_and(|recv| {
            recv.kind == GuardTokKind::Word
                && (has_ghost_name_marker(recv.text)
                    || GHOST_COLLECTION_TYPE_NAMES.contains(&recv.text))
        })
    };
    for idx in 0..toks.len() {
        // `<expr with .len()> as <FixedPath>`
        if toks[idx].is_word("as")
            && let Some((leaf, _)) = read_type_path(toks, idx + 1)
            && let Some((fixed_width_type, line)) = resolve_fixed_width_leaf(leaf, aliases)
        {
            let matched = if idx >= 4 && is_len_call_at(idx - 4) && receiver_is_ghost(idx - 4) {
                true
            } else if idx >= 1
                && toks[idx - 1].is_sym(")")
                && let Some(open) = matching_open_paren(toks, idx - 1)
            {
                (open..idx).any(|at| is_len_call_at(at) && receiver_is_ghost(at))
            } else {
                false
            };
            if matched {
                out.push(GhostLengthWidthDiagnostic {
                    source_label: String::from(source_label),
                    line,
                    declaration: String::from(declaration),
                    fixed_width_type,
                    kind: GhostLengthWidthKind::WraparoundCast,
                });
            }
            continue;
        }
        // `<FixedPath>::from(<expr with .len()>)`, `::try_from(…)`, `::new(…)`
        let at_path_root = idx == 0 || toks[idx - 1].kind != GuardTokKind::PathSep;
        if at_path_root
            && (toks[idx].kind == GuardTokKind::Word || toks[idx].kind == GuardTokKind::PathSep)
            && let Some((leaf, after_path)) = read_type_path(toks, idx)
            && matches!(leaf.text, "from" | "try_from" | "new")
            && after_path >= idx + 3
            && toks[after_path - 2].kind == GuardTokKind::PathSep
            && let Some((fixed_width_type, line)) =
                resolve_fixed_width_leaf(&toks[after_path - 3], aliases)
            && toks.get(after_path).is_some_and(|open| open.is_sym("("))
            && let Some(close) = matching_close(toks, after_path)
            && (after_path + 1..close).any(|at| is_len_call_at(at) && receiver_is_ghost(at))
        {
            out.push(GhostLengthWidthDiagnostic {
                source_label: String::from(source_label),
                line,
                declaration: String::from(declaration),
                fixed_width_type,
                kind: GhostLengthWidthKind::WraparoundCast,
            });
        }
    }
}

/// Whether the Rust `const` keyword at `idx` introduces a `const fn` (possibly
/// with `unsafe` / `extern "..."` qualifiers before `fn`).
fn rust_const_introduces_fn(toks: &[GuardTok<'_>], idx: usize) -> bool {
    let mut cursor = idx + 1;
    while let Some(t) = toks.get(cursor) {
        if t.is_word("fn") {
            return true;
        }
        if t.is_word("unsafe") || t.is_word("async") {
            cursor += 1;
        } else if t.is_word("extern") {
            cursor += 1;
            if toks
                .get(cursor)
                .is_some_and(|lit| lit.kind == GuardTokKind::Literal)
            {
                cursor += 1;
            }
        } else {
            return false;
        }
    }
    false
}

/// Skip a Rust generic parameter list `<…>` starting at `start` (handling
/// nested `<…>` and `Fn(…) -> …` bounds), returning the index right after `>`.
fn skip_rust_generics(toks: &[GuardTok<'_>], start: usize) -> usize {
    if !toks.get(start).is_some_and(|t| t.is_sym("<")) {
        return start;
    }
    let mut angle = 0i32;
    let mut paren = 0i32;
    let mut cursor = start;
    while let Some(t) = toks.get(cursor) {
        if t.is_sym("(") || t.is_sym("[") || t.is_sym("{") {
            paren += 1;
        } else if t.is_sym(")") || t.is_sym("]") || t.is_sym("}") {
            paren -= 1;
        } else if paren == 0 {
            if t.is_sym("<") {
                angle += 1;
            } else if t.is_sym(">") {
                angle -= 1;
                if angle == 0 {
                    return cursor + 1;
                }
            }
        }
        cursor += 1;
    }
    cursor
}

/// Scan a Rust `#[model] struct` body `{ field: Ty, … }` for fixed-width ghost
/// length fields.
fn scan_rust_ghost_struct_fields(
    source_label: &str,
    struct_name: &str,
    body: &[GuardTok<'_>],
    aliases: &[(String, String)],
    out: &mut Vec<GhostLengthWidthDiagnostic>,
) {
    if body.len() < 2 || !body[0].is_sym("{") {
        return;
    }
    let inner = &body[1..body.len() - 1];
    let mut idx = 0usize;
    while idx < inner.len() {
        if inner[idx].is_sym("#")
            && let Some(open) = if inner.get(idx + 1).is_some_and(|t| t.is_sym("[")) {
                Some(idx + 1)
            } else {
                None
            }
        {
            idx = matching_close(inner, open).map_or(inner.len(), |c| c + 1);
            continue;
        }
        if inner[idx].is_word("pub") {
            idx += 1;
            if inner.get(idx).is_some_and(|t| t.is_sym("(")) {
                idx = matching_close(inner, idx).map_or(inner.len(), |c| c + 1);
            }
            continue;
        }
        if inner[idx].kind == GuardTokKind::Word
            && inner.get(idx + 1).is_some_and(|c| c.is_sym(":"))
        {
            let field_name = inner[idx].text;
            let ty_start = idx + 2;
            let mut ty_end = ty_start;
            let mut depth = 0i32;
            while let Some(t) = inner.get(ty_end) {
                if depth == 0 && t.is_sym(",") {
                    break;
                }
                if t.is_sym("<") || t.is_sym("(") || t.is_sym("[") || t.is_sym("{") {
                    depth += 1;
                } else if t.is_sym(">") || t.is_sym(")") || t.is_sym("]") || t.is_sym("}") {
                    depth -= 1;
                }
                ty_end += 1;
            }
            if is_ghost_length_name(field_name)
                && let Some((fixed_width_type, line)) =
                    fixed_width_type_within(&inner[ty_start..ty_end], aliases)
            {
                out.push(GhostLengthWidthDiagnostic {
                    source_label: String::from(source_label),
                    line,
                    declaration: format!("{struct_name}.{field_name}"),
                    fixed_width_type,
                    kind: GhostLengthWidthKind::FixedWidthReturnType,
                });
            }
            idx = (ty_end + 1).min(inner.len());
        } else {
            idx += 1;
        }
    }
}

/// Scan Rust source for ghost length functions, `#[model]` structs, ghost
/// `impl` blocks, and length wraparound casts inside ghost functions and
/// `#[spec]` / `#[invariant]` attributes. Only items in ghost/specification
/// context are inspected, so ordinary runtime code is never flagged.
fn scan_rust_ghost_length_fns(
    source_label: &str,
    toks: &[GuardTok<'_>],
    aliases: &[(String, String)],
    out: &mut Vec<GhostLengthWidthDiagnostic>,
) {
    let mut pending: Option<RustGhostAttr> = None;
    let mut pending_attr_ranges: Vec<(usize, usize)> = Vec::new();
    // Active enclosing `impl` blocks: `(closing_brace_idx, is_model_impl, is_ghost_collection_impl)`.
    let mut impl_scopes: Vec<(usize, bool, bool)> = Vec::new();
    let mut idx = 0usize;
    while idx < toks.len() {
        while let Some(&(end_idx, _, _)) = impl_scopes.last() {
            if idx > end_idx {
                impl_scopes.pop();
            } else {
                break;
            }
        }
        let tok = &toks[idx];
        // Attributes: `#[…]` and `#![…]`.
        if tok.is_sym("#") {
            let mut open = idx + 1;
            if toks.get(open).is_some_and(|bang| bang.is_sym("!")) {
                open += 1;
            }
            if toks.get(open).is_some_and(|bracket| bracket.is_sym("[")) {
                let close = matching_close(toks, open);
                if let Some(attr) = rust_ghost_attr(toks, open) {
                    if pending != Some(RustGhostAttr::Model) {
                        pending = Some(attr);
                    }
                    if let Some(close_idx) = close {
                        pending_attr_ranges.push((open, close_idx));
                        // Always scan `#[spec(...)]` / `#[invariant(...)]` for
                        // wraparound casts on explicit ghost receivers (e.g.
                        // `#[invariant(self.ghost_items.len() as u64 <= ...)]`).
                        scan_rust_slice_wraparound_casts(
                            source_label,
                            "",
                            &toks[open..=close_idx],
                            aliases,
                            true,
                            out,
                        );
                    }
                }
                idx = close.map_or(toks.len(), |c| c + 1);
                continue;
            }
        }
        // `#[model] struct GhostBuf { len: u64 }`,
        // `#[model] struct GhostLen(u64);`, and
        // `#[invariant(self.items.len() as u64 <= CAP)] struct Buf { items: Seq<u8> }`.
        if tok.is_word("struct") {
            let attr = pending.take();
            let attr_ranges = std::mem::take(&mut pending_attr_ranges);
            if attr.is_some()
                && let Some(name_tok) = toks.get(idx + 1).filter(|t| t.kind == GuardTokKind::Word)
            {
                let mut open = skip_rust_generics(toks, idx + 2);
                while open < toks.len()
                    && !toks[open].is_sym("{")
                    && !toks[open].is_sym("(")
                    && !toks[open].is_sym(";")
                {
                    open += 1;
                }
                if toks.get(open).is_some_and(|t| t.is_sym("{"))
                    && let Some(close) = matching_close(toks, open)
                {
                    if attr == Some(RustGhostAttr::Model) {
                        scan_rust_ghost_struct_fields(
                            source_label,
                            name_tok.text,
                            &toks[open..=close],
                            aliases,
                            out,
                        );
                    }
                    // A specification attribute on a struct holding a ghost
                    // collection may cast that collection's length.
                    if mentions_ghost_collection(&toks[idx + 1..=close]) {
                        for (attr_open, attr_close) in &attr_ranges {
                            scan_rust_slice_wraparound_casts(
                                source_label,
                                name_tok.text,
                                &toks[*attr_open..=*attr_close],
                                aliases,
                                false,
                                out,
                            );
                        }
                    }
                    idx = close + 1;
                    continue;
                } else if toks.get(open).is_some_and(|t| t.is_sym("("))
                    && let Some(close) = matching_close(toks, open)
                {
                    if attr == Some(RustGhostAttr::Model) && is_ghost_length_name(name_tok.text) {
                        for field in split_top_level_toks(&toks[open + 1..close], |t| t.is_sym(","))
                        {
                            if let Some((fixed_width_type, line)) =
                                fixed_width_type_within(strip_rust_field_prefix(field), aliases)
                            {
                                out.push(GhostLengthWidthDiagnostic {
                                    source_label: String::from(source_label),
                                    line,
                                    declaration: String::from(name_tok.text),
                                    fixed_width_type,
                                    kind: GhostLengthWidthKind::FixedWidthReturnType,
                                });
                            }
                        }
                    }
                    if mentions_ghost_collection(&toks[idx + 1..=close]) {
                        for (attr_open, attr_close) in &attr_ranges {
                            scan_rust_slice_wraparound_casts(
                                source_label,
                                name_tok.text,
                                &toks[*attr_open..=*attr_close],
                                aliases,
                                false,
                                out,
                            );
                        }
                    }
                    idx = close + 1;
                    continue;
                }
            }
            idx += 1;
            continue;
        }
        // `#[model] impl<T> GhostSeq<T> { ... }` or `impl<T> GhostSeq<T> { ... }`
        // (a `#[model] trait` scopes its methods the same way).
        if tok.is_word("impl") || tok.is_word("trait") {
            let attr = pending.take();
            pending_attr_ranges.clear();
            let mut open = idx + 1;
            while open < toks.len() && !toks[open].is_sym("{") && !toks[open].is_sym(";") {
                open += 1;
            }
            if toks.get(open).is_some_and(|t| t.is_sym("{"))
                && let Some(close) = matching_close(toks, open)
            {
                let header = &toks[idx + 1..open];
                let is_model_impl = attr == Some(RustGhostAttr::Model);
                let is_ghost_coll = mentions_ghost_collection(header);
                if is_model_impl || is_ghost_coll {
                    impl_scopes.push((close, is_model_impl, is_ghost_coll));
                }
                idx = open + 1;
                continue;
            }
            idx += 1;
            continue;
        }
        if tok.kind == GuardTokKind::Word
            && matches!(tok.text, "enum" | "mod" | "static" | "type" | "use")
        {
            pending = None;
            pending_attr_ranges.clear();
            idx += 1;
            continue;
        }
        if tok.is_word("const") && !rust_const_introduces_fn(toks, idx) {
            pending = None;
            pending_attr_ranges.clear();
            idx += 1;
            continue;
        }
        if !tok.is_word("fn") {
            idx += 1;
            continue;
        }
        let in_model_impl = impl_scopes.iter().any(|(_, m, _)| *m);
        let in_ghost_coll_impl = impl_scopes.iter().any(|(_, _, g)| *g);
        let attr = pending.take().or_else(|| {
            if in_model_impl {
                Some(RustGhostAttr::Model)
            } else {
                None
            }
        });
        let attr_ranges = std::mem::take(&mut pending_attr_ranges);
        let Some(name_tok) = toks.get(idx + 1).filter(|t| t.kind == GuardTokKind::Word) else {
            idx += 1;
            continue;
        };
        let name = name_tok.text;
        // Skip generic parameter list `<…>` before locating the parameter list `(`.
        let mut open = skip_rust_generics(toks, idx + 2);
        while open < toks.len() && !toks[open].is_sym("(") {
            if toks[open].is_sym("{") || toks[open].is_sym(";") {
                break;
            }
            open += 1;
        }
        let Some(close) = toks
            .get(open)
            .filter(|t| t.is_sym("("))
            .and_then(|_| matching_close(toks, open))
        else {
            idx += 2;
            continue;
        };
        // Return type: tokens after `->` up to the body, `where`, or `;`.
        let mut sig_end = close + 1;
        while sig_end < toks.len()
            && !toks[sig_end].is_sym("{")
            && !toks[sig_end].is_sym(";")
            && !toks[sig_end].is_word("where")
        {
            sig_end += 1;
        }
        let ret = if toks.get(close + 1).is_some_and(|arrow| arrow.is_sym("->")) {
            &toks[close + 2..sig_end]
        } else {
            &toks[sig_end..sig_end]
        };
        // Body.
        let mut body_open = sig_end;
        while body_open < toks.len() && !toks[body_open].is_sym("{") && !toks[body_open].is_sym(";")
        {
            body_open += 1;
        }
        let body_close = toks
            .get(body_open)
            .filter(|t| t.is_sym("{"))
            .and_then(|_| matching_close(toks, body_open));
        idx = body_close.map_or(body_open.max(idx + 2), |end| end + 1);

        let Some(attr) = attr else { continue };
        let signature = &toks[open..sig_end];
        let ghost_collection = mentions_ghost_collection(signature) || in_ghost_coll_impl;
        let ghost_context =
            attr == RustGhostAttr::Model || ghost_collection || has_ghost_name_marker(name);
        if !ghost_context {
            continue;
        }
        if is_ghost_length_name(name)
            && let Some((fixed_width_type, line)) = fixed_width_type_within(ret, aliases)
        {
            out.push(GhostLengthWidthDiagnostic {
                source_label: String::from(source_label),
                line,
                declaration: String::from(name),
                fixed_width_type,
                kind: GhostLengthWidthKind::FixedWidthReturnType,
            });
        }
        // Inside a ghost-collection `fn`, scan both its spec attributes and
        // its body for `.len() as u64` / `u64::from(s.len())` wraparound casts.
        if ghost_collection {
            for (attr_open, attr_close) in &attr_ranges {
                scan_rust_slice_wraparound_casts(
                    source_label,
                    name,
                    &toks[*attr_open..=*attr_close],
                    aliases,
                    false,
                    out,
                );
            }
            if let Some(body_close) = body_close {
                scan_rust_slice_wraparound_casts(
                    source_label,
                    name,
                    &toks[body_open..=body_close],
                    aliases,
                    false,
                    out,
                );
            }
        }
    }
}

/// Scan a Lean (`Specs/`, `Obligations/`, `Assumptions/`) or Rust (`#[model]`,
/// `#[spec]`, `#[invariant]`) specification source for ghost collection
/// lengths typed at a fixed machine width (`Slate` soundness bug 121).
///
/// The dialect is inferred from `source_label` ([`SpecSourceDialect`]);
/// comments and string literals are never inspected.
///
/// Flagged:
///
/// - a Lean `def` / `axiom` / `opaque` / `abbrev` / `theorem` / `lemma` whose
///   name marks a length or cardinality (`len`, `length`, `card`, `size`,
///   `count`, `cap`, `bound`, …), that is ghost (its name has a `ghost`
///   segment or its signature mentions a [`GHOST_COLLECTION_TYPE_NAMES`]
///   type), and whose result type is, or wraps, one of
///   [`FIXED_WIDTH_GHOST_INT_TYPE_NAMES`], `BitVec <N>`, or a closed
///   `Fin <N>` (`Option UInt64`, `UInt64 × Bool`, `Std.BitVec 64`,
///   `Fin (2 ^ 64)`), and such a field of a ghost `structure` / `class`;
/// - a Rust `fn` under `#[model]` (also `#[cfg_attr(…, model)]`, or inside a
///   `#[model]` `impl` / `trait`) with such a name and a return type that is,
///   or wraps, a fixed-width integer (`u64`, `Option<u64>`, `&u64`,
///   `(u64, bool)`, [`RUST_FIXED_WIDTH_WRAPPER_TYPE_NAMES`]), or under
///   `#[spec]` / `#[embed_spec]` / `#[external_spec]` / `#[invariant]` when
///   it is additionally ghost by name or signature;
/// - either of the above through a module-local alias or newtype
///   (`abbrev GhostLen := UInt64`, `type GhostLen = u64;`,
///   `struct GhostLen(u64);`);
/// - Lean casts of a collection length into a fixed-width type
///   (`UInt64.ofNat xs.length`, `UInt64.ofNat <| xs.length`,
///   `xs.length.toUSize`, `xs.length |>.toUInt64`, `(xs.length : UInt64)`),
///   and `.len() as u64` inside a Rust specification function, or a
///   specification attribute of a struct, over a ghost collection.
///
/// `Nat` / `Int` lengths, declarations that are not lengths, and Rust
/// functions without a specification attribute are accepted. Malformed source
/// yields a single [`GhostLengthWidthKind::MalformedSource`] diagnostic.
pub fn scan_ghost_length_width_diagnostics(
    source_label: &str,
    source_text: &str,
) -> Vec<GhostLengthWidthDiagnostic> {
    let dialect = SpecSourceDialect::from_source_label(source_label);
    let toks = match tokenize_spec_source(source_text, dialect) {
        Ok(toks) => toks,
        Err(unclosed) => {
            return vec![GhostLengthWidthDiagnostic {
                source_label: String::from(source_label),
                line: unclosed.line,
                declaration: String::new(),
                fixed_width_type: String::new(),
                kind: GhostLengthWidthKind::MalformedSource,
            }];
        }
    };
    let aliases = collect_fixed_width_type_aliases(&toks, dialect);
    let mut out = Vec::new();
    if dialect != SpecSourceDialect::Rust {
        scan_lean_ghost_length_decls(source_label, &toks, &aliases, &mut out);
        scan_lean_wraparound_casts(source_label, &toks, &aliases, &mut out);
    }
    if dialect != SpecSourceDialect::Lean {
        scan_rust_ghost_length_fns(source_label, &toks, &aliases, &mut out);
    }
    out.sort();
    out.dedup();
    // A cast found both while scanning an attribute on its own and while
    // scanning the item that carries it is reported once, under the item.
    let attributed: Vec<(usize, String)> = out
        .iter()
        .filter(|d| d.kind == GhostLengthWidthKind::WraparoundCast && !d.declaration.is_empty())
        .map(|d| (d.line, d.fixed_width_type.clone()))
        .collect();
    out.retain(|d| {
        !(d.kind == GhostLengthWidthKind::WraparoundCast
            && d.declaration.is_empty()
            && attributed
                .iter()
                .any(|(line, ty)| *line == d.line && *ty == d.fixed_width_type))
    });
    out
}

// ----------------------------------------------------------------------------
// Guard 3: error-branch wildcard scanner (`awsm2`)
// ----------------------------------------------------------------------------

/// Syntactic shape of an error-branch wildcard
/// (`anneal_spec::spec_check::ErrorWildcardPattern`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorBranchWildcardKind {
    /// `Err(_) => true`, `| Err _ => True`, `| .err _ => True`,
    /// `| .error _ => True`.
    ErrArmTrue,
    /// `| .ub => True`, `| .fail .ub => True`, `| .fail _ => True`.
    UbArmTrue,
    /// `| .unsupported => True`.
    UnsupportedArmTrue,
    /// `matches!(out, Ok(_) | Err(_))`.
    MatchesAnyErr,
    /// `_ => true` in a postcondition that also matches an `Ok` constructor.
    CatchAllArmTrue,
    /// The source has an unclosed comment or literal and cannot be scanned.
    MalformedSource,
}

impl ErrorBranchWildcardKind {
    /// Short wire tag, equal to `ErrorWildcardPattern::as_str` in
    /// `anneal-spec` for every shape both scanners report.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ErrArmTrue => "err_arm_true",
            Self::UbArmTrue => "ub_arm_true",
            Self::UnsupportedArmTrue => "unsupported_arm_true",
            Self::MatchesAnyErr => "matches_any_err",
            Self::CatchAllArmTrue => "catch_all_arm_true",
            Self::MalformedSource => "unclosed_literal_or_comment",
        }
    }
}

/// An `error_branch_wildcard` finding (`awsm2`, `cl/1028766308`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ErrorBranchWildcardDiagnostic {
    /// Label of the scanned source (usually its path).
    pub source_label: String,
    /// 1-based line of the arm's `=>` (or of the `matches!` pattern end).
    pub line: usize,
    /// What was found.
    pub kind: ErrorBranchWildcardKind,
}

impl ErrorBranchWildcardDiagnostic {
    /// The guard every diagnostic of this type reports under.
    pub const GUARD: SpecBoundaryGuardId = SpecBoundaryGuardId::ErrorBranchWildcard;
}

impl fmt::Display for ErrorBranchWildcardDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}: ", self.source_label, self.line, Self::GUARD)?;
        f.write_str(match self.kind {
            ErrorBranchWildcardKind::ErrArmTrue => {
                "postcondition arm accepts every error payload (`Err(_) => true`); constrain the \
                 error or state when it may occur"
            }
            ErrorBranchWildcardKind::UbArmTrue => {
                "postcondition arm accepts undefined behavior (`| .ub => True`)"
            }
            ErrorBranchWildcardKind::UnsupportedArmTrue => {
                "postcondition arm accepts an unsupported construct (`| .unsupported => True`)"
            }
            ErrorBranchWildcardKind::MatchesAnyErr => {
                "`matches!` pattern accepts every error payload (`Ok(_) | Err(_)`)"
            }
            ErrorBranchWildcardKind::CatchAllArmTrue => {
                "catch-all arm `_ => true` covers the error branches of an `Ok` match"
            }
            ErrorBranchWildcardKind::MalformedSource => {
                "unclosed comment or literal; the source cannot be scanned (fail-closed)"
            }
        })
    }
}

/// Error-like constructor an arm alternative accepts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WildcardCtor {
    Err,
    Ub,
    Unsupported,
    Fail,
}

impl WildcardCtor {
    /// Capitalized names stand on their own (`Err`, `Result::Err`); lowercase
    /// names are constructors only in dotted position (`.err`,
    /// `Except.error`), since a bare lowercase word is a variable.
    fn of(word: &str, after_dot: bool) -> Option<Self> {
        match word {
            "Err" => Some(Self::Err),
            "Ub" | "UB" => Some(Self::Ub),
            "Unsupported" => Some(Self::Unsupported),
            "err" | "error" if after_dot => Some(Self::Err),
            "ub" if after_dot => Some(Self::Ub),
            "unsupported" if after_dot => Some(Self::Unsupported),
            "fail" if after_dot => Some(Self::Fail),
            _ => None,
        }
    }

    fn kind(self) -> ErrorBranchWildcardKind {
        match self {
            Self::Err => ErrorBranchWildcardKind::ErrArmTrue,
            Self::Ub | Self::Fail => ErrorBranchWildcardKind::UbArmTrue,
            Self::Unsupported => ErrorBranchWildcardKind::UnsupportedArmTrue,
        }
    }
}

/// Whether `word`, as an error payload, binds or ignores the payload instead
/// of constraining it (`_`, `_e`, `e`, `ref`).
fn is_wildcard_payload_word(word: &str) -> bool {
    if matches!(word, "true" | "false") {
        return false;
    }
    match word.chars().next() {
        Some(first) => first == '_' || (!first.is_uppercase() && !first.is_numeric()),
        None => true,
    }
}

/// Whether `word`, standing alone as a pattern alternative, binds every value
/// (`_`, `_rest`, `e`, `other`). Capitalized names, literals, and the
/// lowercase Lean constructors of `Option`, `List`, `Nat`, and `Unit` are
/// specific patterns.
fn is_catch_all_binder_word(word: &str) -> bool {
    if matches!(
        word,
        "true" | "false" | "none" | "some" | "nil" | "zero" | "unit"
    ) {
        return false;
    }
    word.chars()
        .next()
        .is_some_and(|first| first == '_' || first.is_lowercase())
}

/// One pattern alternative of a match arm, or the arm body after `=>`.
#[derive(Clone, Copy, Debug, Default)]
struct WildcardAlternative {
    depth: u32,
    arm_base_depth: u32,
    catch_all_parens: u32,
    tokens: u32,
    /// The alternative is exactly a catch-all so far (`_`, a bare binding,
    /// or a binding behind `&` / `ref` / `mut` / `(...)` / Lean `(_ : T)`).
    catch_all: bool,
    only_modifiers: bool,
    error_ctor: Option<WildcardCtor>,
    error_ctor_depth: Option<u32>,
    constrained: bool,
    type_ascription_depth: Option<u32>,
    after_arrow: bool,
    /// Bracket depth at which the arm body began: a `|` at this depth starts
    /// the next arm, a deeper one belongs to the body.
    body_depth: u32,
    in_lambda: bool,
    /// Bracket depth just inside the outermost struct-pattern brace around
    /// the scan position; a `:=` at or below it separates a field from its
    /// pattern (Lean `{ val := .err _ }`).
    struct_pattern_depth: Option<u32>,
    /// An earlier `|` alternative of the current component of a
    /// parenthesized catch-all candidate was a catch-all (`(_ | 0)`).
    or_wild: bool,
    /// A `,` was seen directly inside the outer catch-all parentheses.
    tuple_started: bool,
    /// Every completed component of that tuple was a catch-all.
    tuple_wild: bool,
}

impl WildcardAlternative {
    fn pattern(depth: u32) -> Self {
        Self {
            depth,
            arm_base_depth: depth,
            ..Self::default()
        }
    }

    fn next_alt(&self, catch_all_parens: u32) -> Self {
        Self {
            depth: self.depth,
            arm_base_depth: self.arm_base_depth,
            catch_all_parens,
            struct_pattern_depth: self.struct_pattern_depth,
            ..Self::default()
        }
    }

    /// Whether the scan position is directly inside the outer catch-all
    /// parentheses (not in a nested bracket).
    fn at_catch_all_paren_level(&self) -> bool {
        self.catch_all_parens > 0 && self.depth == self.arm_base_depth + self.catch_all_parens
    }

    fn body(depth: u32) -> Self {
        Self {
            depth,
            arm_base_depth: depth,
            after_arrow: true,
            body_depth: depth,
            ..Self::default()
        }
    }

    fn push_non_word(&mut self) {
        self.tokens += 1;
        self.catch_all = false;
        self.only_modifiers = false;
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct WildcardArm {
    wildcard: Option<WildcardCtor>,
    catch_all: bool,
    guarded: bool,
    guard_tokens: u32,
    guard_trivial: bool,
}

impl WildcardArm {
    fn absorb(&mut self, alt: &WildcardAlternative) {
        if alt.tokens == 0 || alt.after_arrow || alt.in_lambda {
            return;
        }
        if self.wildcard.is_none()
            && !alt.constrained
            && let Some(ctor) = alt.error_ctor
        {
            self.wildcard = Some(ctor);
        }
        if alt.catch_all {
            self.catch_all = true;
        }
    }

    fn guard_blocks(&self) -> bool {
        self.guarded && !(self.guard_tokens == 1 && self.guard_trivial)
    }
}

/// Kind of a scope tracked for [`ErrorBranchWildcardKind::CatchAllArmTrue`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OkScopeKind {
    /// A `{ … }` block; `saved_depth` is the bracket depth around it.
    Brace { saved_depth: u32 },
    /// The arms of a Lean `match … with` opened at bracket depth `depth`;
    /// they extend to the bracket closing that depth, to the brace closing
    /// the enclosing block, or to the next declaration.
    LeanMatch { depth: u32 },
}

#[derive(Clone, Copy, Debug)]
struct OkScope {
    kind: OkScopeKind,
    saw_ok: bool,
}

/// Maximum nested `{ … }` / Lean `match … with` scopes tracked for
/// `CatchAllArmTrue`.
const MAX_OK_SCOPE_DEPTH: usize = 32;

/// Stack of the scopes enclosing the scan position; mirrors `OkScopes` in
/// `anneal_spec::spec_check` (same fixed capacity, same overflow behavior).
#[derive(Clone, Copy, Debug)]
struct OkScopes {
    root_saw_ok: bool,
    stack: [OkScope; MAX_OK_SCOPE_DEPTH],
    len: usize,
    overflow: u32,
}

impl OkScopes {
    fn new() -> Self {
        Self {
            root_saw_ok: false,
            stack: [OkScope {
                kind: OkScopeKind::Brace { saved_depth: 0 },
                saw_ok: false,
            }; MAX_OK_SCOPE_DEPTH],
            len: 0,
            overflow: 0,
        }
    }

    fn mark_ok(&mut self) {
        if self.overflow > 0 {
            return;
        }
        match self.len {
            0 => self.root_saw_ok = true,
            len => self.stack[len - 1].saw_ok = true,
        }
    }

    /// Scopes nested beyond the tracked capacity answer `true` (fail closed).
    fn saw_ok(&self) -> bool {
        self.overflow > 0
            || match self.len {
                0 => self.root_saw_ok,
                len => self.stack[len - 1].saw_ok,
            }
    }

    fn push(&mut self, kind: OkScopeKind) {
        if self.len < MAX_OK_SCOPE_DEPTH {
            self.stack[self.len] = OkScope {
                kind,
                saw_ok: false,
            };
            self.len += 1;
        } else if matches!(kind, OkScopeKind::Brace { .. }) {
            self.overflow = self.overflow.saturating_add(1);
        }
    }

    /// Close the innermost brace scope above `floor` and the Lean matches
    /// opened inside it; returns the bracket depth to restore.
    fn pop_brace(&mut self, floor: usize) -> Option<u32> {
        if self.overflow > 0 {
            self.overflow -= 1;
            return Some(0);
        }
        let mut idx = self.len;
        while idx > floor {
            idx -= 1;
            if let OkScopeKind::Brace { saved_depth } = self.stack[idx].kind {
                self.len = idx;
                return Some(saved_depth);
            }
        }
        None
    }

    /// Close the innermost Lean matches opened at depth `min_depth` or more.
    fn close_lean_matches(&mut self, min_depth: u32) {
        if self.overflow > 0 {
            return;
        }
        while self.len > 0
            && matches!(
                self.stack[self.len - 1].kind,
                OkScopeKind::LeanMatch { depth } if depth >= min_depth
            )
        {
            self.len -= 1;
        }
    }

    fn begin_declaration(&mut self) {
        self.close_lean_matches(0);
        if self.len == 0 && self.overflow == 0 {
            self.root_saw_ok = false;
        }
    }
}

/// Whether the operator following a trivially true arm body combines it into
/// a body that is no longer trivially true (`true && p`, `True ∧ P`).
fn is_constraining_continuation(tok: &GuardTok<'_>) -> bool {
    match tok.kind {
        GuardTokKind::Sym => matches!(
            tok.text,
            "&&" | "&"
                | "∧"
                | "/\\"
                | "->"
                | "→"
                | "↔"
                | "<->"
                | "="
                | "=="
                | "!="
                | "≠"
                | "==>"
                | "."
                | "?"
                | "^"
                | "<"
                | ">"
                | "<="
                | ">="
                | "≤"
                | "≥"
                | "+"
                | "-"
                | "*"
                | "/"
                | "%"
                | "@"
        ),
        GuardTokKind::PathSep | GuardTokKind::DotDot => true,
        GuardTokKind::Word => matches!(tok.text, "as" | "and"),
        GuardTokKind::Literal | GuardTokKind::FatArrow => false,
    }
}

/// Maximum number of `&&` / `∧` terms unfolded in a trivially-true arm body.
const MAX_TRIVIAL_CONJUNCTS: usize = 8;

/// Maximum nesting of parenthesized / braced expressions inspected inside a
/// trivially-true arm body.
const MAX_TRIVIAL_EXPR_DEPTH: u32 = 8;

/// Maximum tokens scanned while inspecting disjunctions inside an arm body.
const MAX_ARM_BODY_SCAN_TOKENS: usize = 128;

fn is_disjunction_tok(tok: &GuardTok<'_>) -> bool {
    (tok.kind == GuardTokKind::Sym && matches!(tok.text, "||" | "∨" | "\\/")) || tok.is_word("or")
}

fn is_conjunction_tok(tok: &GuardTok<'_>) -> bool {
    (tok.kind == GuardTokKind::Sym && matches!(tok.text, "&&" | "∧" | "/\\")) || tok.is_word("and")
}

fn is_looser_than_disjunction(tok: &GuardTok<'_>) -> bool {
    tok.kind == GuardTokKind::Sym && matches!(tok.text, "->" | "→" | "↔" | "<->" | "==>")
}

/// Whether `tok` (followed by `next`) ends an arm body that no bracket
/// closes: the next arm, a statement or item boundary, or the next top-level
/// command of a Lean module (`#eval …`, `@[simp] theorem …`, `namespace …`).
/// Scanning past it would attribute unrelated code to the arm.
fn is_arm_body_terminator(tok: &GuardTok<'_>, next: Option<&GuardTok<'_>>) -> bool {
    match tok.kind {
        GuardTokKind::FatArrow => true,
        GuardTokKind::Sym => {
            matches!(tok.text, "," | "|" | ";" | ")" | "]" | "}" | "#")
                || (tok.text == "@" && next.is_some_and(|open| open.is_sym("[")))
        }
        GuardTokKind::Word => {
            is_lean_decl_reset_word(tok.text)
                || matches!(
                    tok.text,
                    "fn" | "pub"
                        | "struct"
                        | "enum"
                        | "impl"
                        | "trait"
                        | "mod"
                        | "use"
                        | "const"
                        | "static"
                        | "type"
                        | "where"
                        | "end"
                        | "namespace"
                        | "section"
                        | "open"
                        | "export"
                        | "import"
                        | "variable"
                        | "universe"
                        | "set_option"
                        | "attribute"
                        | "class"
                        | "mutual"
                        | "noncomputable"
                        | "private"
                        | "protected"
                        | "local"
                        | "scoped"
                        | "notation"
                        | "infix"
                        | "infixl"
                        | "infixr"
                        | "prefix"
                        | "postfix"
                        | "macro"
                        | "syntax"
                        | "deriving"
                        | "termination_by"
                        | "decreasing_by"
                )
        }
        _ => false,
    }
}

/// Whether `tok` starts a construct that extends as far to the right as
/// possible (`if … then … else e`, `fun x => e`, `∀ x, e`, `let x := v; e`):
/// a later disjunction belongs to that construct, not to the whole body.
fn extends_to_the_right(tok: &GuardTok<'_>) -> bool {
    match tok.kind {
        GuardTokKind::Word => matches!(
            tok.text,
            "if" | "then"
                | "else"
                | "fun"
                | "λ"
                | "match"
                | "let"
                | "have"
                | "show"
                | "from"
                | "do"
                | "forall"
                | "exists"
        ),
        GuardTokKind::Sym => matches!(tok.text, "∀" | "∃" | "Σ" | "∑" | "∏"),
        _ => false,
    }
}

/// Consume one trivially-true boolean/Prop atom (`true`, `True`, `trivial`,
/// `!false`, `¬False`, `Not False`, or a parenthesized/braced trivially-true
/// expression, optionally preceded by `return`/`by` and followed by `as bool`).
/// Returns `Some(next_idx)` on match.
fn consume_trivial_true_atom(toks: &[GuardTok<'_>], start: usize, depth: u32) -> Option<usize> {
    if depth == 0 {
        return None;
    }
    let mut idx = start;
    while toks
        .get(idx)
        .is_some_and(|t| t.is_word("return") || t.is_word("by"))
    {
        idx += 1;
    }
    let tok = toks.get(idx)?;
    if tok.is_sym("(") {
        idx = expr_is_trivially_true(toks, idx + 1, Some(")"), depth - 1)?;
    } else if tok.is_sym("{") {
        idx = expr_is_trivially_true(toks, idx + 1, Some("}"), depth - 1)?;
    } else if tok.kind == GuardTokKind::Word && matches!(tok.text, "true" | "True" | "trivial") {
        idx += 1;
    } else if tok.is_sym("!") && toks.get(idx + 1).is_some_and(|t| t.is_word("false")) {
        idx += 2;
    } else if (tok.is_sym("¬") || tok.is_word("Not"))
        && toks.get(idx + 1).is_some_and(|t| t.is_word("False"))
    {
        idx += 2;
    } else {
        return None;
    }
    // Optional `as bool`.
    if toks.get(idx).is_some_and(|t| t.is_word("as"))
        && toks.get(idx + 1).is_some_and(|t| t.is_word("bool"))
    {
        idx += 2;
    }
    Some(idx)
}

/// Consume a conjunction of trivially-true atoms (`true && true`,
/// `(True ∧ True)`, optionally followed by `as bool` or a parenthesized
/// `: Prop` / `: Bool` ascription) not continued by a constraining operator.
fn consume_trivial_conjunction(
    toks: &[GuardTok<'_>],
    start: usize,
    allow_type_ascription: bool,
    depth: u32,
) -> Option<usize> {
    let mut idx = consume_trivial_true_atom(toks, start, depth)?;
    for _ in 0..MAX_TRIVIAL_CONJUNCTS {
        let Some(next) = toks.get(idx) else {
            return Some(idx);
        };
        if is_conjunction_tok(next) {
            idx = consume_trivial_true_atom(toks, idx + 1, depth)?;
        } else if next.is_word("as") {
            if toks.get(idx + 1).is_some_and(|t| t.is_word("bool")) {
                idx += 2;
            } else {
                return None;
            }
        } else if allow_type_ascription && next.is_sym(":") {
            if toks.get(idx + 1).is_some_and(|t| {
                t.kind == GuardTokKind::Word && matches!(t.text, "Prop" | "Bool" | "bool")
            }) {
                idx += 2;
            } else {
                return None;
            }
        } else if !is_constraining_continuation(next) {
            return Some(idx);
        } else {
            return None;
        }
    }
    None
}

/// Evaluate whether the expression starting at `start` (up to `stop_delim` at
/// inner depth 0, or up to the arm-body terminator when `stop_delim` is
/// `None`) is trivially true; returns `Some(next_idx)` right after the closing
/// delimiter (or at the terminator) on match.
fn expr_is_trivially_true(
    toks: &[GuardTok<'_>],
    start: usize,
    stop_delim: Option<&str>,
    depth: u32,
) -> Option<usize> {
    if depth == 0 {
        return None;
    }
    let mut idx = start;
    while toks
        .get(idx)
        .is_some_and(|t| t.is_word("return") || t.is_word("by"))
    {
        idx += 1;
    }
    let mut found_trivial = false;
    let mut scanned = 0usize;
    let mut at_disjunct_start = true;
    let mut inner_depth = 0u32;
    let mut prev_closed_brace_at_zero = false;
    // A right-extending construct was seen: later disjuncts are its own.
    let mut disjuncts_blocked = false;
    loop {
        if at_disjunct_start && inner_depth == 0 {
            at_disjunct_start = false;
            if !disjuncts_blocked
                && let Some(after) =
                    consume_trivial_conjunction(toks, idx, stop_delim == Some(")"), depth)
            {
                found_trivial = true;
                idx = after;
            }
        }
        let Some(tok) = toks.get(idx) else {
            return (stop_delim.is_none() && found_trivial).then_some(idx);
        };
        let before = idx;
        idx += 1;
        scanned += 1;
        if scanned > MAX_ARM_BODY_SCAN_TOKENS {
            return None;
        }
        if inner_depth == 0 {
            if prev_closed_brace_at_zero {
                prev_closed_brace_at_zero = false;
                if stop_delim.is_none()
                    && tok.kind == GuardTokKind::Word
                    && !matches!(tok.text, "else" | "or" | "and" | "as")
                {
                    return found_trivial.then_some(before);
                }
            }
            if let Some(delim) = stop_delim {
                if tok.is_sym(delim) {
                    return found_trivial.then_some(idx);
                }
                if delim == "}" && tok.is_sym(";") {
                    return (toks.get(idx).is_some_and(|t| t.is_sym("}")) && found_trivial)
                        .then_some(idx + 1);
                }
                // A tuple or argument list (`(true, x)`) is not a
                // parenthesized proposition.
                if tok.kind == GuardTokKind::Sym && matches!(tok.text, ")" | "]" | "}" | ",") {
                    return None;
                }
            } else if is_arm_body_terminator(tok, toks.get(idx)) {
                return found_trivial.then_some(before);
            }
            if is_looser_than_disjunction(tok) {
                return None;
            }
            if extends_to_the_right(tok) {
                disjuncts_blocked = true;
            }
            if is_disjunction_tok(tok) {
                at_disjunct_start = true;
                continue;
            }
            if stop_delim == Some(")") && tok.is_sym(":") {
                if toks.get(idx).is_some_and(|t| {
                    t.kind == GuardTokKind::Word && matches!(t.text, "Prop" | "Bool" | "bool")
                }) && toks.get(idx + 1).is_some_and(|t| t.is_sym(")"))
                {
                    return found_trivial.then_some(idx + 2);
                }
                return None;
            }
            if tok.is_word("as") {
                if toks.get(idx).is_some_and(|t| t.is_word("bool")) {
                    idx += 1;
                    continue;
                }
                found_trivial = false;
            }
        }
        if tok.kind == GuardTokKind::Sym {
            match tok.text {
                "(" | "[" | "{" => inner_depth += 1,
                ")" | "]" | "}" => {
                    if inner_depth == 0 {
                        return None;
                    }
                    inner_depth -= 1;
                    if inner_depth == 0 && tok.text == "}" {
                        prev_closed_brace_at_zero = true;
                    }
                }
                _ => {}
            }
        }
    }
}

/// Whether the arm body starting at `start` is trivially true: `true`,
/// `True`, `trivial`, `!false`, `¬False`, `Not False`, optionally wrapped
/// (`(true)`, `{ true }`, `{ return true; }`, `by trivial`, `true as bool`),
/// a conjunction of trivially-true atoms, or a disjunction containing one,
/// and not combined with a constraining operator.
fn arm_body_is_trivially_true(toks: &[GuardTok<'_>], start: usize) -> bool {
    expr_is_trivially_true(toks, start, None, MAX_TRIVIAL_EXPR_DEPTH).is_some()
}

/// Lean declaration keywords that begin a fresh top-level item and close any
/// prior match/arm state.
fn is_lean_decl_reset_word(word: &str) -> bool {
    matches!(
        word,
        "def"
            | "theorem"
            | "lemma"
            | "axiom"
            | "opaque"
            | "abbrev"
            | "instance"
            | "example"
            | "structure"
            | "inductive"
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MatchesMacroState {
    Outside,
    Scrutinee { depth: u32 },
    Pattern,
}

/// Maximum tokens of a brace group inspected to recognize a struct pattern.
const MAX_STRUCT_PATTERN_TOKENS: usize = 256;

/// Whether the brace group whose `{` precedes `start` closes within
/// [`MAX_STRUCT_PATTERN_TOKENS`] tokens without containing `=>` or `;`: such
/// a group has no arms or statements of its own.
fn brace_is_pattern_like(toks: &[GuardTok<'_>], start: usize) -> bool {
    let mut depth = 1u32;
    for tok in toks.iter().skip(start).take(MAX_STRUCT_PATTERN_TOKENS) {
        if tok.kind == GuardTokKind::FatArrow || tok.is_sym(";") {
            return false;
        }
        if tok.is_sym("{") {
            depth += 1;
        } else if tok.is_sym("}") {
            depth -= 1;
            if depth == 0 {
                return true;
            }
        }
    }
    false
}

/// Token-level error-branch wildcard scan; the same algorithm as
/// `scan_error_branch_wildcard` in `anneal_spec::spec_check`, reporting every
/// occurrence instead of the first.
fn scan_error_branch_wildcard_tokens(
    toks: &[GuardTok<'_>],
    dialect: SpecSourceDialect,
) -> Vec<(usize, ErrorBranchWildcardKind)> {
    let lean_keywords = dialect != SpecSourceDialect::Rust;
    let mut found = Vec::new();
    let mut alt = WildcardAlternative::default();
    let mut arm = WildcardArm::default();
    let mut matches_state = MatchesMacroState::Outside;
    let mut matches_saw_ok = false;
    let mut matches_scope_floor = 0usize;
    let mut after_dot = false;
    let mut in_match_scrutinee = false;
    let mut scopes = OkScopes::new();

    let mut idx = 0usize;
    while idx < toks.len() {
        let tok = &toks[idx];
        idx += 1;
        let was_after_dot = after_dot;
        after_dot = tok.is_sym(".");

        if let MatchesMacroState::Scrutinee { depth } = matches_state {
            if tok.kind == GuardTokKind::Sym {
                match tok.text {
                    "(" | "[" | "{" => {
                        matches_state = MatchesMacroState::Scrutinee { depth: depth + 1 };
                    }
                    ")" | "]" | "}" => {
                        matches_state = if depth <= 1 {
                            MatchesMacroState::Outside
                        } else {
                            MatchesMacroState::Scrutinee { depth: depth - 1 }
                        };
                    }
                    "," if depth == 1 => {
                        matches_state = MatchesMacroState::Pattern;
                        matches_saw_ok = false;
                        matches_scope_floor = scopes.len;
                        in_match_scrutinee = false;
                        alt = WildcardAlternative::default();
                        arm = WildcardArm::default();
                    }
                    _ => {}
                }
            }
            continue;
        }

        match tok.kind {
            GuardTokKind::FatArrow => {
                in_match_scrutinee = false;
                if !alt.in_lambda {
                    arm.absorb(&alt);
                    if !arm.guard_blocks() && arm_body_is_trivially_true(toks, idx) {
                        if let Some(ctor) = arm.wildcard {
                            found.push((tok.line, ctor.kind()));
                        } else if arm.catch_all && scopes.saw_ok() {
                            found.push((tok.line, ErrorBranchWildcardKind::CatchAllArmTrue));
                        }
                    }
                }
                arm = WildcardArm::default();
                alt = WildcardAlternative::body(alt.depth);
            }
            GuardTokKind::Sym
                if tok.text == "|"
                    && !arm.guarded
                    && (!alt.after_arrow || alt.depth == alt.body_depth) =>
            {
                if alt.after_arrow {
                    // The previous arm's body ends here.
                    arm = WildcardArm::default();
                    alt = WildcardAlternative::pattern(alt.depth);
                } else {
                    if alt.at_catch_all_paren_level() {
                        // Record the error wildcard now; the catch-all
                        // verdict waits for the closing parenthesis.
                        arm.absorb(&WildcardAlternative {
                            catch_all: false,
                            ..alt
                        });
                    } else {
                        arm.absorb(&alt);
                    }
                    match alt.error_ctor_depth {
                        Some(ctor_depth) if alt.depth > ctor_depth => {
                            // Or-pattern inside an error payload: directly
                            // under the constructor the next alternative
                            // starts unconstrained; deeper, the enclosing
                            // constructor still constrains the payload.
                            alt.push_non_word();
                            if alt.depth == ctor_depth + 1 {
                                alt.constrained = false;
                                alt.type_ascription_depth = None;
                            }
                        }
                        // Or-pattern directly inside catch-all parentheses
                        // (`(0 | _)`, `(_ | 0, y)`): whether the group is a
                        // catch-all is only known once it closes.
                        _ if alt.at_catch_all_paren_level() => {
                            let or_wild = alt.or_wild || alt.catch_all;
                            let (tuple_started, tuple_wild) = (alt.tuple_started, alt.tuple_wild);
                            alt = alt.next_alt(alt.catch_all_parens);
                            alt.or_wild = or_wild;
                            alt.tuple_started = tuple_started;
                            alt.tuple_wild = tuple_wild;
                        }
                        _ => alt = alt.next_alt(alt.catch_all_parens),
                    }
                }
            }
            GuardTokKind::Sym
                if tok.text == ","
                    && !arm.guarded
                    && !alt.after_arrow
                    && !alt.in_lambda
                    && alt.error_ctor_depth.is_some_and(|d| alt.depth <= d) =>
            {
                // A sibling of the error constructor (`(Err(_), Ok(_))`,
                // `| .err _, .ok v`), not part of its payload.
                arm.absorb(&WildcardAlternative {
                    catch_all: false,
                    ..alt
                });
                alt = alt.next_alt(0);
            }
            GuardTokKind::Sym if matches!(tok.text, "," | ";") && alt.depth == 0 => {
                in_match_scrutinee = false;
                if matches_state == MatchesMacroState::Pattern {
                    // Allow a Rust trailing comma in `matches!(out, pat,)`.
                    if tok.text == ","
                        && toks.get(idx).is_some_and(|next| {
                            next.kind == GuardTokKind::Sym && matches!(next.text, ")" | "]" | "}")
                        })
                    {
                        continue;
                    }
                    matches_state = MatchesMacroState::Outside;
                }
                arm = WildcardArm::default();
                alt = WildcardAlternative::default();
            }
            GuardTokKind::Sym if tok.text == "(" => {
                let outer_wrapper = (alt.tokens == 0 || alt.only_modifiers)
                    && alt.depth == alt.arm_base_depth + alt.catch_all_parens;
                alt.depth += 1;
                if alt.type_ascription_depth.is_some() {
                    alt.tokens += 1;
                } else {
                    alt.tokens += 1;
                    alt.catch_all = false;
                    alt.only_modifiers = outer_wrapper;
                    if outer_wrapper {
                        alt.catch_all_parens += 1;
                    }
                }
            }
            GuardTokKind::Sym if tok.text == "[" => {
                alt.depth += 1;
                if alt.type_ascription_depth.is_some() {
                    alt.tokens += 1;
                } else {
                    alt.push_non_word();
                }
            }
            GuardTokKind::Sym if tok.text == "{" => {
                // In pattern position a brace group without `=>` or `;` is a
                // struct pattern (`W { r: Err(_) }`, Lean `{ val := .err _ }`)
                // or a small expression: it holds no arms of its own, so it
                // is tracked by depth and its error constructors stay with
                // the arm around it.
                let is_struct_pattern_brace = !alt.after_arrow
                    && !arm.guarded
                    && !in_match_scrutinee
                    && (matches_state == MatchesMacroState::Pattern
                        || brace_is_pattern_like(toks, idx));
                if is_struct_pattern_brace {
                    alt.depth += 1;
                    if alt.struct_pattern_depth.is_none() {
                        alt.struct_pattern_depth = Some(alt.depth);
                    }
                    if alt.type_ascription_depth.is_some() {
                        alt.tokens += 1;
                    } else {
                        alt.push_non_word();
                    }
                } else {
                    in_match_scrutinee = false;
                    scopes.push(OkScopeKind::Brace {
                        saved_depth: alt.depth,
                    });
                    arm = WildcardArm::default();
                    alt = WildcardAlternative::default();
                }
            }
            GuardTokKind::Sym if matches!(tok.text, ")" | "]" | "}") => {
                let brace_floor = if matches_state == MatchesMacroState::Pattern {
                    matches_scope_floor
                } else {
                    0
                };
                if alt.depth > 0 {
                    alt.depth -= 1;
                    let was_ascription = alt.type_ascription_depth.is_some();
                    if alt.type_ascription_depth.is_some_and(|d| alt.depth < d) {
                        alt.type_ascription_depth = None;
                    }
                    if alt.struct_pattern_depth.is_some_and(|d| alt.depth < d) {
                        alt.struct_pattern_depth = None;
                    }
                    let closed_outer_catch_all_paren = tok.text == ")"
                        && alt.catch_all_parens > 0
                        && alt.depth < alt.arm_base_depth + alt.catch_all_parens;
                    if closed_outer_catch_all_paren {
                        alt.catch_all_parens -= 1;
                        // The group is a catch-all when its last component
                        // is and, for a tuple, every earlier one was too.
                        let last_wild = alt.catch_all || alt.or_wild;
                        alt.catch_all = if alt.tuple_started {
                            alt.tuple_wild && (last_wild || alt.only_modifiers)
                        } else {
                            last_wild
                        };
                        alt.or_wild = false;
                        alt.tuple_started = false;
                        alt.tuple_wild = false;
                    }
                    if was_ascription || closed_outer_catch_all_paren {
                        alt.tokens += 1;
                        if !was_ascription {
                            alt.only_modifiers = false;
                        }
                    } else {
                        alt.push_non_word();
                    }
                    if alt.after_arrow && alt.depth < alt.body_depth {
                        // The bracket around the arm list closed.
                        alt.body_depth = alt.depth;
                    }
                    scopes.close_lean_matches(alt.depth + 1);
                } else if tok.text == "}"
                    && let Some(saved_depth) = scopes.pop_brace(brace_floor)
                {
                    // The block closed: a new arm pattern may follow.
                    in_match_scrutinee = false;
                    arm = WildcardArm::default();
                    alt = WildcardAlternative::pattern(saved_depth);
                } else {
                    // The closer of a bracket opened before the scanned
                    // text, or of `matches!(…)`.
                    if matches_state == MatchesMacroState::Pattern {
                        arm.absorb(&alt);
                        if !arm.guard_blocks()
                            && (arm.wildcard.is_some() || (arm.catch_all && matches_saw_ok))
                        {
                            found.push((tok.line, ErrorBranchWildcardKind::MatchesAnyErr));
                        }
                        matches_state = MatchesMacroState::Outside;
                    }
                    in_match_scrutinee = false;
                    scopes.close_lean_matches(0);
                    arm = WildcardArm::default();
                    alt = WildcardAlternative::default();
                }
            }
            GuardTokKind::Sym
                if tok.text == ":="
                    && alt.struct_pattern_depth.is_some()
                    && !alt.after_arrow
                    && !alt.in_lambda =>
            {
                // Lean structure pattern field `{ val := pattern }`.
                if !arm.guarded {
                    if alt.type_ascription_depth.is_some() {
                        alt.tokens += 1;
                    } else {
                        alt.push_non_word();
                    }
                }
            }
            GuardTokKind::Sym if tok.text == ":=" => {
                in_match_scrutinee = false;
                arm = WildcardArm::default();
                alt = WildcardAlternative::body(alt.depth);
            }
            GuardTokKind::Word => {
                let word = tok.text;
                if word == "Ok" || (was_after_dot && word == "ok") {
                    if matches_state == MatchesMacroState::Pattern {
                        matches_saw_ok = true;
                    } else {
                        scopes.mark_ok();
                    }
                }
                if word == "matches"
                    && matches_state == MatchesMacroState::Outside
                    && toks.get(idx).is_some_and(|bang| bang.is_sym("!"))
                    && toks.get(idx + 1).is_some_and(|open| {
                        open.kind == GuardTokKind::Sym && matches!(open.text, "(" | "[" | "{")
                    })
                {
                    idx += 2;
                    after_dot = false;
                    matches_state = MatchesMacroState::Scrutinee { depth: 1 };
                    continue;
                }
                if !arm.guarded && alt.depth == 0 && is_lean_decl_reset_word(word) {
                    in_match_scrutinee = false;
                    scopes.begin_declaration();
                    arm = WildcardArm::default();
                    alt = WildcardAlternative::default();
                    continue;
                }
                if !arm.guarded
                    && lean_keywords
                    && matches!(word, "fun" | "λ")
                    && alt.error_ctor.is_none()
                    && (alt.after_arrow || alt.tokens == 0)
                {
                    arm = WildcardArm::default();
                    alt = WildcardAlternative {
                        in_lambda: true,
                        ..WildcardAlternative::pattern(alt.depth)
                    };
                    continue;
                }
                if !arm.guarded && matches!(word, "match" | "with") {
                    in_match_scrutinee = word == "match";
                    if word == "with" && lean_keywords {
                        scopes.push(OkScopeKind::LeanMatch { depth: alt.depth });
                    }
                    arm = WildcardArm::default();
                    alt = WildcardAlternative::pattern(alt.depth);
                    continue;
                }
                if arm.guarded {
                    arm.guard_tokens += 1;
                    arm.guard_trivial = word == "true";
                } else if word == "if" && alt.depth == 0 && !alt.after_arrow && !alt.in_lambda {
                    arm.absorb(&alt);
                    alt = WildcardAlternative::default();
                    arm.guarded = true;
                } else if !alt.after_arrow && !alt.in_lambda {
                    if alt.type_ascription_depth.is_some() {
                        alt.tokens += 1;
                        continue;
                    }
                    let leading = (alt.tokens == 0 || alt.only_modifiers)
                        && alt.depth == alt.arm_base_depth + alt.catch_all_parens;
                    alt.catch_all = leading && is_catch_all_binder_word(word);
                    alt.only_modifiers = leading && matches!(word, "ref" | "mut");
                    alt.tokens += 1;
                    if let Some(ctor) = WildcardCtor::of(word, was_after_dot) {
                        match alt.error_ctor {
                            None => {
                                alt.error_ctor = Some(ctor);
                                alt.error_ctor_depth = Some(alt.depth);
                            }
                            Some(WildcardCtor::Fail)
                                if matches!(ctor, WildcardCtor::Ub | WildcardCtor::Unsupported) =>
                            {
                                alt.error_ctor = Some(ctor);
                            }
                            Some(_) => {
                                alt.constrained = true;
                            }
                        }
                    } else if alt.error_ctor.is_some()
                        && (was_after_dot || !is_wildcard_payload_word(word))
                    {
                        alt.constrained = true;
                    }
                }
            }
            GuardTokKind::Literal | GuardTokKind::PathSep => {
                if arm.guarded {
                    arm.guard_tokens += 1;
                    arm.guard_trivial = false;
                } else if !alt.after_arrow && !alt.in_lambda {
                    if alt.type_ascription_depth.is_some() {
                        alt.tokens += 1;
                    } else {
                        alt.push_non_word();
                        if alt.error_ctor.is_some() {
                            alt.constrained = true;
                        }
                    }
                }
            }
            GuardTokKind::DotDot | GuardTokKind::Sym => {
                if arm.guarded {
                    arm.guard_tokens += 1;
                    arm.guard_trivial = false;
                } else if !alt.after_arrow && !alt.in_lambda {
                    if alt.type_ascription_depth.is_some() {
                        alt.tokens += 1;
                    } else if tok.kind == GuardTokKind::Sym && matches!(tok.text, "&" | "&&") {
                        let keep_mod = alt.tokens == 0 || alt.only_modifiers;
                        alt.tokens += 1;
                        alt.catch_all = false;
                        alt.only_modifiers = keep_mod;
                    } else if tok.is_sym(",") && alt.at_catch_all_paren_level() {
                        // A tuple component ended (`(_, _)`).
                        let component_wild = alt.catch_all || alt.or_wild;
                        alt.tuple_wild =
                            component_wild && (alt.tuple_wild || !alt.tuple_started);
                        alt.tuple_started = true;
                        alt.or_wild = false;
                        alt.tokens += 1;
                        alt.catch_all = false;
                        alt.only_modifiers = alt.tuple_wild;
                    } else if tok.is_sym("@") && alt.catch_all {
                        alt.tokens += 1;
                        alt.catch_all = false;
                        alt.only_modifiers = true;
                    } else if tok.is_sym(":")
                        && alt.depth > 0
                        && ((alt.error_ctor.is_some() && !alt.constrained) || alt.catch_all)
                    {
                        alt.tokens += 1;
                        alt.type_ascription_depth = Some(alt.depth);
                    } else {
                        alt.push_non_word();
                    }
                }
            }
        }
    }
    found
}

/// Scan a Lean `Specs/` module or a Rust specification source for
/// postcondition arms that accept every error escape (`awsm2`):
/// `| Err _ => True`, `Err(_) => true`, `| .err _ => True`,
/// `| .error _ => True`, `| .ub => True`, `| .unsupported => True`,
/// `| .fail .ub => True`, `matches!(out, Ok(_) | Err(_))`, and a catch-all
/// `_ => true` in an `Ok` match.
///
/// Arms that constrain the error payload (`Err(E::Overflow) => …`), carry a
/// non-trivial guard, or have any other body (`| .ub => False`) are accepted,
/// and comments and literals are never inspected. Every occurrence is
/// reported, in source order. Malformed source yields a single
/// [`ErrorBranchWildcardKind::MalformedSource`] diagnostic.
pub fn scan_error_branch_wildcard_diagnostics(
    source_label: &str,
    source_text: &str,
) -> Vec<ErrorBranchWildcardDiagnostic> {
    let dialect = SpecSourceDialect::from_source_label(source_label);
    match tokenize_spec_source(source_text, dialect) {
        Ok(toks) => scan_error_branch_wildcard_tokens(&toks, dialect)
            .into_iter()
            .map(|(line, kind)| ErrorBranchWildcardDiagnostic {
                source_label: String::from(source_label),
                line,
                kind,
            })
            .collect(),
        Err(unclosed) => vec![ErrorBranchWildcardDiagnostic {
            source_label: String::from(source_label),
            line: unclosed.line,
            kind: ErrorBranchWildcardKind::MalformedSource,
        }],
    }
}

// ----------------------------------------------------------------------------
// Guard 1: entry-point `requires` audit (`verus#3606`)
// ----------------------------------------------------------------------------

/// Whether `seg` is a valid crate-root segment name (`isValidCrateSegment` in
/// Lean): non-empty, starting with an ASCII letter or `_`, containing only
/// ASCII alphanumerics, `_`, or `-`. Rejects rustc impl/trait pseudo-segments
/// such as `<MyType as Trait>`, `<impl Foo>`, and `{{impl}}`.
fn is_valid_crate_segment(seg: &str) -> bool {
    let mut chars = seg.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '-')
}

/// Name-only binary entry-point test on a crate-qualified definition path
/// (`isBinaryEntrySymbol` in Lean, `is_binary_entry_symbol` in `anneal-spec`):
/// `main`, `::main`, `<crate>::main`, `::<crate>::main`, `_start`,
/// `<crate>::_start`, `__start`, and `<crate>::__start`.
///
/// Matching is on whole `::` segments with a validated crate segment, so
/// `domain`, `maintain`, `main_loop`, `<crate>::Type::main`,
/// `<MyType as Trait>::main`, `{{impl}}::main`, and `:::main` are rejected.
pub fn is_binary_entry_def_path(def_path: &str) -> bool {
    let stripped = def_path.strip_prefix("::").unwrap_or(def_path);
    let mut iter = stripped.split("::");
    let Some(first) = iter.next() else {
        return false;
    };
    match iter.next() {
        None => matches!(first, "main" | "_start" | "__start"),
        Some(second) => {
            iter.next().is_none()
                && is_valid_crate_segment(first)
                && matches!(second, "main" | "_start" | "__start")
        }
    }
}

/// Where an entry-point precondition was found.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EntryPointRequiresKind {
    /// A Rust `requires` companion (`IrContractRole::Requires`) whose MIR
    /// body is not the constant `true`.
    MirRequiresCompanion,
    /// An authored Lean precondition (`def pre` / `pre :=`) that is neither
    /// `True` nor a delegation to the generated default.
    AuthoredLeanPre,
    /// The authored Lean source has an unclosed comment or literal.
    MalformedSource,
}

impl EntryPointRequiresKind {
    /// Short wire tag of the finding.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MirRequiresCompanion => "mir_requires_companion",
            Self::AuthoredLeanPre => "authored_lean_pre",
            Self::MalformedSource => "malformed_source",
        }
    }
}

/// An `entry_point_requires` finding (`verus#3606`).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EntryPointRequiresDiagnostic {
    /// Definition path of the binary entry point.
    pub entry_def_path: String,
    /// Label of the offending source: the companion's definition path, or
    /// the authored Lean module's label.
    pub source_label: String,
    /// 1-based line of the authored precondition (`0` for a MIR companion).
    pub line: usize,
    /// Where the precondition was found.
    pub kind: EntryPointRequiresKind,
}

impl EntryPointRequiresDiagnostic {
    /// The guard every diagnostic of this type reports under.
    pub const GUARD: SpecBoundaryGuardId = SpecBoundaryGuardId::EntryPointRequires;
}

impl fmt::Display for EntryPointRequiresDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}: ", self.source_label, self.line, Self::GUARD)?;
        match self.kind {
            EntryPointRequiresKind::MirRequiresCompanion => write!(
                f,
                "binary entry point `{}` carries a non-trivial Rust `requires`; no verified \
                 caller discharges it",
                self.entry_def_path
            ),
            EntryPointRequiresKind::AuthoredLeanPre => write!(
                f,
                "binary entry point `{}` carries a non-trivial authored precondition `pre`; no \
                 verified caller discharges it",
                self.entry_def_path
            ),
            EntryPointRequiresKind::MalformedSource => write!(
                f,
                "unclosed comment or literal in the specification of binary entry point `{}` \
                 (fail-closed)",
                self.entry_def_path
            ),
        }
    }
}

/// Whether a `requires` companion body is the constant `true`: a single basic
/// block that only assigns `const true` to the return place and returns.
pub fn ir_requires_body_is_trivially_true(mir: &IrCapturedMir) -> bool {
    let [block] = mir.basic_blocks.as_slice() else {
        return false;
    };
    if !matches!(block.terminator.kind, IrTerminatorKind::Return) {
        return false;
    }
    let mut returns_true = false;
    for stmt in &block.statements {
        match &stmt.kind {
            IrStatementKind::StorageLive(_)
            | IrStatementKind::StorageDead(_)
            | IrStatementKind::Coverage
            | IrStatementKind::ConstEvalCounter
            | IrStatementKind::Nop => {}
            IrStatementKind::Assign(place, IrRvalue::Use(IrOperand::Constant(constant)))
                if place.local_ == 0 && place.projection.is_empty() =>
            {
                let is_true = matches!(constant.ty.kind, IrRigidTy::Bool)
                    && matches!(
                        constant.val,
                        IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
                            bits: 1,
                            size_bytes: 1,
                        }))
                    );
                if !is_true {
                    return false;
                }
                returns_true = true;
            }
            _ => return false,
        }
    }
    returns_true
}

/// Audit the Rust `requires` companions of a subject item.
///
/// When `subject` is a binary entry point — by [`is_binary_entry_def_path`]
/// or because the caller lists its definition path in `extra_entry_def_paths`
/// (items the front end classified by attribute, such as `#[entry]`) — every
/// companion in `companions` with role `IrContractRole::Requires(subject)`
/// whose body is not the constant `true` is reported.
pub fn audit_mir_entry_point_requires(
    subject: &IrCapturedMir,
    companions: &[IrCapturedMir],
    extra_entry_def_paths: &[&str],
) -> Vec<EntryPointRequiresDiagnostic> {
    let is_entry = is_binary_entry_def_path(&subject.def_path)
        || extra_entry_def_paths.contains(&subject.def_path.as_str());
    if !is_entry || subject.role != IrContractRole::Subject {
        return Vec::new();
    }
    let mut out = Vec::new();
    for companion in companions {
        if let IrContractRole::Requires(target) = &companion.role
            && target == &subject.def_path
            && !ir_requires_body_is_trivially_true(companion)
        {
            out.push(EntryPointRequiresDiagnostic {
                entry_def_path: subject.def_path.clone(),
                source_label: companion.def_path.clone(),
                line: 0,
                kind: EntryPointRequiresKind::MirRequiresCompanion,
            });
        }
    }
    out.sort();
    out
}

/// Whether a Lean precondition body is trivial for the entry-point guard:
/// `True` (possibly behind nested `fun … =>` and matched parentheses), or a
/// delegation to the generated default precondition
/// (`Obligations.<Item>.defaultPre args`,
/// `Obligations.<Item>.defaultSpec.pre args`,
/// `Obligations.<Item>.rustRequires args`), whose own triviality is decided
/// by the MIR companion audit.
fn lean_pre_body_is_trivial(body: &[GuardTok<'_>], module_defines_pre: bool) -> bool {
    let mut body = body;
    // Repeatedly strip matched outer parentheses and leading `fun <binders> =>`.
    loop {
        if body.len() >= 2 && body[0].is_sym("(") && matching_close(body, 0) == Some(body.len() - 1)
        {
            body = &body[1..body.len() - 1];
            continue;
        }
        if body
            .first()
            .is_some_and(|tok| tok.is_word("fun") || tok.is_word("λ"))
            && let Some(arrow) = body
                .iter()
                .position(|tok| tok.kind == GuardTokKind::FatArrow || tok.is_sym("↦"))
        {
            body = &body[arrow + 1..];
            continue;
        }
        break;
    }
    // `True`, or a reference to this module's own `def pre`, which the audit
    // inspects where it is defined. A `pre` the module does not define comes
    // from elsewhere and cannot be inspected.
    if body.len() == 1
        && (body[0].is_word("True") || (module_defines_pre && body[0].is_word("pre")))
    {
        return true;
    }
    // `Obligations.<path>.<defaultPre|rustRequires|pre> <lowercase args>`
    if !body.first().is_some_and(|tok| tok.is_word("Obligations")) {
        return false;
    }
    let mut idx = 1usize;
    let mut last_component = "";
    while body.get(idx).is_some_and(|tok| tok.is_sym("."))
        && let Some(component) = body
            .get(idx + 1)
            .filter(|tok| tok.kind == GuardTokKind::Word)
    {
        last_component = component.text;
        idx += 2;
    }
    matches!(last_component, "defaultPre" | "rustRequires" | "pre")
        && body[idx..].iter().all(|tok| {
            tok.kind == GuardTokKind::Word
                && tok
                    .text
                    .chars()
                    .next()
                    .is_some_and(|first| first.is_lowercase() || first == '_')
        })
}

/// Index, among the explicit arguments of the generated
/// `Obligations.<Item>.refine*Spec` constructors, of the argument that becomes
/// (a conjunct of) the specification's `pre`.
fn refine_spec_pre_argument(leaf: &str) -> Option<usize> {
    match leaf {
        "refineSpec"
        | "refineStatefulSpec"
        | "refineTotalSpec"
        | "refineSafeSpec"
        | "refineSafeStatefulSpec" => Some(0),
        "refineEquivSpec" | "refineModularSpec" | "refineUbExceptionSpec" => Some(1),
        _ => None,
    }
}

/// Whether `tok` begins a new Lean command.
fn is_lean_command_start(toks: &[GuardTok<'_>], idx: usize) -> bool {
    toks.get(idx).is_some_and(|tok| {
        (tok.kind == GuardTokKind::Word && LEAN_COMMAND_KEYWORDS.contains(&tok.text))
            || (tok.is_sym("@") && toks.get(idx + 1).is_some_and(|open| open.is_sym("[")))
    })
}

/// End (exclusive) of the Lean command whose body starts at `start`: the next
/// command keyword or attribute at bracket depth 0.
fn lean_command_end(toks: &[GuardTok<'_>], start: usize) -> usize {
    let mut end = start;
    let mut depth = 0i32;
    while let Some(tok) = toks.get(end) {
        if depth == 0 && is_lean_command_start(toks, end) {
            break;
        }
        depth += bracket_delta(tok);
        end += 1;
    }
    end
}

/// Whether the token at `idx` is the first token on its source line.
fn is_first_on_line(toks: &[GuardTok<'_>], idx: usize) -> bool {
    idx == 0 || toks[idx - 1].line < toks[idx].line
}

/// Kind of a Lean structure / instance field definition starting at `idx`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LeanFieldHead {
    /// `name [binders] [: Type] := …` at the index of `:=`.
    Assign(usize),
    /// `name [binders] [: Type] | pat => …` at the index of the first `|`.
    Equations(usize),
}

/// If a structure or `where` field definition starts at `idx` (`name := …`,
/// `name args := …`, `name (args : T) := …`, `name : T := …`, or
/// equation-compiler `name | pat => …`), returns its header terminator.
fn lean_field_header(toks: &[GuardTok<'_>], idx: usize) -> Option<LeanFieldHead> {
    let name = toks.get(idx)?;
    if name.kind != GuardTokKind::Word
        || LEAN_COMMAND_KEYWORDS.contains(&name.text)
        || matches!(
            name.text,
            "where" | "with" | "in" | "then" | "else" | "do" | "by" | "fun" | "match"
        )
        || (idx > 0 && toks[idx - 1].is_sym("."))
    {
        return None;
    }
    let field_position = idx == 0
        || is_first_on_line(toks, idx)
        || toks[idx - 1].is_word("where")
        || toks[idx - 1].is_word("with")
        || toks[idx - 1].is_sym("{")
        || toks[idx - 1].is_sym(",");
    let mut cursor = idx + 1;
    while let Some(binder) = toks.get(cursor) {
        let is_plain_binder = binder.kind == GuardTokKind::Word
            && !LEAN_COMMAND_KEYWORDS.contains(&binder.text)
            && !matches!(
                binder.text,
                "where" | "with" | "in" | "then" | "else" | "do" | "by" | "fun" | "match"
            )
            && binder
                .text
                .chars()
                .next()
                .is_some_and(|first| first.is_lowercase() || first == '_');
        if is_plain_binder {
            cursor += 1;
            continue;
        }
        if field_position
            && (binder.is_sym("(") || binder.is_sym("{") || binder.is_sym("["))
            && let Some(close) = matching_close(toks, cursor)
        {
            cursor = close + 1;
            continue;
        }
        break;
    }
    // Optional explicit field type annotation `: Type` in field position.
    if field_position && toks.get(cursor).is_some_and(|t| t.is_sym(":")) {
        cursor += 1;
        let mut depth = 0i32;
        while let Some(t) = toks.get(cursor) {
            if depth == 0
                && (t.is_sym(":=")
                    || t.is_sym("|")
                    || is_lean_command_start(toks, cursor)
                    || (t.kind == GuardTokKind::Sym && matches!(t.text, "," | "}" | ")" | "]")))
            {
                break;
            }
            depth += bracket_delta(t);
            cursor += 1;
        }
    }
    let head = toks.get(cursor)?;
    if head.is_sym(":=") {
        (cursor == idx + 1 || field_position).then_some(LeanFieldHead::Assign(cursor))
    } else if head.is_sym("|") && field_position {
        Some(LeanFieldHead::Equations(cursor))
    } else {
        None
    }
}

/// Strip matched outer parentheses.
fn strip_outer_parens<'t, 'a>(mut toks: &'t [GuardTok<'a>]) -> &'t [GuardTok<'a>] {
    while toks.len() >= 2 && toks[0].is_sym("(") && matching_close(toks, 0) == Some(toks.len() - 1)
    {
        toks = &toks[1..toks.len() - 1];
    }
    toks
}

/// Split the arguments of a Lean application (`a (b c) d.e ⟨f⟩`) into token
/// ranges. `None` when an argument is not an identifier, literal, or
/// bracketed group (an operator such as `<|` or `$`, a bare `fun`).
fn lean_application_args<'t, 'a>(toks: &'t [GuardTok<'a>]) -> Option<Vec<&'t [GuardTok<'a>]>> {
    let mut args = Vec::new();
    let mut idx = 0usize;
    while let Some(tok) = toks.get(idx) {
        let start = idx;
        if bracket_delta(tok) > 0 {
            let mut depth = 0i32;
            loop {
                depth += bracket_delta(toks.get(idx)?);
                idx += 1;
                if depth == 0 {
                    break;
                }
            }
        } else if tok.kind == GuardTokKind::Word && !matches!(tok.text, "fun" | "by" | "λ") {
            idx += 1;
            while toks.get(idx).is_some_and(|dot| dot.is_sym("."))
                && toks
                    .get(idx + 1)
                    .is_some_and(|part| part.kind == GuardTokKind::Word)
            {
                idx += 2;
            }
        } else if tok.kind == GuardTokKind::Literal {
            idx += 1;
        } else {
            return None;
        }
        args.push(&toks[start..idx]);
    }
    Some(args)
}

/// Body tokens of every `def` / `abbrev` in `toks` whose leaf name is `leaf`,
/// or `None` for a declaration without a plain `:= body` (equation compiler,
/// `where` structure, bodiless).
fn lean_definition_bodies<'t, 'a>(
    toks: &'t [GuardTok<'a>],
    leaf: &str,
) -> Vec<Option<&'t [GuardTok<'a>]>> {
    let mut bodies = Vec::new();
    for idx in 0..toks.len() {
        if !(toks[idx].is_word("def") || toks[idx].is_word("abbrev")) {
            continue;
        }
        let (name, after_name) = read_lean_dotted_name(toks, idx + 1);
        if name.is_empty() || declaration_leaf(&name) != leaf {
            continue;
        }
        let end = lean_command_end(toks, after_name);
        let mut depth = 0i32;
        let mut assign = None;
        for cursor in after_name..end {
            let tok = &toks[cursor];
            if depth == 0 && (tok.is_sym(":=") || tok.is_sym("|") || tok.is_word("where")) {
                assign = tok.is_sym(":=").then_some(cursor);
                break;
            }
            depth += bracket_delta(tok);
        }
        bodies.push(assign.map(|assign| &toks[assign + 1..end]));
    }
    bodies
}

/// Whether the tokens between a declaration's name and its body give it a
/// specification-class type (`ItemSpec "…"`, `StatefulItemSpec "…"`, …).
fn is_lean_spec_class_header(header: &[GuardTok<'_>]) -> bool {
    header.iter().any(|tok| {
        tok.kind == GuardTokKind::Word && declaration_leaf(tok.text).ends_with("ItemSpec")
    })
}

/// A specification-valued Lean declaration: `instance … : ItemSpec "…"`,
/// `def name : StatefulItemSpec "…"`, ….
struct LeanSpecValueDecl<'t, 'a> {
    /// Declared name; empty for an anonymous instance.
    name: String,
    line: usize,
    /// Tokens after `:=`; `None` for a `where` structure (whose fields the
    /// field audit inspects).
    value: Option<&'t [GuardTok<'a>]>,
    /// Field tokens after `where`, for a `where` structure.
    where_fields: Option<&'t [GuardTok<'a>]>,
}

/// Whether a structure-instance field takes its value from a whole base
/// structure: the spread field `__ := base` or a parent projection
/// `toItemSpec := base`. Such a field supplies `pre` from `base`.
fn is_lean_spread_field_name(name: &str) -> bool {
    name == "__"
        || name
            .strip_prefix("to")
            .is_some_and(|rest| rest.starts_with(|first: char| first.is_uppercase()))
}

/// Values of the spread fields ([`is_lean_spread_field_name`]) among the
/// fields of a structure instance (`{ … }` or `where …`).
fn lean_spread_field_values<'t, 'a>(fields: &'t [GuardTok<'a>]) -> Vec<&'t [GuardTok<'a>]> {
    let mut values = Vec::new();
    let mut depth = 0i32;
    let mut pos = 0usize;
    while pos < fields.len() {
        let tok = &fields[pos];
        if depth == 0
            && tok.kind == GuardTokKind::Word
            && is_lean_spread_field_name(tok.text)
            && fields.get(pos + 1).is_some_and(|assign| assign.is_sym(":="))
            && !(pos > 0 && fields[pos - 1].is_sym("."))
        {
            let start = pos + 2;
            let mut end = start;
            let mut value_depth = 0i32;
            while let Some(value_tok) = fields.get(end) {
                if value_depth == 0
                    && (value_tok.is_sym(",")
                        || (end > start
                            && is_first_on_line(fields, end)
                            && lean_field_header(fields, end).is_some()))
                {
                    break;
                }
                value_depth += bracket_delta(value_tok);
                end += 1;
            }
            values.push(&fields[start..end]);
            pos = end;
            continue;
        }
        depth += bracket_delta(tok);
        pos += 1;
    }
    values
}

/// Every specification-valued declaration of a Lean module, in source order.
fn lean_spec_value_decls<'t, 'a>(toks: &'t [GuardTok<'a>]) -> Vec<LeanSpecValueDecl<'t, 'a>> {
    let mut decls = Vec::new();
    for idx in 0..toks.len() {
        let keyword = &toks[idx];
        if !(keyword.is_word("instance") || keyword.is_word("def") || keyword.is_word("abbrev")) {
            continue;
        }
        let end = lean_command_end(toks, idx + 1);
        let mut depth = 0i32;
        let mut body = None;
        for cursor in idx + 1..end {
            let tok = &toks[cursor];
            if depth == 0 && (tok.is_sym(":=") || tok.is_word("where")) {
                body = Some(cursor);
                break;
            }
            depth += bracket_delta(tok);
        }
        let header_end = body.unwrap_or(end);
        // The type follows the last top-level `:` of the header.
        let mut depth = 0i32;
        let mut colon = None;
        for cursor in idx + 1..header_end {
            let tok = &toks[cursor];
            if depth == 0 && tok.is_sym(":") {
                colon = Some(cursor);
            }
            depth += bracket_delta(tok);
        }
        let Some(colon) = colon else {
            continue;
        };
        if !is_lean_spec_class_header(&toks[colon + 1..header_end]) {
            continue;
        }
        let (name, _) = read_lean_dotted_name(toks, idx + 1);
        let (value, where_fields) = match body {
            Some(body) if toks[body].is_sym(":=") => (Some(&toks[body + 1..end]), None),
            Some(body) => (None, Some(&toks[body + 1..end])),
            // A specification-typed declaration without a body: fail closed.
            None => (Some(&toks[end..end]), None),
        };
        decls.push(LeanSpecValueDecl {
            name,
            line: keyword.line,
            value,
            where_fields,
        });
    }
    decls
}

/// Whether a function-valued `pre` argument (`extraPre` of `refineSpec`) is
/// trivially true: `fun _ => True`, a delegation to the generated default, or
/// the name of a definition of this module whose body is.
fn lean_pre_argument_is_trivial(
    arg: &[GuardTok<'_>],
    toks: &[GuardTok<'_>],
    module_defines_pre: bool,
) -> bool {
    let arg = strip_outer_parens(arg);
    let is_plain_name = !arg.is_empty()
        && arg.iter().enumerate().all(|(pos, tok)| {
            if pos % 2 == 0 {
                tok.kind == GuardTokKind::Word
            } else {
                tok.is_sym(".")
            }
        })
        && arg.len() % 2 == 1;
    if is_plain_name && !arg[0].is_word("Obligations") && !arg[0].is_word("True") {
        let leaf = arg[arg.len() - 1].text;
        let bodies = lean_definition_bodies(toks, leaf);
        return !bodies.is_empty()
            && bodies.iter().all(|body| {
                body.is_some_and(|body| lean_pre_body_is_trivial(body, module_defines_pre))
            });
    }
    lean_pre_body_is_trivial(arg, module_defines_pre)
}

/// Whether a specification value (the body of `instance : ItemSpec "…" := …`)
/// provably carries a trivial or generated-default precondition:
///
/// * a structure instance `{ … }` (its `pre` field, if any, is inspected by
///   the field audit; a `{ base with … }` base must itself be safe);
/// * `Obligations.<Item>.default*Spec`;
/// * `Obligations.<Item>.refine*Spec …` whose `pre` argument is trivially
///   true;
/// * the name of another specification-valued declaration of this module
///   (inspected where it is declared).
///
/// Anything else (an anonymous constructor `⟨pre, post⟩`, `ItemSpec.mk …`, a
/// tactic block, an imported value) cannot be inspected and fails closed.
fn lean_spec_value_is_safe(
    value: &[GuardTok<'_>],
    toks: &[GuardTok<'_>],
    decls: &[LeanSpecValueDecl<'_, '_>],
    module_defines_pre: bool,
) -> bool {
    let value = strip_outer_parens(value);
    let Some(first) = value.first() else {
        return false;
    };
    if first.is_sym("{") {
        if matching_close(value, 0) != Some(value.len() - 1) {
            return false;
        }
        let inner = &value[1..value.len() - 1];
        let mut depth = 0i32;
        let mut fields_start = 0usize;
        for (pos, tok) in inner.iter().enumerate() {
            if depth == 0 && tok.is_word("with") {
                if !lean_spec_value_is_safe(&inner[..pos], toks, decls, module_defines_pre) {
                    return false;
                }
                fields_start = pos + 1;
                break;
            }
            depth += bracket_delta(tok);
        }
        // Fail closed on a Lean structure field pun `{ pre, … }` or
        // `{ base with pre }` unless `pre` is defined (and thus audited) in
        // this module.
        let fields = &inner[fields_start..];
        // A spread field (`__ := base`) supplies `pre` like a `with` base.
        if lean_spread_field_values(fields)
            .into_iter()
            .any(|base| !lean_spec_value_is_safe(base, toks, decls, module_defines_pre))
        {
            return false;
        }
        let mut fdepth = 0i32;
        let mut at_field_start = true;
        for (pos, tok) in fields.iter().enumerate() {
            if fdepth == 0 {
                if at_field_start
                    && tok.is_word("pre")
                    && fields.get(pos + 1).is_none_or(|next| next.is_sym(","))
                    && !module_defines_pre
                {
                    return false;
                }
                at_field_start = tok.is_sym(",");
            }
            fdepth += bracket_delta(tok);
        }
        return true;
    }
    if first.kind != GuardTokKind::Word {
        return false;
    }
    let (name, after_name) = read_lean_dotted_name(value, 0);
    let leaf = declaration_leaf(&name);
    let args = &value[after_name..];
    if name.starts_with("Obligations.") {
        if leaf.starts_with("default") && leaf.ends_with("Spec") {
            return args.is_empty();
        }
        let Some(pre_index) = refine_spec_pre_argument(leaf) else {
            return false;
        };
        return lean_application_args(args)
            .and_then(|args| args.get(pre_index).copied())
            .is_some_and(|pre| lean_pre_argument_is_trivial(pre, toks, module_defines_pre));
    }
    args.is_empty()
        && decls
            .iter()
            .any(|decl| !decl.name.is_empty() && declaration_leaf(&decl.name) == leaf)
}

/// Item module paths a `Specs` module stands for: `Demo.main` for the source
/// label `…/Specs/Demo/main.lean` and for a `namespace Specs.Demo.main`
/// command. Empty when neither is present.
fn lean_spec_module_item_paths(source_label: &str, toks: &[GuardTok<'_>]) -> Vec<String> {
    let mut paths = Vec::new();
    if let Some(at) = source_label.rfind("Specs/")
        && let Some(stem) = source_label[at + "Specs/".len()..].strip_suffix(".lean")
        && !stem.is_empty()
    {
        paths.push(stem.replace('/', "."));
    }
    for idx in 0..toks.len() {
        if toks[idx].is_word("namespace") {
            let (name, _) = read_lean_dotted_name(toks, idx + 1);
            if let Some(item) = name.strip_prefix("Specs.")
                && !item.is_empty()
                && !paths.iter().any(|known| known == item)
            {
                paths.push(String::from(item));
            }
        }
    }
    paths
}

/// Audit an authored Lean `Specs/<Item>.lean` module of a binary entry point.
///
/// Reports every precondition (`def pre` / `abbrev pre` / `opaque pre` /
/// dotted `<Prefix>.pre` in `:=` or equation-compiler `|` form, or an instance
/// / struct field `pre := body`) whose body is neither `True` nor a delegation
/// to the generated default. A module without a precondition, and the module of
/// a non-entry item, yield no diagnostics.
pub fn audit_lean_spec_entry_point_requires(
    entry_def_path: &str,
    source_label: &str,
    specs_source: &str,
    extra_entry_def_paths: &[&str],
) -> Vec<EntryPointRequiresDiagnostic> {
    if !(is_binary_entry_def_path(entry_def_path)
        || extra_entry_def_paths.contains(&entry_def_path))
    {
        return Vec::new();
    }
    let diagnostic = |line, kind| EntryPointRequiresDiagnostic {
        entry_def_path: String::from(entry_def_path),
        source_label: String::from(source_label),
        line,
        kind,
    };
    let toks = match tokenize_spec_source(specs_source, SpecSourceDialect::Lean) {
        Ok(toks) => toks,
        Err(unclosed) => {
            return vec![diagnostic(
                unclosed.line,
                EntryPointRequiresKind::MalformedSource,
            )];
        }
    };
    let mut out = Vec::new();
    let module_defines_pre = (0..toks.len()).any(|idx| {
        toks[idx].kind == GuardTokKind::Word
            && matches!(toks[idx].text, "def" | "abbrev" | "opaque")
            && declaration_leaf(&read_lean_dotted_name(&toks, idx + 1).0) == "pre"
    });
    // Specification values that are not structure instances (`:= ⟨pre, post⟩`,
    // `:= Obligations.<Item>.refineSpec extraPre extraPost`, …).
    let spec_decls = lean_spec_value_decls(&toks);
    for decl in &spec_decls {
        let unsafe_value = decl.value.is_some_and(|value| {
            !lean_spec_value_is_safe(value, &toks, &spec_decls, module_defines_pre)
        });
        // `where __ := base` takes `pre` from `base`.
        let unsafe_spread = decl.where_fields.is_some_and(|fields| {
            lean_spread_field_values(fields).into_iter().any(|base| {
                !lean_spec_value_is_safe(base, &toks, &spec_decls, module_defines_pre)
            })
        });
        if unsafe_value || unsafe_spread {
            out.push(diagnostic(
                decl.line,
                EntryPointRequiresKind::AuthoredLeanPre,
            ));
        }
    }
    // `attribute [instance] name` registers `name` as the specification;
    // it must be a specification value declared (and inspected) here.
    for idx in 0..toks.len() {
        if !toks[idx].is_word("attribute") || !toks.get(idx + 1).is_some_and(|t| t.is_sym("[")) {
            continue;
        }
        let Some(close) = matching_close(&toks, idx + 1) else {
            continue;
        };
        if !toks[idx + 2..close].iter().any(|t| t.is_word("instance")) {
            continue;
        }
        let mut cursor = close + 1;
        while toks.get(cursor).is_some_and(|t| t.kind == GuardTokKind::Word)
            && !is_lean_command_start(&toks, cursor)
        {
            let (name, next) = read_lean_dotted_name(&toks, cursor);
            let leaf = declaration_leaf(&name);
            if !spec_decls
                .iter()
                .any(|decl| !decl.name.is_empty() && declaration_leaf(&decl.name) == leaf)
            {
                out.push(diagnostic(
                    toks[idx].line,
                    EntryPointRequiresKind::AuthoredLeanPre,
                ));
            }
            cursor = next.max(cursor + 1);
        }
    }
    // A delegation to generated obligations is only trivial for this
    // module's own item; another item's `requires` is not audited as an
    // entry-point precondition.
    let item_paths = lean_spec_module_item_paths(source_label, &toks);
    if !item_paths.is_empty() {
        for idx in 0..toks.len() {
            if !toks[idx].is_word("Obligations")
                || (idx > 0
                    && (toks[idx - 1].is_sym(".")
                        || toks[idx - 1].is_word("import")
                        || toks[idx - 1].is_word("open")))
            {
                continue;
            }
            let (name, _) = read_lean_dotted_name(&toks, idx);
            let components: Vec<&str> = name.split('.').collect();
            let Some(leaf_at) = components.iter().skip(1).position(|component| {
                matches!(*component, "defaultPre" | "rustRequires" | "pre")
                    || (component.ends_with("Spec")
                        && (component.starts_with("default") || component.starts_with("refine")))
            }) else {
                continue;
            };
            let item = components[1..=leaf_at].join(".");
            if !item_paths.contains(&item) {
                out.push(diagnostic(
                    toks[idx].line,
                    EntryPointRequiresKind::AuthoredLeanPre,
                ));
            }
        }
    }
    let mut idx = 0usize;
    while idx < toks.len() {
        // `def|abbrev|opaque [Prefix.]pre ...` or the instance/struct field
        // `pre := body` / `pre args := body`.
        let mut decl_after_name = None;
        if toks[idx].kind == GuardTokKind::Word
            && matches!(toks[idx].text, "def" | "abbrev" | "opaque")
        {
            let (name, after_name) = read_lean_dotted_name(&toks, idx + 1);
            if declaration_leaf(&name) == "pre" {
                decl_after_name = Some(after_name);
            }
        }
        let field_head = if toks[idx].is_word("pre") {
            lean_field_header(&toks, idx)
        } else {
            None
        };
        if decl_after_name.is_none() && field_head.is_none() {
            idx += 1;
            continue;
        }
        let line = toks[idx].line;
        if let Some(after_name) = decl_after_name {
            // Find `:=`, `|`, or the next command (so equation-compiler `def pre`
            // with `|` arms cannot bleed into a later `def post := True`).
            let mut cursor = after_name;
            let mut depth = 0i32;
            while let Some(tok) = toks.get(cursor) {
                if depth == 0
                    && (tok.is_sym(":=")
                        || tok.is_sym("|")
                        || (tok.kind == GuardTokKind::Word
                            && LEAN_COMMAND_KEYWORDS.contains(&tok.text))
                        || (tok.is_sym("@") && toks.get(cursor + 1).is_some_and(|o| o.is_sym("["))))
                {
                    break;
                }
                depth += bracket_delta(tok);
                cursor += 1;
            }
            if toks.get(cursor).is_some_and(|t| t.is_sym("|")) {
                // Equation-compiler `def pre : ... | pat => body`: skip to next
                // top-level command and fail closed unless every arm body is trivial.
                let mut end = cursor;
                let mut d = 0i32;
                let mut all_arms_trivial = true;
                let mut saw_arm = false;
                while let Some(t) = toks.get(end) {
                    if d == 0
                        && ((t.kind == GuardTokKind::Word
                            && LEAN_COMMAND_KEYWORDS.contains(&t.text))
                            || (t.is_sym("@") && toks.get(end + 1).is_some_and(|o| o.is_sym("["))))
                    {
                        break;
                    }
                    if d == 0 && t.is_sym("|") {
                        saw_arm = true;
                        let mut arrow = end + 1;
                        let mut ad = 0i32;
                        while let Some(at) = toks.get(arrow) {
                            if ad == 0 && at.kind == GuardTokKind::FatArrow {
                                break;
                            }
                            if ad == 0
                                && at.kind == GuardTokKind::Word
                                && LEAN_COMMAND_KEYWORDS.contains(&at.text)
                            {
                                break;
                            }
                            ad += bracket_delta(at);
                            arrow += 1;
                        }
                        if toks
                            .get(arrow)
                            .is_some_and(|at| at.kind == GuardTokKind::FatArrow)
                        {
                            let b_start = arrow + 1;
                            let mut b_end = b_start;
                            let mut bd = 0i32;
                            while let Some(bt) = toks.get(b_end) {
                                if bd == 0
                                    && (bt.is_sym("|")
                                        || (bt.kind == GuardTokKind::Word
                                            && LEAN_COMMAND_KEYWORDS.contains(&bt.text))
                                        || (bt.is_sym("@")
                                            && toks.get(b_end + 1).is_some_and(|o| o.is_sym("["))))
                                {
                                    break;
                                }
                                bd += bracket_delta(bt);
                                b_end += 1;
                            }
                            if !lean_pre_body_is_trivial(&toks[b_start..b_end], module_defines_pre)
                            {
                                all_arms_trivial = false;
                            }
                            end = b_end;
                            continue;
                        } else {
                            all_arms_trivial = false;
                        }
                    }
                    d += bracket_delta(t);
                    end += 1;
                }
                if !saw_arm || !all_arms_trivial {
                    out.push(diagnostic(line, EntryPointRequiresKind::AuthoredLeanPre));
                }
                idx = end.max(idx + 1);
                continue;
            }
            if !toks.get(cursor).is_some_and(|t| t.is_sym(":=")) {
                // `opaque pre : ...` or bodiless declaration: fail closed.
                out.push(diagnostic(line, EntryPointRequiresKind::AuthoredLeanPre));
                idx = cursor.max(idx + 1);
                continue;
            }
            let body_start = (cursor + 1).min(toks.len());
            let mut body_end = body_start;
            let mut d = 0i32;
            while let Some(tok) = toks.get(body_end) {
                if d == 0 {
                    let next_command =
                        tok.kind == GuardTokKind::Word && LEAN_COMMAND_KEYWORDS.contains(&tok.text);
                    let next_field = tok.kind == GuardTokKind::Word
                        && body_end > body_start
                        && toks.get(body_end + 1).is_some_and(|a| a.is_sym(":="));
                    let attribute =
                        tok.is_sym("@") && toks.get(body_end + 1).is_some_and(|o| o.is_sym("["));
                    if next_command || next_field || attribute {
                        break;
                    }
                }
                d += bracket_delta(tok);
                body_end += 1;
            }
            if !lean_pre_body_is_trivial(&toks[body_start..body_end], module_defines_pre) {
                out.push(diagnostic(line, EntryPointRequiresKind::AuthoredLeanPre));
            }
            idx = body_end.max(idx + 1);
            continue;
        }
        // Instance or struct literal field:
        //   - `pre [binders] [: Type] := body`
        //   - `pre [binders] [: Type] | pat => body` (equation compiler inside `where`)
        let is_next_field = |pos: usize, start: usize| -> bool {
            pos > start
                && lean_field_header(&toks, pos).is_some_and(|head| match head {
                    LeanFieldHead::Assign(assign) => {
                        assign == pos + 1 || is_first_on_line(&toks, pos)
                    }
                    LeanFieldHead::Equations(_) => is_first_on_line(&toks, pos),
                })
        };
        match field_head {
            Some(LeanFieldHead::Equations(pipe_idx)) => {
                let mut end = pipe_idx;
                let mut d = 0i32;
                let mut all_arms_trivial = true;
                let mut saw_arm = false;
                while let Some(t) = toks.get(end) {
                    if d == 0 {
                        let next_command =
                            t.kind == GuardTokKind::Word && LEAN_COMMAND_KEYWORDS.contains(&t.text);
                        let attribute =
                            t.is_sym("@") && toks.get(end + 1).is_some_and(|o| o.is_sym("["));
                        let struct_sep =
                            t.kind == GuardTokKind::Sym && matches!(t.text, "," | "}" | ")" | "]");
                        if next_command || attribute || struct_sep || is_next_field(end, pipe_idx) {
                            break;
                        }
                    }
                    if d == 0 && t.is_sym("|") {
                        saw_arm = true;
                        let mut arrow = end + 1;
                        let mut ad = 0i32;
                        while let Some(at) = toks.get(arrow) {
                            if ad == 0 && at.kind == GuardTokKind::FatArrow {
                                break;
                            }
                            if ad == 0
                                && at.kind == GuardTokKind::Word
                                && LEAN_COMMAND_KEYWORDS.contains(&at.text)
                            {
                                break;
                            }
                            ad += bracket_delta(at);
                            arrow += 1;
                        }
                        if toks
                            .get(arrow)
                            .is_some_and(|at| at.kind == GuardTokKind::FatArrow)
                        {
                            let b_start = arrow + 1;
                            let mut b_end = b_start;
                            let mut bd = 0i32;
                            while let Some(bt) = toks.get(b_end) {
                                if bd == 0 {
                                    let next_command = bt.kind == GuardTokKind::Word
                                        && LEAN_COMMAND_KEYWORDS.contains(&bt.text);
                                    let attribute = bt.is_sym("@")
                                        && toks.get(b_end + 1).is_some_and(|o| o.is_sym("["));
                                    let struct_sep = bt.kind == GuardTokKind::Sym
                                        && matches!(bt.text, "," | "}" | ")" | "]");
                                    if bt.is_sym("|")
                                        || next_command
                                        || attribute
                                        || struct_sep
                                        || is_next_field(b_end, b_start)
                                    {
                                        break;
                                    }
                                }
                                bd += bracket_delta(bt);
                                b_end += 1;
                            }
                            if !lean_pre_body_is_trivial(&toks[b_start..b_end], module_defines_pre)
                            {
                                all_arms_trivial = false;
                            }
                            end = b_end;
                            continue;
                        } else {
                            all_arms_trivial = false;
                        }
                    }
                    d += bracket_delta(t);
                    end += 1;
                }
                if !saw_arm || !all_arms_trivial {
                    out.push(diagnostic(line, EntryPointRequiresKind::AuthoredLeanPre));
                }
                idx = end.max(idx + 1);
            }
            Some(LeanFieldHead::Assign(assign)) => {
                let body_start = assign + 1;
                let mut body_end = body_start;
                let mut depth = 0i32;
                while let Some(tok) = toks.get(body_end) {
                    if depth == 0 {
                        let next_command = tok.kind == GuardTokKind::Word
                            && LEAN_COMMAND_KEYWORDS.contains(&tok.text);
                        let attribute = tok.is_sym("@")
                            && toks.get(body_end + 1).is_some_and(|open| open.is_sym("["));
                        let struct_sep = tok.kind == GuardTokKind::Sym
                            && matches!(tok.text, "," | "}" | ")" | "]");
                        if next_command
                            || is_next_field(body_end, body_start)
                            || attribute
                            || struct_sep
                        {
                            break;
                        }
                    }
                    depth += bracket_delta(tok);
                    body_end += 1;
                }
                if !lean_pre_body_is_trivial(&toks[body_start..body_end], module_defines_pre) {
                    out.push(diagnostic(line, EntryPointRequiresKind::AuthoredLeanPre));
                }
                idx = body_end.max(idx + 1);
            }
            None => idx += 1,
        }
    }
    out.sort_by_key(|diagnostic| diagnostic.line);
    out.dedup();
    out
}

/// Audit one binary entry point end to end: its Rust `requires` companions
/// ([`audit_mir_entry_point_requires`]) and, when present, its authored Lean
/// `Specs/<Item>.lean` module ([`audit_lean_spec_entry_point_requires`]),
/// given as `(source_label, source_text)`.
pub fn audit_entry_point_requires_bundle(
    subject: &IrCapturedMir,
    companions: &[IrCapturedMir],
    authored_specs: Option<(&str, &str)>,
    extra_entry_def_paths: &[&str],
) -> Vec<EntryPointRequiresDiagnostic> {
    let mut out = audit_mir_entry_point_requires(subject, companions, extra_entry_def_paths);
    if let Some((source_label, specs_source)) = authored_specs {
        out.extend(audit_lean_spec_entry_point_requires(
            &subject.def_path,
            source_label,
            specs_source,
            extra_entry_def_paths,
        ));
    }
    out
}

// ----------------------------------------------------------------------------
// Unified spec-boundary guard audit
// ----------------------------------------------------------------------------

/// A finding of any spec-boundary guard in a uniform shape.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SpecBoundaryGuardDiagnostic {
    /// The guard that fired.
    pub guard: SpecBoundaryGuardId,
    /// Label of the offending source.
    pub source_label: String,
    /// 1-based source line (`0` when the finding is not tied to a line).
    pub line: usize,
    /// Rendered diagnostic message.
    pub message: String,
}

impl fmt::Display for SpecBoundaryGuardDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl From<&GhostLengthWidthDiagnostic> for SpecBoundaryGuardDiagnostic {
    fn from(diagnostic: &GhostLengthWidthDiagnostic) -> Self {
        Self {
            guard: GhostLengthWidthDiagnostic::GUARD,
            source_label: diagnostic.source_label.clone(),
            line: diagnostic.line,
            message: diagnostic.to_string(),
        }
    }
}

impl From<&ErrorBranchWildcardDiagnostic> for SpecBoundaryGuardDiagnostic {
    fn from(diagnostic: &ErrorBranchWildcardDiagnostic) -> Self {
        Self {
            guard: ErrorBranchWildcardDiagnostic::GUARD,
            source_label: diagnostic.source_label.clone(),
            line: diagnostic.line,
            message: diagnostic.to_string(),
        }
    }
}

impl From<&EntryPointRequiresDiagnostic> for SpecBoundaryGuardDiagnostic {
    fn from(diagnostic: &EntryPointRequiresDiagnostic) -> Self {
        Self {
            guard: EntryPointRequiresDiagnostic::GUARD,
            source_label: diagnostic.source_label.clone(),
            line: diagnostic.line,
            message: diagnostic.to_string(),
        }
    }
}

/// A labeled specification source text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpecBoundarySource<'a> {
    /// Label of the source, usually its path; its extension selects the
    /// dialect ([`SpecSourceDialect::from_source_label`]).
    pub label: &'a str,
    /// Source text.
    pub text: &'a str,
}

/// Input of [`audit_spec_boundary_guards`].
#[derive(Clone, Copy, Debug, Default)]
pub struct SpecBoundaryAuditInput<'a> {
    /// Lean and Rust specification sources scanned for fixed-width ghost
    /// lengths and error-branch wildcards.
    pub spec_sources: &'a [SpecBoundarySource<'a>],
    /// Captured MIR items: subjects and their contract companions.
    pub mir_items: &'a [IrCapturedMir],
    /// Authored Lean `Specs/<Item>.lean` modules, keyed by the definition
    /// path of the item they specify.
    pub authored_entry_specs: &'a [(&'a str, SpecBoundarySource<'a>)],
    /// Definition paths the front end classified as binary entry points by
    /// attribute (`#[entry]`, `#[no_mangle]` `_start`), in addition to the
    /// name-only test [`is_binary_entry_def_path`].
    pub extra_entry_def_paths: &'a [&'a str],
}

/// Result of [`audit_spec_boundary_guards`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SpecBoundaryGuardAuditReport {
    /// All findings, sorted by guard rank, source label, line, and message.
    pub diagnostics: Vec<SpecBoundaryGuardDiagnostic>,
}

impl SpecBoundaryGuardAuditReport {
    /// Returns `true` iff no guard fired.
    pub fn is_clean(&self) -> bool {
        self.diagnostics.is_empty()
    }

    /// Number of findings per guard, in guard rank order.
    pub fn counts_by_guard(&self) -> [usize; SpecBoundaryGuardId::COUNT] {
        let mut counts = [0usize; SpecBoundaryGuardId::COUNT];
        for diagnostic in &self.diagnostics {
            counts[diagnostic.guard.rank()] += 1;
        }
        counts
    }

    /// Render a deterministic single-line summary of the audit.
    pub fn summary_line(&self) -> String {
        let counts = self.counts_by_guard();
        let parts: Vec<String> = SpecBoundaryGuardId::ALL
            .into_iter()
            .map(|guard| format!("{guard}={}", counts[guard.rank()]))
            .collect();
        format!(
            "SpecBoundaryGuardAudit(total={}, {})",
            self.diagnostics.len(),
            parts.join(", ")
        )
    }

    /// Render the findings one per line, preceded by the summary line.
    pub fn render_diagnostic_report(&self) -> String {
        let mut out = self.summary_line();
        out.push('\n');
        for diagnostic in &self.diagnostics {
            out.push_str(&diagnostic.message);
            out.push('\n');
        }
        out
    }
}

/// Run all three spec-boundary guards over a verification bundle:
///
/// - `fixed_width_ghost_length` and `error_branch_wildcard` over every source
///   in [`SpecBoundaryAuditInput::spec_sources`] and every authored entry
///   spec;
/// - `entry_point_requires` over every subject item in
///   [`SpecBoundaryAuditInput::mir_items`] and every authored entry spec.
///
/// The report is deterministic: findings are sorted and deduplicated.
pub fn audit_spec_boundary_guards(
    input: &SpecBoundaryAuditInput<'_>,
) -> SpecBoundaryGuardAuditReport {
    let mut diagnostics: Vec<SpecBoundaryGuardDiagnostic> = Vec::new();
    let authored_sources = input.authored_entry_specs.iter().map(|(_, source)| source);
    for source in input.spec_sources.iter().chain(authored_sources) {
        diagnostics.extend(
            scan_ghost_length_width_diagnostics(source.label, source.text)
                .iter()
                .map(SpecBoundaryGuardDiagnostic::from),
        );
        diagnostics.extend(
            scan_error_branch_wildcard_diagnostics(source.label, source.text)
                .iter()
                .map(SpecBoundaryGuardDiagnostic::from),
        );
    }
    for subject in input.mir_items {
        diagnostics.extend(
            audit_mir_entry_point_requires(subject, input.mir_items, input.extra_entry_def_paths)
                .iter()
                .map(SpecBoundaryGuardDiagnostic::from),
        );
        // Also flag orphan `Requires(target)` companions whose target is an
        // entry point even when the subject MIR item is absent from `mir_items`.
        if let IrContractRole::Requires(target) = &subject.role
            && (is_binary_entry_def_path(target)
                || input.extra_entry_def_paths.contains(&target.as_str()))
            && !ir_requires_body_is_trivially_true(subject)
        {
            let diag = EntryPointRequiresDiagnostic {
                entry_def_path: target.clone(),
                source_label: subject.def_path.clone(),
                line: 0,
                kind: EntryPointRequiresKind::MirRequiresCompanion,
            };
            diagnostics.push(SpecBoundaryGuardDiagnostic::from(&diag));
        }
    }
    for (entry_def_path, source) in input.authored_entry_specs {
        diagnostics.extend(
            audit_lean_spec_entry_point_requires(
                entry_def_path,
                source.label,
                source.text,
                input.extra_entry_def_paths,
            )
            .iter()
            .map(SpecBoundaryGuardDiagnostic::from),
        );
    }
    diagnostics.sort();
    diagnostics.dedup();
    SpecBoundaryGuardAuditReport { diagnostics }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anneal_rustc_capture::lean_emit::emit_mir_lean_module;

    #[test]
    fn property_registry_covers_all_12_classes_with_bijective_ranks_and_slugs() {
        assert_eq!(PropertyClass::ALL.len(), 12);
        let mut seen_slugs = BTreeSet::new();
        for (idx, class) in PropertyClass::ALL.into_iter().enumerate() {
            assert_eq!(class.rank(), idx);
            assert_eq!(PropertyClass::from_rank(idx), Some(class));
            assert!(seen_slugs.insert(class.as_str()), "duplicate slug `{class}`");
            assert_eq!(class.as_str().parse::<PropertyClass>(), Ok(class));
            assert!(!class.description().is_empty());
        }
        assert_eq!(PropertyClass::from_rank(12), None);
        assert!("bogus_class".parse::<PropertyClass>().is_err());

        let strict = PropertyRegistry::strict();
        assert_eq!(strict.entries().len(), 12);
        for class in PropertyClass::ALL {
            if class == PropertyClass::UnsupportedFallback {
                assert!(!class.is_waivable());
                assert_eq!(
                    strict.disposition(class),
                    &PropertyDisposition::UnsupportedFailClosed
                );
            } else {
                assert!(class.is_waivable());
                assert_eq!(strict.disposition(class), &PropertyDisposition::Discharged);
            }
        }
        assert_eq!(
            strict.summary_line(),
            "PropertyRegistry(total=12, discharged=11, waived=0, unemitted_gap=0, unsupported_fail_closed=1)"
        );

        let mut reg = PropertyRegistry::strict();
        assert!(
            reg.try_set_disposition(
                PropertyClass::UnsupportedFallback,
                PropertyDisposition::Discharged
            )
            .is_err()
        );
        assert!(
            reg.try_set_disposition(
                PropertyClass::UnsupportedFallback,
                PropertyDisposition::ExplicitlyWaived {
                    reason: String::from("never allowed")
                }
            )
            .is_err()
        );
        assert!(
            reg.try_set_disposition(
                PropertyClass::LoopTermination,
                PropertyDisposition::ExplicitlyWaived {
                    reason: String::from("   ")
                }
            )
            .is_err()
        );
    }

    #[test]
    fn census_enumerates_all_12_property_classes_and_roundtrips_lean_mir() {
        let u32_ty = IrTy {
            kind: IrRigidTy::Uint(IrUintTy::U32),
            layout_idx: 0,
        };
        let ptr_u32_ty = IrTy {
            kind: IrRigidTy::RawPtr(IrMutability::Mut, Box::new(IrRigidTy::Uint(IrUintTy::U32))),
            layout_idx: 1,
        };
        let arr_ty = IrTy {
            kind: IrRigidTy::Array(Box::new(IrRigidTy::Uint(IrUintTy::U32)), 4),
            layout_idx: 0,
        };
        let opt_ty = IrTy {
            kind: IrRigidTy::Adt(
                String::from("core::option::Option"),
                vec![u32_ty.kind.clone()],
            ),
            layout_idx: 0,
        };

        let mut mir = IrCapturedMir {
            def_path: String::from("demo::all_twelve_classes"),
            phase: IrMirPhaseTag::RuntimePostCleanup,
            role: IrContractRole::Subject,
            type_param_count: 0,
            generic_params: Vec::new(),
            trait_impls: Vec::new(),
            arg_count: 2,
            local_decls: vec![
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: u32_ty.clone(),
                    debug_name: None,
                },
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: u32_ty.clone(),
                    debug_name: Some(String::from("x")),
                },
                IrLocalDecl {
                    mutability: IrMutability::Not,
                    ty: ptr_u32_ty.clone(),
                    debug_name: Some(String::from("p")),
                },
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: arr_ty,
                    debug_name: Some(String::from("arr")),
                },
                IrLocalDecl {
                    mutability: IrMutability::Mut,
                    ty: opt_ty,
                    debug_name: Some(String::from("opt")),
                },
            ],
            basic_blocks: vec![
                IrBasicBlockData {
                    statements: vec![
                        IrStatement {
                            kind: IrStatementKind::Assign(
                                IrPlace {
                                    local_: 1,
                                    projection: Vec::new(),
                                },
                                IrRvalue::BinaryOp(
                                    IrBinOp::AddUnchecked,
                                    IrOperand::Copy(IrPlace {
                                        local_: 1,
                                        projection: Vec::new(),
                                    }),
                                    const_u32_operand(1),
                                ),
                            ),
                            span: String::from("s0 «comment-safe»"),
                            comment: Some(String::from("comment with «guillemets»")),
                        },
                        IrStatement {
                            kind: IrStatementKind::Assign(
                                IrPlace {
                                    local_: 1,
                                    projection: Vec::new(),
                                },
                                IrRvalue::BinaryOp(
                                    IrBinOp::ShlUnchecked,
                                    IrOperand::Copy(IrPlace {
                                        local_: 1,
                                        projection: Vec::new(),
                                    }),
                                    const_u32_operand(2),
                                ),
                            ),
                            span: String::from("s1\u{0085}"),
                            comment: None,
                        },
                        IrStatement {
                            kind: IrStatementKind::Assign(
                                IrPlace {
                                    local_: 1,
                                    projection: Vec::new(),
                                },
                                IrRvalue::BinaryOp(
                                    IrBinOp::Rem,
                                    IrOperand::Copy(IrPlace {
                                        local_: 1,
                                        projection: Vec::new(),
                                    }),
                                    const_u32_operand(3),
                                ),
                            ),
                            span: String::from("s2"),
                            comment: None,
                        },
                        IrStatement {
                            kind: IrStatementKind::Assign(
                                IrPlace {
                                    local_: 3,
                                    projection: vec![IrProjectionElem::Index(1)],
                                },
                                IrRvalue::Use(const_u32_operand(7)),
                            ),
                            span: String::from("s3"),
                            comment: None,
                        },
                        IrStatement {
                            kind: IrStatementKind::SetDiscriminant(
                                IrPlace {
                                    local_: 4,
                                    projection: Vec::new(),
                                },
                                1,
                            ),
                            span: String::from("s4"),
                            comment: None,
                        },
                        IrStatement {
                            kind: IrStatementKind::Intrinsic(
                                IrNonDivergingIntrinsic::CopyNonOverlapping {
                                    src: IrOperand::Copy(IrPlace {
                                        local_: 2,
                                        projection: Vec::new(),
                                    }),
                                    dst: IrOperand::Copy(IrPlace {
                                        local_: 2,
                                        projection: Vec::new(),
                                    }),
                                    count: const_u32_operand(0),
                                },
                            ),
                            span: String::from("s5"),
                            comment: None,
                        },
                    ],
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::SwitchInt(
                            IrOperand::Copy(IrPlace {
                                local_: 1,
                                projection: Vec::new(),
                            }),
                            IrSwitchTargets {
                                branches: vec![(0, 0)],
                                otherwise: 1,
                            },
                        ),
                        span: String::from("t0"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: Vec::new(),
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Call {
                            func: IrOperand::Constant(IrConstOperand {
                                ty: IrTy {
                                    kind: IrRigidTy::FnDef(
                                        String::from("core::intrinsics::wrapping_add"),
                                        Vec::new(),
                                    ),
                                    layout_idx: 2,
                                },
                                val: IrConstValue::ZeroSized,
                            }),
                            args: vec![const_u32_operand(0), const_u32_operand(1)],
                            destination: IrPlace {
                                local_: 0,
                                projection: Vec::new(),
                            },
                            target: Some(2),
                            unwind: IrUnwindAction::Continue,
                        },
                        span: String::from("t1"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
                IrBasicBlockData {
                    statements: Vec::new(),
                    terminator: IrTerminator {
                        kind: IrTerminatorKind::Return,
                        span: String::from("t2"),
                        comment: None,
                    },
                    is_cleanup: false,
                },
            ],
            fn_abi: IrFnAbi {
                args: Vec::new(),
                ret: IrArgAbi {
                    layout: scalar_u32_layout(),
                    mode: IrAbiPassMode::Direct,
                },
                conv: IrCallConv::Rust,
                can_unwind: true,
            },
            layouts: IrLayoutTable {
                pointer_bits: 64,
                is_little_endian: true,
                entries: vec![scalar_u32_layout(), ptr_layout(), unit_layout()],
            },
            allocations: Vec::new(),
        };

        let ir_census = FaultSiteCensus::from_ir_captured_mir(&mir);
        let lean_text = emit_mir_lean_module("Mir.Demo.all_twelve_classes", &mir);
        let lean_census =
            FaultSiteCensus::from_lean_mir_module(&lean_text).expect("parse emitted Mir module");
        assert_eq!(ir_census, lean_census);

        for class in PropertyClass::ALL {
            if class != PropertyClass::UnsupportedFallback {
                assert!(
                    ir_census.sites.iter().any(|s| s.class == class),
                    "expected census to include `{class}`, got {:?}",
                    ir_census.sites
                );
            }
        }

        let reconciler = FaultSiteCoverageReconciler::new(PropertyRegistry::strict());
        let coverage = collect_reachable_body_obligations(
            &mir,
            true,
            false,
            CallCoverageContext {
                enforce_callee_closure: true,
                ..CallCoverageContext::default()
            },
        );
        let ok_report = reconciler.reconcile_with_call_context(
            &ir_census,
            coverage.discharged_sites.iter().copied(),
            coverage.explicit_waivers.iter().cloned(),
            &coverage.call_context,
        );
        assert!(ok_report.is_covered(), "{}", ok_report.render_diagnostic_report());

        mir.basic_blocks[2].statements.push(IrStatement {
            kind: IrStatementKind::Assign(
                IrPlace {
                    local_: 2,
                    projection: Vec::new(),
                },
                IrRvalue::ThreadLocalRef(String::from("demo::TLS")),
            ),
            span: String::from("tls"),
            comment: None,
        });
        let ir_census_12 = FaultSiteCensus::from_ir_captured_mir(&mir);
        let lean_12 = emit_mir_lean_module("Mir.Demo.all_twelve_classes", &mir);
        let parsed_12 = FaultSiteCensus::from_lean_mir_module(&lean_12).expect("parse TLS module");
        assert_eq!(ir_census_12, parsed_12);
        for class in PropertyClass::ALL {
            assert!(
                ir_census_12.sites.iter().any(|s| s.class == class),
                "missing class `{class}` in 12-class census"
            );
        }

        let fail_report =
            reconciler.reconcile(&ir_census_12, ir_census_12.sites.iter().copied(), []);
        assert!(!fail_report.is_covered());
        assert_eq!(fail_report.uncovered_diagnostics.len(), 1);
        assert_eq!(
            fail_report.uncovered_diagnostics[0].site,
            FaultSite::statement(2, 0, PropertyClass::UnsupportedFallback)
        );
    }

    #[test]
    fn reconciler_rejects_omitted_sites_unemitted_registry_gaps_and_malformed_mir() {
        let scenario = MutationProbeScenario::build(FalseProofMutationProbe::SwitchBreakStripProbe);
        let strict_rec = FaultSiteCoverageReconciler::new(PropertyRegistry::strict());
        let (base_rep, mut_rep) = scenario.execute(&strict_rec);
        assert!(base_rep.is_covered());
        assert!(!mut_rep.is_covered());
        let uncovered: BTreeSet<FaultSite> = mut_rep
            .uncovered_diagnostics
            .iter()
            .map(|d| d.site)
            .collect();
        assert_eq!(uncovered, scenario.expected_uncovered_sites);

        let gap_reg = PropertyRegistry::strict()
            .try_with_disposition(PropertyClass::DivRemUb, PropertyDisposition::UnemittedGap)
            .expect("configure DivRemUb as UnemittedGap");
        let gap_rec = FaultSiteCoverageReconciler::new(gap_reg);
        let gap_rep = gap_rec.reconcile(
            &scenario.census,
            scenario.baseline_coverage.discharged_sites.iter().copied(),
            [],
        );
        assert!(!gap_rep.is_covered());
        assert!(gap_rep.uncovered_diagnostics.iter().any(|d| {
            d.site == FaultSite::statement(2, 0, PropertyClass::DivRemUb)
                && d.reason == UncoveredReason::RegistryUnemittedGap
        }));

        for bad_lean in [
            "import Trusted\nimport Evil\ndef body : CapturedMir := { defPath := \"x\", basicBlocks := [] }\n",
            "import Trusted\ndef body : CapturedMir := helperFn\n",
            "import Trusted\ndef «body» : CapturedMir := { defPath := \"x\", basicBlocks := [] }\n",
            "import Trusted\ndef body : CapturedMir := { base with defPath := \"x\", basicBlocks := [] }\n",
            "import Trusted\nnamespace Mir.Unclosed\ndef body : CapturedMir := { defPath := \"x\", basicBlocks := [] }\n",
            "import Trusted\ndef body : CapturedMir := { defPath := \"x\", basicBlocks := [] }\nend Mir.Orphan\n",
            "import Trusted\nopen Trusted in\ndef body : CapturedMir := { defPath := \"x\", basicBlocks := [] }\n",
        ] {
            assert!(FaultSiteCensus::from_lean_mir_module(bad_lean).is_err(), "{bad_lean}");
            let fc = FaultSiteCensus::from_lean_mir_fail_closed("demo::bad", bad_lean);
            let rep = strict_rec.reconcile(&fc, fc.sites.iter().copied(), []);
            assert!(!rep.is_covered(), "malformed MIR must fail closed: {bad_lean}");
        }
    }

    #[test]
    fn indirect_fn_ptr_calls_and_unmodeled_intrinsics_do_not_fail_open() {
        // 1. `core::hint::black_box` and `core::intrinsics::volatile_load` are NOT
        //    in `MirSemantics`'s inline intrinsic table and must NOT pass without
        //    `defaultCallees` or `ModularItemSpec.envAssumed`.
        assert!(!is_natively_modeled_mir_call("core::hint::black_box", false));
        assert!(!is_natively_modeled_mir_call("core::intrinsics::volatile_load", false));
        assert!(!is_natively_modeled_mir_call("core::panicking::panic", false));
        assert!(is_natively_modeled_mir_call("core::panicking::panic", true));
        assert!(is_natively_modeled_mir_call("core::intrinsics::exact_div", false));

        // 2. An indirect `fn_ptr` call is NOT waived merely because an unrelated
        //    `FnDef` appears in `reified_fn_defs` or `traitImpls`!
        let mut indirect_mir = build_probe_mir_body(FalseProofMutationProbe::CallArgBlindProbe);
        indirect_mir.trait_impls.push(IrTraitImplEntry {
            trait_ref: IrTraitRef {
                def_path: String::from("probes::MyTrait"),
                args: Vec::new(),
            },
            impl_path: String::from("probes::callee_u32"),
        });
        indirect_mir.local_decls[1].ty = IrTy {
            kind: IrRigidTy::FnPtr(
                Vec::new(),
                Box::new(IrRigidTy::Uint(IrUintTy::U32)),
                IrSafety::Safe,
                IrCallConv::Rust,
            ),
            layout_idx: 1,
        };
        indirect_mir.basic_blocks[0].terminator.kind = IrTerminatorKind::Call {
            func: IrOperand::Copy(IrPlace {
                local_: 1,
                projection: Vec::new(),
            }),
            args: Vec::new(),
            destination: IrPlace {
                local_: 0,
                projection: Vec::new(),
            },
            target: Some(1),
            unwind: IrUnwindAction::Continue,
        };

        let census = FaultSiteCensus::from_ir_captured_mir(&indirect_mir);
        assert!(census.has_indirect_call());
        assert!(census.reified_fn_defs.contains("probes::callee_u32"));

        let mut call_ctx = CallCoverageContext {
            enforce_callee_closure: true,
            allow_modular_indirect_calls: false,
            ..CallCoverageContext::default()
        };
        call_ctx
            .linked_callees
            .insert(String::from("probes::callee_u32"));

        let cov = collect_reachable_body_obligations(&indirect_mir, true, false, call_ctx.clone());
        let rec = FaultSiteCoverageReconciler::new(PropertyRegistry::strict());
        let rep = rec.reconcile_with_call_context(
            &census,
            cov.discharged_sites,
            cov.explicit_waivers,
            &call_ctx,
        );
        assert!(!rep.is_covered(), "indirect fn_ptr call without modular handler must fail closed");
        assert!(rep.uncovered_diagnostics.iter().any(|d| {
            matches!(
                &d.reason,
                UncoveredReason::UnresolvedCallContract { callee } if callee == "<indirect fn_ptr>"
            )
        }));
    }

    #[test]
    fn partial_vs_total_correctness_loop_termination_and_unresolved_callee_checks() {
        let loop_scenario =
            MutationProbeScenario::build(FalseProofMutationProbe::LoopUpdateOverflowProbe);
        let loop_site = FaultSite::terminator(2, 1, PropertyClass::LoopTermination);
        assert!(loop_scenario.census.sites.contains(&loop_site));

        let partial_cov = collect_reachable_body_obligations(
            &loop_scenario.mir,
            false,
            false,
            CallCoverageContext::default(),
        );
        assert!(!partial_cov.discharged_sites.contains(&loop_site));
        assert_eq!(partial_cov.explicit_waivers.len(), 1);
        assert_eq!(partial_cov.explicit_waivers[0].site, loop_site);

        let strict_rec = FaultSiteCoverageReconciler::new(PropertyRegistry::strict());
        assert!(
            strict_rec
                .reconcile(
                    &loop_scenario.census,
                    partial_cov.discharged_sites.iter().copied(),
                    partial_cov.explicit_waivers.iter().cloned(),
                )
                .is_covered()
        );
        let missing_loop_rep = strict_rec.reconcile(
            &loop_scenario.census,
            partial_cov.discharged_sites.iter().copied(),
            [],
        );
        assert!(!missing_loop_rep.is_covered());
        assert_eq!(missing_loop_rep.uncovered_diagnostics.len(), 1);
        assert_eq!(missing_loop_rep.uncovered_diagnostics[0].site, loop_site);

        let call_scenario =
            MutationProbeScenario::build(FalseProofMutationProbe::CallArgBlindProbe);
        let unlinked_ctx = CallCoverageContext {
            enforce_callee_closure: true,
            ..CallCoverageContext::default()
        };
        let unlinked_rep = strict_rec.reconcile_with_call_context(
            &call_scenario.census,
            call_scenario.baseline_coverage.discharged_sites.iter().copied(),
            [],
            &unlinked_ctx,
        );
        assert!(!unlinked_rep.is_covered());
        assert!(unlinked_rep.uncovered_diagnostics.iter().any(|d| {
            d.site == FaultSite::terminator(0, 0, PropertyClass::CallContract)
                && matches!(
                    &d.reason,
                    UncoveredReason::UnresolvedCallContract { callee } if callee == "probes::callee_u32"
                )
        }));
    }

    // ---- Spec-boundary guard taxonomy & canonical manifest ------------------

    #[test]
    fn spec_boundary_guard_ids_match_frozen_cross_language_contract() {
        let table: [(usize, &str, &str, &str); 3] = [
            (
                0,
                "entry_point_requires",
                "EntryPointPrecondition",
                "DeadPrecondition",
            ),
            (
                1,
                "fixed_width_ghost_length",
                "FixedWidthGhostLength",
                "SpecViolation",
            ),
            (
                2,
                "error_branch_wildcard",
                "ErrorBranchWildcard",
                "SurvivedAllMutants",
            ),
        ];
        assert_eq!(SpecBoundaryGuardId::COUNT, 3);
        assert_eq!(SpecBoundaryGuardId::ALL.len(), 3);
        for (guard, (rank, id, name, vacuity)) in SpecBoundaryGuardId::ALL.into_iter().zip(table) {
            assert_eq!(guard.rank(), rank);
            assert_eq!(SpecBoundaryGuardId::from_rank(rank), Some(guard));
            assert_eq!(guard.as_str(), id);
            assert_eq!(guard.to_string(), id);
            assert_eq!(id.parse::<SpecBoundaryGuardId>(), Ok(guard));
            assert_eq!(guard.canonical_name(), name);
            assert_eq!(guard.vacuity_class(), vacuity);
            assert!(!guard.description().is_empty());
            // Guard identifiers are disjoint from property class identifiers.
            assert!(id.parse::<PropertyClass>().is_err());
        }
        assert_eq!(SpecBoundaryGuardId::from_rank(3), None);
        for near_miss in [
            "",
            "EntryPointPrecondition",
            "entry_point_precondition",
            "entry_point_requires ",
            "Entry_Point_Requires",
            "fixed_width_ghost_len",
            "error_branch_wildcards",
            "arithmetic_overflow",
        ] {
            assert!(
                near_miss.parse::<SpecBoundaryGuardId>().is_err(),
                "{near_miss:?}"
            );
        }
        for class in PropertyClass::ALL {
            assert!(class.as_str().parse::<SpecBoundaryGuardId>().is_err());
        }
    }

    #[test]
    fn property_class_table_matches_frozen_cross_language_contract() {
        let table: [(usize, &str, &str, bool); 12] = [
            (0, "arithmetic_overflow", "ArithmeticOverflow", true),
            (1, "shift_bounds", "ShiftBounds", true),
            (2, "div_rem_ub", "DivRemUb", true),
            (3, "pointer_deref", "PointerDereference", true),
            (4, "slice_array_bounds", "SliceArrayBounds", true),
            (5, "discriminant_validity", "DiscriminantValidity", true),
            (6, "call_contract", "CallContract", true),
            (7, "loop_termination", "LoopTermination", true),
            (8, "switch_exhaustiveness", "SwitchExhaustiveness", true),
            (9, "memory_copy_overlap", "MemoryCopyOverlap", true),
            (10, "uninit_read", "UninitRead", true),
            (11, "unsupported_fallback", "UnsupportedFallback", false),
        ];
        for (class, (rank, id, variant, waivable)) in PropertyClass::ALL.into_iter().zip(table) {
            assert_eq!(class.rank(), rank);
            assert_eq!(class.as_str(), id);
            assert_eq!(class.variant_name(), variant);
            assert_eq!(format!("{class:?}"), variant);
            assert_eq!(class.is_waivable(), waivable);
        }
    }

    #[test]
    fn taxonomy_manifest_json_is_deterministic_and_roundtrips() {
        let json = render_property_taxonomy_json();
        assert_eq!(json, render_property_taxonomy_json());
        assert_eq!(json, PropertyTaxonomyManifest::canonical().to_json());
        assert!(json.starts_with("{\n  \"schema_version\": 1,\n  \"property_classes\": [\n"));
        assert!(json.ends_with("  ]\n}\n"));
        // One entry per line, in rank order, with a fixed key order.
        assert!(json.contains(
            "    {\"rank\": 0, \"id\": \"arithmetic_overflow\", \"variant\": \
             \"ArithmeticOverflow\", \"is_waivable\": true, \"strict_disposition\": \
             \"discharged\", \"partial_disposition\": \"discharged\", \"description\": "
        ));
        assert!(json.contains(
            "    {\"rank\": 7, \"id\": \"loop_termination\", \"variant\": \"LoopTermination\", \
             \"is_waivable\": true, \"strict_disposition\": \"discharged\", \
             \"partial_disposition\": \"explicitly_waived\", \"description\": "
        ));
        assert!(json.contains(
            "    {\"rank\": 11, \"id\": \"unsupported_fallback\", \"variant\": \
             \"UnsupportedFallback\", \"is_waivable\": false, \"strict_disposition\": \
             \"unsupported_fail_closed\", \"partial_disposition\": \"unsupported_fail_closed\", \
             \"description\": "
        ));
        assert!(json.contains(
            "    {\"rank\": 0, \"id\": \"entry_point_requires\", \"canonical_name\": \
             \"EntryPointPrecondition\", \"vacuity_class\": \"DeadPrecondition\", \
             \"description\": "
        ));
        assert!(json.contains(
            "    {\"rank\": 1, \"id\": \"fixed_width_ghost_length\", \"canonical_name\": \
             \"FixedWidthGhostLength\", \"vacuity_class\": \"SpecViolation\", \"description\": "
        ));
        assert!(json.contains(
            "    {\"rank\": 2, \"id\": \"error_branch_wildcard\", \"canonical_name\": \
             \"ErrorBranchWildcard\", \"vacuity_class\": \"SurvivedAllMutants\", \
             \"description\": "
        ));
        // The canonical manifest carries no registry-specific annotation.
        assert!(!json.contains("\"disposition\""));
        assert_eq!(json.lines().count(), 3 + 12 + 2 + 3 + 2);

        let manifest = parse_property_taxonomy_json(&json).expect("canonical manifest parses");
        assert_eq!(manifest, PropertyTaxonomyManifest::canonical());
        assert_eq!(manifest.schema_version, PROPERTY_TAXONOMY_SCHEMA_VERSION);
        assert_eq!(manifest.property_classes.len(), PropertyClass::COUNT);
        assert_eq!(
            manifest.spec_boundary_guards.len(),
            SpecBoundaryGuardId::COUNT
        );
        assert_eq!(manifest.check_canonical(), Ok(()));
        assert_eq!(manifest.to_json(), json);
        assert_eq!(
            parse_canonical_property_taxonomy_json(&json),
            Ok(PropertyTaxonomyManifest::canonical())
        );

        // Every entry agrees with the compiled enums.
        for (entry, class) in manifest.property_classes.iter().zip(PropertyClass::ALL) {
            assert_eq!(entry.rank, class.rank());
            assert_eq!(entry.id.parse::<PropertyClass>(), Ok(class));
            assert_eq!(entry.variant, class.variant_name());
            assert_eq!(entry.is_waivable, class.is_waivable());
            assert_eq!(entry.description, class.description());
            assert_eq!(entry.disposition, None);
        }
        for (entry, guard) in manifest
            .spec_boundary_guards
            .iter()
            .zip(SpecBoundaryGuardId::ALL)
        {
            assert_eq!(entry.rank, guard.rank());
            assert_eq!(entry.id.parse::<SpecBoundaryGuardId>(), Ok(guard));
            assert_eq!(entry.canonical_name, guard.canonical_name());
            assert_eq!(entry.vacuity_class, guard.vacuity_class());
            assert_eq!(entry.description, guard.description());
        }

        // Whitespace-insensitive parsing accepts a reformatted manifest.
        let compact: String = json.split('\n').map(str::trim).collect();
        assert_eq!(parse_property_taxonomy_json(&compact), Ok(manifest));
    }

    #[test]
    fn registry_taxonomy_export_carries_dispositions() {
        for (registry, loop_tag, overflow_tag) in [
            (PropertyRegistry::strict(), "discharged", "discharged"),
            (
                PropertyRegistry::for_partial_correctness(),
                "explicitly_waived",
                "discharged",
            ),
            (
                PropertyRegistry::all_unemitted(),
                "unemitted_gap",
                "unemitted_gap",
            ),
        ] {
            let json = registry.to_taxonomy_json();
            assert_eq!(json, registry.to_taxonomy_json());
            let manifest = parse_property_taxonomy_json(&json).expect("registry export parses");
            assert_eq!(manifest, PropertyTaxonomyManifest::for_registry(&registry));
            assert_eq!(manifest.to_json(), json);
            // The export still describes the canonical taxonomy.
            assert_eq!(manifest.check_canonical(), Ok(()));
            let disposition = |class: PropertyClass| {
                manifest.property_classes[class.rank()]
                    .disposition
                    .as_deref()
            };
            assert_eq!(disposition(PropertyClass::LoopTermination), Some(loop_tag));
            assert_eq!(
                disposition(PropertyClass::ArithmeticOverflow),
                Some(overflow_tag)
            );
            assert_eq!(
                disposition(PropertyClass::UnsupportedFallback),
                Some("unsupported_fail_closed")
            );
            for class in PropertyClass::ALL {
                assert_eq!(disposition(class), Some(registry.disposition(class).tag()));
            }
        }
    }

    #[test]
    fn taxonomy_manifest_parser_is_strict() {
        let json = render_property_taxonomy_json();
        let must_fail = |mutated: String, why: &str| {
            assert!(
                parse_property_taxonomy_json(&mutated).is_err(),
                "parser accepted a manifest with {why}"
            );
        };
        must_fail(String::new(), "no content");
        must_fail(format!("{json}x"), "trailing input");
        must_fail(format!("{json}{json}"), "a second document");
        must_fail(
            json.replace("\"schema_version\": 1", "\"schema_version\": 2"),
            "an unsupported schema version",
        );
        must_fail(
            json.replace("\"schema_version\": 1", "\"schema_version\": 01"),
            "a leading zero",
        );
        must_fail(
            json.replace("\"schema_version\": 1", "\"schema_version\": 1.0"),
            "a float",
        );
        must_fail(
            json.replace("\"schema_version\": 1", "\"schema_version\": -1"),
            "a negative number",
        );
        must_fail(
            json.replace("\"schema_version\": 1", "\"schema_version\": \"1\""),
            "a string schema version",
        );
        must_fail(
            json.replace(
                "\"schema_version\": 1,",
                "\"schema_version\": 1, \"schema_version\": 1,",
            ),
            "a duplicate key",
        );
        must_fail(
            json.replace(
                "\"schema_version\": 1,",
                "\"schema_version\": 1, \"extra\": 0,",
            ),
            "an unknown root key",
        );
        must_fail(
            json.replace("\"variant\": \"ShiftBounds\", ", ""),
            "a missing entry key",
        );
        must_fail(
            json.replace(
                "\"variant\": \"ShiftBounds\", ",
                "\"variant\": \"ShiftBounds\", \"alias\": \"sb\", ",
            ),
            "an unknown entry key",
        );
        must_fail(
            json.replace("\"is_waivable\": false", "\"is_waivable\": \"false\""),
            "a string boolean",
        );
        must_fail(
            json.replace(
                "{\"rank\": 1, \"id\": \"shift_bounds\"",
                "{\"rank\": 5, \"id\": \"shift_bounds\"",
            ),
            "entries out of rank order",
        );
        must_fail(
            json.replace("\"id\": \"shift_bounds\"", "\"id\": \"shift_bounds"),
            "an unterminated string",
        );
        must_fail(
            json.replace("\"id\": \"shift_bounds\"", "\"id\": \"shift\\qbounds\""),
            "an unknown escape",
        );
        must_fail(
            json.replace("\"id\": \"shift_bounds\"", "\"id\": \"shift\\u+041bounds\""),
            "a signed \\u escape",
        );
        must_fail(
            json.replace(
                "  ],\n  \"spec_boundary_guards\"",
                "  ]\n  \"spec_boundary_guards\"",
            ),
            "a missing comma",
        );
        must_fail(
            json.trim_end().trim_end_matches('}').to_string(),
            "an unclosed object",
        );
        must_fail(format!("{}1", "[".repeat(64)), "deep nesting");
        must_fail(String::from("[]"), "a non-object root");
        must_fail(String::from("null"), "a null root");
        // RFC 8259 `\b` and `\f` escapes parse cleanly inside strings.
        let with_bf = json.replace(
            "\"description\": \"bit-shift",
            "\"description\": \"\\b\\fbit-shift",
        );
        let parsed_bf = parse_property_taxonomy_json(&with_bf).expect("\\b and \\f parse");
        assert!(
            parsed_bf.property_classes[1]
                .description
                .starts_with("\u{0008}\u{000c}bit-shift")
        );
    }

    #[test]
    fn taxonomy_manifest_drift_is_detected() {
        let json = render_property_taxonomy_json();
        let drifted = |mutated: String, why: &str| {
            let manifest = parse_property_taxonomy_json(&mutated)
                .unwrap_or_else(|err| panic!("structurally valid manifest with {why}: {err}"));
            let err = manifest
                .check_canonical()
                .expect_err(&format!("drift not detected: {why}"));
            assert!(err.contains("drift"), "{err}");
            assert!(
                parse_canonical_property_taxonomy_json(&mutated).is_err(),
                "{why}"
            );
        };
        drifted(
            json.replace("\"id\": \"div_rem_ub\"", "\"id\": \"div_rem\""),
            "a renamed property class identifier",
        );
        drifted(
            json.replace("\"variant\": \"DivRemUb\"", "\"variant\": \"DivRem\""),
            "a renamed variant",
        );
        drifted(
            json.replace("\"is_waivable\": false", "\"is_waivable\": true"),
            "a waivable unsupported fallback",
        );
        drifted(
            json.replace(
                "\"partial_disposition\": \"explicitly_waived\"",
                "\"partial_disposition\": \"discharged\"",
            ),
            "a changed partial disposition",
        );
        drifted(
            json.replace(
                "\"vacuity_class\": \"SurvivedAllMutants\"",
                "\"vacuity_class\": \"SpecViolation\"",
            ),
            "a changed guard vacuity class",
        );
        drifted(
            json.replace(
                "\"canonical_name\": \"EntryPointPrecondition\"",
                "\"canonical_name\": \"EntryPointRequires\"",
            ),
            "a renamed guard",
        );
        drifted(
            json.replace(
                "\"id\": \"error_branch_wildcard\"",
                "\"id\": \"error_wildcard\"",
            ),
            "a renamed guard identifier",
        );
        // Dropping the last class and the last guard keeps the ranks contiguous.
        let without_last_class: String = json
            .lines()
            .filter(|line| !line.contains("\"unsupported_fallback\""))
            .map(|line| {
                if line.contains("\"uninit_read\"") {
                    format!("{}\n", line.trim_end_matches(','))
                } else {
                    format!("{line}\n")
                }
            })
            .collect();
        drifted(without_last_class, "a missing property class");
        let without_last_guard: String = json
            .lines()
            .filter(|line| !line.contains("\"error_branch_wildcard\""))
            .map(|line| {
                if line.contains("\"fixed_width_ghost_length\"") {
                    format!("{}\n", line.trim_end_matches(','))
                } else {
                    format!("{line}\n")
                }
            })
            .collect();
        drifted(without_last_guard, "a missing guard");
        // An unknown registry disposition tag is drift as well.
        let annotated = PropertyRegistry::strict().to_taxonomy_json().replacen(
            "\"disposition\": \"discharged\"",
            "\"disposition\": \"proved\"",
            1,
        );
        drifted(annotated, "an unknown disposition tag");
        // Marking the non-waivable `unsupported_fallback` class as waived or
        // discharged violates `validate_disposition_for_class` and must fail.
        let waived_unsupported = PropertyRegistry::strict().to_taxonomy_json().replace(
            "\"disposition\": \"unsupported_fail_closed\"",
            "\"disposition\": \"explicitly_waived\"",
        );
        drifted(
            waived_unsupported,
            "an explicitly_waived unsupported_fallback disposition",
        );
        let discharged_unsupported = PropertyRegistry::strict().to_taxonomy_json().replace(
            "\"disposition\": \"unsupported_fail_closed\"",
            "\"disposition\": \"discharged\"",
        );
        drifted(
            discharged_unsupported,
            "a discharged unsupported_fallback disposition",
        );
    }

    // ---- Guard 2: fixed-width ghost length scanner --------------------------

    #[test]
    fn ghost_length_type_name_tables_match_lean() {
        assert_eq!(
            FIXED_WIDTH_GHOST_INT_TYPE_NAMES,
            [
                "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
                "ISize", "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64",
                "i128", "isize",
            ]
        );
        assert_eq!(UNBOUNDED_GHOST_INT_TYPE_NAMES, ["Nat", "Int"]);
        for unbounded in UNBOUNDED_GHOST_INT_TYPE_NAMES {
            assert!(!FIXED_WIDTH_GHOST_INT_TYPE_NAMES.contains(&unbounded));
        }
        assert_eq!(
            GhostLengthWidthDiagnostic::GUARD,
            SpecBoundaryGuardId::FixedWidthGhostLength
        );
    }

    fn ghost_findings(
        label: &str,
        text: &str,
    ) -> Vec<(usize, String, String, GhostLengthWidthKind)> {
        scan_ghost_length_width_diagnostics(label, text)
            .into_iter()
            .map(|d| {
                assert_eq!(d.source_label, label);
                (d.line, d.declaration, d.fixed_width_type, d.kind)
            })
            .collect()
    }

    #[test]
    fn ghost_length_scanner_flags_fixed_width_lean_ghost_lengths() {
        use GhostLengthWidthKind::{FixedWidthReturnType, WraparoundCast};
        let lean = "\
axiom GhostList.len : GhostList α → UInt64
def ghostLen (xs : GhostSeq α) : USize := measure xs
def card (s : Finset α) : UInt64 := 0
def Seq.count (s : Seq α) (p : α → Bool) : BitVec 64 := 0
opaque ghost_cap (m : GhostMap K V) : u64
theorem GhostSet.size (s : GhostSet α) : (Int32) := 0
def len (xs : List α) : UInt64 := UInt64.ofNat xs.length
def next (xs : List α) : USize := USize.ofNat (xs.length + 1)
theorem cast (xs : List α) (n : USize) : xs.length.toUSize = n := rfl
theorem cast2 (xs : List α) : (xs.length).toUInt64 = 0 := rfl
def setSize (s : Multiset α) : UInt32 := UInt32.ofNat s.card
";
        assert_eq!(
            ghost_findings("Specs/Ghost.lean", lean),
            vec![
                (
                    1,
                    "GhostList.len".into(),
                    "UInt64".into(),
                    FixedWidthReturnType
                ),
                (2, "ghostLen".into(), "USize".into(), FixedWidthReturnType),
                (3, "card".into(), "UInt64".into(), FixedWidthReturnType),
                (
                    4,
                    "Seq.count".into(),
                    "BitVec 64".into(),
                    FixedWidthReturnType
                ),
                (5, "ghost_cap".into(), "u64".into(), FixedWidthReturnType),
                (
                    6,
                    "GhostSet.size".into(),
                    "Int32".into(),
                    FixedWidthReturnType
                ),
                (7, String::new(), "UInt64".into(), WraparoundCast),
                (8, String::new(), "USize".into(), WraparoundCast),
                (9, String::new(), "USize".into(), WraparoundCast),
                (10, String::new(), "UInt64".into(), WraparoundCast),
                (11, String::new(), "UInt32".into(), WraparoundCast),
                (11, "setSize".into(), "UInt32".into(), FixedWidthReturnType),
            ]
        );
        // Every flagged type name is flagged when it is a ghost length type.
        for ty in FIXED_WIDTH_GHOST_INT_TYPE_NAMES {
            let src = format!("axiom GhostSeq.len : GhostSeq α → {ty}\n");
            assert_eq!(
                ghost_findings("Assumptions/Ghost.lean", &src),
                vec![(
                    1,
                    "GhostSeq.len".into(),
                    ty.to_string(),
                    FixedWidthReturnType
                )],
                "{ty}"
            );
        }
        let rendered = scan_ghost_length_width_diagnostics("Specs/Ghost.lean", lean)[0].to_string();
        assert_eq!(
            rendered,
            "Specs/Ghost.lean:1: fixed_width_ghost_length: ghost length `GhostList.len` has \
             fixed-width type `UInt64`, which wraps at its bit width; use Nat or Int"
        );

        // Namespaces, `∀` binders, ghost `structure` fields, `BitVec.ofNat`,
        // `Nat.toUInt64`, and parenthesized length expressions before `.to*`.
        let extra_lean = "\
namespace GhostList
axiom len (xs : List α) : UInt64
end GhostList
axiom GhostSeq.card : ∀ (xs : GhostSeq α), USize
structure GhostBuf (α : Type) where
  items : GhostSeq α
  len : UInt64
def bv (xs : List α) : BitVec 64 := BitVec.ofNat 64 xs.length
def prefixCast (xs : List α) : UInt64 := Nat.toUInt64 xs.length
theorem parenCast (xs : List α) : (List.length xs).toUInt64 = 0 := rfl
theorem arithCast (xs : List α) : (xs.length + 1).toUSize = 0 := rfl
";
        assert_eq!(
            ghost_findings("Specs/ExtraGhost.lean", extra_lean),
            vec![
                (
                    2,
                    "GhostList.len".into(),
                    "UInt64".into(),
                    FixedWidthReturnType
                ),
                (
                    4,
                    "GhostSeq.card".into(),
                    "USize".into(),
                    FixedWidthReturnType
                ),
                (
                    7,
                    "GhostBuf.len".into(),
                    "UInt64".into(),
                    FixedWidthReturnType
                ),
                (8, String::new(), "BitVec 64".into(), WraparoundCast),
                (9, String::new(), "UInt64".into(), WraparoundCast),
                (10, String::new(), "UInt64".into(), WraparoundCast),
                (11, String::new(), "USize".into(), WraparoundCast),
            ]
        );
    }

    #[test]
    fn ghost_length_scanner_accepts_unbounded_and_non_ghost_lean() {
        let lean = "\
axiom GhostList.len : GhostList α → Nat
def ghostLen (xs : GhostSeq α) : Int := 0
def card (s : Finset α) : Nat := s.card
def GhostMap.get (m : GhostMap K UInt64) (k : K) : UInt64 := m k
def bufLen (b : Buffer) : UInt64 := b.len
def toU64 (n : Nat) : UInt64 := UInt64.ofNat n
def width : USize := USize.ofNat 8
def unrelated (n : Nat) (xs : List α) : Prop := UInt64.ofNat n = 0 ∧ xs.length > 0
def primed (b' : Nat) : Nat := b'
axiom GhostSeq.push_len (s : GhostSeq α) (x : α) : (s.push x).len = s.len + 1
def GhostSeq.lenBounded (s : GhostSeq α) : Prop := s.len < 2 ^ 64
def GhostSeq.take (s : GhostSeq α) (n : UInt64) : GhostSeq α := s
-- axiom GhostList.len : GhostList α → UInt64
/- def ghostLen (xs : GhostSeq α) : USize := 0
   /- nested: UInt64.ofNat xs.length -/ -/
def doc : String := \"axiom GhostList.len : GhostList α → UInt64; xs.length.toUSize\"
theorem natLen (xs : List α) : xs.length = xs.length := rfl
";
        assert_eq!(ghost_findings("Specs/Clean.lean", lean), vec![]);
        for ty in UNBOUNDED_GHOST_INT_TYPE_NAMES {
            let src = format!("axiom GhostSeq.len : GhostSeq α → {ty}\n");
            assert_eq!(ghost_findings("Specs/Clean.lean", &src), vec![], "{ty}");
        }
    }

    #[test]
    fn ghost_length_scanner_flags_rust_model_lengths_only_in_ghost_context() {
        use GhostLengthWidthKind::{FixedWidthReturnType, WraparoundCast};
        let rust = "\
#[model]
fn ghost_len(s: Seq<u8>) -> u64 { s.len() as u64 }

#[anneal_spec::model]
fn card(s: &GhostSet<u32>) -> usize { 0 }

#[model]
fn total_count(xs: &Chunks) -> u32 { 0 }

#[spec(ensures: |r| r >= 0)]
fn seq_size(s: Seq<u8>) -> usize { 0 }

#[invariant(self.items.len() > 0)]
#[model]
pub fn ghost_cap(m: &GhostMap<u32, u8>) -> isize { m.count() as isize }
";
        assert_eq!(
            ghost_findings("src/model.rs", rust),
            vec![
                (2, "ghost_len".into(), "u64".into(), FixedWidthReturnType),
                (2, "ghost_len".into(), "u64".into(), WraparoundCast),
                (5, "card".into(), "usize".into(), FixedWidthReturnType),
                (8, "total_count".into(), "u32".into(), FixedWidthReturnType),
                (11, "seq_size".into(), "usize".into(), FixedWidthReturnType),
                (15, "ghost_cap".into(), "isize".into(), FixedWidthReturnType),
                (15, "ghost_cap".into(), "isize".into(), WraparoundCast),
            ]
        );

        let extra_rust = "\
#[model]
pub const unsafe fn ghost_len(s: Seq<u8>) -> core::primitive::u64 { (s.len()) as u64 }

#[model]
fn ghost_size<T: Fn() -> u8>(s: Seq<T>) -> usize { 0 }

#[model]
struct GhostQueue {
    items: GhostSeq<u8>,
    len: u64,
}

#[model]
impl<T> GhostSeq<T> {
    fn len(&self) -> u64 { 0 }
}

impl<T> GhostSeq<T> {
    #[spec(ensures: |r| r >= 0)]
    fn card(&self) -> usize { 0 }
}

#[spec(ensures: |r| r == (s.len() as u64))]
fn seq_ok(s: GhostSeq<u8>) -> Nat { 0 }

#[invariant(self.ghost_items.len() as u64 <= self.cap)]
struct BoundedBuf { cap: u64 }
";
        assert_eq!(
            ghost_findings("src/extra_model.rs", extra_rust),
            vec![
                (2, "ghost_len".into(), "u64".into(), FixedWidthReturnType),
                (2, "ghost_len".into(), "u64".into(), WraparoundCast),
                (5, "ghost_size".into(), "usize".into(), FixedWidthReturnType),
                (
                    10,
                    "GhostQueue.len".into(),
                    "u64".into(),
                    FixedWidthReturnType
                ),
                (15, "len".into(), "u64".into(), FixedWidthReturnType),
                (20, "card".into(), "usize".into(), FixedWidthReturnType),
                (23, "seq_ok".into(), "u64".into(), WraparoundCast),
                (26, String::new(), "u64".into(), WraparoundCast),
            ]
        );

        let clean = "\
fn len(s: &Seq<u8>) -> usize { 0 }

#[spec(ensures: |r| r == self.items.len())]
fn len(&self) -> usize { self.items.len() }

#[model]
fn ghost_len_nat(s: Seq<u8>) -> Nat { s.len() }

#[model]
fn ghost_bounded_inc(x: u32, step: u32) -> u64 { (x as u64) + (step as u64) }

#[model]
fn lookup(m: &GhostMap<u32, u64>, k: u32) -> u64 { 0 }

#[inline]
fn ghost_len(s: &[u8]) -> usize { s.len() }

// #[model] fn ghost_len(s: Seq<u8>) -> u64 { 0 }
/* #[model] fn ghost_len(s: Seq<u8>) -> u64 { 0 } /* nested */ */
const DOC: &str = \"#[model] fn ghost_len(s: Seq<u8>) -> u64\";
const RAW: &str = r#\"#[model] fn ghost_len(s: Seq<u8>) -> u64 \"quoted\" \"#;

#[spec(requires: true)]
struct Wrapper;
fn wrapper_len(w: &Wrapper) -> usize { 0 }
";
        assert_eq!(ghost_findings("src/clean.rs", clean), vec![]);
    }

    #[test]
    fn ghost_length_scanner_sees_through_aliases_wrappers_and_cast_forms() {
        use GhostLengthWidthKind::{FixedWidthReturnType, WraparoundCast};
        let found = |label: &str, text: &str| -> Vec<(usize, String, GhostLengthWidthKind)> {
            ghost_findings(label, text)
                .into_iter()
                .map(|(line, _, ty, kind)| (line, ty, kind))
                .collect()
        };
        let ret = |line: usize, ty: &str| vec![(line, String::from(ty), FixedWidthReturnType)];
        let cast = |line: usize, ty: &str| vec![(line, String::from(ty), WraparoundCast)];

        // Lean: aliases, wrappers, qualified and bounded types, class fields.
        for (text, expected) in [
            (
                "abbrev GhostLen := UInt64\ndef ghostLen (s : GhostSeq Nat) : GhostLen := 0",
                ret(2, "UInt64"),
            ),
            (
                "def GhostLen : Type := USize\nabbrev Len := GhostLen\ndef ghostLen (s : GhostSeq Nat) : Len := 0",
                ret(3, "USize"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : Option UInt64 := none",
                ret(1, "UInt64"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : UInt64 × Bool := (0, true)",
                ret(1, "UInt64"),
            ),
            (
                "axiom ghostCard : GhostSet Nat → Option USize",
                ret(1, "USize"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : Std.BitVec 64 := 0",
                ret(1, "BitVec 64"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : Fin (2 ^ 64) := 0",
                ret(1, "Fin 2 ^ 64"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : Fin UInt64.size := 0",
                ret(1, "Fin UInt64"),
            ),
            (
                "class HasGhostLen (α : Type) where\n  ghostLen : α → UInt64",
                ret(2, "UInt64"),
            ),
        ] {
            assert_eq!(found("Specs/Buf.lean", text), expected, "{text:?}");
        }
        // Lean: cast forms.
        for (text, expected) in [
            (
                "def cap (xs : List Nat) : Prop := (xs.length : UInt64) < 10",
                cast(1, "UInt64"),
            ),
            (
                "def cap (xs : List Nat) : Prop := (xs.length + 1 : BitVec 64) < 10",
                cast(1, "BitVec 64"),
            ),
            (
                "def cap (xs : List Nat) : Prop := xs.length |>.toUInt64 < 10",
                cast(1, "UInt64"),
            ),
            (
                "def cap (xs : List Nat) : Prop := (xs.length + 1) |>.toUSize < 10",
                cast(1, "USize"),
            ),
            (
                "def cap (xs : List Nat) : Prop := UInt64.ofNat <| xs.length < 10",
                cast(1, "UInt64"),
            ),
            (
                "abbrev Len := UInt32\ndef cap (xs : List Nat) : Prop := (xs.length : Len) < 10",
                cast(2, "UInt32"),
            ),
        ] {
            assert_eq!(found("Specs/Buf.lean", text), expected, "{text:?}");
        }
        // Lean: unbounded lengths, propositions, and dependent bounds stay clean.
        for clean in [
            "abbrev GhostLen := Nat\ndef ghostLen (s : GhostSeq Nat) : GhostLen := 0",
            "abbrev Byte := UInt8\ndef ghostLen (s : GhostSeq Byte) : Nat := s.length",
            "def ghostLenBound (s : GhostSeq Nat) : Prop := s.length < UInt64.size",
            "axiom ghost_len_le (s : GhostSeq Nat) : s.len ≤ USize.size",
            "theorem ghost_len_lt (s : GhostSeq Nat) : s.len < UInt64.size := by simp",
            "def ghostLen (s : GhostSeq Nat) : Fin (s.cap + 1) := 0",
            "def ghostCount (s : GhostSeq UInt64) : Nat := s.length",
            "def cap (xs : List Nat) (n : UInt64) : Prop := (xs.length : Nat) < n.toNat",
            "def cap (xs : List Nat) (h : xs.length = 3) : Prop := (n : UInt64) = 0",
            "class HasGhostLen (α : Type) where\n  ghostLen : α → Nat",
        ] {
            assert_eq!(found("Specs/Buf.lean", clean), vec![], "{clean:?}");
        }

        // Rust: aliases, newtypes, wrappers, references, and C aliases.
        for (text, expected) in [
            (
                "type GhostLen = u64;\n#[model]\nfn ghost_len(s: Seq<u8>) -> GhostLen { 0 }",
                ret(3, "u64"),
            ),
            (
                "struct GhostLen(usize);\ntype Len = GhostLen;\n#[model]\nfn ghost_len(s: Seq<u8>) -> Len { Len(0) }",
                ret(4, "usize"),
            ),
            (
                "#[model]\nfn ghost_len(s: Seq<u8>) -> Option<u64> { None }",
                ret(2, "u64"),
            ),
            (
                "#[model]\nfn ghost_len(s: Seq<u8>) -> Wrapping<u64> { Wrapping(0) }",
                ret(2, "u64"),
            ),
            (
                "#[model]\nfn ghost_len(s: Seq<u8>) -> (u64, bool) { (0, true) }",
                ret(2, "u64"),
            ),
            (
                "#[model]\nfn ghost_len<'a>(s: &'a Seq<u8>) -> &'a u64 { &0 }",
                ret(2, "u64"),
            ),
            (
                "#[model]\nfn ghost_len(s: Seq<u8>) -> core::num::NonZeroU64 { NZ }",
                ret(2, "NonZeroU64"),
            ),
            (
                "#[model]\nfn ghost_len(s: Seq<u8>) -> libc::size_t { 0 }",
                ret(2, "size_t"),
            ),
            (
                "#[model]\nstruct GhostBuf { len: Option<u32>, items: Seq<u8> }",
                ret(2, "u32"),
            ),
            // Conditional and trait-scoped ghost attributes.
            (
                "#[cfg_attr(anneal, model)]\nfn ghost_len(s: Seq<u8>) -> u64 { 0 }",
                ret(2, "u64"),
            ),
            (
                "#[cfg_attr(feature = \"spec\", inline, anneal::model)]\nfn ghost_len(s: Seq<u8>) -> u64 { 0 }",
                ret(2, "u64"),
            ),
            (
                "#[model]\ntrait HasLen { fn ghost_len(&self) -> u64; }",
                ret(2, "u64"),
            ),
        ] {
            assert_eq!(found("src/model.rs", text), expected, "{text:?}");
        }
        // Rust: an invariant on a struct that holds a ghost collection.
        assert_eq!(
            found(
                "src/model.rs",
                "#[invariant(self.items.len() as u64 <= CAP)]\nstruct Buf { items: Seq<u8> }"
            ),
            cast(1, "u64")
        );
        // A cast seen through both the attribute and its item is reported once.
        assert_eq!(
            ghost_findings(
                "src/model.rs",
                "#[invariant(self.ghost_items.len() as u64 <= CAP)]\nstruct Buf { ghost_items: Seq<u8> }"
            ),
            vec![(1, String::from("Buf"), String::from("u64"), WraparoundCast)]
        );
        for clean in [
            "type GhostLen = Nat;\n#[model]\nfn ghost_len(s: Seq<u8>) -> GhostLen { 0 }",
            "#[model]\nfn ghost_len(s: Seq<u64>) -> Nat { s.len() }",
            "#[model]\nfn ghost_size_hint(s: Seq<u8>) -> (Nat, Option<Nat>) { (0, None) }",
            "#[cfg_attr(model, inline)]\nfn ghost_len(s: Seq<u8>) -> u64 { 0 }",
            "#[invariant(self.items.len() as u64 <= CAP)]\nstruct Buf { items: Vec<u8> }",
            "trait HasLen { fn len(&self) -> usize; }",
            "struct Meters(u64);\nfn len(m: Meters) -> Meters { m }",
        ] {
            assert_eq!(found("src/model.rs", clean), vec![], "{clean:?}");
        }
    }

    #[test]
    fn ghost_length_scanner_distinguishes_collections_scopes_newtypes_and_extra_casts() {
        use GhostLengthWidthKind::{FixedWidthReturnType, WraparoundCast};
        let found = |label: &str, text: &str| -> Vec<(usize, String, GhostLengthWidthKind)> {
            ghost_findings(label, text)
                .into_iter()
                .map(|(line, _, ty, kind)| (line, ty, kind))
                .collect()
        };
        let ret = |line: usize, ty: &str| vec![(line, String::from(ty), FixedWidthReturnType)];
        let cast = |line: usize, ty: &str| vec![(line, String::from(ty), WraparoundCast)];

        // Collection/slice/error-slot element types must NOT be falsely flagged
        // as fixed-width ghost lengths.
        for clean_rust in [
            "#[model]\nfn ghost_len_prefix(s: GhostSeq<u8>) -> GhostSeq<u8> { s }",
            "#[model]\nfn bound_slice<'a>(s: &'a GhostSeq<u8>) -> &'a [u8] { &[] }",
            "#[model]\nfn ghost_len_or_err(s: Seq<u8>) -> Result<Nat, u8> { Ok(s.len()) }",
            "struct ByteSeq(GhostSeq<u8>);\n#[model]\nfn ghost_len_seq(s: Seq<u8>) -> ByteSeq { ByteSeq(s) }",
            "struct Pair(Nat, u8);\n#[model]\nfn ghost_len_pair(s: Seq<u8>) -> Pair { Pair(s.len(), 0) }",
        ] {
            assert_eq!(
                found("src/clean_elem.rs", clean_rust),
                vec![],
                "{clean_rust:?}"
            );
        }
        for clean_lean in [
            "def GhostSeq.boundSeq (xs : GhostSeq UInt64) : GhostSeq UInt64 := xs",
            "def ghostLenBytes (xs : GhostSeq UInt8) : List UInt8 := []",
            "def ghostLenOrErr (xs : GhostSeq UInt8) : Except UInt32 Nat := .ok xs.length",
            "abbrev ByteSeq := GhostSeq UInt8\ndef ghostLenSeq (xs : ByteSeq) : ByteSeq := xs",
            "def cap (xs : List Nat) : UInt64 := (if xs.length == 0 then 0 else 1 : UInt64)",
            "def prefix (xs : List UInt8) : List UInt8 := (xs.take xs.length : List UInt8)",
        ] {
            assert_eq!(
                found("Specs/CleanElem.lean", clean_lean),
                vec![],
                "{clean_lean:?}"
            );
        }

        // Scalar/result-ok/subtype wrappers, Lean `section`/`end` scopes,
        // `ofNatTruncate`/`ofInt`, standalone Rust `#[model]` tuple structs,
        // and Rust alias/conversion wraparound casts MUST be flagged.
        for (text, expected) in [
            (
                "namespace GhostList\nsection Helpers\nend Helpers\naxiom len (xs : List α) : UInt64\nend GhostList",
                ret(4, "UInt64"),
            ),
            (
                "namespace GhostList\nsection\nend\naxiom len (xs : List α) : USize\nend GhostList",
                ret(4, "USize"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : Except String UInt64 := .ok 0",
                ret(1, "UInt64"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : { n : UInt64 // n < 10 } := ⟨0, by decide⟩",
                ret(1, "UInt64"),
            ),
            (
                "def ghostLen (s : GhostSeq Nat) : Option { n : USize // n < 10 } := none",
                ret(1, "USize"),
            ),
            (
                "def cap (xs : List Nat) : UInt64 := UInt64.ofNatTruncate xs.length",
                cast(1, "UInt64"),
            ),
            (
                "def cap (xs : List Nat) : Int64 := Int64.ofInt xs.length",
                cast(1, "Int64"),
            ),
        ] {
            assert_eq!(found("Specs/Scope.lean", text), expected, "{text:?}");
        }
        for (text, expected) in [
            ("#[model]\nstruct GhostLen(u64);", ret(2, "u64")),
            ("#[model]\nstruct SeqCard(pub usize);", ret(2, "usize")),
            (
                "struct GhostLen(pub u64);\n#[model]\nfn ghost_len(s: Seq<u8>) -> GhostLen { GhostLen(0) }",
                ret(3, "u64"),
            ),
            (
                "#[model]\nfn ghost_len_res(s: Seq<u8>) -> Result<u64, String> { Ok(0) }",
                ret(2, "u64"),
            ),
            (
                "#[model]\nfn ghost_len_nz(s: Seq<u8>) -> core::num::NonZero<u64> { NZ }",
                ret(2, "u64"),
            ),
            (
                "type GhostLen = u64;\n#[model]\nfn ok(s: Seq<u8>) -> Nat { let _ = s.len() as GhostLen; 0 }",
                cast(3, "u64"),
            ),
            (
                "#[model]\nfn ok(s: Seq<u8>) -> Nat { let _ = s.len() as core::primitive::u64; 0 }",
                cast(2, "u64"),
            ),
            (
                "#[model]\nfn ok(s: Seq<u8>) -> Nat { let _ = s.len() as libc::size_t; 0 }",
                cast(2, "size_t"),
            ),
            (
                "#[model]\nfn ok(s: Seq<u8>) -> Nat { let _ = u64::try_from(s.len()); 0 }",
                cast(2, "u64"),
            ),
            (
                "#[model]\nfn ok(s: Seq<u8>) -> Nat { let _ = core::num::NonZeroUsize::new(s.len()); 0 }",
                cast(2, "NonZeroUsize"),
            ),
        ] {
            assert_eq!(found("src/model_ext.rs", text), expected, "{text:?}");
        }
    }

    #[test]
    fn ghost_length_scanner_looks_through_unknown_wrappers() {
        use GhostLengthWidthKind::FixedWidthReturnType;
        let found = |label: &str, text: &str| -> Vec<(usize, String, GhostLengthWidthKind)> {
            ghost_findings(label, text)
                .into_iter()
                .map(|(line, _, ty, kind)| (line, ty, kind))
                .collect()
        };
        let ret = |line: usize, ty: &str| vec![(line, String::from(ty), FixedWidthReturnType)];
        // A wrapper the scanner has never heard of is still a machine integer.
        for (ret_ty, fixed) in [
            ("Tracked<u64>", "u64"),
            ("Mutex<u64>", "u64"),
            ("core::cmp::Reverse<usize>", "usize"),
            ("ControlFlow<E, u64>", "u64"),
            ("Either<u64, Nat>", "u64"),
            ("impl Into<u64>", "u64"),
            ("dyn Into<u32> + Send", "u32"),
            ("<u64 as Id>::T", "u64"),
            ("Result<Tracked<usize>, E>", "usize"),
        ] {
            let text = format!("#[model]\nfn ghost_len(s: Seq<u8>) -> {ret_ty} {{ x }}");
            assert_eq!(found("src/model.rs", &text), ret(2, fixed), "{text:?}");
        }
        for (text, expected) in [
            (
                "use core::primitive::u64 as Len;\n#[model]\nfn ghost_len(s: Seq<u8>) -> Len { 0 }",
                ret(3, "u64"),
            ),
            (
                "struct GhostLen { n: u64 }\n#[model]\nfn ghost_len(s: Seq<u8>) -> GhostLen { g }",
                ret(3, "u64"),
            ),
            (
                "type Len<T> = Wrapping<T>;\n#[model]\nfn ghost_len(s: Seq<u8>) -> Len<u64> { 0 }",
                ret(3, "u64"),
            ),
        ] {
            assert_eq!(found("src/model.rs", text), expected, "{text:?}");
        }
        for (ret_ty, fixed) in [
            ("WithTop UInt64", "UInt64"),
            ("Tracked UInt64", "UInt64"),
            ("IO USize", "USize"),
            ("UInt64 ⊕ Nat", "UInt64"),
            ("Sum Nat UInt32", "UInt32"),
            ("ExceptT String Id UInt64", "UInt64"),
            ("Fin (2 ^ 64 - 1 + 1)", "Fin 2 ^ 64 - 1 + 1"),
        ] {
            let text = format!("def ghostLen (s : GhostSeq Nat) : {ret_ty} := x");
            assert_eq!(found("Specs/Buf.lean", &text), ret(1, fixed), "{text:?}");
        }
        // Element, key, marker, parameter, and error-slot types are not the
        // length.
        for ret_ty in [
            "Vec<u64>",
            "Seq<u8>",
            "HashMap<u64, Nat>",
            "(Nat, Seq<u8>)",
            "Result<Nat, u8>",
            "PhantomData<u64>",
            "[u64; 1]",
            "&[u8]",
            "fn(u64) -> Nat",
            "impl Fn(u64) -> Nat",
            "Self::Len",
        ] {
            let text = format!("#[model]\nfn ghost_len(s: Seq<u8>) -> {ret_ty} {{ x }}");
            assert_eq!(found("src/model.rs", &text), vec![], "{text:?}");
        }
        for ret_ty in [
            "List UInt8",
            "Array UInt64",
            "Except UInt32 Nat",
            "ExceptT UInt32 Id Nat",
            "Nat × List UInt8",
            "Fin (s.cap - 1)",
        ] {
            let text = format!("def ghostLen (s : GhostSeq Nat) : {ret_ty} := x");
            assert_eq!(found("Specs/Buf.lean", &text), vec![], "{text:?}");
        }
        for clean in [
            "use core::primitive::u64 as Len;\n#[model]\nfn ghost_len(s: Seq<Len>) -> Nat { 0 }",
            "struct Pair { n: Nat, m: u64 }\n#[model]\nfn ghost_len(s: Seq<u8>) -> Pair { p }",
        ] {
            assert_eq!(found("src/model.rs", clean), vec![], "{clean:?}");
        }
    }

    #[test]
    fn ghost_length_scanner_fails_closed_on_malformed_source() {
        for (label, text) in [
            (
                "Specs/Bad.lean",
                "/- unclosed\naxiom GhostList.len : GhostList α → Nat",
            ),
            ("Specs/Bad.lean", "def doc : String := \"unclosed"),
            (
                "src/bad.rs",
                "/* unclosed\n#[model] fn ghost_len() -> Nat { 0 }",
            ),
            ("src/bad.rs", "const S: &str = r#\"unclosed\";"),
        ] {
            let diagnostics = scan_ghost_length_width_diagnostics(label, text);
            assert_eq!(diagnostics.len(), 1, "{text:?}");
            assert_eq!(diagnostics[0].kind, GhostLengthWidthKind::MalformedSource);
            assert_eq!(diagnostics[0].line, 1);
            assert!(diagnostics[0].to_string().contains("fail-closed"));
        }
    }

    #[test]
    fn ghost_length_scanner_uses_the_dialect_of_the_source_label() {
        assert_eq!(
            SpecSourceDialect::from_source_label("a/b.rs"),
            SpecSourceDialect::Rust
        );
        assert_eq!(
            SpecSourceDialect::from_source_label("a/B.lean"),
            SpecSourceDialect::Lean
        );
        assert_eq!(
            SpecSourceDialect::from_source_label("spec.txt"),
            SpecSourceDialect::Unknown
        );
        // `--` hides the declaration in Lean only.
        let hidden_in_lean = "-- axiom GhostList.len : GhostList α → UInt64\n";
        assert_eq!(ghost_findings("Specs/A.lean", hidden_in_lean), vec![]);
        // `//` does not start a Lean comment, so the declaration is seen.
        let visible_in_lean = "// note\naxiom GhostList.len : GhostList α → UInt64\n";
        assert_eq!(ghost_findings("Specs/A.lean", visible_in_lean).len(), 1);
        // An unlabeled source is scanned with both comment families and both
        // declaration grammars.
        let mixed = "#[model]\nfn ghost_len(s: Seq<u8>) -> u64 { 0 }\naxiom GhostList.len : GhostList α → UInt64\n";
        assert_eq!(ghost_findings("spec.txt", mixed).len(), 2);
    }

    // ---- Guard 3: error-branch wildcard scanner -----------------------------

    fn wildcard_findings(label: &str, text: &str) -> Vec<(usize, ErrorBranchWildcardKind)> {
        scan_error_branch_wildcard_diagnostics(label, text)
            .into_iter()
            .map(|d| {
                assert_eq!(d.source_label, label);
                (d.line, d.kind)
            })
            .collect()
    }

    #[test]
    fn error_branch_wildcard_scanner_reports_every_wildcard_arm() {
        use ErrorBranchWildcardKind::{
            CatchAllArmTrue, ErrArmTrue, MatchesAnyErr, UbArmTrue, UnsupportedArmTrue,
        };
        let lean = "\
def post (x : Nat) : Except String Nat → Prop
  | .ok v => v = x + 1
  | .error _ => True

def post2 (x : Nat) : FallibleOutcome Nat String → Prop
  | .ok v => v = x + 1
  | .err _ => (True)
  | .ub => True
  | .unsupported => True

def post3 : Outcome → Prop
  | .ok v => v = 1
  | .fail .ub => True
  | Err _ => True
  | .ub | .unsupported => True
  | _ => True
";
        assert_eq!(
            wildcard_findings("Specs/Post.lean", lean),
            vec![
                (3, ErrArmTrue),
                (7, ErrArmTrue),
                (8, UbArmTrue),
                (9, UnsupportedArmTrue),
                (13, UbArmTrue),
                (14, ErrArmTrue),
                (15, UbArmTrue),
                (16, CatchAllArmTrue),
            ]
        );
        let rust = "\
#[spec(ensures: |out| match out {
    Ok(v) => *v == x + 1,
    Err(_) => true,
})]
fn incr(x: u32) -> Result<u32, E> { step(x) }

#[spec(ensures: |out| matches!(out, Ok(_) | Err(_)))]
fn any(x: u32) -> Result<u32, E> { run(x) }

#[spec(ensures: |out| match out { Ok(v) => *v == 1, Err(..) => (true), })]
fn one() -> Result<u32, E> { Ok(1) }
";
        assert_eq!(
            wildcard_findings("src/lib.rs", rust),
            vec![(3, ErrArmTrue), (7, MatchesAnyErr), (10, ErrArmTrue)]
        );
        let diagnostics = scan_error_branch_wildcard_diagnostics("Specs/Post.lean", lean);
        assert_eq!(
            diagnostics[0].to_string(),
            "Specs/Post.lean:3: error_branch_wildcard: postcondition arm accepts every error \
             payload (`Err(_) => true`); constrain the error or state when it may occur"
        );
        assert_eq!(
            ErrorBranchWildcardDiagnostic::GUARD,
            SpecBoundaryGuardId::ErrorBranchWildcard
        );
    }

    /// The same shapes are asserted by `detect_error_branch_wildcard` in
    /// `anneal_spec::spec_check`.
    #[test]
    fn error_branch_wildcard_scanner_matches_anneal_spec_vectors() {
        use ErrorBranchWildcardKind::{
            CatchAllArmTrue, ErrArmTrue, MatchesAnyErr, UbArmTrue, UnsupportedArmTrue,
        };
        let flagged: &[(&str, ErrorBranchWildcardKind)] = &[
            ("Err(_) => true", ErrArmTrue),
            ("Err(..) => true", ErrArmTrue),
            ("Err(_e) => true", ErrArmTrue),
            ("Err(e) => true", ErrArmTrue),
            ("Err(fun) => true", ErrArmTrue),
            ("Result::Err(_) => true", ErrArmTrue),
            ("Err(_) => (true)", ErrArmTrue),
            ("Err(_) => { return true; }", ErrArmTrue),
            ("Err(_) => !false", ErrArmTrue),
            ("Err(_) => true && true", ErrArmTrue),
            ("Err(_) => (true || x == 3)", ErrArmTrue),
            ("Err(_) => true as bool", ErrArmTrue),
            ("Err(_) => (true as bool)", ErrArmTrue),
            ("Err(_) if true => true", ErrArmTrue),
            ("Ok(0) | Err(_) => true", ErrArmTrue),
            ("Some(Err(_) | Ok(0)) => true", ErrArmTrue),
            ("(Err(_) | Ok(0)) => true", ErrArmTrue),
            ("Err(E::A | _) => true", ErrArmTrue),
            ("Err(_ | E::A) => true", ErrArmTrue),
            ("Err(()) => true", ErrArmTrue),
            ("(Err(_), _) => true", ErrArmTrue),
            ("SemanticOutcome::Ub => true", UbArmTrue),
            ("SemanticOutcome::Unsupported => true", UnsupportedArmTrue),
            ("matches!(out, Ok(_) | Err(_))", MatchesAnyErr),
            ("matches!(out, Ok(_) | Err(_),)", MatchesAnyErr),
            ("matches!(out, Err(_) if true)", MatchesAnyErr),
            ("matches!(out, Ok(v) | _)", MatchesAnyErr),
            ("matches!(out, (Err(_) | Ok(0)))", MatchesAnyErr),
            ("matches!(out, Err(_))", MatchesAnyErr),
            ("match out { Ok(v) => *v == 1, _ => true }", CatchAllArmTrue),
            ("| Err _ => True", ErrArmTrue),
            ("| .err _ => True", ErrArmTrue),
            ("| .error _ => True", ErrArmTrue),
            ("| .err () => True", ErrArmTrue),
            ("| .err (_ : String) => True", ErrArmTrue),
            ("| .err (e : Result Nat String) => True", ErrArmTrue),
            ("| Except.error _ => True", ErrArmTrue),
            ("| .err _ => trivial", ErrArmTrue),
            ("| .err _ => ¬False", ErrArmTrue),
            ("| .err _ => ¬ False", ErrArmTrue),
            ("| .err _ => Not False", ErrArmTrue),
            ("| .err _ => True ∧ True", ErrArmTrue),
            ("| .err _ => (True ∨ x = 3)", ErrArmTrue),
            ("| .err _ => True ∨ x = 3", ErrArmTrue),
            ("match out with .err _ => True", ErrArmTrue),
            ("| .ub => True", UbArmTrue),
            ("| .unsupported => True", UnsupportedArmTrue),
            ("| .fail .ub => True", UbArmTrue),
            ("| .fail _ => True", UbArmTrue),
            ("| .ub | .unsupported => True", UbArmTrue),
            ("| .ok v => v = 1 | _ => True", CatchAllArmTrue),
        ];
        for (src, expected) in flagged {
            assert_eq!(
                wildcard_findings("spec.txt", src),
                vec![(1, *expected)],
                "{src:?}"
            );
        }
        for src in [
            "match out { Ok(v) => *v == x + 1, Err(E::Overflow) => x == u32::MAX }",
            "Err(E::Overflow) => true",
            "Err(Unsupported) => true",
            "Err(E::A | E::B) => true",
            "Err(0) => true",
            "Err(\"overflow\") => true",
            "Err(_) => x == u32::MAX",
            "Err(()) => *x == u32::MAX",
            "Err(_) => false",
            "Err(_) if x == u32::MAX => true",
            "Err(_) => true && x == 3",
            "Err(_) => (true || x == 3) && y == 4",
            "Err(_) => true as u8 == 1",
            "Err(_) => true as bool && x == 1",
            "| .ub => False",
            "| .err _ => False",
            "| .err e => e = .overflow",
            "| .err .overflow => True",
            "| .err .ub => True",
            "| .err .unsupported => True",
            "| .fail .outOfFuel => True",
            "| .err _ => True ∧ x = 3",
            "| .err _ => True → False",
            "| .ok _ => True",
            "match out { Ok(v) => match *v { 0 => false, _ => true }, Err(E::A) => true }",
            "match out { Ok(v) => *v == 1, Err(E::A) => true }\nfn other(x: u32) { match x { 0 => false, _ => true } }",
            "def post1 : Except String Nat → Prop\n  | .ok v => v = 1\n  | .error e => e = \"a\"\ndef helper : Nat → Prop\n  | 0 => False\n  | _ => True",
            "def post : Except String Nat → Prop\n  | .ok v => (match v with | 0 => False | _ => True)\n  | .error e => e = \"a\"",
            "def helper (e : String) := Except.error e\ndef f := fun _ => True",
            "| .ok v => let fallback := Outcome.err e\n  fun _ => True",
            "| .ok v => fun _ => True",
            "// Err(_) => true\nmatch out { Ok(v) => *v == 1, Err(e) => *e == E::A }",
            "/* Err(_) => true */ out.is_ok()",
            "-- | .err _ => True\n| .err e => e = E.a",
            "/- | .ub => True -/ | .ub => False",
            "let s = \"Err(_) => true\"; out == Ok(1)",
            "let s = r#\"| .err _ => True\"#; out == Ok(1)",
            "let s = cr#\"quote \" Err(_) => true \"#; out == Ok(1)",
            "match x { 0 => out == 1, _ => true }",
            "matches!(out, Ok(_))",
            "matches!(out, Err(E::Overflow))",
            "matches!(out, Err(_) if x == u32::MAX)",
            "| .none => r = .err | .some w => True",
            "| .ok v' => v' = f x' | .err e => e = g x'",
            "| .ok b' => b' = x' | .err e => e = b'",
            "",
        ] {
            assert_eq!(wildcard_findings("spec.txt", src), vec![], "{src:?}");
        }
        for malformed in [
            "/* unclosed Err(_) => false",
            "/- unclosed | .ub => False",
            "\"unclosed string",
            "cr#\"unclosed raw c\"",
            "'\\n\nfn f<'a>() {}",
            "Err(_) => true /* unclosed",
        ] {
            assert_eq!(
                wildcard_findings("spec.txt", malformed),
                vec![(1, ErrorBranchWildcardKind::MalformedSource)],
                "{malformed:?}"
            );
        }
        // The dialect of the label decides what a comment is.
        let src = "Err(_) => true -- && x == 3";
        assert_eq!(
            wildcard_findings("Specs/A.lean", src),
            vec![(1, ErrArmTrue)]
        );
        assert_eq!(wildcard_findings("src/a.rs", src), vec![]);
    }

    /// Regression vectors shared byte-for-byte by `anneal_spec::spec_check`
    /// and `cargo_anneal::property_registry` (the two crates cannot depend on
    /// each other): `(dialect, source, wire tag of the first finding)`, where
    /// an empty tag means "no finding".
    const WILDCARD_PARITY_VECTORS: &[(&str, &str, &str)] = &[
        // A parenthesized or bracketed Lean `match` has arms below depth 0.
        (
            "lean",
            "(match r with | .ok v => v = 1 | .err _ => True)",
            "err_arm_true",
        ),
        (
            "any",
            "(match r with | .ok v => v = 1 | .err _ => True)",
            "err_arm_true",
        ),
        (
            "lean",
            "P ∧ (match r with | .ok v => v = 1 | .err _ => True)",
            "err_arm_true",
        ),
        (
            "lean",
            "fun x out => (match out with | .ok v => v = x + 1 | .ub => True)",
            "ub_arm_true",
        ),
        (
            "lean",
            "def post (x : Nat) (out : Outcome) : Prop :=\n  (match out with\n  | .ok v => v = x\n  | .unsupported => True)",
            "unsupported_arm_true",
        ),
        (
            "lean",
            "(match r with | .ok v => v = 1 | _ => True)",
            "catch_all_arm_true",
        ),
        (
            "lean",
            "[match r with | .ok v => v = 1 | .err _ => True]",
            "err_arm_true",
        ),
        (
            "lean",
            "(fun out => match out with | .ok v => v = 1 | .err _ => True)",
            "err_arm_true",
        ),
        (
            "lean",
            "| .ok v => (match v with | 0 => False | _ => True) ∧ Q | .err _ => True",
            "err_arm_true",
        ),
        (
            "lean",
            "| .ok v => xs.all (fun x => x ||| 1 = v) | .err _ => True",
            "err_arm_true",
        ),
        (
            "lean",
            "(match r with | .ok v => v = 1 | .err e => e = 2) ∧ (match q with | 0 => False | _ => True)",
            "",
        ),
        // A Lean `match` without parentheses owns every later arm.
        (
            "lean",
            "match out with | .err e => e = .a | .ok v => match v with | 0 => False | _ => True",
            "",
        ),
        (
            "lean",
            "match out with | .err e => e = .a | .ok v => match v with | 0 => False | n => True",
            "",
        ),
        (
            "lean",
            "match out with | .ok v => { s with a := v } = t | _ => True",
            "catch_all_arm_true",
        ),
        // Tuple components and Lean discriminants are siblings, not payloads.
        ("rust", "(Err(_), Err(_)) => true", "err_arm_true"),
        ("rust", "(Err(_), Ok(_)) => true", "err_arm_true"),
        ("rust", "(Err(E::A), Err(_)) => true", "err_arm_true"),
        ("rust", "(Err(_), Err(E::A)) => true", "err_arm_true"),
        ("rust", "Wrap(Err(_), 3) => true", "err_arm_true"),
        (
            "rust",
            "match (a, b) { (Ok(x), Ok(y)) => x == y, (Err(_), _) | (_, Err(_)) => true }",
            "err_arm_true",
        ),
        ("lean", "| .err _, .ok v => True", "err_arm_true"),
        ("lean", "| .ok v, .err _ => True", "err_arm_true"),
        ("lean", "| .err .a, .ok v => True", ""),
        ("rust", "(Err(E::A), Err(E::B)) => true", ""),
        ("rust", "Err((_, E::A)) => true", ""),
        // A bare binding is a catch-all exactly like `_`.
        (
            "rust",
            "match out { Ok(v) => *v == 1, e => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => *v == 1, _e => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => *v == 1, ref other => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => { *v == 1 } e => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => { *v == 1 } Err(_) => true }",
            "err_arm_true",
        ),
        ("lean", "| .ok v => v = 1 | e => True", "catch_all_arm_true"),
        (
            "lean",
            "match out with | .ok v => v = 1 | _e => True",
            "catch_all_arm_true",
        ),
        ("rust", "match x { 0 => out == 1, n => true }", ""),
        ("rust", "match out { Ok(v) => *v == 1, MAX => true }", ""),
        (
            "rust",
            "match out { Ok(v) => match v.kind { Kind::A => true, other => true }, Err(e) => *e == E::A }",
            "",
        ),
        (
            "lean",
            "match x with | some (.ok v) => v = 1 | none => True",
            "",
        ),
        (
            "lean",
            "| .ok v => f (fun e => True) | .err e => e = .a",
            "",
        ),
        // Scopes: a block restores the bracket depth around it, and neither
        // dialect leaks a nested scope into the arms that follow it.
        (
            "any",
            "match out { Ok(v) => (match v { 0 => false, _ => true }), _ => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "matches!(out, Ok(Foo { x: 1 }) | Err(_))",
            "matches_any_err",
        ),
        (
            "rust",
            "fn f() -> bool { matches!{out, Err(_)} }",
            "matches_any_err",
        ),
        ("rust", "matches!(out, Ok(Foo { x: 1 }) | Err(E::A))", ""),
        // Lean raw strings: a backslash does not escape the closing quote.
        (
            "lean",
            "| .ok v => v = r\"\\\" ∧ True | .err _ => True -- \"",
            "err_arm_true",
        ),
        (
            "any",
            "| .ok v => v = r\"\\\" ∧ True | .err _ => True -- \"",
            "err_arm_true",
        ),
        (
            "lean",
            "| .ok v => v = r\"| .err _ => True\" | .err e => e = .a",
            "",
        ),
        (
            "lean",
            "| .ok v => v = r#\"\"| .err _ => True\"\"# | .err e => e = .a",
            "",
        ),
        // Trivially-true bodies.
        ("lean", "| .err _ => (True : Prop)", "err_arm_true"),
        ("rust", "Err(_) => { return true || p; }", "err_arm_true"),
        ("rust", "Err(_) => { true || p; false }", ""),
        ("lean", "| .err _ => (True : Prop) ∧ x = 3", ""),
        // An or-pattern below a payload constructor stays constrained.
        ("rust", "Err(Wrap(E::A | _)) => true", ""),
        ("rust", "Err(Wrap(E::A) | _) => true", "err_arm_true"),
        ("lean", "| .err (.a | _) => True", "err_arm_true"),
        ("lean", "| .err (.wrap (.a | _)) => True", ""),
        // Struct patterns after `|` must not wipe an earlier wildcard or
        // `matches!` arm state.
        (
            "rust",
            "matches!(out, Err(_) | Ok(Foo { x: 1 }))",
            "matches_any_err",
        ),
        (
            "rust",
            "matches!(out, Err(_) | Foo { x: 1 })",
            "matches_any_err",
        ),
        ("rust", "Err(_) | Ok(Foo { x: 1 }) => true", "err_arm_true"),
        ("rust", "Err(_) | Foo { x: 1 } => true", "err_arm_true"),
        (
            "rust",
            "match out { Ok(v) => v == 1, _ | Foo { x: 1 } => true }",
            "catch_all_arm_true",
        ),
        // Catch-all binders behind `&`, `&mut`, `(...)`, `@`, and Lean type
        // ascriptions, without false-positiving on constructor-wrapped or-patterns.
        (
            "rust",
            "match out { &Ok(v) => v == 1, &_ => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { &Ok(v) => v == 1, &e => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, &mut e => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, &&_ => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, (_) => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, ((e)) => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, e @ _ => true }",
            "catch_all_arm_true",
        ),
        (
            "lean",
            "| .ok v => v = 1 | (_ : Except String Nat) => True",
            "catch_all_arm_true",
        ),
        (
            "lean",
            "(match r with | .ok v => v = 1 | (e : Except String (List Nat)) => True)",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, Some(0 | _) => true }",
            "",
        ),
        ("rust", "match out { Ok(v) => v == 1, &E::A => true }", ""),
        (
            "rust",
            "match out { Ok(v) => v == 1, e @ E::A => true }",
            "",
        ),
        // Parenthesized conjunctions and right-hand disjunctions in arm bodies,
        // respecting `&&` > `||` and `∨` > `→` precedence.
        ("rust", "Err(_) => (true && true)", "err_arm_true"),
        ("lean", "| .err _ => (True ∧ True)", "err_arm_true"),
        ("rust", "Err(_) => x == 1 || true", "err_arm_true"),
        ("rust", "Err(_) => (x == 1 || true)", "err_arm_true"),
        (
            "rust",
            "Err(_) => { return x == 1 || true; }",
            "err_arm_true",
        ),
        ("rust", "Err(_) => x == 1 || (true && true)", "err_arm_true"),
        ("lean", "| .err _ => x = 1 ∨ True", "err_arm_true"),
        ("lean", "| .err _ => (x = 1 ∨ True)", "err_arm_true"),
        ("rust", "Err(_) => x == 1 || true && y == 2", ""),
        ("rust", "Err(_) => (x == 1 || true) && y == 2", ""),
        ("lean", "| .err _ => x = 1 ∨ True → False", ""),
        ("lean", "| .err _ => True ∨ x = 1 → False", ""),
        ("rust", "Err(_) => { check() } _ if a || true => false", ""),
        // Unicode Lean lambda `λ` behaves like `fun`.
        ("lean", "| .ok v => λ _ => True", ""),
        ("lean", "| .ok v => f (λ e => True) | .err e => e = .a", ""),
        // An arm body ends at the next top-level command: later code is
        // not part of it.
        (
            "lean",
            "def post : Outcome → Prop\n  | .ok v => v = 1\n  | .err _ => False\n\n#eval decide (1 = 1) || true",
            "",
        ),
        (
            "lean",
            "def post : Outcome → Prop\n  | .ok v => v = 1\n  | .err _ => False\n\n#check P ∨ True",
            "",
        ),
        (
            "lean",
            "def post : Outcome → Prop\n  | .ok v => v = 1\n  | .ub => False\n\nnamespace Foo\nvariable (x : Nat)\n#reduce x = x ∨ True",
            "",
        ),
        (
            "lean",
            "| .err _ => False\n@[simp] theorem t : P ∨ True := trivial",
            "",
        ),
        (
            "lean",
            "| .err _ => e = .a\nopen Foo in\n#check Q ∨ True",
            "",
        ),
        // Right-extending constructs own the disjunctions after them.
        ("lean", "| .err _ => if c then False else P ∨ True", ""),
        (
            "lean",
            "| .err _ => True ∨ if c then P else Q",
            "err_arm_true",
        ),
        ("lean", "| .err _ => False ∨ True", "err_arm_true"),
        // A tuple is not a parenthesized proposition.
        ("rust", "Err(_) => (true, x)", ""),
        ("rust", "Err(_) => (true || x, y)", ""),
        // Struct patterns keep their error constructors.
        (
            "rust",
            "match out { Ok(v) => v == 1, Wrapper { inner: Err(_) } => true }",
            "err_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, Wrapper { x: 1, inner: Err(_) } => true }",
            "err_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, Wrapper { inner: Err(_), x: 1, y: 2 } => true }",
            "err_arm_true",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, Wrapper { inner: Err(E::A), x: 1 } => true }",
            "",
        ),
        (
            "rust",
            "match w { W { r: Ok(v), .. } => v == 1, _ => true }",
            "catch_all_arm_true",
        ),
        (
            "lean",
            "match out with | { val := .ok v } => v = 1 | { val := .err _ } => True",
            "err_arm_true",
        ),
        (
            "lean",
            "match out with | { val := .ok v } => v = 1 | { val := .err .a } => True",
            "",
        ),
        (
            "rust",
            "fn f() -> Foo { Foo { r: Err(e) } }\nfn g(x: u8) -> bool { match x { 0 => false, _ => true } }",
            "",
        ),
        (
            "rust",
            "match out { Ok(v) => { check(Err(e)) } Err(E::A) => true }",
            "",
        ),
        // A tuple of catch-alls is a catch-all.
        (
            "rust",
            "match (a, b) { (Ok(x), Ok(y)) => x == y, (_, _) => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match (a, b) { (Ok(x), Ok(y)) => x == y, (e, f,) => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match (a, b) { (Ok(x), Ok(y)) => x == y, ((_, _), _) => true }",
            "catch_all_arm_true",
        ),
        (
            "rust",
            "match (a, b) { (Ok(x), Ok(y)) => x == y, (_, Ok(y)) => true }",
            "",
        ),
        (
            "rust",
            "match (a, b) { (Ok(x), Ok(y)) => x == y, (_ | 0, Ok(y)) => true }",
            "",
        ),
        (
            "rust",
            "match out { Ok(v) => v == 1, (_ | 0) => true }",
            "catch_all_arm_true",
        ),
        // Lean identifier quotes are transparent.
        (
            "lean",
            "match out with | .ok v => v = 1 | «e» => True",
            "catch_all_arm_true",
        ),
        ("lean", "| «Except.error» _ => True", "err_arm_true"),
    ];

    /// The same table is asserted by `scan_error_branch_wildcard` in
    /// `anneal_spec::spec_check`.
    #[test]
    fn error_branch_wildcard_scanner_agrees_with_the_parity_vectors() {
        for (dialect, src, expected) in WILDCARD_PARITY_VECTORS {
            let label = match *dialect {
                "rust" => "src/spec.rs",
                "lean" => "Specs/Spec.lean",
                "any" => "spec.txt",
                other => panic!("unknown dialect {other:?}"),
            };
            let findings = wildcard_findings(label, src);
            let found = findings.first().map_or("", |(_, kind)| kind.as_str());
            assert_eq!(found, *expected, "{dialect}: {src:?}");
        }
    }

    #[test]
    fn error_branch_wildcard_scope_tracking_is_bounded_and_fails_closed() {
        use ErrorBranchWildcardKind::CatchAllArmTrue;
        let depth = MAX_OK_SCOPE_DEPTH + 8;
        let opens = "{ ".repeat(depth);
        let closes = " }".repeat(depth);
        // Beyond the tracked capacity a catch-all is reported (fail closed).
        let deep = format!("{opens}match x {{ 0 => false, _ => true }}{closes}");
        assert_eq!(
            wildcard_findings("spec.txt", &deep),
            vec![(1, CatchAllArmTrue)]
        );
        // The stack unwinds: after the nest, scopes are tracked exactly again.
        let after = format!("{opens}{closes} match y {{ 0 => false, _ => true }}");
        assert_eq!(wildcard_findings("spec.txt", &after), vec![]);
        let after_ok = format!("{opens}{closes} match out {{ Ok(v) => *v == 1, _ => true }}");
        assert_eq!(
            wildcard_findings("spec.txt", &after_ok),
            vec![(1, CatchAllArmTrue)]
        );
        // Sequential Lean matches never accumulate scopes.
        let mut many = String::new();
        for _ in 0..(4 * MAX_OK_SCOPE_DEPTH) {
            many.push_str("(match a with | 0 => False | _ => True) ∧ ");
        }
        let clean = format!("{many}(match r with | .ok v => v = 1 | .err e => e = 2)");
        assert_eq!(wildcard_findings("Specs/A.lean", &clean), vec![]);
        let dirty = format!("{many}(match r with | .ok v => v = 1 | _ => True)");
        assert_eq!(
            wildcard_findings("Specs/A.lean", &dirty),
            vec![(1, CatchAllArmTrue)]
        );
        // Closers of brackets opened before the snippet are tolerated.
        assert_eq!(
            wildcard_findings(
                "spec.txt",
                "} ) ] } match out { Ok(v) => *v == 1, _ => true }"
            ),
            vec![(1, CatchAllArmTrue)]
        );
        assert_eq!(
            wildcard_findings("spec.txt", "} ) ] } match x { 0 => false, _ => true }"),
            vec![]
        );
    }

    // ---- Guard 1: entry-point `requires` audit ------------------------------

    #[test]
    fn binary_entry_def_paths_match_lean_vectors() {
        for accepted in [
            "main",
            "::main",
            "my_crate::main",
            "::my_crate::main",
            "_start",
            "::_start",
            "my_crate::_start",
            "::my_crate::_start",
            "__start",
            "::__start",
            "my_crate::__start",
            "::my_crate::__start",
            "crate::main",
        ] {
            assert!(is_binary_entry_def_path(accepted), "{accepted:?}");
        }
        for rejected in [
            "",
            "domain",
            "maintain",
            "main_loop",
            "mainx",
            "xmain",
            "Main",
            "MAIN",
            "start",
            "_start_",
            "___start",
            "my_crate::domain",
            "my_crate::maintain",
            "my_crate::main_loop",
            "my_crate::Type::main",
            "my_crate::module::_start",
            "my_crate::main::helper",
            "main::",
            "my_crate::main ",
            "my_crate:main",
            "<MyType as Trait>::main",
            "<impl Foo>::main",
            "{{impl}}::main",
            ":::main",
            "::::main",
            "my_crate::::main",
            "123::main",
            "my crate::main",
            " ::main",
        ] {
            assert!(!is_binary_entry_def_path(rejected), "{rejected:?}");
        }
    }

    fn guard_test_mir(def_path: &str, role: IrContractRole, ret: IrOperand) -> IrCapturedMir {
        let mut mir = build_probe_mir_body(FalseProofMutationProbe::CallArgBlindProbe);
        mir.def_path = String::from(def_path);
        mir.role = role;
        mir.basic_blocks = vec![IrBasicBlockData {
            statements: vec![
                IrStatement {
                    kind: IrStatementKind::StorageLive(1),
                    span: String::new(),
                    comment: None,
                },
                IrStatement {
                    kind: IrStatementKind::Assign(
                        IrPlace {
                            local_: 0,
                            projection: Vec::new(),
                        },
                        IrRvalue::Use(ret),
                    ),
                    span: String::new(),
                    comment: None,
                },
            ],
            terminator: IrTerminator {
                kind: IrTerminatorKind::Return,
                span: String::new(),
                comment: None,
            },
            is_cleanup: false,
        }];
        mir
    }

    fn const_bool_operand(value: bool) -> IrOperand {
        IrOperand::Constant(IrConstOperand {
            ty: IrTy {
                kind: IrRigidTy::Bool,
                layout_idx: 0,
            },
            val: IrConstValue::Scalar(IrConstScalar::Int(IrScalarInt {
                bits: u128::from(value),
                size_bytes: 1,
            })),
        })
    }

    fn copy_arg_operand() -> IrOperand {
        IrOperand::Copy(IrPlace {
            local_: 1,
            projection: Vec::new(),
        })
    }

    #[test]
    fn requires_companion_triviality_is_structural() {
        let requires = |ret| {
            guard_test_mir(
                "m::__anodized_fn_requires_main",
                IrContractRole::Requires(String::from("m::main")),
                ret,
            )
        };
        assert!(ir_requires_body_is_trivially_true(&requires(
            const_bool_operand(true)
        )));
        assert!(!ir_requires_body_is_trivially_true(&requires(
            const_bool_operand(false)
        )));
        assert!(!ir_requires_body_is_trivially_true(&requires(
            copy_arg_operand()
        )));
        // A `u32` constant `1` is not the boolean `true`.
        assert!(!ir_requires_body_is_trivially_true(&requires(
            const_u32_operand(1)
        )));
        // No assignment to the return place at all.
        let mut empty = requires(const_bool_operand(true));
        empty.basic_blocks[0].statements.clear();
        assert!(!ir_requires_body_is_trivially_true(&empty));
        // Two blocks, or a non-`return` terminator, are never trivial.
        let mut two_blocks = requires(const_bool_operand(true));
        let block = two_blocks.basic_blocks[0].clone();
        two_blocks.basic_blocks.push(block);
        assert!(!ir_requires_body_is_trivially_true(&two_blocks));
        let mut unreachable = requires(const_bool_operand(true));
        unreachable.basic_blocks[0].terminator.kind = IrTerminatorKind::Unreachable;
        assert!(!ir_requires_body_is_trivially_true(&unreachable));
        // A later overwrite with a non-constant makes it non-trivial.
        let mut overwritten = requires(const_bool_operand(true));
        let stmt = IrStatement {
            kind: IrStatementKind::Assign(
                IrPlace {
                    local_: 0,
                    projection: Vec::new(),
                },
                IrRvalue::Use(copy_arg_operand()),
            ),
            span: String::new(),
            comment: None,
        };
        overwritten.basic_blocks[0].statements.push(stmt);
        assert!(!ir_requires_body_is_trivially_true(&overwritten));
    }

    #[test]
    fn mir_entry_point_requires_audit_flags_main_and_start_only() {
        let subject =
            |path: &str| guard_test_mir(path, IrContractRole::Subject, copy_arg_operand());
        let requires = |target: &str, ret| {
            guard_test_mir(
                &format!("{target}::__anodized_fn_requires"),
                IrContractRole::Requires(String::from(target)),
                ret,
            )
        };

        for entry in ["demo::main", "main", "fw::_start", "fw::__start"] {
            let items = [subject(entry), requires(entry, copy_arg_operand())];
            let diagnostics = audit_mir_entry_point_requires(&items[0], &items, &[]);
            assert_eq!(
                diagnostics,
                vec![EntryPointRequiresDiagnostic {
                    entry_def_path: String::from(entry),
                    source_label: format!("{entry}::__anodized_fn_requires"),
                    line: 0,
                    kind: EntryPointRequiresKind::MirRequiresCompanion,
                }],
                "{entry}"
            );
            assert!(diagnostics[0].to_string().contains("entry_point_requires"));
            assert!(diagnostics[0].to_string().contains(entry));

            // A constant-`true` companion is not a precondition.
            let trivial = [subject(entry), requires(entry, const_bool_operand(true))];
            assert_eq!(
                audit_mir_entry_point_requires(&trivial[0], &trivial, &[]),
                vec![]
            );
            // No companion at all.
            assert_eq!(
                audit_mir_entry_point_requires(&trivial[0], &trivial[..1], &[]),
                vec![]
            );
        }

        // Non-entry items may carry any precondition.
        for helper in [
            "demo::helper",
            "demo::domain",
            "demo::maintain",
            "demo::main_loop",
            "demo::Type::main",
            "demo::module::_start",
        ] {
            let items = [subject(helper), requires(helper, copy_arg_operand())];
            assert_eq!(
                audit_mir_entry_point_requires(&items[0], &items, &[]),
                vec![],
                "{helper}"
            );
        }

        // A companion of another item is not attributed to the entry point.
        let items = [
            subject("demo::main"),
            requires("demo::helper", copy_arg_operand()),
        ];
        assert_eq!(
            audit_mir_entry_point_requires(&items[0], &items, &[]),
            vec![]
        );

        // Attribute-classified entry points are supplied by the front end.
        let items = [
            subject("fw::reset"),
            requires("fw::reset", copy_arg_operand()),
        ];
        assert_eq!(
            audit_mir_entry_point_requires(&items[0], &items, &[]),
            vec![]
        );
        assert_eq!(
            audit_mir_entry_point_requires(&items[0], &items, &["fw::reset"]).len(),
            1
        );

        // The audit is about subjects: a companion is never itself an entry.
        let companion = requires("demo::main", copy_arg_operand());
        assert_eq!(
            audit_mir_entry_point_requires(&companion, std::slice::from_ref(&companion), &[]),
            vec![]
        );
    }

    #[test]
    fn lean_entry_point_pre_audit_accepts_trivial_and_default_preconditions() {
        let audit = |path: &str, text: &str| {
            audit_lean_spec_entry_point_requires(path, "Specs/Demo/main.lean", text, &[])
                .into_iter()
                .map(|d| (d.line, d.kind))
                .collect::<Vec<_>>()
        };
        for clean in [
            "def pre (args : List Value) : Prop :=\n  True\n\ndef post (args : List Value) (ret : Value) : Prop := ret = args.head!\n",
            "def pre (args : List Value) : Prop := (True)\n",
            "def pre (args : List Value) : Prop :=\n  Obligations.Demo.main.defaultPre args\n",
            "def pre (args : List Value) (mem : Memory) : Prop :=\n  Obligations.Demo.main.defaultModularSpec.pre args mem\n",
            "def pre (args : List Value) : Prop := Obligations.Demo.main.rustRequires args\n",
            "instance : ItemSpec \"demo::main\" where\n  pre := fun _ => True\n  post := fun _ ret => ret = .unit\n",
            "def pre (args : List Value) : Prop := True\n\ninstance : ItemSpec \"demo::main\" where\n  pre := pre\n  post := post\n",
            "def spec : Claim := { pre := fun _ => True, post := fun _ _ => True }\n",
            "def pre : List Value → Memory → Prop := (fun _ => fun _ => True)\n",
            "-- def pre (args : List Value) : Prop := args.length = 1\ndef pre (args : List Value) : Prop := True\n",
            "/- def pre (args : List Value) : Prop := args.length = 1 -/\n",
            "def post (args : List Value) (ret : Value) : Prop := ret = .unit\n",
            "def preamble (args : List Value) : Prop := args.length = 1\n",
            "",
        ] {
            assert_eq!(audit("demo::main", clean), vec![], "{clean:?}");
        }

        use EntryPointRequiresKind::{AuthoredLeanPre, MalformedSource};
        assert_eq!(
            audit(
                "demo::main",
                "import Trusted\n\ndef pre (args : List Value) : Prop :=\n  args = [Value.scalar ⟨1, 1⟩]\n\ndef post (args : List Value) (ret : Value) : Prop := True\n"
            ),
            vec![(3, AuthoredLeanPre)]
        );
        assert_eq!(
            audit(
                "fw::_start",
                "instance : ItemSpec \"fw::_start\" where\n  pre := fun args => args.length = 1\n  post := fun _ _ => True\n"
            ),
            vec![(2, AuthoredLeanPre)]
        );
        // Strengthening the default is a non-trivial precondition.
        assert_eq!(
            audit(
                "demo::main",
                "def pre (args : List Value) : Prop :=\n  Obligations.Demo.main.defaultPre args ∧ args.length = 1\n"
            ),
            vec![(1, AuthoredLeanPre)]
        );
        assert_eq!(
            audit(
                "demo::main",
                "def pre (args : List Value) : Prop := False\n"
            ),
            vec![(1, AuthoredLeanPre)]
        );
        // `abbrev pre`, `opaque pre`, dotted `MainSpec.pre`, and equation-compiler
        // `def pre` with `|` arms (followed by `def post := True`) must all fire.
        assert_eq!(
            audit(
                "demo::main",
                "abbrev pre (args : List Value) : Prop := args.length = 1\n"
            ),
            vec![(1, AuthoredLeanPre)]
        );
        assert_eq!(
            audit(
                "demo::main",
                "opaque pre : List Value → Prop\ndef post (args : List Value) (ret : Value) : Prop := True\n"
            ),
            vec![(1, AuthoredLeanPre)]
        );
        assert_eq!(
            audit(
                "demo::main",
                "def MainSpec.pre (args : List Value) : Prop := args.length = 1\n"
            ),
            vec![(1, AuthoredLeanPre)]
        );
        assert_eq!(
            audit(
                "demo::main",
                "def pre : List Value → Prop\n  | [Value.scalar ⟨1, 1⟩] => True\n  | _ => False\n\ndef post (args : List Value) (ret : Value) : Prop := True\n"
            ),
            vec![(1, AuthoredLeanPre)]
        );
        // A string that merely spells `True` is not the proposition `True`.
        assert_eq!(
            audit(
                "demo::main",
                "def pre (args : List Value) : Prop := args = \"True\"\n"
            ),
            vec![(1, AuthoredLeanPre)]
        );
        assert_eq!(
            audit(
                "demo::main",
                "/- unclosed\ndef pre (args : List Value) : Prop := True\n"
            ),
            vec![(1, MalformedSource)]
        );
        // Non-entry items are exempt.
        assert_eq!(
            audit(
                "demo::helper",
                "def pre (args : List Value) : Prop := args.length = 1\n"
            ),
            vec![]
        );
        assert_eq!(
            audit_lean_spec_entry_point_requires(
                "fw::reset",
                "Specs/Fw/reset.lean",
                "def pre (args : List Value) : Prop := args.length = 1\n",
                &["fw::reset"],
            )
            .len(),
            1
        );
    }

    #[test]
    fn lean_entry_point_audit_inspects_every_specification_value_shape() {
        use EntryPointRequiresKind::AuthoredLeanPre;
        let audit = |text: &str| {
            audit_lean_spec_entry_point_requires("demo::main", "Specs/Demo/main.lean", text, &[])
                .into_iter()
                .map(|d| (d.line, d.kind))
                .collect::<Vec<_>>()
        };
        // Shapes whose precondition is trivial or the generated default.
        for clean in [
            "instance : ItemSpec \"demo::main\" := Obligations.Demo.main.defaultSpec\n",
            "instance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec (fun _ => True) (fun _ ret => ret = .unit)\n",
            "def extraPre (args : List Value) : Prop := True\ndef extraPost (args : List Value) (ret : Value) : Prop := ret = .unit\n\ninstance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec extraPre extraPost\n",
            "def envAssumed (h : ExternalCallHandler) : Prop := h = h0\n\ninstance : ModularItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineModularSpec envAssumed (fun _ _ => True) (fun _ _ ret _ => ret = .unit)\n",
            "instance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSafeSpec (fun _ => True) (fun args => args.length = 1) (fun _ _ => True)\n",
            "instance (priority := high) : ItemSpec \"demo::main\" where\n  pre args := True\n  post args ret := ret = .unit\n",
            "instance : ItemSpec \"demo::main\" := { pre := fun _ => True, post := fun _ _ => True }\n",
            "instance : ItemSpec \"demo::main\" :=\n  { Obligations.Demo.main.defaultSpec with post := fun _ ret => ret = .unit }\n",
            "def mainSpec : ItemSpec \"demo::main\" where\n  pre _ := True\n  post _ ret := ret = .unit\n\ninstance : ItemSpec \"demo::main\" := mainSpec\n",
            // Not specification values.
            "instance : Inhabited Marker := ⟨Marker.mk⟩\ndef helper pre x := pre x\n",
            "def bound : Nat := 4\ntheorem bound_pos : 0 < bound := by decide\n",
        ] {
            assert_eq!(audit(clean), vec![], "{clean:?}");
        }
        // The documented `refineSpec extraPre extraPost` route conjoins
        // `extraPre` onto the entry point's precondition.
        for (flagged, line) in [
            (
                "instance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec (fun args => args.length = 1) (fun _ _ => True)\n",
                1,
            ),
            (
                "def extraPre (args : List Value) : Prop := args.length = 1\ndef extraPost (args : List Value) (ret : Value) : Prop := True\n\ninstance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec extraPre extraPost\n",
                4,
            ),
            // `extraPre` defined elsewhere, by equations, or not at all.
            (
                "instance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec extraPre extraPost\n",
                1,
            ),
            (
                "def extraPre : List Value → Prop\n  | [] => True\n  | _ => False\n\ninstance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec extraPre (fun _ _ => True)\n",
                5,
            ),
            (
                "instance : StatefulItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineStatefulSpec (fun args m => args.length = 1) (fun _ _ _ _ => True)\n",
                1,
            ),
            // The `pre` argument is the second one of these constructors.
            (
                "instance : ModularItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineModularSpec (fun _ => True) (fun args _ => args.length = 1) (fun _ _ _ _ => True)\n",
                1,
            ),
            (
                "instance : UbExceptionItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineUbExceptionSpec (fun _ _ => True) (fun args _ => args = []) (fun _ _ _ _ => True)\n",
                1,
            ),
            // `safetyDomain` is the precondition of a safe specification.
            (
                "instance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSafeSpec (fun args => args.length = 1) (fun _ => True) (fun _ _ => True)\n",
                1,
            ),
            // Partial application, operators, and unknown constructors.
            (
                "instance : ItemSpec \"demo::main\" := Obligations.Demo.main.refineSpec\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec <| fun args => args.length = 1\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" := Obligations.Demo.main.refineFancySpec (fun _ => True)\n",
                1,
            ),
            // Positional constructors cannot be inspected: fail closed.
            (
                "instance : ItemSpec \"demo::main\" := ⟨fun args => args.length = 1, fun _ _ => True⟩\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" := ItemSpec.mk (fun args => args.length = 1) (fun _ _ => True)\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" := by\n  exact ⟨fun args => args.length = 1, fun _ _ => True⟩\n",
                1,
            ),
            (
                "def mainSpec : ItemSpec \"demo::main\" := ⟨fun args => args.length = 1, fun _ _ => True⟩\n\ninstance : ItemSpec \"demo::main\" := mainSpec\n",
                1,
            ),
            // A value or a `pre` that this module does not define.
            ("instance : ItemSpec \"demo::main\" := importedSpec\n", 1),
            (
                "instance : ItemSpec \"demo::main\" := { importedSpec with post := fun _ _ => True }\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" where\n  pre := pre\n  post := post\n",
                2,
            ),
            // Structure fields with binders.
            (
                "instance : ItemSpec \"demo::main\" where\n  pre args := args.length = 1\n  post args ret := True\n",
                2,
            ),
            (
                "instance : StatefulItemSpec \"demo::main\" where\n  pre args m := m.valid ∧ args = []\n  post _ _ _ _ := True\n",
                2,
            ),
            (
                "instance : ItemSpec \"demo::main\" := { pre args := args.length = 1, post _ _ := True }\n",
                1,
            ),
            // Typed binders, field type annotations, equation-compiler `where`
            // fields, and un-audited structure field puns.
            (
                "instance : ItemSpec \"demo::main\" where\n  pre (args : List Value) := args.length = 1\n  post _ _ := True\n",
                2,
            ),
            (
                "instance : ItemSpec \"demo::main\" where\n  pre : List Value → Prop := fun args => args.length = 1\n  post _ _ := True\n",
                2,
            ),
            (
                "instance : ItemSpec \"demo::main\" := { Obligations.Demo.main.defaultSpec with\n  pre (args : List Value) := args.length = 1\n}\n",
                2,
            ),
            (
                "instance : ItemSpec \"demo::main\" where\n  pre\n    | [Value.scalar ⟨1, 1⟩] => True\n    | _ => False\n  post _ _ := True\n",
                2,
            ),
            (
                "instance : ItemSpec \"demo::main\" := { pre, post := fun _ _ => True }\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" := { Obligations.Demo.main.defaultSpec with pre }\n",
                1,
            ),
        ] {
            assert_eq!(audit(flagged), vec![(line, AuthoredLeanPre)], "{flagged:?}");
        }
        // Trivial `pre` with Unicode `λ`, typed binders, equation-compiler
        // `where` field, or followed by a typed `post` field must stay clean.
        for clean in [
            "instance : ItemSpec \"demo::main\" where\n  pre := λ _ => True\n  post (args : List Value) (ret : Value) := ret = Value.unit\n",
            "instance : ItemSpec \"demo::main\" where\n  pre (args : List Value) := True\n  post (args : List Value) (ret : Value) := ret = Value.unit\n",
            "instance : ItemSpec \"demo::main\" where\n  pre : List Value → Prop := λ args => Obligations.Demo.main.defaultPre args\n  post (args : List Value) (ret : Value) := True\n",
            "instance : ItemSpec \"demo::main\" where\n  pre\n    | _ => True\n  post (args : List Value) (ret : Value) := ret = Value.unit\n",
        ] {
            assert_eq!(audit(clean), vec![], "{clean:?}");
        }
    }

    /// The `Specs/<Item>.lean` starter modules rendered by
    /// `obligations::render_specs_template` delegate to the generated
    /// defaults and must pass the audit unchanged.
    #[test]
    fn lean_entry_point_audit_accepts_the_generated_specs_templates() {
        use EntryPointRequiresKind::AuthoredLeanPre;
        let audit = |text: &str| {
            audit_lean_spec_entry_point_requires("demo::main", "Specs/Demo/main.lean", text, &[])
                .into_iter()
                .map(|d| (d.line, d.kind))
                .collect::<Vec<_>>()
        };
        let plain = "\
import Trusted
import Mir.Demo.main
import Obligations.Demo.main

namespace Specs.Demo.main

set_option linter.unusedVariables false

open Trusted.MirSemantics
open Trusted.VerificationResult

/-!
Durable specification override module for `demo::main`.

To strengthen the contract while preserving Rust `#[spec]` companions,
use `Obligations.Demo.main.refineSpec` (or `refineStatefulSpec`) or
conjoin `Obligations.Demo.main.rustRequires` and
`Obligations.Demo.main.rustEnsures` directly.
-/

/-- Precondition over the incoming argument list `args`. -/
def pre (args : List Value) : Prop :=
  Obligations.Demo.main.defaultPre args

/-- Postcondition relating the incoming argument list `args` and return
    value `ret`. -/
def post (args : List Value) (ret : Value) : Prop :=
  Obligations.Demo.main.defaultPost args ret

/-- Normal-priority `ItemSpec` instance overriding
    `Obligations.Demo.main.defaultSpec`.
    Alternatively, define `instance : ItemSpec \"demo::main\" :=
    Obligations.Demo.main.refineSpec extraPre extraPost`. -/
instance : ItemSpec \"demo::main\" where
  pre := pre
  post := post

end Specs.Demo.main
";
        assert_eq!(audit(plain), vec![]);
        let modular = "\
namespace Specs.Demo.main

/-- Assumed external call-handler environment contract. -/
def envAssumed (h : ExternalCallHandler) : Prop :=
  Obligations.Demo.main.defaultModularSpec.envAssumed h

/-- Precondition over the incoming argument list `args` and initial `mem`. -/
def pre (args : List Value) (mem : Memory) : Prop :=
  Obligations.Demo.main.defaultModularSpec.pre args mem

/-- Postcondition relating `(args, mem)` to `(ret, mem')`. -/
def post (args : List Value) (mem : Memory) (ret : Value) (mem' : Memory) : Prop :=
  Obligations.Demo.main.defaultModularSpec.post args mem ret mem'

instance : ModularItemSpec \"demo::main\" where
  envAssumed := envAssumed
  pre := pre
  post := post

end Specs.Demo.main
";
        assert_eq!(audit(modular), vec![]);
        // Editing the template's `pre`, or switching to the documented
        // `refineSpec` alternative with a real `extraPre`, is reported.
        let edited = plain.replace(
            "  Obligations.Demo.main.defaultPre args\n",
            "  Obligations.Demo.main.defaultPre args ∧ args.length = 1\n",
        );
        assert_eq!(audit(&edited), vec![(22, AuthoredLeanPre)]);
        let refined = plain.replace(
            "instance : ItemSpec \"demo::main\" where\n  pre := pre\n  post := post\n",
            "def extraPre (args : List Value) : Prop := args.length = 1\n\ninstance : ItemSpec \"demo::main\" :=\n  Obligations.Demo.main.refineSpec extraPre post\n",
        );
        assert_eq!(audit(&refined), vec![(36, AuthoredLeanPre)]);
    }

    #[test]
    fn lean_entry_point_audit_closes_spread_quote_and_foreign_item_routes() {
        let audit_as = |label: &str, text: &str| {
            audit_lean_spec_entry_point_requires("demo::main", label, text, &[])
                .into_iter()
                .map(|d| d.line)
                .collect::<Vec<_>>()
        };
        let audit = |text: &str| audit_as("Specs/Demo/main.lean", text);
        for (flagged, line) in [
            // A spread or parent field supplies `pre` from a base value.
            (
                "instance : ItemSpec \"demo::main\" where\n  __ := importedSpec\n  post := post\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" where\n  toItemSpecBase := importedBase\n  post := post\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" := { __ := importedSpec, post := fun _ _ => True }\n",
                1,
            ),
            (
                "def base : ItemSpec \"demo::main\" := ⟨fun a => a = [], fun _ _ => True⟩\ninstance : ItemSpec \"demo::main\" where\n  __ := base\n",
                1,
            ),
            // `«pre»` is the identifier `pre`.
            (
                "def «pre» (args : List Value) : Prop := args.length = 1\n",
                1,
            ),
            (
                "instance : ItemSpec \"demo::main\" where\n  «pre» := fun args => args.length = 1\n  post := post\n",
                2,
            ),
            // Another item's generated precondition is not this entry point's.
            (
                "def pre (args : List Value) : Prop :=\n  Obligations.Other.helper.defaultPre args\n",
                2,
            ),
            (
                "def pre (args : List Value) : Prop := Obligations.Other.helper.rustRequires args\n",
                1,
            ),
            (
                "def pre (args : List Value) (m : Memory) : Prop :=\n  Obligations.Demo.helper.defaultModularSpec.pre args m\n",
                2,
            ),
            // An instance attribute on a value this module does not declare.
            ("attribute [instance] importedSpec\n", 1),
            ("attribute [local instance, simp] importedSpec\n", 1),
        ] {
            assert_eq!(audit(flagged), vec![line], "{flagged:?}");
        }
        for clean in [
            "instance : ItemSpec \"demo::main\" where\n  __ := Obligations.Demo.main.defaultSpec\n  post := fun _ ret => ret = .unit\n",
            "def base : ItemSpec \"demo::main\" := Obligations.Demo.main.defaultSpec\ninstance : ItemSpec \"demo::main\" := { __ := base, post := fun _ _ => True }\n",
            "def mainSpec : ItemSpec \"demo::main\" where\n  pre _ := True\n  post _ _ := True\nattribute [instance] mainSpec\n",
            "instance : ItemSpec \"demo::main\" where\n  pre := fun _ ↦ True\n  post := post\n",
            "def «pre» (args : List Value) : Prop := True\n",
            "import Obligations.Other.helper\nopen Obligations.Other.helper in\ndef pre (args : List Value) : Prop := Obligations.Demo.main.defaultPre args\n",
            "def post (args : List Value) (ret : Value) : Prop := Obligations.Other.helper.rustEnsures args ret\n",
            "attribute [simp] importedLemma\n",
        ] {
            assert_eq!(audit(clean), vec![], "{clean:?}");
        }
        // The module's item comes from its path or its `namespace Specs.…`.
        let foreign = "def pre (args : List Value) : Prop := Obligations.Other.helper.defaultPre args\n";
        assert_eq!(audit_as("main.lean", foreign), vec![]);
        let namespaced = format!("namespace Specs.Demo.main\n{foreign}end Specs.Demo.main\n");
        assert_eq!(audit_as("main.lean", &namespaced), vec![2]);
        assert_eq!(
            lean_spec_module_item_paths("proofs/Specs/Demo/main.lean", &[]),
            vec![String::from("Demo.main")]
        );
    }

    #[test]
    fn entry_point_requires_bundle_combines_mir_and_lean_findings() {
        let subject = guard_test_mir("demo::main", IrContractRole::Subject, copy_arg_operand());
        let requires = guard_test_mir(
            "demo::__anodized_fn_requires_main",
            IrContractRole::Requires(String::from("demo::main")),
            copy_arg_operand(),
        );
        let specs = (
            "Specs/Demo/main.lean",
            "def pre (args : List Value) : Prop := args.length = 1\n",
        );
        let diagnostics = audit_entry_point_requires_bundle(
            &subject,
            std::slice::from_ref(&requires),
            Some(specs),
            &[],
        );
        assert_eq!(
            diagnostics.iter().map(|d| d.kind).collect::<Vec<_>>(),
            vec![
                EntryPointRequiresKind::MirRequiresCompanion,
                EntryPointRequiresKind::AuthoredLeanPre
            ]
        );
        assert_eq!(
            EntryPointRequiresDiagnostic::GUARD,
            SpecBoundaryGuardId::EntryPointRequires
        );
        assert_eq!(
            audit_entry_point_requires_bundle(&subject, &[], None, &[]),
            vec![]
        );
    }

    // ---- Unified audit ------------------------------------------------------

    #[test]
    fn unified_spec_boundary_audit_reports_all_three_guards_deterministically() {
        let mir_items = [
            guard_test_mir("demo::main", IrContractRole::Subject, copy_arg_operand()),
            guard_test_mir(
                "demo::__anodized_fn_requires_main",
                IrContractRole::Requires(String::from("demo::main")),
                copy_arg_operand(),
            ),
            guard_test_mir("demo::helper", IrContractRole::Subject, copy_arg_operand()),
            guard_test_mir(
                "demo::__anodized_fn_requires_helper",
                IrContractRole::Requires(String::from("demo::helper")),
                copy_arg_operand(),
            ),
        ];
        let spec_sources = [
            SpecBoundarySource {
                label: "Specs/Demo/ghost.lean",
                text: "axiom GhostList.len : GhostList α → UInt64\n",
            },
            SpecBoundarySource {
                label: "src/lib.rs",
                text: "#[spec(ensures: |out| match out { Ok(v) => *v == 1, Err(_) => true })]\nfn one() -> Result<u32, E> { Ok(1) }\n",
            },
        ];
        let authored_entry_specs = [(
            "demo::main",
            SpecBoundarySource {
                label: "Specs/Demo/main.lean",
                text: "def pre (args : List Value) : Prop := args.length = 1\n\ndef post (args : List Value) : Outcome → Prop\n  | .ok v => v = args.head!\n  | .ub => True\n",
            },
        )];
        let input = SpecBoundaryAuditInput {
            spec_sources: &spec_sources,
            mir_items: &mir_items,
            authored_entry_specs: &authored_entry_specs,
            extra_entry_def_paths: &[],
        };
        let report = audit_spec_boundary_guards(&input);
        assert!(!report.is_clean());
        assert_eq!(report.counts_by_guard(), [2, 1, 2]);
        assert_eq!(
            report.summary_line(),
            "SpecBoundaryGuardAudit(total=5, entry_point_requires=2, \
             fixed_width_ghost_length=1, error_branch_wildcard=2)"
        );
        // Sorted by guard rank, then source label, then line.
        assert_eq!(
            report
                .diagnostics
                .iter()
                .map(|d| (d.guard, d.source_label.as_str(), d.line))
                .collect::<Vec<_>>(),
            vec![
                (
                    SpecBoundaryGuardId::EntryPointRequires,
                    "Specs/Demo/main.lean",
                    1
                ),
                (
                    SpecBoundaryGuardId::EntryPointRequires,
                    "demo::__anodized_fn_requires_main",
                    0
                ),
                (
                    SpecBoundaryGuardId::FixedWidthGhostLength,
                    "Specs/Demo/ghost.lean",
                    1
                ),
                (
                    SpecBoundaryGuardId::ErrorBranchWildcard,
                    "Specs/Demo/main.lean",
                    5
                ),
                (SpecBoundaryGuardId::ErrorBranchWildcard, "src/lib.rs", 1),
            ]
        );
        assert_eq!(report, audit_spec_boundary_guards(&input));
        let rendered = report.render_diagnostic_report();
        assert_eq!(rendered.lines().count(), 6);
        assert!(rendered.starts_with("SpecBoundaryGuardAudit(total=5"));
        for diagnostic in &report.diagnostics {
            assert!(rendered.contains(&diagnostic.to_string()));
            assert!(diagnostic.message.contains(diagnostic.guard.as_str()));
        }

        // A clean bundle produces a clean report.
        let clean_sources = [
            SpecBoundarySource {
                label: "Specs/Demo/ghost.lean",
                text: "axiom GhostList.len : GhostList α → Nat\n",
            },
            SpecBoundarySource {
                label: "src/lib.rs",
                text: "#[spec(ensures: |out| match out { Ok(v) => *v == 1, Err(e) => *e == E::A })]\nfn one() -> Result<u32, E> { Ok(1) }\n",
            },
        ];
        let clean_specs = [(
            "demo::main",
            SpecBoundarySource {
                label: "Specs/Demo/main.lean",
                text: "def pre (args : List Value) : Prop := True\n",
            },
        )];
        let clean = audit_spec_boundary_guards(&SpecBoundaryAuditInput {
            spec_sources: &clean_sources,
            mir_items: &mir_items[2..],
            authored_entry_specs: &clean_specs,
            extra_entry_def_paths: &[],
        });
        assert!(clean.is_clean(), "{clean:?}");
        assert_eq!(clean.counts_by_guard(), [0, 0, 0]);
        assert_eq!(
            clean.summary_line(),
            "SpecBoundaryGuardAudit(total=0, entry_point_requires=0, \
             fixed_width_ghost_length=0, error_branch_wildcard=0)"
        );
        assert!(audit_spec_boundary_guards(&SpecBoundaryAuditInput::default()).is_clean());

        // Orphan `Requires` companion targeting a binary entry point fires
        // even when the subject MIR item is omitted from `mir_items`.
        let orphan_only = [guard_test_mir(
            "demo::__anodized_fn_requires_main",
            IrContractRole::Requires(String::from("demo::main")),
            copy_arg_operand(),
        )];
        let orphan_report = audit_spec_boundary_guards(&SpecBoundaryAuditInput {
            mir_items: &orphan_only,
            ..SpecBoundaryAuditInput::default()
        });
        assert_eq!(orphan_report.counts_by_guard(), [1, 0, 0]);
        assert_eq!(
            orphan_report.diagnostics[0].source_label,
            "demo::__anodized_fn_requires_main"
        );
    }
}
