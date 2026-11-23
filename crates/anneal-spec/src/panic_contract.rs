// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `#![no_std]` dynamic panic-contract checker, guard mutant-kill harness, and
//! `kani#5095` call-boundary non-inlining verifier.
//!
//! This module is the `#![no_std]` (`core`-only, zero-allocation) Rust
//! counterpart to Episode 1's kernel-verified Lean 4 `Anneal.PanicContracts`
//! library (`theory/Anneal/PanicContracts.lean`) and complements
//! [`crate::spec_check`]:
//!
//! 1. **Explicit [`AbortPolicy`] (No Boolean `allows_abort` Footgun)**:
//!    Mirrors Lean's `Anneal.PanicContracts.AbortPolicy` (`forbidAbort`,
//!    `abortOnlyIf`, `waiveAbortUnchecked`). Unconditional abort waivers must
//!    be requested by name and are rejected in [`PanicContractMode::Exact`]
//!    mode ([`PanicFailureClass::WaiveAbortIncompatibleWithExactContract`]).
//! 2. **Typed Panic-Contract Modes & Builders**:
//!    Supports [`PanicContractMode::OnlyIf`] (`PanicsOnlyIf`),
//!    [`PanicContractMode::If`] (`PanicsIf`), [`PanicContractMode::Exact`]
//!    (`ExactPanicContract`), and [`PanicContractMode::NeverPanics`]
//!    (`NeverPanics`), plus generic [`PanicContractSpec`] and
//!    [`StatefulPanicContractSpec`] builders compatible with both standalone
//!    closures and `anneal-spec` macro companions (`__anodized_fn_requires_*`,
//!    `__anodized_fn_ensures_*`).
//! 3. **Multi-Stage Dynamic Checker & Mutant-Kill Harnesses**:
//!    - Universal UB-freedom: [`PanicExecOutcome::UbOrFault`] fails immediately
//!      on *every* precondition-admissible input, including inputs where
//!      `panic_cond` or `abort_cond` holds.
//!    - Strict domain safety: `panic_cond` and `abort_cond` are evaluated only
//!      when `pre(input)` returned `true`; `post` is evaluated only on
//!      non-panicking, non-aborting `pre`-admissible inputs (unless
//!      [`ProbeDomain::Unconstrained`] is explicitly requested for Stage P3a
//!      classification probes, and even then never with uninitialized outputs).
//!    - Stateful `&mut S` checking with optional `panic_state_inv` verifying
//!      `(initial_state, panicked_post_state)` to catch pre-panic `&mut` state
//!      corruption hazards (`kani#4230`).
//!    - **Stage P3a**: Normal-branch output-mutant dichotomy via
//!      [`ReturnMutants`] with stack deduplication and [`KILL_FREE_OVERSCAN`].
//!    - **Stage P3b**: Behavioral & panic-guard mutant-kill harnesses
//!      ([`check_panic_guard_mutants`], [`check_stateful_panic_guard_mutants`])
//!      confirming mutated implementations (dropped `assert!`, off-by-one guard,
//!      unexpected panic, wrong return value) are rejected by the contract.
//!    - Deterministic counterexample replay ([`replay_panic_trial_input`],
//!      [`replay_stateful_panic_trial_input`]).
//! 4. **Zero-`std`-Feature Unwind Macros**:
//!    `crates/anneal-spec` defines no `std` Cargo feature. All library code
//!    outside `#[cfg(test)]` is strictly `core`-only, while `#[macro_export]`
//!    macros (`panic_unwind_runner!`, `stateful_panic_unwind_runner!`,
//!    `check_panic_contract_unwind!`, `check_stateful_panic_contract_unwind!`,
//!    `assert_panic_contract_strong_unwind!`,
//!    `assert_stateful_panic_contract_strong_unwind!`,
//!    `panic_guard_mutant_unwind!`, `stateful_panic_guard_mutant_unwind!`)
//!    expand `::std::panic::catch_unwind` cleanly at caller `#[test]` sites.
//! 5. **`kani#5095` Call-Boundary Non-Inlining Guard & Verifiers**:
//!    - `const fn` [`CallBoundaryGuard`] descriptor and `#[inline(never)]` +
//!      [`core::hint::black_box`] dynamic boundary wrappers
//!      ([`invoke_boundary_guarded`], [`invoke_stateful_boundary_guarded`]).
//!    - Pure-`core` Rust lexical/attribute scanner
//!      ([`verify_fn_inline_never_source`],
//!      [`verify_fn_inline_never_source_with_options`]) verifying explicit
//!      `#[inline(never)]` on target functions without being fooled by comments,
//!      raw/byte/C strings, char literals, lifetimes, inner attributes, or
//!      macro bodies.
//!    - Pure-`core` stack-allocated MIR CFG & multi-hop call-chain verifiers
//!      mirroring `Anneal.PanicContracts` §6–§7
//!      ([`verify_callee_table_excludes`], [`verify_traits_preserved`],
//!      [`verify_call_boundary`], [`verify_counted_call_sites`],
//!      [`verify_reachable_call_boundary`], [`verify_reachable_call_sites`],
//!      [`verify_call_chain_boundary`]).

use core::array;
use core::fmt;
use core::hint::black_box;

use crate::spec_check::{
    KILL_FREE_OVERSCAN, MAX_PROBE_INPUTS, ProbeDomain, ReturnMutants, SampleInput,
    SpecCheckConfig, SplitMix64, SyntacticBindingHint, VacuityClass,
};

// ===========================================================================
// 1. AbortPolicy, Execution Outcomes & Contract Modes
// ===========================================================================

/// Tag-only classification of an [`AbortPolicy`], matching Lean's
/// `Anneal.PanicContracts.AbortPolicy` constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbortPolicyKind {
    /// No execution may abort (`Anneal.PanicContracts.AbortPolicy.forbidAbort`).
    ForbidAbort,
    /// Execution may abort only when an explicit abort condition holds
    /// (`Anneal.PanicContracts.AbortPolicy.abortOnlyIf`).
    AbortOnlyIf,
    /// Unconditional opt-in waiver accepting any abort
    /// (`Anneal.PanicContracts.AbortPolicy.waiveAbortUnchecked`).
    WaiveAbortUnchecked,
}

impl AbortPolicyKind {
    /// All three policy kinds in Lean declaration order.
    pub const ALL: [Self; 3] = [
        Self::ForbidAbort,
        Self::AbortOnlyIf,
        Self::WaiveAbortUnchecked,
    ];

    /// Returns the canonical cross-language identifier matching Lean's
    /// `Anneal.PanicContracts.AbortPolicy` constructor name.
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::ForbidAbort => "forbidAbort",
            Self::AbortOnlyIf => "abortOnlyIf",
            Self::WaiveAbortUnchecked => "waiveAbortUnchecked",
        }
    }

    /// Parses a canonical cross-language identifier back into its policy kind.
    /// Matching is exact and case-sensitive.
    pub fn from_canonical_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|kind| kind.canonical_name() == name)
    }
}

impl fmt::Display for AbortPolicyKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.canonical_name())
    }
}

/// Predicate-carrying abort policy mirroring Lean's
/// `Anneal.PanicContracts.AbortPolicy`.
///
/// There is intentionally no boolean `allows_abort` flag: an unconditional
/// waiver must be requested explicitly via [`Self::WaiveAbortUnchecked`], and
/// a `-C panic=abort` contract states its abort predicate via
/// [`Self::AbortOnlyIf`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbortPolicy<AbortCond> {
    /// Reject every [`PanicExecOutcome::Aborted`].
    ForbidAbort,
    /// Permit [`PanicExecOutcome::Aborted`] only when `AbortCond` holds (and
    /// require `Aborted` in [`PanicContractMode::Exact`] and
    /// [`PanicContractMode::If`] modes).
    AbortOnlyIf(AbortCond),
    /// Unconditionally accept [`PanicExecOutcome::Aborted`]. Explicitly
    /// rejected in [`PanicContractMode::Exact`] mode.
    WaiveAbortUnchecked,
}

impl<AbortCond> AbortPolicy<AbortCond> {
    /// Returns the predicate-free [`AbortPolicyKind`] tag.
    pub const fn kind(&self) -> AbortPolicyKind {
        match self {
            Self::ForbidAbort => AbortPolicyKind::ForbidAbort,
            Self::AbortOnlyIf(_) => AbortPolicyKind::AbortOnlyIf,
            Self::WaiveAbortUnchecked => AbortPolicyKind::WaiveAbortUnchecked,
        }
    }

    /// Returns `true` iff this policy is [`Self::ForbidAbort`].
    pub const fn is_forbid(&self) -> bool {
        matches!(self, Self::ForbidAbort)
    }

    /// Returns `true` iff this policy is [`Self::AbortOnlyIf`].
    pub const fn is_abort_only_if(&self) -> bool {
        matches!(self, Self::AbortOnlyIf(_))
    }

    /// Returns `true` iff this policy is [`Self::WaiveAbortUnchecked`].
    pub const fn is_waived(&self) -> bool {
        matches!(self, Self::WaiveAbortUnchecked)
    }

    /// Transforms the carried abort predicate, leaving `ForbidAbort` and
    /// `WaiveAbortUnchecked` unchanged.
    pub fn map_cond<F, AbortCond2>(self, f: F) -> AbortPolicy<AbortCond2>
    where
        F: FnOnce(AbortCond) -> AbortCond2,
    {
        match self {
            Self::ForbidAbort => AbortPolicy::ForbidAbort,
            Self::AbortOnlyIf(cond) => AbortPolicy::AbortOnlyIf(f(cond)),
            Self::WaiveAbortUnchecked => AbortPolicy::WaiveAbortUnchecked,
        }
    }
}

/// Constructs [`AbortPolicy::ForbidAbort`] with a concrete infallible stateless
/// predicate type so callers need no turbofish annotations.
pub const fn forbid_abort<I>() -> AbortPolicy<fn(&I) -> bool> {
    AbortPolicy::ForbidAbort
}

/// Constructs [`AbortPolicy::WaiveAbortUnchecked`] with a concrete infallible
/// stateless predicate type.
pub const fn waive_abort_unchecked<I>() -> AbortPolicy<fn(&I) -> bool> {
    AbortPolicy::WaiveAbortUnchecked
}

/// Constructs [`AbortPolicy::ForbidAbort`] with a concrete fallible stateless
/// predicate type.
pub const fn forbid_abort_fallible<I>() -> AbortPolicy<fn(&I) -> Result<bool, ()>> {
    AbortPolicy::ForbidAbort
}

/// Constructs [`AbortPolicy::WaiveAbortUnchecked`] with a concrete fallible
/// stateless predicate type.
pub const fn waive_abort_unchecked_fallible<I>() -> AbortPolicy<fn(&I) -> Result<bool, ()>> {
    AbortPolicy::WaiveAbortUnchecked
}

/// Constructs [`AbortPolicy::ForbidAbort`] with a concrete infallible stateful
/// predicate type.
pub const fn forbid_stateful_abort<S, A>() -> AbortPolicy<fn(&S, &A) -> bool> {
    AbortPolicy::ForbidAbort
}

/// Constructs [`AbortPolicy::WaiveAbortUnchecked`] with a concrete infallible
/// stateful predicate type.
pub const fn waive_stateful_abort_unchecked<S, A>() -> AbortPolicy<fn(&S, &A) -> bool> {
    AbortPolicy::WaiveAbortUnchecked
}

/// Constructs [`AbortPolicy::ForbidAbort`] with a concrete fallible stateful
/// predicate type.
pub const fn forbid_stateful_abort_fallible<S, A>() -> AbortPolicy<fn(&S, &A) -> Result<bool, ()>> {
    AbortPolicy::ForbidAbort
}

/// Constructs [`AbortPolicy::WaiveAbortUnchecked`] with a concrete fallible
/// stateful predicate type.
pub const fn waive_stateful_abort_unchecked_fallible<S, A>()
-> AbortPolicy<fn(&S, &A) -> Result<bool, ()>> {
    AbortPolicy::WaiveAbortUnchecked
}

/// Observable execution outcome of a single trial under panic-contract
/// checking, mirroring Lean's `Outcome Val` plus fault/UB failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PanicExecOutcome<R> {
    /// Execution returned normally with `R`.
    Returned(R),
    /// Execution unwound via a Rust panic (`Outcome.panic`).
    Panicked,
    /// Execution terminated via a defined abort (`Outcome.abort`).
    Aborted,
    /// Execution exhibited undefined behavior or an engine/machine fault
    /// (`FaultEffect`). Always forbidden on every `pre`-admissible input.
    UbOrFault,
}

impl<R> PanicExecOutcome<R> {
    /// Returns `true` iff this outcome is [`Self::Returned`].
    pub const fn is_returned(&self) -> bool {
        matches!(self, Self::Returned(_))
    }

    /// Returns `true` iff this outcome is [`Self::Panicked`].
    pub const fn is_panicked(&self) -> bool {
        matches!(self, Self::Panicked)
    }

    /// Returns `true` iff this outcome is [`Self::Aborted`].
    pub const fn is_aborted(&self) -> bool {
        matches!(self, Self::Aborted)
    }

    /// Returns `true` iff this outcome is [`Self::UbOrFault`].
    pub const fn is_ub_or_fault(&self) -> bool {
        matches!(self, Self::UbOrFault)
    }

    /// Borrows the normal return value, if any.
    pub const fn returned_ref(&self) -> Option<&R> {
        match self {
            Self::Returned(val) => Some(val),
            Self::Panicked | Self::Aborted | Self::UbOrFault => None,
        }
    }

    /// Extracts the normal return value, if any.
    pub fn into_returned(self) -> Option<R> {
        match self {
            Self::Returned(val) => Some(val),
            Self::Panicked | Self::Aborted | Self::UbOrFault => None,
        }
    }

    /// Maps the normal return value while preserving panic, abort, and UB
    /// outcomes.
    pub fn map<U, F>(self, f: F) -> PanicExecOutcome<U>
    where
        F: FnOnce(R) -> U,
    {
        match self {
            Self::Returned(val) => PanicExecOutcome::Returned(f(val)),
            Self::Panicked => PanicExecOutcome::Panicked,
            Self::Aborted => PanicExecOutcome::Aborted,
            Self::UbOrFault => PanicExecOutcome::UbOrFault,
        }
    }
}

/// Contract discipline enforced by the panic-contract checker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PanicContractMode {
    /// `panics_only_if`: every observed panic implies `panic_cond`, normal
    /// returns satisfy `post`, aborts obey [`AbortPolicy`], and every `pre`
    /// execution is UB-free.
    OnlyIf,
    /// `panics_if`: every `pre && panic_cond` input must panic (and every
    /// `pre && abort_cond` input under [`AbortPolicy::AbortOnlyIf`] must
    /// abort), and every `pre` execution is UB-free. Normal-return `post` is
    /// not enforced in this mode.
    If,
    /// `ExactPanicContract`: combines `OnlyIf` and `If` (`panic_cond` iff
    /// panics, `abort_cond` iff aborts under `AbortOnlyIf`, normal returns on
    /// `pre && !panic_cond && !abort_cond` satisfy `post`, universally UB-free).
    Exact,
    /// `NeverPanics`: `panic_cond` is identically `false`; every panic is
    /// rejected, normal returns satisfy `post`, and every `pre` execution is
    /// UB-free. Bridges cleanly to total/non-panicking `#[spec]` contracts.
    NeverPanics,
}

impl PanicContractMode {
    /// Returns the canonical Lean/Rust identifier for this mode.
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::OnlyIf => "PanicsOnlyIf",
            Self::If => "PanicsIf",
            Self::Exact => "ExactPanicContract",
            Self::NeverPanics => "NeverPanics",
        }
    }
}

impl fmt::Display for PanicContractMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.canonical_name())
    }
}

// ===========================================================================
// 2. Configuration, Diagnostics & Statistics
// ===========================================================================

/// Configuration parameters for dynamic panic-contract checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PanicCheckConfig {
    /// Underlying [`SpecCheckConfig`] controlling PRNG seed, trial budget,
    /// minimum precondition hits, mutant budget, syntactic hints, stateful
    /// dual-axis requirement, and vacuity probe domain.
    pub spec_config: SpecCheckConfig,
    /// Minimum number of `pre && panic_cond` hits required (ignored in
    /// [`PanicContractMode::NeverPanics`]). Defaults to `1`.
    pub min_panic_hits: usize,
    /// Minimum number of `pre && abort_cond` hits required when using
    /// [`AbortPolicy::AbortOnlyIf`] (ignored under `ForbidAbort` and
    /// `WaiveAbortUnchecked`). Defaults to `1`.
    pub min_abort_hits: usize,
    /// Whether [`PanicContractMode::Exact`] requires at least one normal return
    /// (failing with [`PanicFailureClass::DeadNormalBranch`] when `0`).
    /// Defaults to `true`.
    pub require_normal_hits_in_exact: bool,
    /// Whether [`PanicContractMode::OnlyIf`] requires at least one normal
    /// return (failing with [`PanicFailureClass::DeadNormalBranch`] when `0` so
    /// an always-panicking implementation cannot bypass `post`). Defaults to
    /// `true`.
    pub require_normal_hits_in_only_if: bool,
    /// Whether Stage P3a runs normal-branch output-mutant dichotomy checking on
    /// `Returned` trials (in `OnlyIf`, `Exact`, and `NeverPanics` modes).
    /// Defaults to `true`.
    pub check_normal_return_mutants: bool,
}

impl Default for PanicCheckConfig {
    fn default() -> Self {
        Self {
            spec_config: SpecCheckConfig::default(),
            min_panic_hits: 1,
            min_abort_hits: 1,
            require_normal_hits_in_exact: true,
            require_normal_hits_in_only_if: true,
            check_normal_return_mutants: true,
        }
    }
}

impl PanicCheckConfig {
    /// Wraps an existing [`SpecCheckConfig`] with default panic-contract gates.
    pub const fn from_spec_config(spec_config: SpecCheckConfig) -> Self {
        Self {
            spec_config,
            min_panic_hits: 1,
            min_abort_hits: 1,
            require_normal_hits_in_exact: true,
            require_normal_hits_in_only_if: true,
            check_normal_return_mutants: true,
        }
    }

    /// Sets the PRNG seed on the inner [`SpecCheckConfig`].
    pub const fn with_seed(mut self, seed: u64) -> Self {
        self.spec_config = self.spec_config.with_seed(seed);
        self
    }

    /// Sets the maximum number of input trials on the inner [`SpecCheckConfig`].
    pub const fn with_max_trials(mut self, max_trials: usize) -> Self {
        self.spec_config = self.spec_config.with_max_trials(max_trials);
        self
    }

    /// Sets the minimum precondition hits on the inner [`SpecCheckConfig`].
    pub const fn with_min_precondition_hits(mut self, min_precondition_hits: usize) -> Self {
        self.spec_config = self
            .spec_config
            .with_min_precondition_hits(min_precondition_hits);
        self
    }

    /// Sets the per-hit normal-branch output-mutant budget.
    pub const fn with_max_mutants_per_hit(mut self, max_mutants_per_hit: usize) -> Self {
        self.spec_config = self
            .spec_config
            .with_max_mutants_per_hit(max_mutants_per_hit);
        self
    }

    /// Attaches (or clears) a [`SyntacticBindingHint`].
    pub fn with_syntactic_hint(mut self, hint: impl Into<Option<SyntacticBindingHint>>) -> Self {
        self.spec_config = self.spec_config.with_syntactic_hint(hint);
        self
    }

    /// Sets whether stateful checks require independent kills along both `S`
    /// and `R` axes on normal returns.
    pub const fn with_require_both_state_and_return_kills(mut self, require_both: bool) -> Self {
        self.spec_config = self
            .spec_config
            .with_require_both_state_and_return_kills(require_both);
        self
    }

    /// Sets the [`ProbeDomain`] used by Stage P3a vacuity classification.
    pub const fn with_probe_domain(mut self, probe_domain: ProbeDomain) -> Self {
        self.spec_config = self.spec_config.with_probe_domain(probe_domain);
        self
    }

    /// Sets the minimum number of `pre && panic_cond` hits required.
    pub const fn with_min_panic_hits(mut self, min_panic_hits: usize) -> Self {
        self.min_panic_hits = min_panic_hits;
        self
    }

    /// Sets the minimum number of `pre && abort_cond` hits required under
    /// [`AbortPolicy::AbortOnlyIf`].
    pub const fn with_min_abort_hits(mut self, min_abort_hits: usize) -> Self {
        self.min_abort_hits = min_abort_hits;
        self
    }

    /// Sets whether [`PanicContractMode::Exact`] requires at least one normal
    /// return.
    pub const fn with_require_normal_hits_in_exact(mut self, require: bool) -> Self {
        self.require_normal_hits_in_exact = require;
        self
    }

    /// Sets whether [`PanicContractMode::OnlyIf`] requires at least one normal
    /// return.
    pub const fn with_require_normal_hits_in_only_if(mut self, require: bool) -> Self {
        self.require_normal_hits_in_only_if = require;
        self
    }

    /// Enables or disables Stage P3a normal-branch output-mutant checking.
    pub const fn with_check_normal_return_mutants(mut self, check: bool) -> Self {
        self.check_normal_return_mutants = check;
        self
    }
}

/// Structured failure taxonomy for dynamic panic-contract checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PanicFailureClass {
    /// Precondition fell below `min_precondition_hits` (or config was
    /// degenerate on trial/precondition budgets).
    DeadPrecondition,
    /// `pre && panic_cond` fell below `min_panic_hits`.
    DeadPanicCondition,
    /// `pre && abort_cond` (under [`AbortPolicy::AbortOnlyIf`]) fell below
    /// `min_abort_hits`.
    DeadAbortCondition,
    /// Zero normal returns were observed when a non-empty normal branch was
    /// required.
    DeadNormalBranch,
    /// Both `panic_cond(input)` and `abort_cond(input)` held simultaneously on
    /// a `pre`-admissible input in an exact/trigger mode.
    OverlappingPanicAndAbortConditions,
    /// [`AbortPolicy::WaiveAbortUnchecked`] was combined with
    /// [`PanicContractMode::Exact`].
    WaiveAbortIncompatibleWithExactContract,
    /// Execution produced [`PanicExecOutcome::UbOrFault`] on a `pre`-admissible
    /// input (forbidden even when `panic_cond` or `abort_cond` holds).
    UbOrFaultOnExecution,
    /// Execution panicked when not allowed by the contract (or a specification
    /// predicate `pre` / `panic_cond` / `abort_cond` trapped).
    UnexpectedPanic,
    /// Execution aborted when forbidden by [`AbortPolicy`].
    UnexpectedAbort,
    /// An input satisfying `pre && panic_cond` failed to panic in `If` or
    /// `Exact` mode.
    MissedExpectedPanic,
    /// An input satisfying `pre && abort_cond` failed to abort under
    /// [`AbortPolicy::AbortOnlyIf`] in `If` or `Exact` mode.
    MissedExpectedAbort,
    /// Stateful `panic_state_inv(&old_state, &panicked_state)` returned `false`
    /// or trapped after a panicking execution (pre-panic `&mut` state
    /// corruption hazard).
    PanicStateInvariantViolation,
    /// Normal return violated `post` (returned `false` or trapped on live
    /// normal output).
    NormalPostconditionViolation,
    /// Normal-branch `post` accepted every probed `(input, output)` pair.
    TrivialNormalPostcondition,
    /// Normal-branch `post` rejected some probed inputs yet appears independent
    /// of the normal output (or mutated post-state).
    UnboundNormalReturnOutput,
    /// Normal-branch `post` varies with output somewhere (or zero distinct
    /// mutants were tested), yet every tested output mutant survived.
    SurvivedAllNormalMutants,
    /// A behavioral/guard mutant survived the panic contract in Stage P3b (or
    /// an empty guard-mutant slice was provided).
    SurvivedGuardMutant,
}

impl PanicFailureClass {
    /// All 17 failure classes in canonical declaration order.
    pub const ALL: [Self; 17] = [
        Self::DeadPrecondition,
        Self::DeadPanicCondition,
        Self::DeadAbortCondition,
        Self::DeadNormalBranch,
        Self::OverlappingPanicAndAbortConditions,
        Self::WaiveAbortIncompatibleWithExactContract,
        Self::UbOrFaultOnExecution,
        Self::UnexpectedPanic,
        Self::UnexpectedAbort,
        Self::MissedExpectedPanic,
        Self::MissedExpectedAbort,
        Self::PanicStateInvariantViolation,
        Self::NormalPostconditionViolation,
        Self::TrivialNormalPostcondition,
        Self::UnboundNormalReturnOutput,
        Self::SurvivedAllNormalMutants,
        Self::SurvivedGuardMutant,
    ];

    /// Returns the canonical diagnostic identifier for this class.
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::DeadPrecondition => "DeadPrecondition",
            Self::DeadPanicCondition => "DeadPanicCondition",
            Self::DeadAbortCondition => "DeadAbortCondition",
            Self::DeadNormalBranch => "DeadNormalBranch",
            Self::OverlappingPanicAndAbortConditions => "OverlappingPanicAndAbortConditions",
            Self::WaiveAbortIncompatibleWithExactContract => {
                "WaiveAbortIncompatibleWithExactContract"
            }
            Self::UbOrFaultOnExecution => "UbOrFaultOnExecution",
            Self::UnexpectedPanic => "UnexpectedPanic",
            Self::UnexpectedAbort => "UnexpectedAbort",
            Self::MissedExpectedPanic => "MissedExpectedPanic",
            Self::MissedExpectedAbort => "MissedExpectedAbort",
            Self::PanicStateInvariantViolation => "PanicStateInvariantViolation",
            Self::NormalPostconditionViolation => "NormalPostconditionViolation",
            Self::TrivialNormalPostcondition => "TrivialNormalPostcondition",
            Self::UnboundNormalReturnOutput => "UnboundNormalReturnOutput",
            Self::SurvivedAllNormalMutants => "SurvivedAllNormalMutants",
            Self::SurvivedGuardMutant => "SurvivedGuardMutant",
        }
    }

    /// Parses a canonical identifier back into its [`PanicFailureClass`].
    pub fn from_canonical_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|class| class.canonical_name() == name)
    }

    /// Maps this failure class into the frozen 5-class [`VacuityClass`]
    /// taxonomy where applicable, returning `None` for panic-specific
    /// structural or guard-mutant classes.
    pub const fn to_vacuity_class(self) -> Option<VacuityClass> {
        match self {
            Self::DeadPrecondition => Some(VacuityClass::DeadPrecondition),
            Self::UbOrFaultOnExecution
            | Self::UnexpectedPanic
            | Self::UnexpectedAbort
            | Self::MissedExpectedPanic
            | Self::MissedExpectedAbort
            | Self::PanicStateInvariantViolation
            | Self::NormalPostconditionViolation => Some(VacuityClass::SpecViolation),
            Self::TrivialNormalPostcondition => Some(VacuityClass::TrivialPostcondition),
            Self::UnboundNormalReturnOutput => Some(VacuityClass::UnboundReturnOutput),
            Self::SurvivedAllNormalMutants => Some(VacuityClass::SurvivedAllMutants),
            Self::DeadPanicCondition
            | Self::DeadAbortCondition
            | Self::DeadNormalBranch
            | Self::OverlappingPanicAndAbortConditions
            | Self::WaiveAbortIncompatibleWithExactContract
            | Self::SurvivedGuardMutant => None,
        }
    }
}

impl fmt::Display for PanicFailureClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.canonical_name())
    }
}

/// Identifies which specification predicate trapped during a fallible panic
/// contract check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PanicTrapKind {
    /// `pre` trapped (`Err(())`).
    PreconditionPanicked,
    /// `panic_cond` trapped (`Err(())`) on a `pre`-admissible input.
    PanicConditionPanicked,
    /// `abort_cond` trapped (`Err(())`) on a `pre`-admissible input.
    AbortConditionPanicked,
    /// Live `post` trapped (`Err(())`) on an actual normal return.
    PostconditionPanicked,
    /// `panic_state_inv` trapped (`Err(())`) on a panicked post-state.
    PanicStateInvariantPanicked,
}

/// Detailed diagnostic payload carried by [`PanicCheckFailure`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PanicFailureDetail {
    /// Trial-tied violation at `trial_idx` (reproducible via
    /// [`replay_panic_trial_input`] / [`replay_stateful_panic_trial_input`]).
    TrialViolation { trial_idx: usize },
    /// A specification predicate trapped on `trial_idx`.
    PredicateTrapped {
        trial_idx: usize,
        trap: PanicTrapKind,
    },
    /// Fewer hits than required for precondition, panic condition, abort
    /// condition, or normal branch.
    InsufficientHits { required: usize, observed: usize },
    /// Configuration was zero or mutually unsatisfiable (fail-closed).
    DegenerateConfig,
    /// [`AbortPolicy::WaiveAbortUnchecked`] was rejected in `Exact` mode.
    WaiveAbortInExactMode,
    /// Zero distinct normal-branch output mutants were tested on a
    /// non-subsingleton output.
    NoDistinctNormalMutantsTested,
    /// All tested normal-branch output mutants survived; includes Stage P3a
    /// classification probe telemetry.
    AllNormalMutantsSurvived {
        /// Number of inputs probed (anchor + sampled inputs).
        probed_inputs: usize,
        /// Number of probed inputs outside `pre && !panic_cond && !abort_cond`.
        out_of_normal_domain_probes: usize,
        /// Number of sampled probe inputs withheld under
        /// [`ProbeDomain::PreconditionOnly`] (or because `pre`/`panic_cond`/
        /// `abort_cond` trapped).
        skipped_out_of_normal_domain: usize,
        /// Whether `post` rejected any probed `(input, output)` pair.
        saw_any_false: bool,
        /// Whether `post` both accepted and rejected outputs for one input.
        saw_output_sensitivity: bool,
    },
    /// In a stateful contract check, a required non-subsingleton normal-branch
    /// output axis (`S` or `R`) failed to kill any mutant.
    StatefulNormalAxisUnconstrained {
        return_mutants_tested: usize,
        return_mutants_killed: usize,
        state_mutants_tested: usize,
        state_mutants_killed: usize,
    },
    /// Stage P3b was given an empty guard-mutant slice (fail-closed).
    NoGuardMutantsProvided,
    /// Stage P3b behavioral/guard mutant at `mutant_idx` survived the contract.
    GuardMutantSurvived {
        mutant_idx: usize,
        mutant_name: &'static str,
        surviving_stats: PanicCheckStats,
    },
}

/// Execution statistics collected during a dynamic panic-contract check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct PanicCheckStats {
    /// Total input trials sampled.
    pub trials_run: usize,
    /// Trials satisfying `pre`.
    pub precondition_hits: usize,
    /// `pre` trials satisfying `panic_cond`.
    pub panic_cond_hits: usize,
    /// `pre` trials satisfying `abort_cond` (under [`AbortPolicy::AbortOnlyIf`]).
    pub abort_cond_hits: usize,
    /// `pre` trials whose body returned [`PanicExecOutcome::Returned`].
    pub normal_returns: usize,
    /// `pre` trials whose body returned [`PanicExecOutcome::Panicked`].
    pub observed_panics: usize,
    /// `pre` trials whose body returned [`PanicExecOutcome::Aborted`].
    pub observed_aborts: usize,
    /// Panicking stateful trials validated against `panic_state_inv`.
    pub panic_state_inv_checks: usize,
    /// Normal-return trials on which at least one Stage P3a output/state
    /// mutant was killed.
    pub normal_hits_with_kill: usize,
    /// Total distinct Stage P3a normal-branch output/state mutants evaluated.
    pub normal_mutants_tested: usize,
    /// Total Stage P3a normal-branch output/state mutants killed.
    pub normal_mutants_killed: usize,
    /// Subset of `normal_mutants_killed` rejected by a trapping `post`.
    pub normal_mutants_trapped: usize,
    /// Number of Stage P3b behavioral/guard mutants tested.
    pub guard_mutants_tested: usize,
    /// Number of Stage P3b behavioral/guard mutants killed.
    pub guard_mutants_killed: usize,
    /// True iff `R::IS_SUBSINGLETON`.
    pub subsingleton_return: bool,
}

impl PanicCheckStats {
    /// Returns `true` iff at least one normal return ran and every normal
    /// return killed at least one Stage P3a mutant.
    pub const fn is_normal_branch_pointwise_strong(&self) -> bool {
        self.normal_returns > 0 && self.normal_hits_with_kill == self.normal_returns
    }

    /// Number of Stage P3a normal-branch mutants that survived.
    pub const fn normal_mutants_survived(&self) -> usize {
        self.normal_mutants_tested
            .saturating_sub(self.normal_mutants_killed)
    }
}

/// Structured failure report emitted when a panic contract fails.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PanicCheckFailure {
    /// Exact failure class.
    pub class: PanicFailureClass,
    /// Execution statistics accumulated up to failure.
    pub stats: PanicCheckStats,
    /// Specific diagnostic context.
    pub detail: PanicFailureDetail,
}

impl PanicCheckFailure {
    /// Returns the index of the trial that triggered this failure, or `None`
    /// for aggregate/configuration failures.
    ///
    /// Pass the returned index to [`replay_panic_trial_input`] or
    /// [`replay_stateful_panic_trial_input`] with the same [`PanicCheckConfig`]
    /// to reconstruct the exact counterexample input.
    pub const fn counterexample_trial(&self) -> Option<usize> {
        match self.detail {
            PanicFailureDetail::TrialViolation { trial_idx }
            | PanicFailureDetail::PredicateTrapped { trial_idx, .. } => Some(trial_idx),
            _ => None,
        }
    }
}

/// Outcome of a dynamic panic-contract check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PanicCheckOutcome {
    /// Contract satisfied all reachability, UB-freedom, panic/abort/normal
    /// conformance, and mutant-killing gates.
    Strong(PanicCheckStats),
    /// Contract failed with a structured [`PanicCheckFailure`].
    Failed(PanicCheckFailure),
}

impl PanicCheckOutcome {
    /// Returns `true` iff the check passed all gates.
    pub const fn is_strong(&self) -> bool {
        matches!(self, Self::Strong(_))
    }

    /// Returns the failing [`PanicFailureClass`], or `None` when [`Self::Strong`].
    pub const fn failure_class(&self) -> Option<PanicFailureClass> {
        match self {
            Self::Strong(_) => None,
            Self::Failed(failure) => Some(failure.class),
        }
    }

    /// Returns the accumulated [`PanicCheckStats`].
    pub const fn stats(&self) -> PanicCheckStats {
        match self {
            Self::Strong(stats) => *stats,
            Self::Failed(failure) => failure.stats,
        }
    }

    /// Borrows the [`PanicCheckFailure`] when failed.
    pub const fn failure(&self) -> Option<&PanicCheckFailure> {
        match self {
            Self::Strong(_) => None,
            Self::Failed(failure) => Some(failure),
        }
    }

    /// Converts the outcome into a standard `Result`.
    pub const fn into_result(self) -> Result<PanicCheckStats, PanicCheckFailure> {
        match self {
            Self::Strong(stats) => Ok(stats),
            Self::Failed(failure) => Err(failure),
        }
    }
}

// ===========================================================================
// 3. Deterministic Stream Seeding & Trial Replay
// ===========================================================================

const fn min_usize(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

const fn max_usize(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

/// Seeds the independent streams of a stateless panic-contract check so trial
/// inputs never depend on Stage P3a mutant consumption.
const fn panic_stateless_streams(seed: u64) -> (SplitMix64, SplitMix64) {
    let mut rng = SplitMix64::new(seed);
    let mutant_rng = rng.fork();
    (rng, mutant_rng)
}

/// Seeds the independent streams of a stateful panic-contract check.
const fn panic_stateful_streams(seed: u64) -> (SplitMix64, SplitMix64, SplitMix64) {
    let mut rng = SplitMix64::new(seed);
    let ret_mutant_rng = rng.fork();
    let state_mutant_rng = rng.fork();
    (rng, ret_mutant_rng, state_mutant_rng)
}

/// Reconstructs the exact input sampled at `trial_idx` during a stateless
/// panic-contract check under `config`.
///
/// Returns `None` when `trial_idx >= config.spec_config.max_trials`.
pub fn replay_panic_trial_input<I: SampleInput>(
    config: PanicCheckConfig,
    trial_idx: usize,
) -> Option<I> {
    if trial_idx >= config.spec_config.max_trials {
        return None;
    }
    let (mut rng, _) = panic_stateless_streams(config.spec_config.seed);
    for earlier in 0..trial_idx {
        let _ = I::sample_at(earlier, &mut rng);
    }
    Some(I::sample_at(trial_idx, &mut rng))
}

/// Reconstructs the exact `(initial_state, args)` pair sampled at `trial_idx`
/// during a stateful panic-contract check under `config`.
///
/// Returns `None` when `trial_idx >= config.spec_config.max_trials`.
pub fn replay_stateful_panic_trial_input<S: SampleInput, A: SampleInput>(
    config: PanicCheckConfig,
    trial_idx: usize,
) -> Option<(S, A)> {
    if trial_idx >= config.spec_config.max_trials {
        return None;
    }
    let (mut rng, _, _) = panic_stateful_streams(config.spec_config.seed);
    for earlier in 0..trial_idx {
        let _ = <(S, A) as SampleInput>::sample_at(earlier, &mut rng);
    }
    Some(<(S, A) as SampleInput>::sample_at(trial_idx, &mut rng))
}

// ===========================================================================
// 4. Internal Stage P3a Normal-Branch Output-Mutant & Classification Engine
// ===========================================================================

const STAGE_P3_DEDUP_CAP: usize = 24;
const MUTANT_CHAIN_STEPS: usize = 128;
const MIN_PROBE_PRNG_DRAWS: usize = 16;

const fn stage_p3_budget_spent(tested: usize, killed_this_hit: bool, budget: usize) -> bool {
    tested >= budget && (killed_this_hit || tested >= budget.saturating_add(KILL_FREE_OVERSCAN))
}

const fn probe_input_budget(boundary_count: usize, max_trials: usize) -> usize {
    let target = max_usize(
        64,
        max_usize(
            boundary_count.saturating_add(MIN_PROBE_PRNG_DRAWS),
            max_trials / 4,
        ),
    );
    min_usize(max_trials, min_usize(target, MAX_PROBE_INPUTS))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProbeVerdict {
    Accepted,
    Rejected,
    Undefined,
}

const fn probe_verdict(outcome: Result<bool, ()>, admissible: bool) -> ProbeVerdict {
    match outcome {
        Ok(true) => ProbeVerdict::Accepted,
        Ok(false) => ProbeVerdict::Rejected,
        Err(()) => {
            if admissible {
                ProbeVerdict::Rejected
            } else {
                ProbeVerdict::Undefined
            }
        }
    }
}

fn note_verdict(verdict: ProbeVerdict, accepted: &mut bool, rejected: &mut bool) {
    match verdict {
        ProbeVerdict::Accepted => *accepted = true,
        ProbeVerdict::Rejected => *rejected = true,
        ProbeVerdict::Undefined => {}
    }
}

const fn hint_to_panic_class(hint: SyntacticBindingHint) -> PanicFailureClass {
    match hint {
        SyntacticBindingHint::ReturnUnused => PanicFailureClass::UnboundNormalReturnOutput,
        SyntacticBindingHint::SyntacticallyTautological => {
            PanicFailureClass::TrivialNormalPostcondition
        }
    }
}

/// Evaluates normal-domain admissibility for a probe input:
/// - `panic_cond` and `abort_cond` are NEVER called unless `pre` returned `Ok(true)`.
/// - Returns `Some(true)` iff `pre && !panic_cond && !abort_cond`.
/// - Returns `Some(false)` under [`ProbeDomain::Unconstrained`] when outside
///   the normal domain (with well-defined predicate outcomes).
/// - Returns `None` under [`ProbeDomain::PreconditionOnly`] outside the normal
///   domain, or whenever any gating predicate (`pre`, `panic_cond`, `abort_cond`)
///   traps.
fn normal_probe_admission<Pre, PanicCond, AbortCond>(
    domain: ProbeDomain,
    mode: PanicContractMode,
    pre: Pre,
    panic_cond: PanicCond,
    abort_cond: Option<AbortCond>,
) -> Option<bool>
where
    Pre: FnOnce() -> Result<bool, ()>,
    PanicCond: FnOnce() -> Result<bool, ()>,
    AbortCond: FnOnce() -> Result<bool, ()>,
{
    match pre() {
        Ok(true) => {
            let panics = if mode == PanicContractMode::NeverPanics {
                false
            } else {
                match panic_cond() {
                    Ok(b) => b,
                    Err(()) => return None,
                }
            };
            let aborts = match abort_cond {
                Some(f) => match f() {
                    Ok(b) => b,
                    Err(()) => return None,
                },
                None => false,
            };
            if !panics && !aborts {
                Some(true)
            } else {
                match domain {
                    ProbeDomain::PreconditionOnly => None,
                    ProbeDomain::Unconstrained => Some(false),
                }
            }
        }
        Ok(false) => match domain {
            ProbeDomain::PreconditionOnly => None,
            ProbeDomain::Unconstrained => Some(false),
        },
        Err(()) => None,
    }
}

fn record_normal_mutant(stats: &mut PanicCheckStats, outcome: Result<bool, ()>) -> bool {
    stats.normal_mutants_tested += 1;
    match outcome {
        Ok(true) => false,
        Ok(false) => {
            stats.normal_mutants_killed += 1;
            true
        }
        Err(()) => {
            stats.normal_mutants_killed += 1;
            stats.normal_mutants_trapped += 1;
            true
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct NormalProbeEvidence {
    probed_inputs: usize,
    out_of_normal_domain_probes: usize,
    skipped_out_of_normal_domain: usize,
    saw_any_false: bool,
    saw_output_sensitivity: bool,
}

impl NormalProbeEvidence {
    fn record_input(&mut self, admissible: bool, accepted: bool, rejected: bool) {
        self.probed_inputs += 1;
        if !admissible {
            self.out_of_normal_domain_probes += 1;
        }
        if rejected {
            self.saw_any_false = true;
        }
        if accepted && rejected {
            self.saw_output_sensitivity = true;
        }
    }

    fn record_flip(&mut self) {
        self.saw_any_false = true;
        self.saw_output_sensitivity = true;
    }

    const fn class(&self) -> PanicFailureClass {
        if !self.saw_any_false {
            PanicFailureClass::TrivialNormalPostcondition
        } else if !self.saw_output_sensitivity {
            PanicFailureClass::UnboundNormalReturnOutput
        } else {
            PanicFailureClass::SurvivedAllNormalMutants
        }
    }

    const fn detail(&self) -> PanicFailureDetail {
        PanicFailureDetail::AllNormalMutantsSurvived {
            probed_inputs: self.probed_inputs,
            out_of_normal_domain_probes: self.out_of_normal_domain_probes,
            skipped_out_of_normal_domain: self.skipped_out_of_normal_domain,
            saw_any_false: self.saw_any_false,
            saw_output_sensitivity: self.saw_output_sensitivity,
        }
    }
}

fn mutant_chain_finds_flip<T, F>(start: T, rng: &mut SplitMix64, mut flips: F) -> bool
where
    T: ReturnMutants + PartialEq,
    F: FnMut(&T) -> bool,
{
    let mut cur = start;
    let mut seen: [Option<T>; 4] = [None, None, None, None];
    let mut prev_cur: Option<T> = None;

    for _ in 0..MUTANT_CHAIN_STEPS {
        let mut found = false;
        let mut next_cur: Option<T> = None;
        cur.visit_mutants(rng, |cand| {
            if found {
                return;
            }
            if flips(&cand) {
                found = true;
                return;
            }
            if next_cur.is_none()
                && cand != cur
                && prev_cur.as_ref() != Some(&cand)
                && !seen.iter().any(|slot| slot.as_ref() == Some(&cand))
            {
                next_cur = Some(cand);
            }
        });
        if found {
            return true;
        }
        let Some(next) = next_cur else {
            break;
        };
        if let Some(slot) = seen.iter_mut().find(|slot| slot.is_none()) {
            *slot = Some(cur);
        } else {
            prev_cur = Some(cur);
        }
        cur = next;
    }

    false
}

fn observe_normal_outputs_at<I, R, Post>(
    x: &I,
    admissible: bool,
    anchor_ret: &R,
    rng: &mut SplitMix64,
    post: &mut Post,
) -> (bool, bool)
where
    R: ReturnMutants,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    let mut accepted = false;
    let mut rejected = false;

    note_verdict(
        probe_verdict(post(x, anchor_ret), admissible),
        &mut accepted,
        &mut rejected,
    );

    if !(accepted && rejected) {
        anchor_ret.visit_mutants(rng, |cand| {
            if accepted && rejected {
                return;
            }
            note_verdict(
                probe_verdict(post(x, &cand), admissible),
                &mut accepted,
                &mut rejected,
            );
        });
    }

    (accepted, rejected)
}

fn classify_normal_all_mutants_survived<I, R, Pre, PanicCond, AbortCond, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    anchor_input: I,
    anchor_ret: R,
    pre: &mut Pre,
    panic_cond: &mut PanicCond,
    abort_policy: &mut AbortPolicy<AbortCond>,
    post: &mut Post,
) -> (PanicFailureClass, PanicFailureDetail)
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    PanicCond: FnMut(&I) -> Result<bool, ()>,
    AbortCond: FnMut(&I) -> Result<bool, ()>,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.spec_config.syntactic_hint {
        return (
            hint_to_panic_class(hint),
            NormalProbeEvidence::default().detail(),
        );
    }

    let mut probe_rng = SplitMix64::new(config.spec_config.seed ^ 0xA5A5_5A5A_C3C3_3C3C);
    let probe_input_count = probe_input_budget(I::BOUNDARY_COUNT, config.spec_config.max_trials);

    let mut evidence = NormalProbeEvidence::default();
    let mut rejected_witness: Option<(I, bool)> = None;
    let mut accepted_witness: Option<(I, bool)> = None;

    // Anchor input came from a live `Returned` trial on a `pre`-admissible input.
    let (accepted, rejected) =
        observe_normal_outputs_at(&anchor_input, true, &anchor_ret, &mut probe_rng, post);
    evidence.record_input(true, accepted, rejected);

    if !evidence.saw_output_sensitivity {
        for idx in 0..probe_input_count {
            let x_probe = I::sample_at(idx, &mut probe_rng);
            let admissible = match abort_policy {
                AbortPolicy::AbortOnlyIf(abort_cond) => normal_probe_admission(
                    config.spec_config.probe_domain,
                    mode,
                    || pre(&x_probe),
                    || panic_cond(&x_probe),
                    Some(|| abort_cond(&x_probe)),
                ),
                AbortPolicy::ForbidAbort | AbortPolicy::WaiveAbortUnchecked => {
                    normal_probe_admission(
                        config.spec_config.probe_domain,
                        mode,
                        || pre(&x_probe),
                        || panic_cond(&x_probe),
                        None::<fn() -> Result<bool, ()>>,
                    )
                }
            };
            let Some(admissible) = admissible else {
                evidence.skipped_out_of_normal_domain += 1;
                continue;
            };

            let (accepted, rejected) = observe_normal_outputs_at(
                &x_probe,
                admissible,
                &anchor_ret,
                &mut probe_rng,
                post,
            );
            evidence.record_input(admissible, accepted, rejected);
            if evidence.saw_output_sensitivity {
                break;
            }
            if rejected && rejected_witness.is_none() {
                rejected_witness = Some((x_probe, admissible));
            } else if accepted && accepted_witness.is_none() {
                accepted_witness = Some((x_probe, admissible));
            }
        }
    }

    if !evidence.saw_output_sensitivity {
        let flipped = mutant_chain_finds_flip(anchor_ret, &mut probe_rng, |cand| {
            if probe_verdict(post(&anchor_input, cand), true) == ProbeVerdict::Rejected {
                return true;
            }
            if let Some((x, admissible)) = accepted_witness.as_ref()
                && probe_verdict(post(x, cand), *admissible) == ProbeVerdict::Rejected
            {
                return true;
            }
            if let Some((x, admissible)) = rejected_witness.as_ref()
                && probe_verdict(post(x, cand), *admissible) == ProbeVerdict::Accepted
            {
                return true;
            }
            false
        });
        if flipped {
            evidence.record_flip();
        }
    }

    (evidence.class(), evidence.detail())
}

// ===========================================================================
// 5. Stateless Panic-Contract Checking & Stage P3b Guard-Mutant Harness
// ===========================================================================

const fn trial_failure(
    class: PanicFailureClass,
    stats: PanicCheckStats,
    trial_idx: usize,
) -> PanicCheckOutcome {
    PanicCheckOutcome::Failed(PanicCheckFailure {
        class,
        stats,
        detail: PanicFailureDetail::TrialViolation { trial_idx },
    })
}

const fn predicate_trap_failure(
    class: PanicFailureClass,
    stats: PanicCheckStats,
    trial_idx: usize,
    trap: PanicTrapKind,
) -> PanicCheckOutcome {
    PanicCheckOutcome::Failed(PanicCheckFailure {
        class,
        stats,
        detail: PanicFailureDetail::PredicateTrapped { trial_idx, trap },
    })
}

/// Validates upfront configuration and `AbortPolicy` invariants before running
/// any trial (fail-closed).
fn validate_panic_config(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    abort_kind: AbortPolicyKind,
    stats: PanicCheckStats,
) -> Option<PanicCheckOutcome> {
    if mode == PanicContractMode::Exact && abort_kind == AbortPolicyKind::WaiveAbortUnchecked {
        return Some(PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::WaiveAbortIncompatibleWithExactContract,
            stats,
            detail: PanicFailureDetail::WaiveAbortInExactMode,
        }));
    }

    let max_trials = config.spec_config.max_trials;
    let min_pre = config.spec_config.min_precondition_hits;
    if max_trials == 0 || min_pre == 0 || min_pre > max_trials {
        return Some(PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadPrecondition,
            stats,
            detail: PanicFailureDetail::DegenerateConfig,
        }));
    }

    if mode != PanicContractMode::NeverPanics && config.min_panic_hits > max_trials {
        return Some(PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadPanicCondition,
            stats,
            detail: PanicFailureDetail::DegenerateConfig,
        }));
    }

    if abort_kind == AbortPolicyKind::AbortOnlyIf && config.min_abort_hits > max_trials {
        return Some(PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadAbortCondition,
            stats,
            detail: PanicFailureDetail::DegenerateConfig,
        }));
    }

    if mode == PanicContractMode::Exact {
        let mut required_disjoint = config.min_panic_hits;
        if abort_kind == AbortPolicyKind::AbortOnlyIf {
            required_disjoint = required_disjoint.saturating_add(config.min_abort_hits);
        }
        if config.require_normal_hits_in_exact {
            required_disjoint = required_disjoint.saturating_add(1);
        }
        if required_disjoint > max_trials {
            return Some(PanicCheckOutcome::Failed(PanicCheckFailure {
                class: PanicFailureClass::DeadNormalBranch,
                stats,
                detail: PanicFailureDetail::DegenerateConfig,
            }));
        }
    } else if mode == PanicContractMode::If
        && abort_kind == AbortPolicyKind::AbortOnlyIf
        && config.min_panic_hits.saturating_add(config.min_abort_hits) > max_trials
    {
        return Some(PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadAbortCondition,
            stats,
            detail: PanicFailureDetail::DegenerateConfig,
        }));
    }

    None
}

/// Checks a stateless panic contract whose `pre`, `panic_cond`, `abort_cond`,
/// and `post` callbacks may trap (`Result<bool, ()>`) and whose `body` returns
/// [`PanicExecOutcome<R>`].
///
/// # Domain safety
/// - `panic_cond` and `abort_cond` are evaluated **only** when `pre(&input)`
///   returned `Ok(true)`.
/// - `post` is evaluated **only** on `pre`-admissible trials whose live
///   execution returned [`PanicExecOutcome::Returned`] (and during Stage P3a
///   classification probes, only on `pre && !panic_cond && !abort_cond` inputs
///   unless [`ProbeDomain::Unconstrained`] is explicitly requested).
/// - [`PanicExecOutcome::UbOrFault`] fails immediately on *any* `pre`-admissible
///   input, even when `panic_cond` or `abort_cond` holds.
pub fn check_panic_contract_fallible<I, R, Pre, PanicCond, AbortCond, Body, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    mut abort_policy: AbortPolicy<AbortCond>,
    mut body: Body,
    mut post: Post,
) -> PanicCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    PanicCond: FnMut(&I) -> Result<bool, ()>,
    AbortCond: FnMut(&I) -> Result<bool, ()>,
    Body: FnMut(&I) -> PanicExecOutcome<R>,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    let mut stats = PanicCheckStats {
        subsingleton_return: R::IS_SUBSINGLETON,
        ..PanicCheckStats::default()
    };

    let abort_kind = abort_policy.kind();
    if let Some(early) = validate_panic_config(config, mode, abort_kind, stats) {
        return early;
    }

    let (mut rng, mut mutant_rng) = panic_stateless_streams(config.spec_config.seed);
    let mut anchor: Option<(I, R)> = None;

    for trial_idx in 0..config.spec_config.max_trials {
        let input = I::sample_at(trial_idx, &mut rng);
        stats.trials_run += 1;

        let pre_holds = match pre(&input) {
            Ok(b) => b,
            Err(()) => {
                return predicate_trap_failure(
                    PanicFailureClass::UnexpectedPanic,
                    stats,
                    trial_idx,
                    PanicTrapKind::PreconditionPanicked,
                );
            }
        };
        if !pre_holds {
            continue;
        }
        stats.precondition_hits += 1;

        let panic_expected = if mode == PanicContractMode::NeverPanics {
            false
        } else {
            match panic_cond(&input) {
                Ok(b) => b,
                Err(()) => {
                    return predicate_trap_failure(
                        PanicFailureClass::UnexpectedPanic,
                        stats,
                        trial_idx,
                        PanicTrapKind::PanicConditionPanicked,
                    );
                }
            }
        };
        if panic_expected {
            stats.panic_cond_hits += 1;
        }

        let abort_expected = match &mut abort_policy {
            AbortPolicy::AbortOnlyIf(abort_cond) => match abort_cond(&input) {
                Ok(b) => b,
                Err(()) => {
                    return predicate_trap_failure(
                        PanicFailureClass::UnexpectedPanic,
                        stats,
                        trial_idx,
                        PanicTrapKind::AbortConditionPanicked,
                    );
                }
            },
            AbortPolicy::ForbidAbort | AbortPolicy::WaiveAbortUnchecked => false,
        };
        if abort_expected {
            stats.abort_cond_hits += 1;
        }

        if abort_kind == AbortPolicyKind::AbortOnlyIf
            && matches!(mode, PanicContractMode::Exact | PanicContractMode::If)
            && panic_expected
            && abort_expected
        {
            return trial_failure(
                PanicFailureClass::OverlappingPanicAndAbortConditions,
                stats,
                trial_idx,
            );
        }

        match body(&input) {
            PanicExecOutcome::UbOrFault => {
                return trial_failure(PanicFailureClass::UbOrFaultOnExecution, stats, trial_idx);
            }
            PanicExecOutcome::Panicked => {
                stats.observed_panics += 1;
                match mode {
                    PanicContractMode::NeverPanics => {
                        return trial_failure(PanicFailureClass::UnexpectedPanic, stats, trial_idx);
                    }
                    PanicContractMode::OnlyIf | PanicContractMode::Exact => {
                        if !panic_expected {
                            return trial_failure(
                                PanicFailureClass::UnexpectedPanic,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                    PanicContractMode::If => {
                        if abort_kind == AbortPolicyKind::AbortOnlyIf && abort_expected {
                            return trial_failure(
                                PanicFailureClass::MissedExpectedAbort,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                }
            }
            PanicExecOutcome::Aborted => {
                stats.observed_aborts += 1;
                match abort_kind {
                    AbortPolicyKind::ForbidAbort => {
                        return trial_failure(PanicFailureClass::UnexpectedAbort, stats, trial_idx);
                    }
                    AbortPolicyKind::AbortOnlyIf => {
                        if !abort_expected {
                            return trial_failure(
                                PanicFailureClass::UnexpectedAbort,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                    AbortPolicyKind::WaiveAbortUnchecked => {
                        if mode == PanicContractMode::If && panic_expected {
                            return trial_failure(
                                PanicFailureClass::MissedExpectedPanic,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                }
            }
            PanicExecOutcome::Returned(ret_ok) => {
                if matches!(mode, PanicContractMode::Exact | PanicContractMode::If) {
                    if panic_expected {
                        return trial_failure(
                            PanicFailureClass::MissedExpectedPanic,
                            stats,
                            trial_idx,
                        );
                    }
                    if abort_kind == AbortPolicyKind::AbortOnlyIf && abort_expected {
                        return trial_failure(
                            PanicFailureClass::MissedExpectedAbort,
                            stats,
                            trial_idx,
                        );
                    }
                }

                stats.normal_returns += 1;

                if mode != PanicContractMode::If {
                    let post_ok = match post(&input, &ret_ok) {
                        Ok(b) => b,
                        Err(()) => {
                            return predicate_trap_failure(
                                PanicFailureClass::NormalPostconditionViolation,
                                stats,
                                trial_idx,
                                PanicTrapKind::PostconditionPanicked,
                            );
                        }
                    };
                    if !post_ok {
                        return trial_failure(
                            PanicFailureClass::NormalPostconditionViolation,
                            stats,
                            trial_idx,
                        );
                    }

                    let kills_before = stats.normal_mutants_killed;
                    if config.check_normal_return_mutants
                        && !R::IS_SUBSINGLETON
                        && config.spec_config.max_mutants_per_hit > 0
                    {
                        let mut tested_this_hit = 0usize;
                        let mut seen: [Option<R>; STAGE_P3_DEDUP_CAP] = array::from_fn(|_| None);
                        let mut seen_len = 0usize;
                        ret_ok.visit_mutants(&mut mutant_rng, |ret_bad| {
                            let spent = stage_p3_budget_spent(
                                tested_this_hit,
                                stats.normal_mutants_killed > kills_before,
                                config.spec_config.max_mutants_per_hit,
                            );
                            if spent
                                || ret_bad == ret_ok
                                || seen[..seen_len]
                                    .iter()
                                    .any(|prev| prev.as_ref() == Some(&ret_bad))
                            {
                                return;
                            }
                            tested_this_hit += 1;
                            record_normal_mutant(&mut stats, post(&input, &ret_bad));
                            if seen_len < STAGE_P3_DEDUP_CAP {
                                seen[seen_len] = Some(ret_bad);
                                seen_len += 1;
                            }
                        });
                    }
                    if stats.normal_mutants_killed > kills_before {
                        stats.normal_hits_with_kill += 1;
                    }

                    if anchor.is_none() {
                        anchor = Some((input, ret_ok));
                    }
                }
            }
        }
    }

    // Aggregate reachability gates
    if stats.precondition_hits < config.spec_config.min_precondition_hits {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadPrecondition,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: config.spec_config.min_precondition_hits,
                observed: stats.precondition_hits,
            },
        });
    }

    if mode != PanicContractMode::NeverPanics && stats.panic_cond_hits < config.min_panic_hits {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadPanicCondition,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: config.min_panic_hits,
                observed: stats.panic_cond_hits,
            },
        });
    }

    if abort_kind == AbortPolicyKind::AbortOnlyIf && stats.abort_cond_hits < config.min_abort_hits {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadAbortCondition,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: config.min_abort_hits,
                observed: stats.abort_cond_hits,
            },
        });
    }

    let require_normal = match mode {
        PanicContractMode::NeverPanics => true,
        PanicContractMode::Exact => config.require_normal_hits_in_exact,
        PanicContractMode::OnlyIf => config.require_normal_hits_in_only_if,
        PanicContractMode::If => false,
    };
    if require_normal && stats.normal_returns == 0 {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadNormalBranch,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: 1,
                observed: 0,
            },
        });
    }

    // Stage P3a normal-branch output-mutant dichotomy gate
    if mode != PanicContractMode::If
        && stats.normal_returns > 0
        && config.check_normal_return_mutants
    {
        if R::IS_SUBSINGLETON {
            if config.spec_config.syntactic_hint
                == Some(SyntacticBindingHint::SyntacticallyTautological)
            {
                return PanicCheckOutcome::Failed(PanicCheckFailure {
                    class: PanicFailureClass::TrivialNormalPostcondition,
                    stats,
                    detail: NormalProbeEvidence::default().detail(),
                });
            }
            return PanicCheckOutcome::Strong(stats);
        }

        if config.spec_config.max_mutants_per_hit == 0 {
            return PanicCheckOutcome::Failed(PanicCheckFailure {
                class: PanicFailureClass::SurvivedAllNormalMutants,
                stats,
                detail: PanicFailureDetail::DegenerateConfig,
            });
        }

        if stats.normal_mutants_tested == 0 {
            return PanicCheckOutcome::Failed(PanicCheckFailure {
                class: PanicFailureClass::SurvivedAllNormalMutants,
                stats,
                detail: PanicFailureDetail::NoDistinctNormalMutantsTested,
            });
        }

        if stats.normal_mutants_killed == 0 {
            let (class, detail) = match anchor {
                Some((anchor_input, anchor_ret)) => classify_normal_all_mutants_survived(
                    config,
                    mode,
                    anchor_input,
                    anchor_ret,
                    &mut pre,
                    &mut panic_cond,
                    &mut abort_policy,
                    &mut post,
                ),
                None => (
                    PanicFailureClass::SurvivedAllNormalMutants,
                    PanicFailureDetail::NoDistinctNormalMutantsTested,
                ),
            };
            return PanicCheckOutcome::Failed(PanicCheckFailure {
                class,
                stats,
                detail,
            });
        }
    }

    PanicCheckOutcome::Strong(stats)
}

/// Checks a stateless panic contract with infallible specification predicates
/// and a body returning [`PanicExecOutcome<R>`].
pub fn check_panic_contract<I, R, Pre, PanicCond, AbortCond, Body, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    abort_policy: AbortPolicy<AbortCond>,
    body: Body,
    mut post: Post,
) -> PanicCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    PanicCond: FnMut(&I) -> bool,
    AbortCond: FnMut(&I) -> bool,
    Body: FnMut(&I) -> PanicExecOutcome<R>,
    Post: FnMut(&I, &R) -> bool,
{
    let fallible_abort = abort_policy.map_cond(|mut cond| move |input: &I| Ok(cond(input)));
    check_panic_contract_fallible(
        config,
        mode,
        |input| Ok(pre(input)),
        |input| Ok(panic_cond(input)),
        fallible_abort,
        body,
        |input, ret| Ok(post(input, ret)),
    )
}

/// Panics if [`check_panic_contract`] does not return
/// [`PanicCheckOutcome::Strong`], returning [`PanicCheckStats`] on success.
pub fn assert_panic_contract_strong<I, R, Pre, PanicCond, AbortCond, Body, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    pre: Pre,
    panic_cond: PanicCond,
    abort_policy: AbortPolicy<AbortCond>,
    body: Body,
    post: Post,
) -> PanicCheckStats
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    PanicCond: FnMut(&I) -> bool,
    AbortCond: FnMut(&I) -> bool,
    Body: FnMut(&I) -> PanicExecOutcome<R>,
    Post: FnMut(&I, &R) -> bool,
{
    match check_panic_contract(config, mode, pre, panic_cond, abort_policy, body, post) {
        PanicCheckOutcome::Strong(stats) => stats,
        PanicCheckOutcome::Failed(failure) => {
            panic!(
                "panic contract failed dynamic strength check ({}): {:?}",
                failure.class.canonical_name(),
                failure
            );
        }
    }
}

/// Named stateless behavioral/guard mutant tested in Stage P3b.
pub struct PanicGuardMutant<'a, I, R> {
    /// Human-readable mutant label (e.g., `"dropped_overflow_assert"`).
    pub name: &'static str,
    /// Candidate mutated implementation under test.
    pub runner: &'a dyn Fn(&I) -> PanicExecOutcome<R>,
}

impl<'a, I, R> Clone for PanicGuardMutant<'a, I, R> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, I, R> Copy for PanicGuardMutant<'a, I, R> {}

impl<'a, I, R> PanicGuardMutant<'a, I, R> {
    /// Constructs a named stateless guard mutant.
    pub const fn new(name: &'static str, runner: &'a dyn Fn(&I) -> PanicExecOutcome<R>) -> Self {
        Self { name, runner }
    }
}

/// Stage P3b stateless behavioral & panic-guard mutant-kill harness (fallible
/// predicates).
///
/// 1. Verifies the live `body` passes the contract under full `config`.
/// 2. Fails closed with [`PanicFailureClass::SurvivedGuardMutant`] if `mutants`
///    is empty.
/// 3. Executes every mutant in `mutants` against the contract's live
///    conformance gates (`check_normal_return_mutants = false` so a mutant is
///    killed strictly by violating the contract rather than by Stage P3a on its
///    own outputs). If any mutant survives (`Strong`), fails with
///    [`PanicFailureClass::SurvivedGuardMutant`] carrying its index and name.
pub fn check_panic_guard_mutants_fallible<I, R, Pre, PanicCond, AbortCond, Body, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    mut abort_policy: AbortPolicy<AbortCond>,
    body: Body,
    mut post: Post,
    mutants: &[PanicGuardMutant<'_, I, R>],
) -> PanicCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    PanicCond: FnMut(&I) -> Result<bool, ()>,
    AbortCond: FnMut(&I) -> Result<bool, ()>,
    Body: FnMut(&I) -> PanicExecOutcome<R>,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    let mut live_stats = match check_panic_contract_fallible(
        config,
        mode,
        |x| pre(x),
        |x| panic_cond(x),
        match &mut abort_policy {
            AbortPolicy::ForbidAbort => AbortPolicy::ForbidAbort,
            AbortPolicy::AbortOnlyIf(f) => AbortPolicy::AbortOnlyIf(|x: &I| f(x)),
            AbortPolicy::WaiveAbortUnchecked => AbortPolicy::WaiveAbortUnchecked,
        },
        body,
        |x, r| post(x, r),
    ) {
        PanicCheckOutcome::Strong(stats) => stats,
        failed @ PanicCheckOutcome::Failed(_) => return failed,
    };

    if mutants.is_empty() {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::SurvivedGuardMutant,
            stats: live_stats,
            detail: PanicFailureDetail::NoGuardMutantsProvided,
        });
    }

    let mutant_config = config.with_check_normal_return_mutants(false);
    for (mutant_idx, mutant) in mutants.iter().enumerate() {
        live_stats.guard_mutants_tested += 1;
        let outcome = check_panic_contract_fallible(
            mutant_config,
            mode,
            |x| pre(x),
            |x| panic_cond(x),
            match &mut abort_policy {
                AbortPolicy::ForbidAbort => AbortPolicy::ForbidAbort,
                AbortPolicy::AbortOnlyIf(f) => AbortPolicy::AbortOnlyIf(|x: &I| f(x)),
                AbortPolicy::WaiveAbortUnchecked => AbortPolicy::WaiveAbortUnchecked,
            },
            |x| (mutant.runner)(x),
            |x, r| post(x, r),
        );
        match outcome {
            PanicCheckOutcome::Strong(surviving_stats) => {
                return PanicCheckOutcome::Failed(PanicCheckFailure {
                    class: PanicFailureClass::SurvivedGuardMutant,
                    stats: live_stats,
                    detail: PanicFailureDetail::GuardMutantSurvived {
                        mutant_idx,
                        mutant_name: mutant.name,
                        surviving_stats,
                    },
                });
            }
            PanicCheckOutcome::Failed(_) => {
                live_stats.guard_mutants_killed += 1;
            }
        }
    }

    PanicCheckOutcome::Strong(live_stats)
}

/// Stage P3b stateless behavioral & panic-guard mutant-kill harness (infallible
/// predicates).
pub fn check_panic_guard_mutants<I, R, Pre, PanicCond, AbortCond, Body, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    abort_policy: AbortPolicy<AbortCond>,
    body: Body,
    mut post: Post,
    mutants: &[PanicGuardMutant<'_, I, R>],
) -> PanicCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    PanicCond: FnMut(&I) -> bool,
    AbortCond: FnMut(&I) -> bool,
    Body: FnMut(&I) -> PanicExecOutcome<R>,
    Post: FnMut(&I, &R) -> bool,
{
    let fallible_abort = abort_policy.map_cond(|mut cond| move |input: &I| Ok(cond(input)));
    check_panic_guard_mutants_fallible(
        config,
        mode,
        |x| Ok(pre(x)),
        |x| Ok(panic_cond(x)),
        fallible_abort,
        body,
        |x, r| Ok(post(x, r)),
        mutants,
    )
}

// ===========================================================================
// 6. Stateful `&mut S` Panic-Contract Checking & Pre-Panic Mutation Guard
// ===========================================================================

struct StatefulPanicAnchor<S, A, R> {
    old_s: S,
    args: A,
    new_s: S,
    ret: R,
}

fn observe_stateful_normal_outputs_at<S, A, R, Post>(
    old_s: &S,
    args: &A,
    admissible: bool,
    anchor_new_s: &S,
    anchor_ret: &R,
    rng: &mut SplitMix64,
    post: &mut Post,
) -> (bool, bool)
where
    S: ReturnMutants,
    R: ReturnMutants,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    let mut accepted = false;
    let mut rejected = false;

    note_verdict(
        probe_verdict(post(old_s, args, anchor_new_s, anchor_ret), admissible),
        &mut accepted,
        &mut rejected,
    );

    if !S::IS_SUBSINGLETON {
        note_verdict(
            probe_verdict(post(old_s, args, old_s, anchor_ret), admissible),
            &mut accepted,
            &mut rejected,
        );
        if !(accepted && rejected) {
            anchor_new_s.visit_mutants(rng, |cand_s| {
                if accepted && rejected {
                    return;
                }
                note_verdict(
                    probe_verdict(post(old_s, args, &cand_s, anchor_ret), admissible),
                    &mut accepted,
                    &mut rejected,
                );
            });
        }
    }

    if !R::IS_SUBSINGLETON && !(accepted && rejected) {
        anchor_ret.visit_mutants(rng, |cand_r| {
            if accepted && rejected {
                return;
            }
            note_verdict(
                probe_verdict(post(old_s, args, anchor_new_s, &cand_r), admissible),
                &mut accepted,
                &mut rejected,
            );
        });
    }

    (accepted, rejected)
}

fn classify_stateful_normal_all_survived<S, A, R, Pre, PanicCond, AbortCond, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    anchor: StatefulPanicAnchor<S, A, R>,
    pre: &mut Pre,
    panic_cond: &mut PanicCond,
    abort_policy: &mut AbortPolicy<AbortCond>,
    post: &mut Post,
) -> (PanicFailureClass, PanicFailureDetail)
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    PanicCond: FnMut(&S, &A) -> Result<bool, ()>,
    AbortCond: FnMut(&S, &A) -> Result<bool, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.spec_config.syntactic_hint {
        return (
            hint_to_panic_class(hint),
            NormalProbeEvidence::default().detail(),
        );
    }

    let StatefulPanicAnchor {
        old_s: anchor_old_s,
        args: anchor_args,
        new_s: anchor_new_s,
        ret: anchor_ret,
    } = anchor;

    let mut probe_rng = SplitMix64::new(config.spec_config.seed ^ 0x51A7_E003_C3C3_3C3C);
    let mut evidence = NormalProbeEvidence::default();
    let mut rejected_witness: Option<(S, A, bool)> = None;
    let mut accepted_witness: Option<(S, A, bool)> = None;

    let (accepted, rejected) = observe_stateful_normal_outputs_at(
        &anchor_old_s,
        &anchor_args,
        true,
        &anchor_new_s,
        &anchor_ret,
        &mut probe_rng,
        post,
    );
    evidence.record_input(true, accepted, rejected);

    if !evidence.saw_output_sensitivity {
        let probe_input_count = probe_input_budget(
            <(S, A) as SampleInput>::BOUNDARY_COUNT,
            config.spec_config.max_trials,
        );
        for idx in 0..probe_input_count {
            let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
            let admissible = match abort_policy {
                AbortPolicy::AbortOnlyIf(abort_cond) => normal_probe_admission(
                    config.spec_config.probe_domain,
                    mode,
                    || pre(&old_s, &args),
                    || panic_cond(&old_s, &args),
                    Some(|| abort_cond(&old_s, &args)),
                ),
                AbortPolicy::ForbidAbort | AbortPolicy::WaiveAbortUnchecked => {
                    normal_probe_admission(
                        config.spec_config.probe_domain,
                        mode,
                        || pre(&old_s, &args),
                        || panic_cond(&old_s, &args),
                        None::<fn() -> Result<bool, ()>>,
                    )
                }
            };
            let Some(admissible) = admissible else {
                evidence.skipped_out_of_normal_domain += 1;
                continue;
            };

            let (accepted, rejected) = observe_stateful_normal_outputs_at(
                &old_s,
                &args,
                admissible,
                &anchor_new_s,
                &anchor_ret,
                &mut probe_rng,
                post,
            );
            evidence.record_input(admissible, accepted, rejected);
            if evidence.saw_output_sensitivity {
                break;
            }
            if rejected && rejected_witness.is_none() {
                rejected_witness = Some((old_s, args, admissible));
            } else if accepted && accepted_witness.is_none() {
                accepted_witness = Some((old_s, args, admissible));
            }
        }
    }

    if !evidence.saw_output_sensitivity && !S::IS_SUBSINGLETON {
        let flipped = mutant_chain_finds_flip(anchor_new_s.clone(), &mut probe_rng, |cand_s| {
            if probe_verdict(
                post(&anchor_old_s, &anchor_args, cand_s, &anchor_ret),
                true,
            ) == ProbeVerdict::Rejected
            {
                return true;
            }
            if let Some((os, a, admissible)) = accepted_witness.as_ref()
                && probe_verdict(post(os, a, cand_s, &anchor_ret), *admissible)
                    == ProbeVerdict::Rejected
            {
                return true;
            }
            if let Some((os, a, admissible)) = rejected_witness.as_ref()
                && probe_verdict(post(os, a, cand_s, &anchor_ret), *admissible)
                    == ProbeVerdict::Accepted
            {
                return true;
            }
            false
        });
        if flipped {
            evidence.record_flip();
        }
    }

    if !evidence.saw_output_sensitivity && !R::IS_SUBSINGLETON {
        let flipped = mutant_chain_finds_flip(anchor_ret, &mut probe_rng, |cand_r| {
            if probe_verdict(
                post(&anchor_old_s, &anchor_args, &anchor_new_s, cand_r),
                true,
            ) == ProbeVerdict::Rejected
            {
                return true;
            }
            if let Some((os, a, admissible)) = accepted_witness.as_ref()
                && probe_verdict(post(os, a, &anchor_new_s, cand_r), *admissible)
                    == ProbeVerdict::Rejected
            {
                return true;
            }
            if let Some((os, a, admissible)) = rejected_witness.as_ref()
                && probe_verdict(post(os, a, &anchor_new_s, cand_r), *admissible)
                    == ProbeVerdict::Accepted
            {
                return true;
            }
            false
        });
        if flipped {
            evidence.record_flip();
        }
    }

    (evidence.class(), evidence.detail())
}

fn probe_stateful_normal_return_axis<S, A, R, Pre, PanicCond, AbortCond, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    anchor: StatefulPanicAnchor<S, A, R>,
    pre: &mut Pre,
    panic_cond: &mut PanicCond,
    abort_policy: &mut AbortPolicy<AbortCond>,
    post: &mut Post,
) -> PanicFailureClass
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    PanicCond: FnMut(&S, &A) -> Result<bool, ()>,
    AbortCond: FnMut(&S, &A) -> Result<bool, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.spec_config.syntactic_hint {
        return hint_to_panic_class(hint);
    }

    let StatefulPanicAnchor {
        old_s: anchor_old_s,
        args: anchor_args,
        new_s: anchor_new_s,
        ret: anchor_ret,
    } = anchor;

    let mut probe_rng = SplitMix64::new(config.spec_config.seed ^ 0x51A7_E001_C3C3_3C3C);
    let mut state_probe_rng = probe_rng.fork();
    let mut ret_probe_rng = probe_rng.fork();
    let mut saw_sensitivity = false;
    let mut rejected_witnesses: [Option<(S, A, S, bool)>; 4] = [None, None, None, None];
    let mut accepted_witnesses: [Option<(S, A, S, bool)>; 2] = [None, None];

    let probe_input_count = probe_input_budget(
        <(S, A) as SampleInput>::BOUNDARY_COUNT,
        config.spec_config.max_trials,
    );
    for idx in 0..probe_input_count {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
        let admissible = match abort_policy {
            AbortPolicy::AbortOnlyIf(abort_cond) => normal_probe_admission(
                config.spec_config.probe_domain,
                mode,
                || pre(&old_s, &args),
                || panic_cond(&old_s, &args),
                Some(|| abort_cond(&old_s, &args)),
            ),
            AbortPolicy::ForbidAbort | AbortPolicy::WaiveAbortUnchecked => normal_probe_admission(
                config.spec_config.probe_domain,
                mode,
                || pre(&old_s, &args),
                || panic_cond(&old_s, &args),
                None::<fn() -> Result<bool, ()>>,
            ),
        };
        let Some(admissible) = admissible else {
            continue;
        };

        let mut state_cands: [Option<(S, usize)>; 4] = [
            Some((anchor_new_s.clone(), 0)),
            Some((old_s.clone(), 0)),
            None,
            None,
        ];
        if !S::IS_SUBSINGLETON {
            let mut slot = 2usize;
            old_s.visit_mutants(&mut state_probe_rng, |cand_s| {
                if slot < state_cands.len() && cand_s != old_s {
                    state_cands[slot] = Some((cand_s, 1));
                    slot += 1;
                }
            });
        }

        let acc_slot = usize::from(admissible);
        let mut best_rej: Option<(usize, S)> = None;
        let mut best_acc: Option<(usize, S)> = None;

        for cand_slot in state_cands {
            let Some((probe_new_s, kind)) = cand_slot else {
                continue;
            };
            let base = probe_verdict(post(&old_s, &args, &probe_new_s, &anchor_ret), admissible);
            if base == ProbeVerdict::Undefined {
                continue;
            }
            let mut varied = false;
            anchor_ret.visit_mutants(&mut ret_probe_rng, |cand| {
                if varied {
                    return;
                }
                let v = probe_verdict(post(&old_s, &args, &probe_new_s, &cand), admissible);
                if v != ProbeVerdict::Undefined && v != base {
                    varied = true;
                }
            });
            if varied {
                saw_sensitivity = true;
                break;
            }
            if base == ProbeVerdict::Rejected {
                let rej_slot = acc_slot * 2 + kind;
                if rejected_witnesses[rej_slot].is_none() && best_rej.is_none() {
                    best_rej = Some((rej_slot, probe_new_s));
                }
            } else if base == ProbeVerdict::Accepted
                && accepted_witnesses[acc_slot].is_none()
                && best_acc.is_none()
            {
                best_acc = Some((acc_slot, probe_new_s));
            }
        }
        if saw_sensitivity {
            break;
        }
        if let Some((slot, probe_new_s)) = best_rej {
            rejected_witnesses[slot] = Some((old_s, args, probe_new_s, admissible));
        } else if let Some((slot, probe_new_s)) = best_acc {
            accepted_witnesses[slot] = Some((old_s, args, probe_new_s, admissible));
        }
    }

    if !saw_sensitivity {
        saw_sensitivity = mutant_chain_finds_flip(anchor_ret, &mut probe_rng, |cand| {
            if probe_verdict(
                post(&anchor_old_s, &anchor_args, &anchor_new_s, cand),
                true,
            ) == ProbeVerdict::Rejected
            {
                return true;
            }
            for (os, a, ns, admissible) in accepted_witnesses.iter().flatten() {
                if probe_verdict(post(os, a, ns, cand), *admissible) == ProbeVerdict::Rejected {
                    return true;
                }
            }
            for (os, a, ns, admissible) in rejected_witnesses.iter().flatten() {
                if probe_verdict(post(os, a, ns, cand), *admissible) == ProbeVerdict::Accepted {
                    return true;
                }
            }
            false
        });
    }

    if saw_sensitivity {
        PanicFailureClass::SurvivedAllNormalMutants
    } else {
        PanicFailureClass::UnboundNormalReturnOutput
    }
}

fn probe_stateful_normal_state_axis<S, A, R, Pre, PanicCond, AbortCond, Post>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    anchor: StatefulPanicAnchor<S, A, R>,
    pre: &mut Pre,
    panic_cond: &mut PanicCond,
    abort_policy: &mut AbortPolicy<AbortCond>,
    post: &mut Post,
) -> PanicFailureClass
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    PanicCond: FnMut(&S, &A) -> Result<bool, ()>,
    AbortCond: FnMut(&S, &A) -> Result<bool, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.spec_config.syntactic_hint {
        return hint_to_panic_class(hint);
    }

    let StatefulPanicAnchor {
        old_s: anchor_old_s,
        args: anchor_args,
        new_s: anchor_new_s,
        ret: anchor_ret,
    } = anchor;

    let mut probe_rng = SplitMix64::new(config.spec_config.seed ^ 0x51A7_E002_C3C3_3C3C);
    let mut state_probe_rng = probe_rng.fork();
    let mut saw_sensitivity = false;
    let mut rejected_witnesses: [Option<(S, A, bool)>; 2] = [None, None];
    let mut accepted_witnesses: [Option<(S, A, bool)>; 2] = [None, None];

    let probe_input_count = probe_input_budget(
        <(S, A) as SampleInput>::BOUNDARY_COUNT,
        config.spec_config.max_trials,
    );
    for idx in 0..probe_input_count {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
        let admissible = match abort_policy {
            AbortPolicy::AbortOnlyIf(abort_cond) => normal_probe_admission(
                config.spec_config.probe_domain,
                mode,
                || pre(&old_s, &args),
                || panic_cond(&old_s, &args),
                Some(|| abort_cond(&old_s, &args)),
            ),
            AbortPolicy::ForbidAbort | AbortPolicy::WaiveAbortUnchecked => normal_probe_admission(
                config.spec_config.probe_domain,
                mode,
                || pre(&old_s, &args),
                || panic_cond(&old_s, &args),
                None::<fn() -> Result<bool, ()>>,
            ),
        };
        let Some(admissible) = admissible else {
            continue;
        };

        let base = probe_verdict(post(&old_s, &args, &anchor_new_s, &anchor_ret), admissible);
        if base == ProbeVerdict::Undefined {
            continue;
        }
        let rev = probe_verdict(post(&old_s, &args, &old_s, &anchor_ret), admissible);
        let mut varied = rev != ProbeVerdict::Undefined && rev != base;
        if !varied {
            anchor_new_s.visit_mutants(&mut state_probe_rng, |cand_s| {
                if varied {
                    return;
                }
                let v = probe_verdict(post(&old_s, &args, &cand_s, &anchor_ret), admissible);
                if v != ProbeVerdict::Undefined && v != base {
                    varied = true;
                }
            });
        }
        if varied {
            saw_sensitivity = true;
            break;
        }

        let slot = usize::from(admissible);
        if base == ProbeVerdict::Rejected && rejected_witnesses[slot].is_none() {
            rejected_witnesses[slot] = Some((old_s, args, admissible));
        } else if base == ProbeVerdict::Accepted && accepted_witnesses[slot].is_none() {
            accepted_witnesses[slot] = Some((old_s, args, admissible));
        }
    }

    if !saw_sensitivity {
        saw_sensitivity = mutant_chain_finds_flip(anchor_new_s, &mut probe_rng, |cand_s| {
            if probe_verdict(
                post(&anchor_old_s, &anchor_args, cand_s, &anchor_ret),
                true,
            ) == ProbeVerdict::Rejected
            {
                return true;
            }
            for (os, a, admissible) in accepted_witnesses.iter().flatten() {
                if probe_verdict(post(os, a, cand_s, &anchor_ret), *admissible)
                    == ProbeVerdict::Rejected
                {
                    return true;
                }
            }
            for (os, a, admissible) in rejected_witnesses.iter().flatten() {
                if probe_verdict(post(os, a, cand_s, &anchor_ret), *admissible)
                    == ProbeVerdict::Accepted
                {
                    return true;
                }
            }
            false
        });
    }

    if saw_sensitivity {
        PanicFailureClass::SurvivedAllNormalMutants
    } else {
        PanicFailureClass::UnboundNormalReturnOutput
    }
}

/// Checks a stateful `&mut S` panic contract with fallible specification
/// predicates and an optional `panic_state_inv(&initial_state, &panicked_state)`
/// guard verifying rollback/invariant preservation on unwinding panics.
///
/// Does not require `S: Copy` (requires only `S: SampleInput + ReturnMutants +
/// Clone + PartialEq`, matching [`crate::spec_check::check_stateful_contract_fallible`]).
#[allow(clippy::too_many_arguments)]
pub fn check_stateful_panic_contract_fallible<
    S,
    A,
    R,
    Pre,
    PanicCond,
    AbortCond,
    Body,
    Post,
    PanicStateInv,
>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    mut abort_policy: AbortPolicy<AbortCond>,
    mut body: Body,
    mut post: Post,
    mut panic_state_inv: Option<PanicStateInv>,
) -> PanicCheckOutcome
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    PanicCond: FnMut(&S, &A) -> Result<bool, ()>,
    AbortCond: FnMut(&S, &A) -> Result<bool, ()>,
    Body: FnMut(&mut S, &A) -> PanicExecOutcome<R>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
    PanicStateInv: FnMut(&S, &S) -> Result<bool, ()>,
{
    let mut stats = PanicCheckStats {
        subsingleton_return: R::IS_SUBSINGLETON,
        ..PanicCheckStats::default()
    };

    let abort_kind = abort_policy.kind();
    if let Some(early) = validate_panic_config(config, mode, abort_kind, stats) {
        return early;
    }

    let (mut rng, mut ret_mutant_rng, mut state_mutant_rng) =
        panic_stateful_streams(config.spec_config.seed);

    let mut return_mutants_tested = 0usize;
    let mut return_mutants_killed = 0usize;
    let mut state_mutants_tested = 0usize;
    let mut state_mutants_killed = 0usize;
    let mut anchor: Option<StatefulPanicAnchor<S, A, R>> = None;

    for trial_idx in 0..config.spec_config.max_trials {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(trial_idx, &mut rng);
        stats.trials_run += 1;

        let pre_holds = match pre(&old_s, &args) {
            Ok(b) => b,
            Err(()) => {
                return predicate_trap_failure(
                    PanicFailureClass::UnexpectedPanic,
                    stats,
                    trial_idx,
                    PanicTrapKind::PreconditionPanicked,
                );
            }
        };
        if !pre_holds {
            continue;
        }
        stats.precondition_hits += 1;

        let panic_expected = if mode == PanicContractMode::NeverPanics {
            false
        } else {
            match panic_cond(&old_s, &args) {
                Ok(b) => b,
                Err(()) => {
                    return predicate_trap_failure(
                        PanicFailureClass::UnexpectedPanic,
                        stats,
                        trial_idx,
                        PanicTrapKind::PanicConditionPanicked,
                    );
                }
            }
        };
        if panic_expected {
            stats.panic_cond_hits += 1;
        }

        let abort_expected = match &mut abort_policy {
            AbortPolicy::AbortOnlyIf(abort_cond) => match abort_cond(&old_s, &args) {
                Ok(b) => b,
                Err(()) => {
                    return predicate_trap_failure(
                        PanicFailureClass::UnexpectedPanic,
                        stats,
                        trial_idx,
                        PanicTrapKind::AbortConditionPanicked,
                    );
                }
            },
            AbortPolicy::ForbidAbort | AbortPolicy::WaiveAbortUnchecked => false,
        };
        if abort_expected {
            stats.abort_cond_hits += 1;
        }

        if abort_kind == AbortPolicyKind::AbortOnlyIf
            && matches!(mode, PanicContractMode::Exact | PanicContractMode::If)
            && panic_expected
            && abort_expected
        {
            return trial_failure(
                PanicFailureClass::OverlappingPanicAndAbortConditions,
                stats,
                trial_idx,
            );
        }

        let mut new_s = old_s.clone();
        match body(&mut new_s, &args) {
            PanicExecOutcome::UbOrFault => {
                return trial_failure(PanicFailureClass::UbOrFaultOnExecution, stats, trial_idx);
            }
            PanicExecOutcome::Panicked => {
                stats.observed_panics += 1;
                match mode {
                    PanicContractMode::NeverPanics => {
                        return trial_failure(PanicFailureClass::UnexpectedPanic, stats, trial_idx);
                    }
                    PanicContractMode::OnlyIf | PanicContractMode::Exact => {
                        if !panic_expected {
                            return trial_failure(
                                PanicFailureClass::UnexpectedPanic,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                    PanicContractMode::If => {
                        if abort_kind == AbortPolicyKind::AbortOnlyIf && abort_expected {
                            return trial_failure(
                                PanicFailureClass::MissedExpectedAbort,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                }

                // Check optional pre-panic `&mut S` invariant against `new_s`
                // (which retains any mutations performed before unwinding).
                if let Some(ref mut inv) = panic_state_inv {
                    stats.panic_state_inv_checks += 1;
                    match inv(&old_s, &new_s) {
                        Ok(true) => {}
                        Ok(false) => {
                            return trial_failure(
                                PanicFailureClass::PanicStateInvariantViolation,
                                stats,
                                trial_idx,
                            );
                        }
                        Err(()) => {
                            return predicate_trap_failure(
                                PanicFailureClass::PanicStateInvariantViolation,
                                stats,
                                trial_idx,
                                PanicTrapKind::PanicStateInvariantPanicked,
                            );
                        }
                    }
                }
            }
            PanicExecOutcome::Aborted => {
                stats.observed_aborts += 1;
                match abort_kind {
                    AbortPolicyKind::ForbidAbort => {
                        return trial_failure(PanicFailureClass::UnexpectedAbort, stats, trial_idx);
                    }
                    AbortPolicyKind::AbortOnlyIf => {
                        if !abort_expected {
                            return trial_failure(
                                PanicFailureClass::UnexpectedAbort,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                    AbortPolicyKind::WaiveAbortUnchecked => {
                        if mode == PanicContractMode::If && panic_expected {
                            return trial_failure(
                                PanicFailureClass::MissedExpectedPanic,
                                stats,
                                trial_idx,
                            );
                        }
                    }
                }
            }
            PanicExecOutcome::Returned(ret_ok) => {
                if matches!(mode, PanicContractMode::Exact | PanicContractMode::If) {
                    if panic_expected {
                        return trial_failure(
                            PanicFailureClass::MissedExpectedPanic,
                            stats,
                            trial_idx,
                        );
                    }
                    if abort_kind == AbortPolicyKind::AbortOnlyIf && abort_expected {
                        return trial_failure(
                            PanicFailureClass::MissedExpectedAbort,
                            stats,
                            trial_idx,
                        );
                    }
                }

                stats.normal_returns += 1;

                if mode != PanicContractMode::If {
                    let post_ok = match post(&old_s, &args, &new_s, &ret_ok) {
                        Ok(b) => b,
                        Err(()) => {
                            return predicate_trap_failure(
                                PanicFailureClass::NormalPostconditionViolation,
                                stats,
                                trial_idx,
                                PanicTrapKind::PostconditionPanicked,
                            );
                        }
                    };
                    if !post_ok {
                        return trial_failure(
                            PanicFailureClass::NormalPostconditionViolation,
                            stats,
                            trial_idx,
                        );
                    }

                    let kills_before = stats.normal_mutants_killed;

                    if config.check_normal_return_mutants
                        && !R::IS_SUBSINGLETON
                        && config.spec_config.max_mutants_per_hit > 0
                    {
                        let mut tested_this_hit = 0usize;
                        let mut seen_ret: [Option<R>; STAGE_P3_DEDUP_CAP] =
                            array::from_fn(|_| None);
                        let mut seen_ret_len = 0usize;
                        let ret_kills_before = return_mutants_killed;
                        ret_ok.visit_mutants(&mut ret_mutant_rng, |ret_bad| {
                            let spent = stage_p3_budget_spent(
                                tested_this_hit,
                                return_mutants_killed > ret_kills_before,
                                config.spec_config.max_mutants_per_hit,
                            );
                            if spent
                                || ret_bad == ret_ok
                                || seen_ret[..seen_ret_len]
                                    .iter()
                                    .any(|prev| prev.as_ref() == Some(&ret_bad))
                            {
                                return;
                            }
                            tested_this_hit += 1;
                            return_mutants_tested += 1;
                            if record_normal_mutant(&mut stats, post(&old_s, &args, &new_s, &ret_bad))
                            {
                                return_mutants_killed += 1;
                            }
                            if seen_ret_len < STAGE_P3_DEDUP_CAP {
                                seen_ret[seen_ret_len] = Some(ret_bad);
                                seen_ret_len += 1;
                            }
                        });
                    }

                    if config.check_normal_return_mutants
                        && !S::IS_SUBSINGLETON
                        && config.spec_config.max_mutants_per_hit > 0
                    {
                        let mut tested_this_hit = 0usize;
                        let state_kills_before = state_mutants_killed;
                        let tested_pre_revert = new_s != old_s;
                        if tested_pre_revert {
                            tested_this_hit += 1;
                            state_mutants_tested += 1;
                            if record_normal_mutant(&mut stats, post(&old_s, &args, &old_s, &ret_ok))
                            {
                                state_mutants_killed += 1;
                            }
                        }

                        let mut seen_s: [Option<S>; STAGE_P3_DEDUP_CAP] = array::from_fn(|_| None);
                        let mut seen_s_len = 0usize;
                        new_s.visit_mutants(&mut state_mutant_rng, |bad_s| {
                            let spent = stage_p3_budget_spent(
                                tested_this_hit,
                                state_mutants_killed > state_kills_before,
                                config.spec_config.max_mutants_per_hit,
                            );
                            if spent
                                || bad_s == new_s
                                || (tested_pre_revert && bad_s == old_s)
                                || seen_s[..seen_s_len]
                                    .iter()
                                    .any(|prev| prev.as_ref() == Some(&bad_s))
                            {
                                return;
                            }
                            tested_this_hit += 1;
                            state_mutants_tested += 1;
                            if record_normal_mutant(&mut stats, post(&old_s, &args, &bad_s, &ret_ok))
                            {
                                state_mutants_killed += 1;
                            }
                            if seen_s_len < STAGE_P3_DEDUP_CAP {
                                seen_s[seen_s_len] = Some(bad_s);
                                seen_s_len += 1;
                            }
                        });
                    }

                    if stats.normal_mutants_killed > kills_before {
                        stats.normal_hits_with_kill += 1;
                    }

                    if anchor.is_none() {
                        anchor = Some(StatefulPanicAnchor {
                            old_s,
                            args,
                            new_s,
                            ret: ret_ok,
                        });
                    }
                }
            }
        }
    }

    if stats.precondition_hits < config.spec_config.min_precondition_hits {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadPrecondition,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: config.spec_config.min_precondition_hits,
                observed: stats.precondition_hits,
            },
        });
    }

    if mode != PanicContractMode::NeverPanics && stats.panic_cond_hits < config.min_panic_hits {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadPanicCondition,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: config.min_panic_hits,
                observed: stats.panic_cond_hits,
            },
        });
    }

    if abort_kind == AbortPolicyKind::AbortOnlyIf && stats.abort_cond_hits < config.min_abort_hits {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadAbortCondition,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: config.min_abort_hits,
                observed: stats.abort_cond_hits,
            },
        });
    }

    let require_normal = match mode {
        PanicContractMode::NeverPanics => true,
        PanicContractMode::Exact => config.require_normal_hits_in_exact,
        PanicContractMode::OnlyIf => config.require_normal_hits_in_only_if,
        PanicContractMode::If => false,
    };
    if require_normal && stats.normal_returns == 0 {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::DeadNormalBranch,
            stats,
            detail: PanicFailureDetail::InsufficientHits {
                required: 1,
                observed: 0,
            },
        });
    }

    if mode != PanicContractMode::If
        && stats.normal_returns > 0
        && config.check_normal_return_mutants
    {
        if S::IS_SUBSINGLETON && R::IS_SUBSINGLETON {
            if config.spec_config.syntactic_hint
                == Some(SyntacticBindingHint::SyntacticallyTautological)
            {
                return PanicCheckOutcome::Failed(PanicCheckFailure {
                    class: PanicFailureClass::TrivialNormalPostcondition,
                    stats,
                    detail: NormalProbeEvidence::default().detail(),
                });
            }
            return PanicCheckOutcome::Strong(stats);
        }

        if config.spec_config.max_mutants_per_hit == 0 {
            return PanicCheckOutcome::Failed(PanicCheckFailure {
                class: PanicFailureClass::SurvivedAllNormalMutants,
                stats,
                detail: PanicFailureDetail::DegenerateConfig,
            });
        }

        if stats.normal_mutants_tested == 0 {
            return PanicCheckOutcome::Failed(PanicCheckFailure {
                class: PanicFailureClass::SurvivedAllNormalMutants,
                stats,
                detail: PanicFailureDetail::NoDistinctNormalMutantsTested,
            });
        }

        let axis_detail = PanicFailureDetail::StatefulNormalAxisUnconstrained {
            return_mutants_tested,
            return_mutants_killed,
            state_mutants_tested,
            state_mutants_killed,
        };

        if stats.normal_mutants_killed == 0 {
            let (class, detail) = match anchor {
                Some(anchor) => classify_stateful_normal_all_survived(
                    config,
                    mode,
                    anchor,
                    &mut pre,
                    &mut panic_cond,
                    &mut abort_policy,
                    &mut post,
                ),
                None => (
                    PanicFailureClass::SurvivedAllNormalMutants,
                    PanicFailureDetail::NoDistinctNormalMutantsTested,
                ),
            };
            return PanicCheckOutcome::Failed(PanicCheckFailure {
                class,
                stats,
                detail,
            });
        }

        if config.spec_config.require_both_state_and_return_kills {
            if !R::IS_SUBSINGLETON && return_mutants_killed == 0 {
                let class = match anchor {
                    Some(anchor) if return_mutants_tested > 0 => probe_stateful_normal_return_axis(
                        config,
                        mode,
                        anchor,
                        &mut pre,
                        &mut panic_cond,
                        &mut abort_policy,
                        &mut post,
                    ),
                    _ => PanicFailureClass::SurvivedAllNormalMutants,
                };
                return PanicCheckOutcome::Failed(PanicCheckFailure {
                    class,
                    stats,
                    detail: axis_detail,
                });
            }

            if !S::IS_SUBSINGLETON && state_mutants_killed == 0 {
                let class = match anchor {
                    Some(anchor) if state_mutants_tested > 0 => probe_stateful_normal_state_axis(
                        config,
                        mode,
                        anchor,
                        &mut pre,
                        &mut panic_cond,
                        &mut abort_policy,
                        &mut post,
                    ),
                    _ => PanicFailureClass::SurvivedAllNormalMutants,
                };
                return PanicCheckOutcome::Failed(PanicCheckFailure {
                    class,
                    stats,
                    detail: axis_detail,
                });
            }
        }
    }

    PanicCheckOutcome::Strong(stats)
}

/// Checks a stateful `&mut S` panic contract with infallible predicates and
/// optional `panic_state_inv`.
#[allow(clippy::too_many_arguments)]
pub fn check_stateful_panic_contract<
    S,
    A,
    R,
    Pre,
    PanicCond,
    AbortCond,
    Body,
    Post,
    PanicStateInv,
>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    abort_policy: AbortPolicy<AbortCond>,
    body: Body,
    mut post: Post,
    panic_state_inv: Option<PanicStateInv>,
) -> PanicCheckOutcome
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> bool,
    PanicCond: FnMut(&S, &A) -> bool,
    AbortCond: FnMut(&S, &A) -> bool,
    Body: FnMut(&mut S, &A) -> PanicExecOutcome<R>,
    Post: FnMut(&S, &A, &S, &R) -> bool,
    PanicStateInv: FnMut(&S, &S) -> bool,
{
    let fallible_abort = abort_policy.map_cond(|mut c| move |s: &S, a: &A| Ok(c(s, a)));
    let fallible_inv = panic_state_inv.map(|mut inv| move |old_s: &S, post_s: &S| Ok(inv(old_s, post_s)));
    check_stateful_panic_contract_fallible(
        config,
        mode,
        |s, a| Ok(pre(s, a)),
        |s, a| Ok(panic_cond(s, a)),
        fallible_abort,
        body,
        |os, a, ns, r| Ok(post(os, a, ns, r)),
        fallible_inv,
    )
}

/// Named stateful behavioral/guard mutant tested in Stage P3b.
pub struct StatefulPanicGuardMutant<'a, S, A, R> {
    /// Human-readable mutant label.
    pub name: &'static str,
    /// Candidate mutated stateful implementation under test.
    pub runner: &'a dyn Fn(&mut S, &A) -> PanicExecOutcome<R>,
}

impl<'a, S, A, R> Clone for StatefulPanicGuardMutant<'a, S, A, R> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, S, A, R> Copy for StatefulPanicGuardMutant<'a, S, A, R> {}

impl<'a, S, A, R> StatefulPanicGuardMutant<'a, S, A, R> {
    /// Constructs a named stateful guard mutant.
    pub const fn new(
        name: &'static str,
        runner: &'a dyn Fn(&mut S, &A) -> PanicExecOutcome<R>,
    ) -> Self {
        Self { name, runner }
    }
}

/// Stage P3b stateful behavioral & panic-guard mutant-kill harness (fallible
/// predicates).
#[allow(clippy::too_many_arguments)]
pub fn check_stateful_panic_guard_mutants_fallible<
    S,
    A,
    R,
    Pre,
    PanicCond,
    AbortCond,
    Body,
    Post,
    PanicStateInv,
>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    mut abort_policy: AbortPolicy<AbortCond>,
    body: Body,
    mut post: Post,
    mut panic_state_inv: Option<PanicStateInv>,
    mutants: &[StatefulPanicGuardMutant<'_, S, A, R>],
) -> PanicCheckOutcome
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    PanicCond: FnMut(&S, &A) -> Result<bool, ()>,
    AbortCond: FnMut(&S, &A) -> Result<bool, ()>,
    Body: FnMut(&mut S, &A) -> PanicExecOutcome<R>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
    PanicStateInv: FnMut(&S, &S) -> Result<bool, ()>,
{
    let mut live_stats = match check_stateful_panic_contract_fallible(
        config,
        mode,
        |s, a| pre(s, a),
        |s, a| panic_cond(s, a),
        match &mut abort_policy {
            AbortPolicy::ForbidAbort => AbortPolicy::ForbidAbort,
            AbortPolicy::AbortOnlyIf(f) => AbortPolicy::AbortOnlyIf(|s: &S, a: &A| f(s, a)),
            AbortPolicy::WaiveAbortUnchecked => AbortPolicy::WaiveAbortUnchecked,
        },
        body,
        |os, a, ns, r| post(os, a, ns, r),
        panic_state_inv
            .as_mut()
            .map(|inv| move |old_s: &S, post_s: &S| inv(old_s, post_s)),
    ) {
        PanicCheckOutcome::Strong(stats) => stats,
        failed @ PanicCheckOutcome::Failed(_) => return failed,
    };

    if mutants.is_empty() {
        return PanicCheckOutcome::Failed(PanicCheckFailure {
            class: PanicFailureClass::SurvivedGuardMutant,
            stats: live_stats,
            detail: PanicFailureDetail::NoGuardMutantsProvided,
        });
    }

    let mutant_config = config.with_check_normal_return_mutants(false);
    for (mutant_idx, mutant) in mutants.iter().enumerate() {
        live_stats.guard_mutants_tested += 1;
        let outcome = check_stateful_panic_contract_fallible(
            mutant_config,
            mode,
            |s, a| pre(s, a),
            |s, a| panic_cond(s, a),
            match &mut abort_policy {
                AbortPolicy::ForbidAbort => AbortPolicy::ForbidAbort,
                AbortPolicy::AbortOnlyIf(f) => AbortPolicy::AbortOnlyIf(|s: &S, a: &A| f(s, a)),
                AbortPolicy::WaiveAbortUnchecked => AbortPolicy::WaiveAbortUnchecked,
            },
            |s, a| (mutant.runner)(s, a),
            |os, a, ns, r| post(os, a, ns, r),
            panic_state_inv
                .as_mut()
                .map(|inv| move |old_s: &S, post_s: &S| inv(old_s, post_s)),
        );
        match outcome {
            PanicCheckOutcome::Strong(surviving_stats) => {
                return PanicCheckOutcome::Failed(PanicCheckFailure {
                    class: PanicFailureClass::SurvivedGuardMutant,
                    stats: live_stats,
                    detail: PanicFailureDetail::GuardMutantSurvived {
                        mutant_idx,
                        mutant_name: mutant.name,
                        surviving_stats,
                    },
                });
            }
            PanicCheckOutcome::Failed(_) => {
                live_stats.guard_mutants_killed += 1;
            }
        }
    }

    PanicCheckOutcome::Strong(live_stats)
}

/// Stage P3b stateful behavioral & panic-guard mutant-kill harness (infallible
/// predicates).
#[allow(clippy::too_many_arguments)]
pub fn check_stateful_panic_guard_mutants<
    S,
    A,
    R,
    Pre,
    PanicCond,
    AbortCond,
    Body,
    Post,
    PanicStateInv,
>(
    config: PanicCheckConfig,
    mode: PanicContractMode,
    mut pre: Pre,
    mut panic_cond: PanicCond,
    abort_policy: AbortPolicy<AbortCond>,
    body: Body,
    mut post: Post,
    panic_state_inv: Option<PanicStateInv>,
    mutants: &[StatefulPanicGuardMutant<'_, S, A, R>],
) -> PanicCheckOutcome
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> bool,
    PanicCond: FnMut(&S, &A) -> bool,
    AbortCond: FnMut(&S, &A) -> bool,
    Body: FnMut(&mut S, &A) -> PanicExecOutcome<R>,
    Post: FnMut(&S, &A, &S, &R) -> bool,
    PanicStateInv: FnMut(&S, &S) -> bool,
{
    let fallible_abort = abort_policy.map_cond(|mut c| move |s: &S, a: &A| Ok(c(s, a)));
    let fallible_inv = panic_state_inv.map(|mut inv| move |old_s: &S, post_s: &S| Ok(inv(old_s, post_s)));
    check_stateful_panic_guard_mutants_fallible(
        config,
        mode,
        |s, a| Ok(pre(s, a)),
        |s, a| Ok(panic_cond(s, a)),
        fallible_abort,
        body,
        |os, a, ns, r| Ok(post(os, a, ns, r)),
        fallible_inv,
        mutants,
    )
}

// ===========================================================================
// 7. Ergonomic Typed Wrappers & Builders
// ===========================================================================

/// Concrete zero-overhead stateless panic-contract descriptor uniting mode,
/// precondition, panic condition, [`AbortPolicy`], and postcondition.
#[derive(Clone, Copy, Debug)]
pub struct PanicContractSpec<Pre, PanicCond, AbortCond, Post> {
    pub mode: PanicContractMode,
    pub pre: Pre,
    pub panic_cond: PanicCond,
    pub abort_policy: AbortPolicy<AbortCond>,
    pub post: Post,
}

impl<Pre, PanicCond, AbortCond, Post> PanicContractSpec<Pre, PanicCond, AbortCond, Post> {
    /// Replaces the [`AbortPolicy`] on this contract descriptor.
    pub fn with_abort_policy<AC2>(
        self,
        abort_policy: AbortPolicy<AC2>,
    ) -> PanicContractSpec<Pre, PanicCond, AC2, Post> {
        PanicContractSpec {
            mode: self.mode,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy,
            post: self.post,
        }
    }

    /// Configures [`AbortPolicy::AbortOnlyIf`] with explicit `abort_cond`.
    pub fn with_abort_only_if<AC2>(
        self,
        abort_cond: AC2,
    ) -> PanicContractSpec<Pre, PanicCond, AC2, Post> {
        self.with_abort_policy(AbortPolicy::AbortOnlyIf(abort_cond))
    }

    /// Explicitly opts into [`AbortPolicy::WaiveAbortUnchecked`].
    pub fn with_waive_abort_unchecked(self) -> PanicContractSpec<Pre, PanicCond, AbortCond, Post> {
        PanicContractSpec {
            mode: self.mode,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: AbortPolicy::WaiveAbortUnchecked,
            post: self.post,
        }
    }

    /// Runs [`check_panic_contract`] against `body` with infallible predicates.
    pub fn check<I, R, Body>(self, config: PanicCheckConfig, body: Body) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        AbortCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        check_panic_contract(
            config,
            self.mode,
            self.pre,
            self.panic_cond,
            self.abort_policy,
            body,
            self.post,
        )
    }

    /// Runs [`check_panic_contract_fallible`] against `body` with fallible
    /// predicates.
    pub fn check_fallible<I, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
    ) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> Result<bool, ()>,
        PanicCond: FnMut(&I) -> Result<bool, ()>,
        AbortCond: FnMut(&I) -> Result<bool, ()>,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> Result<bool, ()>,
    {
        check_panic_contract_fallible(
            config,
            self.mode,
            self.pre,
            self.panic_cond,
            self.abort_policy,
            body,
            self.post,
        )
    }

    /// Runs Stage P3b [`check_panic_guard_mutants`] against `body` and `mutants`.
    pub fn check_guard_mutants<I, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
        mutants: &[PanicGuardMutant<'_, I, R>],
    ) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        AbortCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        check_panic_guard_mutants(
            config,
            self.mode,
            self.pre,
            self.panic_cond,
            self.abort_policy,
            body,
            self.post,
            mutants,
        )
    }

    /// Runs Stage P3b [`check_panic_guard_mutants_fallible`] against `body` and
    /// `mutants`.
    pub fn check_guard_mutants_fallible<I, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
        mutants: &[PanicGuardMutant<'_, I, R>],
    ) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> Result<bool, ()>,
        PanicCond: FnMut(&I) -> Result<bool, ()>,
        AbortCond: FnMut(&I) -> Result<bool, ()>,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> Result<bool, ()>,
    {
        check_panic_guard_mutants_fallible(
            config,
            self.mode,
            self.pre,
            self.panic_cond,
            self.abort_policy,
            body,
            self.post,
            mutants,
        )
    }
}

/// Typed `panics_only_if` contract builder (`Anneal.PanicContracts.PanicsOnlyIf`).
#[derive(Clone, Copy, Debug)]
pub struct PanicsOnlyIf<Pre, PanicCond, Post> {
    pub pre: Pre,
    pub panic_cond: PanicCond,
    pub post: Post,
}

impl<Pre, PanicCond, Post> PanicsOnlyIf<Pre, PanicCond, Post> {
    /// Creates a `PanicsOnlyIf` contract defaulting to [`AbortPolicy::ForbidAbort`].
    pub const fn new(pre: Pre, panic_cond: PanicCond, post: Post) -> Self {
        Self {
            pre,
            panic_cond,
            post,
        }
    }

    /// Converts into a [`PanicContractSpec`] using [`AbortPolicy::ForbidAbort`].
    pub fn into_spec<I>(self) -> PanicContractSpec<Pre, PanicCond, fn(&I) -> bool, Post> {
        PanicContractSpec {
            mode: PanicContractMode::OnlyIf,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: forbid_abort::<I>(),
            post: self.post,
        }
    }

    /// Attaches [`AbortPolicy::AbortOnlyIf`] and returns a [`PanicContractSpec`].
    pub fn with_abort_only_if<AbortCond>(
        self,
        abort_cond: AbortCond,
    ) -> PanicContractSpec<Pre, PanicCond, AbortCond, Post> {
        PanicContractSpec {
            mode: PanicContractMode::OnlyIf,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: AbortPolicy::AbortOnlyIf(abort_cond),
            post: self.post,
        }
    }

    /// Attaches [`AbortPolicy::WaiveAbortUnchecked`] and returns a
    /// [`PanicContractSpec`].
    pub fn with_waive_abort_unchecked<I>(
        self,
    ) -> PanicContractSpec<Pre, PanicCond, fn(&I) -> bool, Post> {
        PanicContractSpec {
            mode: PanicContractMode::OnlyIf,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: waive_abort_unchecked::<I>(),
            post: self.post,
        }
    }

    /// Checks this `PanicsOnlyIf` contract under [`AbortPolicy::ForbidAbort`].
    pub fn check<I, R, Body>(self, config: PanicCheckConfig, body: Body) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        self.into_spec::<I>().check(config, body)
    }

    /// Runs Stage P3b guard-mutant checking under [`AbortPolicy::ForbidAbort`].
    pub fn check_guard_mutants<I, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
        mutants: &[PanicGuardMutant<'_, I, R>],
    ) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        self.into_spec::<I>().check_guard_mutants(config, body, mutants)
    }
}

/// Typed `panics_if` contract builder (`Anneal.PanicContracts.PanicsIf`).
#[derive(Clone, Copy, Debug)]
pub struct PanicsIf<Pre, PanicCond> {
    pub pre: Pre,
    pub panic_cond: PanicCond,
}

fn trivial_unused_post<I, R>(_input: &I, _ret: &R) -> bool {
    true
}

impl<Pre, PanicCond> PanicsIf<Pre, PanicCond> {
    /// Creates a `PanicsIf` contract defaulting to [`AbortPolicy::ForbidAbort`].
    pub const fn new(pre: Pre, panic_cond: PanicCond) -> Self {
        Self { pre, panic_cond }
    }

    /// Converts into a [`PanicContractSpec`] using [`AbortPolicy::ForbidAbort`].
    pub fn into_spec<I, R>(
        self,
    ) -> PanicContractSpec<Pre, PanicCond, fn(&I) -> bool, fn(&I, &R) -> bool> {
        PanicContractSpec {
            mode: PanicContractMode::If,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: forbid_abort::<I>(),
            post: trivial_unused_post::<I, R>,
        }
    }

    /// Attaches [`AbortPolicy::AbortOnlyIf`] and returns a [`PanicContractSpec`].
    pub fn with_abort_only_if<I, R, AbortCond>(
        self,
        abort_cond: AbortCond,
    ) -> PanicContractSpec<Pre, PanicCond, AbortCond, fn(&I, &R) -> bool> {
        PanicContractSpec {
            mode: PanicContractMode::If,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: AbortPolicy::AbortOnlyIf(abort_cond),
            post: trivial_unused_post::<I, R>,
        }
    }

    /// Checks this `PanicsIf` contract under [`AbortPolicy::ForbidAbort`].
    pub fn check<I, R, Body>(self, config: PanicCheckConfig, body: Body) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
    {
        self.into_spec::<I, R>().check(config, body)
    }

    /// Runs Stage P3b guard-mutant checking under [`AbortPolicy::ForbidAbort`].
    pub fn check_guard_mutants<I, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
        mutants: &[PanicGuardMutant<'_, I, R>],
    ) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
    {
        self.into_spec::<I, R>()
            .check_guard_mutants(config, body, mutants)
    }
}

/// Typed exact panic contract builder (`Anneal.PanicContracts.ExactPanicContract`).
#[derive(Clone, Copy, Debug)]
pub struct ExactPanicContract<Pre, PanicCond, Post> {
    pub pre: Pre,
    pub panic_cond: PanicCond,
    pub post: Post,
}

impl<Pre, PanicCond, Post> ExactPanicContract<Pre, PanicCond, Post> {
    /// Creates an `ExactPanicContract` defaulting to [`AbortPolicy::ForbidAbort`].
    pub const fn new(pre: Pre, panic_cond: PanicCond, post: Post) -> Self {
        Self {
            pre,
            panic_cond,
            post,
        }
    }

    /// Converts into a [`PanicContractSpec`] using [`AbortPolicy::ForbidAbort`].
    pub fn into_spec<I>(self) -> PanicContractSpec<Pre, PanicCond, fn(&I) -> bool, Post> {
        PanicContractSpec {
            mode: PanicContractMode::Exact,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: forbid_abort::<I>(),
            post: self.post,
        }
    }

    /// Attaches [`AbortPolicy::AbortOnlyIf`] for dual panic-vs-abort exact
    /// contracts (`Anneal.PanicContracts.ExactPanicAbortContract`).
    pub fn with_abort_only_if<AbortCond>(
        self,
        abort_cond: AbortCond,
    ) -> PanicContractSpec<Pre, PanicCond, AbortCond, Post> {
        PanicContractSpec {
            mode: PanicContractMode::Exact,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: AbortPolicy::AbortOnlyIf(abort_cond),
            post: self.post,
        }
    }

    /// Attaches [`AbortPolicy::WaiveAbortUnchecked`] (which fails closed in
    /// `Exact` mode with
    /// [`PanicFailureClass::WaiveAbortIncompatibleWithExactContract`]).
    pub fn with_waive_abort_unchecked<I>(
        self,
    ) -> PanicContractSpec<Pre, PanicCond, fn(&I) -> bool, Post> {
        PanicContractSpec {
            mode: PanicContractMode::Exact,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: waive_abort_unchecked::<I>(),
            post: self.post,
        }
    }

    /// Checks this `ExactPanicContract` under [`AbortPolicy::ForbidAbort`].
    pub fn check<I, R, Body>(self, config: PanicCheckConfig, body: Body) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        self.into_spec::<I>().check(config, body)
    }

    /// Runs Stage P3b guard-mutant checking under [`AbortPolicy::ForbidAbort`].
    pub fn check_guard_mutants<I, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
        mutants: &[PanicGuardMutant<'_, I, R>],
    ) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        PanicCond: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        self.into_spec::<I>().check_guard_mutants(config, body, mutants)
    }
}

/// Typed non-panicking contract builder (`Anneal.PanicContracts.NeverPanics`),
/// bridging cleanly to total `#[spec]` contracts.
#[derive(Clone, Copy, Debug)]
pub struct NeverPanics<Pre, Post> {
    pub pre: Pre,
    pub post: Post,
}

fn false_panic_cond<I>(_input: &I) -> bool {
    false
}

impl<Pre, Post> NeverPanics<Pre, Post> {
    /// Creates a `NeverPanics` contract defaulting to [`AbortPolicy::ForbidAbort`].
    pub const fn new(pre: Pre, post: Post) -> Self {
        Self { pre, post }
    }

    /// Converts into a [`PanicContractSpec`] using [`AbortPolicy::ForbidAbort`].
    pub fn into_spec<I>(
        self,
    ) -> PanicContractSpec<Pre, fn(&I) -> bool, fn(&I) -> bool, Post> {
        PanicContractSpec {
            mode: PanicContractMode::NeverPanics,
            pre: self.pre,
            panic_cond: false_panic_cond::<I>,
            abort_policy: forbid_abort::<I>(),
            post: self.post,
        }
    }

    /// Checks this `NeverPanics` contract under [`AbortPolicy::ForbidAbort`].
    pub fn check<I, R, Body>(self, config: PanicCheckConfig, body: Body) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        self.into_spec::<I>().check(config, body)
    }

    /// Runs Stage P3b guard-mutant checking under [`AbortPolicy::ForbidAbort`].
    pub fn check_guard_mutants<I, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
        mutants: &[PanicGuardMutant<'_, I, R>],
    ) -> PanicCheckOutcome
    where
        I: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&I) -> bool,
        Body: FnMut(&I) -> PanicExecOutcome<R>,
        Post: FnMut(&I, &R) -> bool,
    {
        self.into_spec::<I>().check_guard_mutants(config, body, mutants)
    }
}

/// Concrete stateful `&mut S` panic-contract descriptor uniting mode,
/// precondition, panic condition, [`AbortPolicy`], normal postcondition, and
/// optional pre-panic state invariant `panic_state_inv`.
#[derive(Clone, Copy, Debug)]
pub struct StatefulPanicContractSpec<Pre, PanicCond, AbortCond, Post, PanicStateInv> {
    pub mode: PanicContractMode,
    pub pre: Pre,
    pub panic_cond: PanicCond,
    pub abort_policy: AbortPolicy<AbortCond>,
    pub post: Post,
    pub panic_state_inv: Option<PanicStateInv>,
}

fn trivial_stateful_post<S, A, R>(_old_s: &S, _args: &A, _new_s: &S, _ret: &R) -> bool {
    true
}

fn false_stateful_panic_cond<S, A>(_s: &S, _a: &A) -> bool {
    false
}

impl<Pre, PanicCond, Post>
    StatefulPanicContractSpec<
        Pre,
        PanicCond,
        fn(&(), &()) -> bool,
        Post,
        fn(&(), &()) -> bool,
    >
{
    /// Constructs a stateful `Exact` panic contract defaulting to
    /// [`AbortPolicy::ForbidAbort`] and no `panic_state_inv`.
    pub fn exact<S, A>(
        pre: Pre,
        panic_cond: PanicCond,
        post: Post,
    ) -> StatefulPanicContractSpec<Pre, PanicCond, fn(&S, &A) -> bool, Post, fn(&S, &S) -> bool>
    {
        StatefulPanicContractSpec {
            mode: PanicContractMode::Exact,
            pre,
            panic_cond,
            abort_policy: forbid_stateful_abort::<S, A>(),
            post,
            panic_state_inv: None,
        }
    }

    /// Constructs a stateful `OnlyIf` panic contract defaulting to
    /// [`AbortPolicy::ForbidAbort`] and no `panic_state_inv`.
    pub fn only_if<S, A>(
        pre: Pre,
        panic_cond: PanicCond,
        post: Post,
    ) -> StatefulPanicContractSpec<Pre, PanicCond, fn(&S, &A) -> bool, Post, fn(&S, &S) -> bool>
    {
        StatefulPanicContractSpec {
            mode: PanicContractMode::OnlyIf,
            pre,
            panic_cond,
            abort_policy: forbid_stateful_abort::<S, A>(),
            post,
            panic_state_inv: None,
        }
    }
}

impl<Pre, PanicCond>
    StatefulPanicContractSpec<
        Pre,
        PanicCond,
        fn(&(), &()) -> bool,
        fn(&(), &(), &(), &()) -> bool,
        fn(&(), &()) -> bool,
    >
{
    /// Constructs a stateful `If` (`panics_if`) contract defaulting to
    /// [`AbortPolicy::ForbidAbort`].
    pub fn panics_if<S, A, R>(
        pre: Pre,
        panic_cond: PanicCond,
    ) -> StatefulPanicContractSpec<
        Pre,
        PanicCond,
        fn(&S, &A) -> bool,
        fn(&S, &A, &S, &R) -> bool,
        fn(&S, &S) -> bool,
    > {
        StatefulPanicContractSpec {
            mode: PanicContractMode::If,
            pre,
            panic_cond,
            abort_policy: forbid_stateful_abort::<S, A>(),
            post: trivial_stateful_post::<S, A, R>,
            panic_state_inv: None,
        }
    }
}

impl<Pre, Post>
    StatefulPanicContractSpec<
        Pre,
        fn(&(), &()) -> bool,
        fn(&(), &()) -> bool,
        Post,
        fn(&(), &()) -> bool,
    >
{
    /// Constructs a stateful `NeverPanics` contract defaulting to
    /// [`AbortPolicy::ForbidAbort`].
    pub fn never_panics<S, A>(
        pre: Pre,
        post: Post,
    ) -> StatefulPanicContractSpec<
        Pre,
        fn(&S, &A) -> bool,
        fn(&S, &A) -> bool,
        Post,
        fn(&S, &S) -> bool,
    > {
        StatefulPanicContractSpec {
            mode: PanicContractMode::NeverPanics,
            pre,
            panic_cond: false_stateful_panic_cond::<S, A>,
            abort_policy: forbid_stateful_abort::<S, A>(),
            post,
            panic_state_inv: None,
        }
    }
}

impl<Pre, PanicCond, AbortCond, Post, PanicStateInv>
    StatefulPanicContractSpec<Pre, PanicCond, AbortCond, Post, PanicStateInv>
{
    /// Replaces the [`AbortPolicy`].
    pub fn with_abort_policy<AC2>(
        self,
        abort_policy: AbortPolicy<AC2>,
    ) -> StatefulPanicContractSpec<Pre, PanicCond, AC2, Post, PanicStateInv> {
        StatefulPanicContractSpec {
            mode: self.mode,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy,
            post: self.post,
            panic_state_inv: self.panic_state_inv,
        }
    }

    /// Configures [`AbortPolicy::AbortOnlyIf`].
    pub fn with_abort_only_if<AC2>(
        self,
        abort_cond: AC2,
    ) -> StatefulPanicContractSpec<Pre, PanicCond, AC2, Post, PanicStateInv> {
        self.with_abort_policy(AbortPolicy::AbortOnlyIf(abort_cond))
    }

    /// Attaches a `panic_state_inv(&initial_state, &panicked_post_state)` guard.
    pub fn with_panic_state_inv<Inv2>(
        self,
        inv: Inv2,
    ) -> StatefulPanicContractSpec<Pre, PanicCond, AbortCond, Post, Inv2> {
        StatefulPanicContractSpec {
            mode: self.mode,
            pre: self.pre,
            panic_cond: self.panic_cond,
            abort_policy: self.abort_policy,
            post: self.post,
            panic_state_inv: Some(inv),
        }
    }

    /// Runs [`check_stateful_panic_contract`] with infallible predicates.
    pub fn check<S, A, R, Body>(self, config: PanicCheckConfig, body: Body) -> PanicCheckOutcome
    where
        S: SampleInput + ReturnMutants + Clone + PartialEq,
        A: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&S, &A) -> bool,
        PanicCond: FnMut(&S, &A) -> bool,
        AbortCond: FnMut(&S, &A) -> bool,
        Body: FnMut(&mut S, &A) -> PanicExecOutcome<R>,
        Post: FnMut(&S, &A, &S, &R) -> bool,
        PanicStateInv: FnMut(&S, &S) -> bool,
    {
        check_stateful_panic_contract(
            config,
            self.mode,
            self.pre,
            self.panic_cond,
            self.abort_policy,
            body,
            self.post,
            self.panic_state_inv,
        )
    }

    /// Runs [`check_stateful_panic_contract_fallible`] with fallible predicates.
    pub fn check_fallible<S, A, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
    ) -> PanicCheckOutcome
    where
        S: SampleInput + ReturnMutants + Clone + PartialEq,
        A: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&S, &A) -> Result<bool, ()>,
        PanicCond: FnMut(&S, &A) -> Result<bool, ()>,
        AbortCond: FnMut(&S, &A) -> Result<bool, ()>,
        Body: FnMut(&mut S, &A) -> PanicExecOutcome<R>,
        Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
        PanicStateInv: FnMut(&S, &S) -> Result<bool, ()>,
    {
        check_stateful_panic_contract_fallible(
            config,
            self.mode,
            self.pre,
            self.panic_cond,
            self.abort_policy,
            body,
            self.post,
            self.panic_state_inv,
        )
    }

    /// Runs Stage P3b [`check_stateful_panic_guard_mutants`].
    pub fn check_guard_mutants<S, A, R, Body>(
        self,
        config: PanicCheckConfig,
        body: Body,
        mutants: &[StatefulPanicGuardMutant<'_, S, A, R>],
    ) -> PanicCheckOutcome
    where
        S: SampleInput + ReturnMutants + Clone + PartialEq,
        A: SampleInput,
        R: ReturnMutants + PartialEq,
        Pre: FnMut(&S, &A) -> bool,
        PanicCond: FnMut(&S, &A) -> bool,
        AbortCond: FnMut(&S, &A) -> bool,
        Body: FnMut(&mut S, &A) -> PanicExecOutcome<R>,
        Post: FnMut(&S, &A, &S, &R) -> bool,
        PanicStateInv: FnMut(&S, &S) -> bool,
    {
        check_stateful_panic_guard_mutants(
            config,
            self.mode,
            self.pre,
            self.panic_cond,
            self.abort_policy,
            body,
            self.post,
            self.panic_state_inv,
            mutants,
        )
    }
}

// ===========================================================================
// 8. Exported `std::panic::catch_unwind` Convenience Macros (Zero `std` Dep)
// ===========================================================================

/// Wraps a stateless Rust function/closure `FnMut(&I) -> R` into a
/// `FnMut(&I) -> PanicExecOutcome<R>` runner using `::std::panic::catch_unwind`
/// at the caller's test site (requiring no `std` Cargo feature in `anneal-spec`).
#[macro_export]
macro_rules! panic_unwind_runner {
    ($body:expr) => {{
        fn __anneal_constrain_panic_runner<I, R, F>(f: F) -> F
        where
            F: ::core::ops::FnMut(&I) -> $crate::panic_contract::PanicExecOutcome<R>,
        {
            f
        }
        let mut __anneal_body = $body;
        __anneal_constrain_panic_runner(move |input| {
            match ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                __anneal_body(input)
            })) {
                ::core::result::Result::Ok(ret) => {
                    $crate::panic_contract::PanicExecOutcome::Returned(ret)
                }
                ::core::result::Result::Err(_) => {
                    $crate::panic_contract::PanicExecOutcome::Panicked
                }
            }
        })
    }};
}

/// Wraps a stateful Rust function/closure `FnMut(&mut S, &A) -> R` into a
/// `FnMut(&mut S, &A) -> PanicExecOutcome<R>` runner using
/// `::std::panic::catch_unwind` at the caller's test site.
///
/// Any mutations written to `&mut S` before a panic unwinds remain observable
/// in the state passed to `panic_state_inv`.
#[macro_export]
macro_rules! stateful_panic_unwind_runner {
    ($body:expr) => {{
        fn __anneal_constrain_stateful_panic_runner<S, A, R, F>(f: F) -> F
        where
            F: ::core::ops::FnMut(&mut S, &A) -> $crate::panic_contract::PanicExecOutcome<R>,
        {
            f
        }
        let mut __anneal_body = $body;
        __anneal_constrain_stateful_panic_runner(move |state, args| {
            match ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                __anneal_body(state, args)
            })) {
                ::core::result::Result::Ok(ret) => {
                    $crate::panic_contract::PanicExecOutcome::Returned(ret)
                }
                ::core::result::Result::Err(_) => {
                    $crate::panic_contract::PanicExecOutcome::Panicked
                }
            }
        })
    }};
}

/// Constructs a named [`PanicGuardMutant`](crate::panic_contract::PanicGuardMutant)
/// wrapping a panicking Rust closure/function with `::std::panic::catch_unwind`.
#[macro_export]
macro_rules! panic_guard_mutant_unwind {
    ($name:expr, $body:expr) => {{
        $crate::panic_contract::PanicGuardMutant::new($name, &move |input| {
            match ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| ($body)(input))) {
                ::core::result::Result::Ok(ret) => {
                    $crate::panic_contract::PanicExecOutcome::Returned(ret)
                }
                ::core::result::Result::Err(_) => {
                    $crate::panic_contract::PanicExecOutcome::Panicked
                }
            }
        })
    }};
}

/// Constructs a named
/// [`StatefulPanicGuardMutant`](crate::panic_contract::StatefulPanicGuardMutant)
/// wrapping a panicking stateful Rust closure/function with
/// `::std::panic::catch_unwind`.
#[macro_export]
macro_rules! stateful_panic_guard_mutant_unwind {
    ($name:expr, $body:expr) => {{
        $crate::panic_contract::StatefulPanicGuardMutant::new($name, &move |state, args| {
            match ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                ($body)(state, args)
            })) {
                ::core::result::Result::Ok(ret) => {
                    $crate::panic_contract::PanicExecOutcome::Returned(ret)
                }
                ::core::result::Result::Err(_) => {
                    $crate::panic_contract::PanicExecOutcome::Panicked
                }
            }
        })
    }};
}

/// Executes [`check_panic_contract_fallible`](crate::panic_contract::check_panic_contract_fallible)
/// with `::std::panic::catch_unwind` guarding `pre`, `panic_cond`, `body`, and
/// `post` at the caller's test site (defaulting to `AbortPolicy::ForbidAbort`).
#[macro_export]
macro_rules! check_panic_contract_unwind {
    ($config:expr, $mode:expr, $pre:expr, $panic_cond:expr, $body:expr, $post:expr $(,)?) => {{
        let mut __anneal_pre = $pre;
        let mut __anneal_panic_cond = $panic_cond;
        let mut __anneal_post = $post;
        $crate::panic_contract::check_panic_contract_fallible(
            $config,
            $mode,
            move |input| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| __anneal_pre(input)))
                    .map_err(|_| ())
            },
            move |input| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                    __anneal_panic_cond(input)
                }))
                .map_err(|_| ())
            },
            $crate::panic_contract::forbid_abort_fallible(),
            $crate::panic_unwind_runner!($body),
            move |input, ret| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                    __anneal_post(input, ret)
                }))
                .map_err(|_| ())
            },
        )
    }};
}

/// Executes [`check_stateful_panic_contract_fallible`](crate::panic_contract::check_stateful_panic_contract_fallible)
/// with `::std::panic::catch_unwind` guarding `pre`, `panic_cond`, `body`,
/// `post`, and optional `panic_state_inv` at the caller's test site.
#[macro_export]
macro_rules! check_stateful_panic_contract_unwind {
    ($config:expr, $mode:expr, $pre:expr, $panic_cond:expr, $body:expr, $post:expr $(,)?) => {{
        let mut __anneal_pre = $pre;
        let mut __anneal_panic_cond = $panic_cond;
        let mut __anneal_post = $post;
        $crate::panic_contract::check_stateful_panic_contract_fallible(
            $config,
            $mode,
            move |s, a| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| __anneal_pre(s, a)))
                    .map_err(|_| ())
            },
            move |s, a| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                    __anneal_panic_cond(s, a)
                }))
                .map_err(|_| ())
            },
            $crate::panic_contract::forbid_stateful_abort_fallible(),
            $crate::stateful_panic_unwind_runner!($body),
            move |old_s, args, new_s, ret| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                    __anneal_post(old_s, args, new_s, ret)
                }))
                .map_err(|_| ())
            },
            ::core::option::Option::<fn(&_, &_) -> ::core::result::Result<bool, ()>>::None,
        )
    }};
    (
        $config:expr,
        $mode:expr,
        $pre:expr,
        $panic_cond:expr,
        $body:expr,
        $post:expr,
        $panic_state_inv:expr $(,)?
    ) => {{
        fn __anneal_constrain_panic_inv<S, F>(f: F) -> ::core::option::Option<F>
        where
            F: ::core::ops::FnMut(&S, &S) -> ::core::result::Result<bool, ()>,
        {
            ::core::option::Option::Some(f)
        }
        let mut __anneal_pre = $pre;
        let mut __anneal_panic_cond = $panic_cond;
        let mut __anneal_post = $post;
        let mut __anneal_panic_inv = $panic_state_inv;
        $crate::panic_contract::check_stateful_panic_contract_fallible(
            $config,
            $mode,
            move |s, a| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| __anneal_pre(s, a)))
                    .map_err(|_| ())
            },
            move |s, a| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                    __anneal_panic_cond(s, a)
                }))
                .map_err(|_| ())
            },
            $crate::panic_contract::forbid_stateful_abort_fallible(),
            $crate::stateful_panic_unwind_runner!($body),
            move |old_s, args, new_s, ret| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                    __anneal_post(old_s, args, new_s, ret)
                }))
                .map_err(|_| ())
            },
            __anneal_constrain_panic_inv(move |old_s, post_s| {
                ::std::panic::catch_unwind(::core::panic::AssertUnwindSafe(|| {
                    __anneal_panic_inv(old_s, post_s)
                }))
                .map_err(|_| ())
            }),
        )
    }};
}

/// Asserts that [`check_panic_contract_unwind!`] returns
/// [`PanicCheckOutcome::Strong`](crate::panic_contract::PanicCheckOutcome::Strong),
/// returning [`PanicCheckStats`](crate::panic_contract::PanicCheckStats) on
/// success.
#[macro_export]
macro_rules! assert_panic_contract_strong_unwind {
    ($config:expr, $mode:expr, $pre:expr, $panic_cond:expr, $body:expr, $post:expr $(,)?) => {{
        match $crate::check_panic_contract_unwind!(
            $config,
            $mode,
            $pre,
            $panic_cond,
            $body,
            $post
        ) {
            $crate::panic_contract::PanicCheckOutcome::Strong(stats) => stats,
            $crate::panic_contract::PanicCheckOutcome::Failed(failure) => {
                ::core::panic!(
                    "panic contract failed dynamic unwind strength check ({}): {:?}",
                    failure.class.canonical_name(),
                    failure
                );
            }
        }
    }};
}

/// Asserts that [`check_stateful_panic_contract_unwind!`] returns
/// [`PanicCheckOutcome::Strong`](crate::panic_contract::PanicCheckOutcome::Strong),
/// returning [`PanicCheckStats`](crate::panic_contract::PanicCheckStats) on
/// success.
#[macro_export]
macro_rules! assert_stateful_panic_contract_strong_unwind {
    ($config:expr, $mode:expr, $pre:expr, $panic_cond:expr, $body:expr, $post:expr $(,)?) => {{
        match $crate::check_stateful_panic_contract_unwind!(
            $config,
            $mode,
            $pre,
            $panic_cond,
            $body,
            $post
        ) {
            $crate::panic_contract::PanicCheckOutcome::Strong(stats) => stats,
            $crate::panic_contract::PanicCheckOutcome::Failed(failure) => {
                ::core::panic!(
                    "stateful panic contract failed dynamic unwind strength check ({}): {:?}",
                    failure.class.canonical_name(),
                    failure
                );
            }
        }
    }};
    (
        $config:expr,
        $mode:expr,
        $pre:expr,
        $panic_cond:expr,
        $body:expr,
        $post:expr,
        $panic_state_inv:expr $(,)?
    ) => {{
        match $crate::check_stateful_panic_contract_unwind!(
            $config,
            $mode,
            $pre,
            $panic_cond,
            $body,
            $post,
            $panic_state_inv
        ) {
            $crate::panic_contract::PanicCheckOutcome::Strong(stats) => stats,
            $crate::panic_contract::PanicCheckOutcome::Failed(failure) => {
                ::core::panic!(
                    "stateful panic contract failed dynamic unwind strength check ({}): {:?}",
                    failure.class.canonical_name(),
                    failure
                );
            }
        }
    }};
}

// ===========================================================================
// 9. `kani#5095` Call-Boundary Non-Inlining Guard & Dynamic Wrapper
// ===========================================================================

/// Compile-time (`const fn`) call-boundary non-inlining guard descriptor for
/// preventing silent MIR-inlining contract bypasses (`kani#5095`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CallBoundaryGuard {
    /// Canonical `DefPath` of the calling function.
    pub caller_path: &'static str,
    /// Canonical `DefPath` of the contracted callee that must not be inlined.
    pub target_path: &'static str,
    /// Expected number of direct call sites to `target_path` in the caller.
    pub expected_call_sites: usize,
    /// Whether the target source item must carry explicit `#[inline(never)]`.
    pub require_inline_never: bool,
    /// Whether trait-dispatch overrides targeting `target_path` or chain hops
    /// are forbidden.
    pub forbid_trait_dispatch: bool,
}

impl CallBoundaryGuard {
    /// Constructs a new `CallBoundaryGuard` with strict defaults
    /// (`expected_call_sites = 1`, `require_inline_never = true`,
    /// `forbid_trait_dispatch = true`).
    pub const fn new(caller_path: &'static str, target_path: &'static str) -> Self {
        Self {
            caller_path,
            target_path,
            expected_call_sites: 1,
            require_inline_never: true,
            forbid_trait_dispatch: true,
        }
    }

    /// Sets the expected direct call-site multiplicity.
    pub const fn with_expected_call_sites(mut self, expected_call_sites: usize) -> Self {
        self.expected_call_sites = expected_call_sites;
        self
    }

    /// Sets whether source scanning enforces explicit `#[inline(never)]`.
    pub const fn with_require_inline_never(mut self, require_inline_never: bool) -> Self {
        self.require_inline_never = require_inline_never;
        self
    }

    /// Sets whether trait dispatch overrides are forbidden.
    pub const fn with_forbid_trait_dispatch(mut self, forbid_trait_dispatch: bool) -> Self {
        self.forbid_trait_dispatch = forbid_trait_dispatch;
        self
    }

    /// Verifies that `fn_name` in `source` satisfies this guard's source-level
    /// `#[inline(never)]` requirement.
    pub fn verify_target_source(&self, source: &str, fn_name: &str) -> InlineBoundaryVerdict {
        if !self.require_inline_never {
            return InlineBoundaryVerdict::Verified;
        }
        verify_fn_inline_never_source_with_options(
            source,
            fn_name,
            InlineScanOptions {
                forbid_polymorphic_or_trait_default: self.forbid_trait_dispatch,
            },
        )
    }

    /// Verifies `ReachableCallSitesPreserved` against `caller_blocks`,
    /// `callees`, and `caller_trait_impls` using this guard's `target_path` and
    /// `expected_call_sites`.
    pub fn verify_reachable_sites(
        &self,
        caller_blocks: &[MirBlockSummary<'_>],
        callees: &[CalleeEntry<'_>],
        caller_trait_impls: &[TraitImplBinding<'_>],
    ) -> CallBoundaryVerdict {
        if !self.forbid_trait_dispatch {
            // Still verify callees exclusion and reachable call sites without
            // rejecting trait-table entries when explicitly opted out.
            return verify_reachable_call_sites_inner(
                caller_blocks,
                callees,
                &[],
                self.target_path,
                self.expected_call_sites,
                false,
            );
        }
        verify_reachable_call_sites(
            caller_blocks,
            callees,
            caller_trait_impls,
            self.target_path,
            self.expected_call_sites,
        )
    }
}

/// Invokes `f(input)` across an explicit `#[inline(never)]` +
/// [`core::hint::black_box`] dynamic call boundary to prevent compiler constant
/// folding or inlining across contract test boundaries.
#[inline(never)]
pub fn invoke_boundary_guarded<I, R, F>(input: I, f: F) -> R
where
    F: FnOnce(I) -> R,
{
    let opaque_input = black_box(input);
    let opaque_fn = black_box(f);
    black_box(opaque_fn(opaque_input))
}

/// Stateful counterpart to [`invoke_boundary_guarded`], preserving an opaque
/// `#[inline(never)]` boundary for `&mut S` calls.
#[inline(never)]
pub fn invoke_stateful_boundary_guarded<S, A, R, F>(state: &mut S, args: A, f: F) -> R
where
    F: FnOnce(&mut S, A) -> R,
{
    let opaque_state = black_box(state);
    let opaque_args = black_box(args);
    let opaque_fn = black_box(f);
    black_box(opaque_fn(opaque_state, opaque_args))
}

// ===========================================================================
// 10. Zero-Allocation Rust Attribute / Declaration Scanner (`#[inline(never)]`)
// ===========================================================================

/// Options controlling [`verify_fn_inline_never_source_with_options`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct InlineScanOptions {
    /// When `true`, rejects generic functions (type/const generics or
    /// `impl Trait` parameters), methods inside generic `impl<T>` blocks, and
    /// trait methods / trait default methods.
    pub forbid_polymorphic_or_trait_default: bool,
}

impl InlineScanOptions {
    /// Strict `kani#5095` scan forbidding generic functions and trait default
    /// methods in addition to requiring unconditional `#[inline(never)]`.
    pub const fn strict() -> Self {
        Self {
            forbid_polymorphic_or_trait_default: true,
        }
    }
}

/// Verdict emitted by [`verify_fn_inline_never_source`] and
/// [`verify_fn_inline_never_source_with_options`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InlineBoundaryVerdict {
    /// Every matching `fn <name>` item carries unconditional `#[inline(never)]`,
    /// no forbidden or conflicting inline attributes, and passes policy checks.
    Verified,
    /// No `fn <name>` item was found in the source text.
    TargetFunctionNotFound,
    /// Target `fn <name>` lacks `#[inline(never)]`.
    MissingInlineNever,
    /// Target `fn <name>` carries only conditional `#[cfg_attr(..., inline(never))]`
    /// without an unconditional `#[inline(never)]`.
    ConditionalInlineNever,
    /// Target `fn <name>` carries `#[inline]` or `#[inline(always)]` (or an
    /// unrecognized `#[inline(...)]` hint).
    ForbiddenInlineHint,
    /// Target `fn <name>` carries conflicting `#[inline(never)]` together with
    /// `#[inline]` or `#[inline(always)]`.
    ConflictingInlineAttributes,
    /// Target `fn <name>` is polymorphic (generic type/const parameter or
    /// `impl Trait` argument) or a trait method / trait default method while
    /// [`InlineScanOptions::forbid_polymorphic_or_trait_default`] is enabled.
    ForbiddenPolymorphicOrTraitDefault,
    /// Source contained malformed lexical or delimiter syntax (unterminated
    /// comment, string, char literal, attribute, or unbalanced braces).
    MalformedSource,
}

impl InlineBoundaryVerdict {
    /// Returns `true` iff this verdict is [`Self::Verified`].
    pub const fn is_verified(self) -> bool {
        matches!(self, Self::Verified)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TokenKind<'a> {
    Ident(&'a str),
    Lifetime,
    Literal,
    Punct(u8),
    Arrow,      // ->
    ColonColon, // ::
    HashBang,   // #!
    Eof,
}

#[derive(Clone, Copy, Debug)]
struct Token<'a> {
    kind: TokenKind<'a>,
    end: usize,
}

struct RustLexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
}

fn is_ident_start(ch: char) -> bool {
    ch == '_' || ch.is_alphabetic()
}

fn is_ident_continue(ch: char) -> bool {
    ch == '_' || ch.is_alphanumeric()
}

impl<'a> RustLexer<'a> {
    const fn new(src: &'a str) -> Self {
        Self {
            src,
            bytes: src.as_bytes(),
            pos: 0,
        }
    }

    fn peek_byte(&self, offset: usize) -> Option<u8> {
        self.bytes.get(self.pos.checked_add(offset)?).copied()
    }

    fn skip_ws_and_comments(&mut self) -> Result<(), ()> {
        loop {
            // Skip whitespace (ASCII and Unicode)
            while self.pos < self.bytes.len() {
                let b = self.bytes[self.pos];
                if b.is_ascii_whitespace() {
                    self.pos += 1;
                } else if !b.is_ascii() {
                    let ch = self.src[self.pos..].chars().next().ok_or(())?;
                    if ch.is_whitespace() {
                        self.pos += ch.len_utf8();
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }

            // Line comment `// ...` (includes `///` and `//!` doc comments)
            if self.peek_byte(0) == Some(b'/') && self.peek_byte(1) == Some(b'/') {
                self.pos += 2;
                while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
                    self.pos += 1;
                }
                continue;
            }

            // Nested block comment `/* ... */`
            if self.peek_byte(0) == Some(b'/') && self.peek_byte(1) == Some(b'*') {
                self.pos += 2;
                let mut depth = 1usize;
                while depth > 0 {
                    if self.pos + 1 >= self.bytes.len() {
                        return Err(());
                    }
                    if self.bytes[self.pos] == b'/' && self.bytes[self.pos + 1] == b'*' {
                        depth += 1;
                        self.pos += 2;
                    } else if self.bytes[self.pos] == b'*' && self.bytes[self.pos + 1] == b'/' {
                        depth -= 1;
                        self.pos += 2;
                    } else {
                        self.pos += 1;
                    }
                }
                continue;
            }

            return Ok(());
        }
    }

    /// Consumes a normal quoted string `"..."` with `\` escapes (cursor starts
    /// on opening `"`).
    fn consume_quoted_string(&mut self) -> Result<(), ()> {
        self.pos += 1; // skip opening '"'
        while self.pos < self.bytes.len() {
            match self.bytes[self.pos] {
                b'\\' => {
                    if self.pos + 1 >= self.bytes.len() {
                        return Err(());
                    }
                    self.pos += 2;
                }
                b'"' => {
                    self.pos += 1;
                    return Ok(());
                }
                _ => self.pos += 1,
            }
        }
        Err(())
    }

    /// Consumes a raw string starting at the first `#` or `"` after `r`/`br`/`cr`.
    fn consume_raw_string(&mut self) -> Result<(), ()> {
        let mut hashes = 0usize;
        while self.peek_byte(0) == Some(b'#') {
            hashes += 1;
            self.pos += 1;
        }
        if self.peek_byte(0) != Some(b'"') {
            return Err(());
        }
        self.pos += 1; // skip opening '"'
        while self.pos < self.bytes.len() {
            if self.bytes[self.pos] == b'"' {
                self.pos += 1;
                let mut matched = 0usize;
                while matched < hashes && self.pos + matched < self.bytes.len() {
                    if self.bytes[self.pos + matched] == b'#' {
                        matched += 1;
                    } else {
                        break;
                    }
                }
                if matched == hashes {
                    self.pos += matched;
                    return Ok(());
                }
            } else {
                self.pos += 1;
            }
        }
        Err(())
    }

    /// Checks whether a raw-string prefix (`r`, `br`, `cr`) at `self.pos +
    /// prefix_len` is followed by zero or more `#` and an opening `"`.
    fn is_raw_string_at(&self, prefix_len: usize) -> bool {
        let mut idx = self.pos + prefix_len;
        while idx < self.bytes.len() && self.bytes[idx] == b'#' {
            idx += 1;
        }
        idx < self.bytes.len() && self.bytes[idx] == b'"'
    }

    /// Consumes a char or byte literal after the opening `'` has been checked
    /// (`self.pos` points to `'`).
    fn consume_char_or_byte_literal(&mut self) -> Result<(), ()> {
        self.pos += 1; // skip opening '\''
        if self.pos >= self.bytes.len() {
            return Err(());
        }
        if self.bytes[self.pos] == b'\\' {
            self.pos += 1;
            if self.pos >= self.bytes.len() {
                return Err(());
            }
            // Skip escape body until closing '\''
            let esc = self.bytes[self.pos];
            self.pos += 1;
            if esc == b'u' && self.peek_byte(0) == Some(b'{') {
                while self.pos < self.bytes.len() && self.bytes[self.pos] != b'}' {
                    self.pos += 1;
                }
                if self.pos >= self.bytes.len() {
                    return Err(());
                }
                self.pos += 1; // '}'
            } else if esc == b'x' {
                if self.pos + 2 > self.bytes.len() {
                    return Err(());
                }
                self.pos += 2;
            }
            if self.peek_byte(0) != Some(b'\'') {
                return Err(());
            }
            self.pos += 1;
            return Ok(());
        }

        // Non-escaped single UTF-8 scalar followed immediately by '\''
        let ch = self.src[self.pos..].chars().next().ok_or(())?;
        if ch == '\'' || ch == '\n' || ch == '\r' {
            return Err(());
        }
        self.pos += ch.len_utf8();
        if self.peek_byte(0) != Some(b'\'') {
            return Err(());
        }
        self.pos += 1;
        Ok(())
    }

    fn next_token(&mut self) -> Result<Token<'a>, ()> {
        self.skip_ws_and_comments()?;
        if self.pos >= self.bytes.len() {
            return Ok(Token {
                kind: TokenKind::Eof,
                end: self.pos,
            });
        }

        let start = self.pos;
        let b = self.bytes[self.pos];

        // Normal string literal `"..."`
        if b == b'"' {
            self.consume_quoted_string()?;
            return Ok(Token {
                kind: TokenKind::Literal,
                end: self.pos,
            });
        }

        // Byte / C / Raw string literals & byte char literals
        if (b == b'b' || b == b'c') && self.peek_byte(1) == Some(b'"') {
            self.pos += 1;
            self.consume_quoted_string()?;
            return Ok(Token {
                kind: TokenKind::Literal,
                end: self.pos,
            });
        }
        if b == b'b' && self.peek_byte(1) == Some(b'\'') {
            self.pos += 1;
            self.consume_char_or_byte_literal()?;
            return Ok(Token {
                kind: TokenKind::Literal,
                end: self.pos,
            });
        }
        if (b == b'b' || b == b'c') && self.peek_byte(1) == Some(b'r') && self.is_raw_string_at(2) {
            self.pos += 2;
            self.consume_raw_string()?;
            return Ok(Token {
                kind: TokenKind::Literal,
                end: self.pos,
            });
        }
        if b == b'r' && self.is_raw_string_at(1) {
            self.pos += 1;
            self.consume_raw_string()?;
            return Ok(Token {
                kind: TokenKind::Literal,
                end: self.pos,
            });
        }

        // Raw identifier `r#ident`
        if b == b'r' && self.peek_byte(1) == Some(b'#') {
            if let Some(ch) = self.src.get(self.pos + 2..).and_then(|s| s.chars().next())
                && is_ident_start(ch)
            {
                self.pos += 2 + ch.len_utf8();
                while let Some(c) = self.src[self.pos..].chars().next() {
                    if is_ident_continue(c) {
                        self.pos += c.len_utf8();
                    } else {
                        break;
                    }
                }
                return Ok(Token {
                    kind: TokenKind::Ident(&self.src[start..self.pos]),
                    end: self.pos,
                });
            }
        }

        // Single quote: distinguish char literal `'x'` / `'\''` / `'\u{...}'`
        // from lifetime or loop label `'a` / `'static` / `'_`.
        if b == b'\'' {
            let is_char_lit = if self.peek_byte(1) == Some(b'\\') {
                true
            } else if let Some(ch) = self.src.get(self.pos + 1..).and_then(|s| s.chars().next()) {
                ch != '\''
                    && ch != '\n'
                    && ch != '\r'
                    && self.bytes.get(self.pos + 1 + ch.len_utf8()) == Some(&b'\'')
            } else {
                false
            };

            if is_char_lit {
                self.consume_char_or_byte_literal()?;
                return Ok(Token {
                    kind: TokenKind::Literal,
                    end: self.pos,
                });
            }

            // Lifetime or label: `'` followed by optional `r#` + identifier
            self.pos += 1;
            if self.peek_byte(0) == Some(b'r') && self.peek_byte(1) == Some(b'#') {
                self.pos += 2;
            }
            if let Some(ch) = self.src[self.pos..].chars().next()
                && is_ident_start(ch)
            {
                self.pos += ch.len_utf8();
                while let Some(c) = self.src[self.pos..].chars().next() {
                    if is_ident_continue(c) {
                        self.pos += c.len_utf8();
                    } else {
                        break;
                    }
                }
                return Ok(Token {
                    kind: TokenKind::Lifetime,
                    end: self.pos,
                });
            }
            // Bare lone `'` (malformed char/lifetime)
            return Err(());
        }

        // Numeric literal (consume digits, underscores, `.` only when followed
        // by digit, and identifier suffix so e.g. `0u32` or `1e+5` stays one token)
        if b.is_ascii_digit() {
            self.pos += 1;
            while self.pos < self.bytes.len() {
                let c = self.bytes[self.pos];
                if c.is_ascii_alphanumeric() || c == b'_' {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            return Ok(Token {
                kind: TokenKind::Literal,
                end: self.pos,
            });
        }

        // Identifier (ASCII or Unicode)
        if let Some(ch) = self.src[self.pos..].chars().next()
            && is_ident_start(ch)
        {
            self.pos += ch.len_utf8();
            while let Some(c) = self.src[self.pos..].chars().next() {
                if is_ident_continue(c) {
                    self.pos += c.len_utf8();
                } else {
                    break;
                }
            }
            return Ok(Token {
                kind: TokenKind::Ident(&self.src[start..self.pos]),
                end: self.pos,
            });
        }

        // Multi-char punctuation
        if b == b'-' && self.peek_byte(1) == Some(b'>') {
            self.pos += 2;
            return Ok(Token {
                kind: TokenKind::Arrow,
                end: self.pos,
            });
        }
        if b == b':' && self.peek_byte(1) == Some(b':') {
            self.pos += 2;
            return Ok(Token {
                kind: TokenKind::ColonColon,
                end: self.pos,
            });
        }
        if b == b'#' && self.peek_byte(1) == Some(b'!') {
            self.pos += 2;
            return Ok(Token {
                kind: TokenKind::HashBang,
                end: self.pos,
            });
        }

        // Single-byte ASCII punctuation (or non-ASCII scalar fallback)
        if b.is_ascii() {
            self.pos += 1;
            Ok(Token {
                kind: TokenKind::Punct(b),
                end: self.pos,
            })
        } else {
            let ch = self.src[self.pos..].chars().next().ok_or(())?;
            self.pos += ch.len_utf8();
            Ok(Token {
                kind: TokenKind::Punct(b'?'),
                end: self.pos,
            })
        }
    }

    fn peek_token(&self) -> Result<Token<'a>, ()> {
        let mut clone = RustLexer {
            src: self.src,
            bytes: self.bytes,
            pos: self.pos,
        };
        clone.next_token()
    }

    /// Consumes a balanced delimiter group starting AFTER the opening delimiter
    /// (`open` is `b'('`, `b'['`, or `b'{'`), returning the inner source slice
    /// excluding the closing delimiter.
    fn consume_balanced_inner(&mut self, open: u8) -> Result<&'a str, ()> {
        let close = match open {
            b'(' => b')',
            b'[' => b']',
            b'{' => b'}',
            _ => return Err(()),
        };
        let inner_start = self.pos;
        let mut depth = 1usize;
        while depth > 0 {
            let tok = self.next_token()?;
            match tok.kind {
                TokenKind::Eof => return Err(()),
                TokenKind::Punct(p) if p == open => depth += 1,
                TokenKind::Punct(p) if p == close => {
                    depth -= 1;
                    if depth == 0 {
                        let inner_end = tok.end - 1;
                        return Ok(&self.src[inner_start..inner_end]);
                    }
                }
                _ => {}
            }
        }
        Err(())
    }

    /// Consumes a balanced `<...>` angle-bracket group starting AFTER `<`,
    /// skipping nested `(...)`, `[...]`, `{...}` and not confusing `->` with `>`.
    /// Returns the inner slice excluding the closing `>`.
    fn consume_angle_inner(&mut self) -> Result<&'a str, ()> {
        let inner_start = self.pos;
        let mut depth = 1usize;
        while depth > 0 {
            let tok = self.next_token()?;
            match tok.kind {
                TokenKind::Eof => return Err(()),
                TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
                    let _ = self.consume_balanced_inner(p)?;
                }
                TokenKind::Punct(b'<') => depth += 1,
                TokenKind::Punct(b'>') => {
                    depth -= 1;
                    if depth == 0 {
                        let inner_end = tok.end - 1;
                        return Ok(&self.src[inner_start..inner_end]);
                    }
                }
                _ => {}
            }
        }
        Err(())
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct InlineAttrSummary {
    saw_unconditional_never: bool,
    saw_conditional_never: bool,
    saw_forbidden_inline: bool,
    saw_malformed: bool,
}

impl InlineAttrSummary {
    fn reset(&mut self) {
        *self = Self::default();
    }
}

/// Checks if a `cfg_attr` predicate slice is syntactically `all()` (always true).
fn is_unconditional_cfg_pred(pred: &str) -> bool {
    let mut lex = RustLexer::new(pred);
    let Ok(t0) = lex.next_token() else {
        return false;
    };
    if t0.kind != TokenKind::Ident("all") {
        return false;
    }
    let Ok(t1) = lex.next_token() else {
        return false;
    };
    if t1.kind != TokenKind::Punct(b'(') {
        return false;
    }
    let Ok(inner) = lex.consume_balanced_inner(b'(') else {
        return false;
    };
    let mut inner_lex = RustLexer::new(inner);
    let Ok(ti) = inner_lex.next_token() else {
        return false;
    };
    if ti.kind != TokenKind::Eof {
        return false;
    }
    matches!(lex.next_token(), Ok(Token { kind: TokenKind::Eof, .. }))
}

/// Parses a comma-separated list of meta items inside `#[...]` or the trailing
/// attributes of `#[cfg_attr(pred, ...)]`.
fn analyze_attr_meta_list(
    meta_list: &str,
    unconditional: bool,
    depth: usize,
    summary: &mut InlineAttrSummary,
) {
    if depth > 8 {
        summary.saw_malformed = true;
        return;
    }

    let mut lex = RustLexer::new(meta_list);
    loop {
        let tok = match lex.next_token() {
            Ok(t) => t,
            Err(()) => {
                summary.saw_malformed = true;
                return;
            }
        };
        if tok.kind == TokenKind::Eof {
            break;
        }
        if tok.kind == TokenKind::Punct(b',') {
            continue;
        }

        if let TokenKind::Ident(ident) = tok.kind {
            let next = match lex.peek_token() {
                Ok(t) => t,
                Err(()) => {
                    summary.saw_malformed = true;
                    return;
                }
            };

            if ident == "inline" && next.kind != TokenKind::ColonColon {
                match next.kind {
                    TokenKind::Eof | TokenKind::Punct(b',') => {
                        // Bare `#[inline]`
                        summary.saw_forbidden_inline = true;
                        if next.kind == TokenKind::Punct(b',') {
                            let _ = lex.next_token();
                        }
                        continue;
                    }
                    TokenKind::Punct(b'(') => {
                        let _ = lex.next_token(); // consume '('
                        let Ok(args) = lex.consume_balanced_inner(b'(') else {
                            summary.saw_malformed = true;
                            return;
                        };
                        let mut arg_lex = RustLexer::new(args);
                        let Ok(a0) = arg_lex.next_token() else {
                            summary.saw_malformed = true;
                            return;
                        };
                        let Ok(a1) = arg_lex.next_token() else {
                            summary.saw_malformed = true;
                            return;
                        };
                        if a1.kind != TokenKind::Eof {
                            summary.saw_forbidden_inline = true;
                        } else {
                            match a0.kind {
                                TokenKind::Ident("never") => {
                                    if unconditional {
                                        summary.saw_unconditional_never = true;
                                    } else {
                                        summary.saw_conditional_never = true;
                                    }
                                }
                                TokenKind::Ident("always") => {
                                    summary.saw_forbidden_inline = true;
                                }
                                _ => {
                                    summary.saw_forbidden_inline = true;
                                }
                            }
                        }
                        continue;
                    }
                    _ => {
                        summary.saw_forbidden_inline = true;
                    }
                }
            } else if ident == "cfg_attr" && next.kind == TokenKind::Punct(b'(') {
                let _ = lex.next_token(); // consume '('
                let Ok(args) = lex.consume_balanced_inner(b'(') else {
                    summary.saw_malformed = true;
                    return;
                };
                // Split `args` at the first top-level comma into `(pred, rest)`.
                let mut split_lex = RustLexer::new(args);
                let mut comma_end: Option<usize> = None;
                let mut pred_end: usize = args.len();
                loop {
                    let Ok(st) = split_lex.next_token() else {
                        summary.saw_malformed = true;
                        return;
                    };
                    match st.kind {
                        TokenKind::Eof => break,
                        TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
                            if split_lex.consume_balanced_inner(p).is_err() {
                                summary.saw_malformed = true;
                                return;
                            }
                        }
                        TokenKind::Punct(b',') => {
                            pred_end = st.end - 1;
                            comma_end = Some(st.end);
                            break;
                        }
                        _ => {}
                    }
                }
                if let Some(rest_start) = comma_end {
                    let pred = &args[..pred_end];
                    let rest = &args[rest_start..];
                    let child_unconditional = unconditional && is_unconditional_cfg_pred(pred);
                    analyze_attr_meta_list(rest, child_unconditional, depth + 1, summary);
                }
                continue;
            }
        }

        // Skip the remainder of this non-inline meta item up to the next
        // top-level comma (handling nested groups safely).
        if let TokenKind::Punct(p @ (b'(' | b'[' | b'{')) = tok.kind
            && lex.consume_balanced_inner(p).is_err()
        {
            summary.saw_malformed = true;
            return;
        }
        loop {
            let Ok(st) = lex.next_token() else {
                summary.saw_malformed = true;
                return;
            };
            match st.kind {
                TokenKind::Eof | TokenKind::Punct(b',') => break,
                TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
                    if lex.consume_balanced_inner(p).is_err() {
                        summary.saw_malformed = true;
                        return;
                    }
                }
                _ => {}
            }
        }
    }
}

/// Returns `true` iff a `<...>` generic parameter list contains at least one
/// non-lifetime (type or const) generic parameter.
fn generic_params_contain_type_or_const(inner: &str) -> Result<bool, ()> {
    let mut lex = RustLexer::new(inner);
    let mut at_param_start = true;
    loop {
        let tok = lex.next_token()?;
        match tok.kind {
            TokenKind::Eof => return Ok(false),
            TokenKind::Punct(b',') => {
                at_param_start = true;
            }
            TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
                let _ = lex.consume_balanced_inner(p)?;
            }
            TokenKind::Punct(b'<') => {
                let _ = lex.consume_angle_inner()?;
            }
            TokenKind::Punct(b'#') => {
                // Skip outer attribute on generic parameter e.g. `#[allow(...)] T`
                let next = lex.next_token()?;
                if next.kind != TokenKind::Punct(b'[') {
                    return Err(());
                }
                let _ = lex.consume_balanced_inner(b'[')?;
            }
            TokenKind::Lifetime => {
                at_param_start = false;
            }
            TokenKind::Ident(_) => {
                if at_param_start {
                    // Either `const N: ...` or a type parameter `T`
                    return Ok(true);
                }
            }
            _ => {
                at_param_start = false;
            }
        }
    }
}

/// Returns `true` iff a function parameter list `(...)` contains an `impl Trait`
/// parameter type (syntactic sugar for a generic type parameter).
fn params_contain_impl_trait(params_inner: &str) -> Result<bool, ()> {
    let mut lex = RustLexer::new(params_inner);
    loop {
        let tok = lex.next_token()?;
        match tok.kind {
            TokenKind::Eof => return Ok(false),
            TokenKind::Ident("impl") => return Ok(true),
            TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
                let sub = lex.consume_balanced_inner(p)?;
                if params_contain_impl_trait(sub)? {
                    return Ok(true);
                }
            }
            _ => {}
        }
    }
}

fn fn_ident_matches(ident: &str, target_name: &str) -> bool {
    ident == target_name || ident.strip_prefix("r#") == Some(target_name)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ScopeKind {
    Module,
    Impl { is_generic: bool },
    Trait,
}

const MAX_SCOPE_DEPTH: usize = 32;

/// Pure-`core` (zero-allocation) Rust source scanner verifying that every
/// `fn <fn_name>` item in `source` carries explicit unconditional
/// `#[inline(never)]` without conflicting or forbidden inline hints.
///
/// Uses default [`InlineScanOptions`] (`forbid_polymorphic_or_trait_default:
/// false`), so generic functions with `where` clauses pass when annotated with
/// `#[inline(never)]`. For strict polymorphism/trait-default enforcement, use
/// [`verify_fn_inline_never_source_with_options`].
pub fn verify_fn_inline_never_source(source: &str, fn_name: &str) -> InlineBoundaryVerdict {
    verify_fn_inline_never_source_with_options(source, fn_name, InlineScanOptions::default())
}

/// Pure-`core` (zero-allocation) Rust source scanner with configurable
/// [`InlineScanOptions`].
pub fn verify_fn_inline_never_source_with_options(
    source: &str,
    fn_name: &str,
    options: InlineScanOptions,
) -> InlineBoundaryVerdict {
    if fn_name.is_empty() {
        return InlineBoundaryVerdict::TargetFunctionNotFound;
    }

    let mut lex = RustLexer::new(source);
    let mut scopes: [ScopeKind; MAX_SCOPE_DEPTH] = [ScopeKind::Module; MAX_SCOPE_DEPTH];
    let mut scope_len = 0usize;
    let mut pending = InlineAttrSummary::default();
    let mut matched_count = 0usize;

    loop {
        let tok = match lex.next_token() {
            Ok(t) => t,
            Err(()) => return InlineBoundaryVerdict::MalformedSource,
        };

        match tok.kind {
            TokenKind::Eof => {
                if scope_len != 0 {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                break;
            }
            TokenKind::Punct(b'}') => {
                if scope_len == 0 {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                scope_len -= 1;
                pending.reset();
            }
            // Inner attribute `#![...]` applies to enclosing module/block, NOT next item.
            TokenKind::HashBang => {
                let Ok(next) = lex.next_token() else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                if next.kind != TokenKind::Punct(b'[') {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                if lex.consume_balanced_inner(b'[').is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
            }
            // Outer attribute `#[...]` attaches to the immediately following item.
            TokenKind::Punct(b'#') => {
                let Ok(next) = lex.next_token() else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                if next.kind != TokenKind::Punct(b'[') {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                let Ok(inner) = lex.consume_balanced_inner(b'[') else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                analyze_attr_meta_list(inner, true, 0, &mut pending);
            }
            // Visibility & function qualifiers preserve `pending` outer attributes.
            TokenKind::Ident("pub") => {
                if matches!(lex.peek_token(), Ok(Token { kind: TokenKind::Punct(b'('), .. })) {
                    let _ = lex.next_token();
                    if lex.consume_balanced_inner(b'(').is_err() {
                        return InlineBoundaryVerdict::MalformedSource;
                    }
                }
            }
            TokenKind::Ident("default" | "async" | "unsafe") => {
                // Keep `pending` for `fn`, `trait`, or `impl` (non-fn resets below).
            }
            TokenKind::Ident("const") => {
                // `const fn`, `const unsafe ... fn`, `const extern ... fn` keep `pending`.
                // `const FOO: T = ...;` is a constant item — skip to `;` and reset `pending`.
                let next_kind = match lex.peek_token() {
                    Ok(t) => t.kind,
                    Err(()) => return InlineBoundaryVerdict::MalformedSource,
                };
                if !matches!(
                    next_kind,
                    TokenKind::Ident("fn" | "unsafe" | "extern" | "async")
                ) {
                    pending.reset();
                    if skip_to_semicolon(&mut lex).is_err() {
                        return InlineBoundaryVerdict::MalformedSource;
                    }
                }
            }
            TokenKind::Ident("extern") => {
                // Optional ABI literal: `extern "C"`, `extern "C-unwind"`, etc.
                if matches!(lex.peek_token(), Ok(Token { kind: TokenKind::Literal, .. })) {
                    let _ = lex.next_token();
                }
                let next_kind = match lex.peek_token() {
                    Ok(t) => t.kind,
                    Err(()) => return InlineBoundaryVerdict::MalformedSource,
                };
                match next_kind {
                    TokenKind::Ident("fn") => {
                        // `extern "C" fn ...`: keep `pending`.
                    }
                    TokenKind::Punct(b'{') => {
                        // `extern "C" { ... }` block: descend as module scope.
                        let _ = lex.next_token();
                        pending.reset();
                        if scope_len >= MAX_SCOPE_DEPTH {
                            return InlineBoundaryVerdict::MalformedSource;
                        }
                        scopes[scope_len] = ScopeKind::Module;
                        scope_len += 1;
                    }
                    TokenKind::Ident("crate") => {
                        pending.reset();
                        if skip_to_semicolon(&mut lex).is_err() {
                            return InlineBoundaryVerdict::MalformedSource;
                        }
                    }
                    _ => {
                        pending.reset();
                    }
                }
            }
            // Function item `fn <name> ...`
            TokenKind::Ident("fn") => {
                let Ok(name_tok) = lex.next_token() else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                let TokenKind::Ident(ident) = name_tok.kind else {
                    // Not a named function item (e.g. stray `fn(...)`).
                    pending.reset();
                    continue;
                };

                // Optional `<...>` generic parameters on the fn item.
                let mut fn_is_generic = false;
                if matches!(lex.peek_token(), Ok(Token { kind: TokenKind::Punct(b'<'), .. })) {
                    let _ = lex.next_token();
                    let Ok(gen_inner) = lex.consume_angle_inner() else {
                        return InlineBoundaryVerdict::MalformedSource;
                    };
                    match generic_params_contain_type_or_const(gen_inner) {
                        Ok(is_gen) => fn_is_generic = is_gen,
                        Err(()) => return InlineBoundaryVerdict::MalformedSource,
                    }
                }

                // Mandatory `(...)` parameter list.
                let Ok(lparen) = lex.next_token() else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                if lparen.kind != TokenKind::Punct(b'(') {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                let Ok(params_inner) = lex.consume_balanced_inner(b'(') else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                let has_impl_trait_param = match params_contain_impl_trait(params_inner) {
                    Ok(v) => v,
                    Err(()) => return InlineBoundaryVerdict::MalformedSource,
                };

                // Advance past optional `-> RetTy` and `where ...` clause until
                // body `{ ... }` or terminating `;`.
                if skip_fn_signature_tail_and_body(&mut lex).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }

                if fn_ident_matches(ident, fn_name) {
                    matched_count += 1;

                    if pending.saw_malformed {
                        return InlineBoundaryVerdict::MalformedSource;
                    }
                    if pending.saw_forbidden_inline
                        && (pending.saw_unconditional_never || pending.saw_conditional_never)
                    {
                        return InlineBoundaryVerdict::ConflictingInlineAttributes;
                    }
                    if pending.saw_forbidden_inline {
                        return InlineBoundaryVerdict::ForbiddenInlineHint;
                    }
                    if !pending.saw_unconditional_never {
                        if pending.saw_conditional_never {
                            return InlineBoundaryVerdict::ConditionalInlineNever;
                        }
                        return InlineBoundaryVerdict::MissingInlineNever;
                    }

                    if options.forbid_polymorphic_or_trait_default {
                        let in_trait =
                            scope_len > 0 && scopes[scope_len - 1] == ScopeKind::Trait;
                        let in_generic_impl = scope_len > 0
                            && matches!(
                                scopes[scope_len - 1],
                                ScopeKind::Impl { is_generic: true }
                            );
                        if in_trait || in_generic_impl || fn_is_generic || has_impl_trait_param {
                            return InlineBoundaryVerdict::ForbiddenPolymorphicOrTraitDefault;
                        }
                    }
                }

                pending.reset();
            }
            // Module item: `mod foo;` or `mod foo { ... }`
            TokenKind::Ident("mod") => {
                pending.reset();
                let Ok(name_tok) = lex.next_token() else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                if !matches!(name_tok.kind, TokenKind::Ident(_)) {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                let Ok(next) = lex.next_token() else {
                    return InlineBoundaryVerdict::MalformedSource;
                };
                match next.kind {
                    TokenKind::Punct(b';') => {}
                    TokenKind::Punct(b'{') => {
                        if scope_len >= MAX_SCOPE_DEPTH {
                            return InlineBoundaryVerdict::MalformedSource;
                        }
                        scopes[scope_len] = ScopeKind::Module;
                        scope_len += 1;
                    }
                    _ => return InlineBoundaryVerdict::MalformedSource,
                }
            }
            // Trait item: `trait Name ... { ... }`
            TokenKind::Ident("trait") => {
                pending.reset();
                if skip_until_open_brace(&mut lex).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                if scope_len >= MAX_SCOPE_DEPTH {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                scopes[scope_len] = ScopeKind::Trait;
                scope_len += 1;
            }
            // Impl item: `impl<...> ... { ... }`
            TokenKind::Ident("impl") => {
                pending.reset();
                let mut impl_is_generic = false;
                if matches!(lex.peek_token(), Ok(Token { kind: TokenKind::Punct(b'<'), .. })) {
                    let _ = lex.next_token();
                    let Ok(gen_inner) = lex.consume_angle_inner() else {
                        return InlineBoundaryVerdict::MalformedSource;
                    };
                    match generic_params_contain_type_or_const(gen_inner) {
                        Ok(is_gen) => impl_is_generic = is_gen,
                        Err(()) => return InlineBoundaryVerdict::MalformedSource,
                    }
                }
                if skip_until_open_brace(&mut lex).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                if scope_len >= MAX_SCOPE_DEPTH {
                    return InlineBoundaryVerdict::MalformedSource;
                }
                scopes[scope_len] = ScopeKind::Impl {
                    is_generic: impl_is_generic,
                };
                scope_len += 1;
            }
            // Non-function item keywords reset `pending` and skip their item body.
            TokenKind::Ident("struct" | "enum" | "union") => {
                pending.reset();
                if skip_type_decl(&mut lex).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
            }
            TokenKind::Ident("use" | "type" | "static") => {
                pending.reset();
                if skip_to_semicolon(&mut lex).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
            }
            TokenKind::Ident("macro_rules") => {
                pending.reset();
                if skip_macro_invocation_tail(&mut lex).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
            }
            TokenKind::Ident(_) => {
                // Path-qualified or local macro invocation `foo!(...)` / `a::b!{...}`.
                pending.reset();
                if skip_path_or_macro_item(&mut lex).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
            }
            TokenKind::Punct(b';') => {
                pending.reset();
            }
            TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
                pending.reset();
                if lex.consume_balanced_inner(p).is_err() {
                    return InlineBoundaryVerdict::MalformedSource;
                }
            }
            _ => {
                pending.reset();
            }
        }
    }

    if matched_count == 0 {
        InlineBoundaryVerdict::TargetFunctionNotFound
    } else {
        InlineBoundaryVerdict::Verified
    }
}

fn skip_to_semicolon(lex: &mut RustLexer<'_>) -> Result<(), ()> {
    loop {
        let tok = lex.next_token()?;
        match tok.kind {
            TokenKind::Eof => return Err(()),
            TokenKind::Punct(b';') => return Ok(()),
            TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
                let _ = lex.consume_balanced_inner(p)?;
            }
            _ => {}
        }
    }
}

fn skip_until_open_brace(lex: &mut RustLexer<'_>) -> Result<(), ()> {
    loop {
        let tok = lex.next_token()?;
        match tok.kind {
            TokenKind::Eof => return Err(()),
            TokenKind::Punct(b'{') => return Ok(()),
            TokenKind::Punct(p @ (b'(' | b'[')) => {
                let _ = lex.consume_balanced_inner(p)?;
            }
            TokenKind::Punct(b'<') => {
                let _ = lex.consume_angle_inner()?;
            }
            _ => {}
        }
    }
}

fn skip_type_decl(lex: &mut RustLexer<'_>) -> Result<(), ()> {
    loop {
        let tok = lex.next_token()?;
        match tok.kind {
            TokenKind::Eof => return Err(()),
            TokenKind::Punct(b';') => return Ok(()),
            TokenKind::Punct(b'{') => {
                let _ = lex.consume_balanced_inner(b'{')?;
                return Ok(());
            }
            TokenKind::Punct(p @ (b'(' | b'[')) => {
                let _ = lex.consume_balanced_inner(p)?;
            }
            TokenKind::Punct(b'<') => {
                let _ = lex.consume_angle_inner()?;
            }
            _ => {}
        }
    }
}

fn skip_fn_signature_tail_and_body(lex: &mut RustLexer<'_>) -> Result<(), ()> {
    loop {
        let tok = lex.next_token()?;
        match tok.kind {
            TokenKind::Eof => return Err(()),
            TokenKind::Punct(b';') => return Ok(()),
            TokenKind::Punct(b'{') => {
                let _ = lex.consume_balanced_inner(b'{')?;
                return Ok(());
            }
            TokenKind::Punct(p @ (b'(' | b'[')) => {
                let _ = lex.consume_balanced_inner(p)?;
            }
            TokenKind::Punct(b'<') => {
                let _ = lex.consume_angle_inner()?;
            }
            _ => {}
        }
    }
}

fn skip_macro_invocation_tail(lex: &mut RustLexer<'_>) -> Result<(), ()> {
    let bang = lex.next_token()?;
    if bang.kind != TokenKind::Punct(b'!') {
        return Err(());
    }
    // Optional macro name for `macro_rules! name { ... }`
    if matches!(lex.peek_token()?, Token { kind: TokenKind::Ident(_), .. }) {
        let _ = lex.next_token()?;
    }
    let delim = lex.next_token()?;
    match delim.kind {
        TokenKind::Punct(p @ (b'(' | b'[' | b'{')) => {
            let _ = lex.consume_balanced_inner(p)?;
            if p != b'{'
                && matches!(lex.peek_token()?, Token { kind: TokenKind::Punct(b';'), .. })
            {
                let _ = lex.next_token()?;
            }
            Ok(())
        }
        _ => Err(()),
    }
}

fn skip_path_or_macro_item(lex: &mut RustLexer<'_>) -> Result<(), ()> {
    loop {
        let tok = lex.peek_token()?;
        match tok.kind {
            TokenKind::ColonColon => {
                let _ = lex.next_token()?;
                let seg = lex.next_token()?;
                if !matches!(seg.kind, TokenKind::Ident(_)) {
                    return Err(());
                }
            }
            TokenKind::Punct(b'!') => {
                return skip_macro_invocation_tail(lex);
            }
            TokenKind::Punct(b';') => {
                let _ = lex.next_token()?;
                return Ok(());
            }
            TokenKind::Eof | TokenKind::Punct(b'}') => return Ok(()),
            _ => {
                let _ = lex.next_token()?;
                return Ok(());
            }
        }
    }
}

// ===========================================================================
// 11. Structured MIR CFG & Multi-Hop Call-Boundary Verifiers
//     (Mirroring Episode 1's `Anneal.PanicContracts` §6–§7)
// ===========================================================================

/// Fixed maximum basic-block count supported by zero-allocation stack BFS.
/// Any CFG exceeding `MAX_MIR_BLOCKS` fails closed with
/// [`CallBoundaryVerdict::CfgExceedsCapacity`].
pub const MAX_MIR_BLOCKS: usize = 256;

/// Lightweight summary of a single MIR basic block for `kani#5095`
/// call-boundary verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MirBlockSummary<'a> {
    /// Direct callee `DefPath` if this block ends in a direct `call` or
    /// `tailCall` to a constant function item; `None` otherwise.
    pub direct_call_target: Option<&'a str>,
    /// Static CFG successor basic-block indices (normal targets, switch
    /// targets, and `UnwindAction::Cleanup(bb)` target).
    pub successors: &'a [usize],
}

impl<'a> MirBlockSummary<'a> {
    /// Constructs a generic basic-block summary.
    pub const fn new(direct_call_target: Option<&'a str>, successors: &'a [usize]) -> Self {
        Self {
            direct_call_target,
            successors,
        }
    }

    /// Constructs a basic block ending in a direct `call` to `target`.
    pub const fn call(target: &'a str, successors: &'a [usize]) -> Self {
        Self {
            direct_call_target: Some(target),
            successors,
        }
    }

    /// Constructs a basic block ending in a direct `tailCall` to `target`
    /// (zero intra-body CFG successors, matching Lean `terminatorSuccessors`).
    pub const fn tail_call(target: &'a str) -> Self {
        Self {
            direct_call_target: Some(target),
            successors: &[],
        }
    }

    /// Constructs a non-calling branching/goto/assert basic block.
    pub const fn branch(successors: &'a [usize]) -> Self {
        Self {
            direct_call_target: None,
            successors,
        }
    }

    /// Constructs a terminal return/unreachable/unwind basic block.
    pub const fn ret() -> Self {
        Self {
            direct_call_target: None,
            successors: &[],
        }
    }
}

/// Entry in the linked/inlineable callee table (`mem.callees` / `callees`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CalleeEntry<'a> {
    /// Canonical `DefPath` of this linked callee body.
    pub def_path: &'a str,
    /// Basic-block CFG summary of this callee's body.
    pub blocks: &'a [MirBlockSummary<'a>],
    /// Trait implementations carried by this linked callee body.
    pub trait_impls: &'a [TraitImplBinding<'a>],
}

impl<'a> CalleeEntry<'a> {
    /// Constructs a linked callee entry with no local trait implementations.
    pub const fn new(def_path: &'a str, blocks: &'a [MirBlockSummary<'a>]) -> Self {
        Self {
            def_path,
            blocks,
            trait_impls: &[],
        }
    }

    /// Constructs a linked callee entry carrying `trait_impls`.
    pub const fn with_trait_impls(
        def_path: &'a str,
        blocks: &'a [MirBlockSummary<'a>],
        trait_impls: &'a [TraitImplBinding<'a>],
    ) -> Self {
        Self {
            def_path,
            blocks,
            trait_impls,
        }
    }
}

/// Trait-method dispatch entry (`mem.traitImpls` / `TraitImplEntry`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TraitImplBinding<'a> {
    /// Trait method `DefPath` intercepted by trait dispatch.
    pub trait_method_path: &'a str,
    /// Concrete implementation `DefPath` dispatched to.
    pub impl_def_path: &'a str,
}

impl<'a> TraitImplBinding<'a> {
    /// Constructs a trait-implementation dispatch binding.
    pub const fn new(trait_method_path: &'a str, impl_def_path: &'a str) -> Self {
        Self {
            trait_method_path,
            impl_def_path,
        }
    }
}

/// Structured verdict returned by the `kani#5095` MIR call-boundary verifiers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallBoundaryVerdict {
    /// All requested boundary invariants hold.
    Preserved {
        observed_call_sites: usize,
        reachable_blocks: usize,
    },
    /// `target_path` is present in the inlineable `callees` table.
    TargetInCalleeTable,
    /// `target_path` is dispatched by a [`TraitImplBinding`] on the caller or a
    /// linked callee.
    TargetDispatchedByTraitImpl,
    /// The trait-implementation table changed across a sequential external call
    /// (violating `withTraitsPreserved`, enabling multi-call trait injection).
    TraitTableMutatedAcrossCall,
    /// No syntactic direct call site to `target_path` exists in the caller.
    MissingCallSite,
    /// Syntactic direct call-site count did not equal `expected`.
    CallSiteCountMismatch { expected: usize, observed: usize },
    /// No CFG-reachable (from `bb0`) direct call site to `target_path` exists
    /// (catches unreachable dead decoy call blocks).
    NoReachableCallSite { syntactic_call_sites: usize },
    /// CFG-reachable direct call-site count did not equal `expected`.
    ReachableCallSiteCountMismatch {
        expected: usize,
        observed_reachable: usize,
        observed_syntactic: usize,
    },
    /// Caller or intermediate hop failed to reach the next hop in
    /// `helper_chain`.
    BrokenCallChainLink { hop_index: usize },
    /// Intermediate hop in `helper_chain` is missing from `callees`.
    MissingChainHopBody { hop_index: usize },
    /// Intermediate hop in `helper_chain` is overridden by a
    /// [`TraitImplBinding`] (violating `ChainHopsNotTraitDispatched`).
    ChainHopTraitDispatched { hop_index: usize },
    /// CFG basic-block count exceeds fixed stack capacity [`MAX_MIR_BLOCKS`].
    CfgExceedsCapacity {
        block_count: usize,
        max_blocks: usize,
    },
    /// Caller or hop CFG has zero basic blocks where a reachable call is needed.
    EmptyCfg,
}

impl CallBoundaryVerdict {
    /// Returns `true` iff this verdict is [`Self::Preserved`].
    pub const fn is_preserved(self) -> bool {
        matches!(self, Self::Preserved { .. })
    }
}

fn has_trait_impl_for_path(
    caller_trait_impls: &[TraitImplBinding<'_>],
    callees: &[CalleeEntry<'_>],
    def_path: &str,
) -> bool {
    if caller_trait_impls
        .iter()
        .any(|t| t.trait_method_path == def_path)
    {
        return true;
    }
    callees.iter().any(|c| {
        c.trait_impls
            .iter()
            .any(|t| t.trait_method_path == def_path)
    })
}

fn check_tables_exclude(
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    target_path: &str,
    check_traits: bool,
) -> Option<CallBoundaryVerdict> {
    if callees.iter().any(|c| c.def_path == target_path) {
        return Some(CallBoundaryVerdict::TargetInCalleeTable);
    }
    if check_traits && has_trait_impl_for_path(caller_trait_impls, callees, target_path) {
        return Some(CallBoundaryVerdict::TargetDispatchedByTraitImpl);
    }
    None
}

/// Fixed-capacity stack BFS computing CFG-reachable basic blocks from `bb0`.
///
/// Mirrors Lean's `Anneal.PanicContracts.reachableBlocks`: out-of-bounds
/// successor indices are safely ignored, cycles are handled in $O(V + E)$ via
/// a stack bitset, and graphs with `blocks.len() > MAX_MIR_BLOCKS` fail closed.
fn compute_reachable_bitset(
    blocks: &[MirBlockSummary<'_>],
) -> Result<([u64; MAX_MIR_BLOCKS / 64], usize), CallBoundaryVerdict> {
    if blocks.len() > MAX_MIR_BLOCKS {
        return Err(CallBoundaryVerdict::CfgExceedsCapacity {
            block_count: blocks.len(),
            max_blocks: MAX_MIR_BLOCKS,
        });
    }
    let mut visited = [0u64; MAX_MIR_BLOCKS / 64];
    if blocks.is_empty() {
        return Ok((visited, 0));
    }

    let mut queue = [0usize; MAX_MIR_BLOCKS];
    let mut head = 0usize;
    let mut tail = 1usize;
    visited[0] |= 1u64;
    let mut count = 1usize;

    while head < tail {
        let cur = queue[head];
        head += 1;
        for &next in blocks[cur].successors {
            if next >= blocks.len() {
                continue;
            }
            let word = next / 64;
            let bit = 1u64 << (next % 64);
            if (visited[word] & bit) == 0 {
                visited[word] |= bit;
                queue[tail] = next;
                tail += 1;
                count += 1;
            }
        }
    }

    Ok((visited, count))
}

const fn bitset_contains(visited: &[u64; MAX_MIR_BLOCKS / 64], idx: usize) -> bool {
    (visited[idx / 64] & (1u64 << (idx % 64))) != 0
}

fn count_syntactic_call_sites(blocks: &[MirBlockSummary<'_>], target_path: &str) -> usize {
    blocks
        .iter()
        .filter(|bb| bb.direct_call_target == Some(target_path))
        .count()
}

fn count_reachable_call_sites(
    blocks: &[MirBlockSummary<'_>],
    visited: &[u64; MAX_MIR_BLOCKS / 64],
    target_path: &str,
) -> usize {
    blocks
        .iter()
        .enumerate()
        .filter(|&(idx, bb)| {
            bitset_contains(visited, idx) && bb.direct_call_target == Some(target_path)
        })
        .count()
}

/// Verifies `CalleeTableExcludes`: `target_path` is absent from both `callees`
/// and all trait-implementation tables (`caller_trait_impls` plus every
/// callee's `trait_impls`).
pub fn verify_callee_table_excludes(
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    target_path: &str,
) -> CallBoundaryVerdict {
    if let Some(err) = check_tables_exclude(callees, caller_trait_impls, target_path, true) {
        return err;
    }
    CallBoundaryVerdict::Preserved {
        observed_call_sites: 0,
        reachable_blocks: 0,
    }
}

/// Verifies `withTraitsPreserved` across sequential external calls: checks that
/// `before_trait_impls == after_trait_impls` (preventing Call 1 from injecting
/// a trait dispatch entry that silently inlines Call 2) and that
/// [`verify_callee_table_excludes`] still holds for `target_path`.
pub fn verify_traits_preserved(
    before_trait_impls: &[TraitImplBinding<'_>],
    after_trait_impls: &[TraitImplBinding<'_>],
    callees: &[CalleeEntry<'_>],
    target_path: &str,
) -> CallBoundaryVerdict {
    if before_trait_impls != after_trait_impls {
        return CallBoundaryVerdict::TraitTableMutatedAcrossCall;
    }
    verify_callee_table_excludes(callees, after_trait_impls, target_path)
}

/// Verifies syntactic `CallBoundaryPreserved`: at least one direct call site to
/// `target_path` exists in `caller_blocks`, and `target_path` is excluded from
/// `callees` and trait-dispatch tables.
pub fn verify_call_boundary(
    caller_blocks: &[MirBlockSummary<'_>],
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    target_path: &str,
) -> CallBoundaryVerdict {
    if let Some(err) = check_tables_exclude(callees, caller_trait_impls, target_path, true) {
        return err;
    }
    let observed = count_syntactic_call_sites(caller_blocks, target_path);
    if observed == 0 {
        return CallBoundaryVerdict::MissingCallSite;
    }
    CallBoundaryVerdict::Preserved {
        observed_call_sites: observed,
        reachable_blocks: caller_blocks.len(),
    }
}

/// Verifies counted syntactic `CallSitesPreserved`: `caller_blocks` contains
/// **exact** `expected_call_sites` direct calls to `target_path` (catching
/// partial 1-of-2 inlining) and `target_path` is excluded from `callees` and
/// trait-dispatch tables.
pub fn verify_counted_call_sites(
    caller_blocks: &[MirBlockSummary<'_>],
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    target_path: &str,
    expected_call_sites: usize,
) -> CallBoundaryVerdict {
    if let Some(err) = check_tables_exclude(callees, caller_trait_impls, target_path, true) {
        return err;
    }
    let observed = count_syntactic_call_sites(caller_blocks, target_path);
    if observed != expected_call_sites {
        return CallBoundaryVerdict::CallSiteCountMismatch {
            expected: expected_call_sites,
            observed,
        };
    }
    CallBoundaryVerdict::Preserved {
        observed_call_sites: observed,
        reachable_blocks: caller_blocks.len(),
    }
}

/// Verifies `ReachableCallBoundaryPreserved`: at least one `bb0`-reachable
/// direct call site to `target_path` exists in `caller_blocks` (rejecting
/// unreachable dead decoy call blocks), and `target_path` is excluded from
/// `callees` and trait-dispatch tables.
pub fn verify_reachable_call_boundary(
    caller_blocks: &[MirBlockSummary<'_>],
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    target_path: &str,
) -> CallBoundaryVerdict {
    if let Some(err) = check_tables_exclude(callees, caller_trait_impls, target_path, true) {
        return err;
    }
    if caller_blocks.is_empty() {
        return CallBoundaryVerdict::EmptyCfg;
    }
    let (visited, reachable_blocks) = match compute_reachable_bitset(caller_blocks) {
        Ok(res) => res,
        Err(err) => return err,
    };
    let reachable_sites = count_reachable_call_sites(caller_blocks, &visited, target_path);
    if reachable_sites == 0 {
        return CallBoundaryVerdict::NoReachableCallSite {
            syntactic_call_sites: count_syntactic_call_sites(caller_blocks, target_path),
        };
    }
    CallBoundaryVerdict::Preserved {
        observed_call_sites: reachable_sites,
        reachable_blocks,
    }
}

fn verify_reachable_call_sites_inner(
    caller_blocks: &[MirBlockSummary<'_>],
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    target_path: &str,
    expected_call_sites: usize,
    check_traits: bool,
) -> CallBoundaryVerdict {
    if let Some(err) = check_tables_exclude(callees, caller_trait_impls, target_path, check_traits)
    {
        return err;
    }
    let (visited, reachable_blocks) = match compute_reachable_bitset(caller_blocks) {
        Ok(res) => res,
        Err(err) => return err,
    };
    let reachable_sites = count_reachable_call_sites(caller_blocks, &visited, target_path);
    if reachable_sites != expected_call_sites {
        return CallBoundaryVerdict::ReachableCallSiteCountMismatch {
            expected: expected_call_sites,
            observed_reachable: reachable_sites,
            observed_syntactic: count_syntactic_call_sites(caller_blocks, target_path),
        };
    }
    CallBoundaryVerdict::Preserved {
        observed_call_sites: reachable_sites,
        reachable_blocks,
    }
}

/// Verifies `ReachableCallSitesPreserved`: exact `expected_call_sites`
/// `bb0`-reachable direct call sites to `target_path` exist in `caller_blocks`,
/// and `target_path` is excluded from `callees` and trait-dispatch tables.
pub fn verify_reachable_call_sites(
    caller_blocks: &[MirBlockSummary<'_>],
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    target_path: &str,
    expected_call_sites: usize,
) -> CallBoundaryVerdict {
    verify_reachable_call_sites_inner(
        caller_blocks,
        callees,
        caller_trait_impls,
        target_path,
        expected_call_sites,
        true,
    )
}

/// Verifies arbitrary-length multi-hop helper call-chain boundary preservation
/// (`caller -> helper_chain[0] -> ... -> helper_chain[k-1] -> target_path`),
/// mirroring Episode 1's `CallChainCallBoundaryPreserved` **together with**
/// `ChainHopsNotTraitDispatched`:
///
/// 1. `target_path` is excluded from `callees` and all trait-dispatch tables.
/// 2. No intermediate hop in `helper_chain` is overridden by any
///    [`TraitImplBinding`] on the caller or on any linked callee.
/// 3. Each step from `caller_blocks` through `helper_chain` to `target_path`
///    has a `bb0`-reachable direct call site in its body and every intermediate
///    hop resolves via `callees` (first match, mirroring Lean `findCallee?`).
pub fn verify_call_chain_boundary(
    caller_blocks: &[MirBlockSummary<'_>],
    callees: &[CalleeEntry<'_>],
    caller_trait_impls: &[TraitImplBinding<'_>],
    helper_chain: &[&str],
    target_path: &str,
) -> CallBoundaryVerdict {
    if let Some(err) = check_tables_exclude(callees, caller_trait_impls, target_path, true) {
        return err;
    }

    // `ChainHopsNotTraitDispatched`: reject any intermediate hop overridden in
    // `caller_trait_impls ++ flatMap(callees, c.trait_impls)`.
    for (hop_index, &hop_path) in helper_chain.iter().enumerate() {
        if has_trait_impl_for_path(caller_trait_impls, callees, hop_path) {
            return CallBoundaryVerdict::ChainHopTraitDispatched { hop_index };
        }
    }

    let mut current_blocks = caller_blocks;
    let mut total_reachable_blocks = 0usize;

    for (hop_index, &hop_path) in helper_chain.iter().enumerate() {
        if current_blocks.is_empty() {
            return CallBoundaryVerdict::EmptyCfg;
        }
        let (visited, reachable_blocks) = match compute_reachable_bitset(current_blocks) {
            Ok(res) => res,
            Err(err) => return err,
        };
        total_reachable_blocks = total_reachable_blocks.saturating_add(reachable_blocks);

        if count_reachable_call_sites(current_blocks, &visited, hop_path) == 0 {
            return CallBoundaryVerdict::BrokenCallChainLink { hop_index };
        }

        let Some(next_entry) = callees.iter().find(|c| c.def_path == hop_path) else {
            return CallBoundaryVerdict::MissingChainHopBody { hop_index };
        };
        current_blocks = next_entry.blocks;
    }

    if current_blocks.is_empty() {
        return CallBoundaryVerdict::EmptyCfg;
    }
    let (visited, reachable_blocks) = match compute_reachable_bitset(current_blocks) {
        Ok(res) => res,
        Err(err) => return err,
    };
    total_reachable_blocks = total_reachable_blocks.saturating_add(reachable_blocks);

    let terminal_sites = count_reachable_call_sites(current_blocks, &visited, target_path);
    if terminal_sites == 0 {
        return CallBoundaryVerdict::NoReachableCallSite {
            syntactic_call_sites: count_syntactic_call_sites(current_blocks, target_path),
        };
    }

    CallBoundaryVerdict::Preserved {
        observed_call_sites: terminal_sites,
        reachable_blocks: total_reachable_blocks,
    }
}

// ===========================================================================
// 12. Internal Unit Tests (`extern crate std;` strictly under `#[cfg(test)]`)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abort_policy_kind_canonical_roundtrip() {
        for kind in AbortPolicyKind::ALL {
            let name = kind.canonical_name();
            assert_eq!(AbortPolicyKind::from_canonical_name(name), Some(kind));
        }
        assert_eq!(AbortPolicyKind::ForbidAbort.canonical_name(), "forbidAbort");
        assert_eq!(AbortPolicyKind::AbortOnlyIf.canonical_name(), "abortOnlyIf");
        assert_eq!(
            AbortPolicyKind::WaiveAbortUnchecked.canonical_name(),
            "waiveAbortUnchecked"
        );
        assert_eq!(AbortPolicyKind::from_canonical_name("ForbidAbort"), None);
    }

    #[test]
    fn panic_failure_class_canonical_roundtrip() {
        for class in PanicFailureClass::ALL {
            let name = class.canonical_name();
            assert_eq!(PanicFailureClass::from_canonical_name(name), Some(class));
        }
        assert_eq!(PanicFailureClass::from_canonical_name("Unknown"), None);
        assert_eq!(
            PanicFailureClass::DeadPrecondition.to_vacuity_class(),
            Some(VacuityClass::DeadPrecondition)
        );
        assert_eq!(
            PanicFailureClass::UbOrFaultOnExecution.to_vacuity_class(),
            Some(VacuityClass::SpecViolation)
        );
        assert_eq!(
            PanicFailureClass::TrivialNormalPostcondition.to_vacuity_class(),
            Some(VacuityClass::TrivialPostcondition)
        );
        assert_eq!(
            PanicFailureClass::UnboundNormalReturnOutput.to_vacuity_class(),
            Some(VacuityClass::UnboundReturnOutput)
        );
        assert_eq!(
            PanicFailureClass::SurvivedAllNormalMutants.to_vacuity_class(),
            Some(VacuityClass::SurvivedAllMutants)
        );
        assert_eq!(
            PanicFailureClass::SurvivedGuardMutant.to_vacuity_class(),
            None
        );
    }

    #[test]
    fn unwind_macros_compile_and_run_inside_no_std_unit_tests() {
        let cfg = PanicCheckConfig::default().with_max_trials(128);
        let stats = crate::assert_panic_contract_strong_unwind!(
            cfg,
            PanicContractMode::Exact,
            |&(_a, _b): &(u8, u8)| true,
            |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > u8::MAX as u16,
            |&(a, b): &(u8, u8)| a.checked_add(b).expect("u8 overflow"),
            |&(a, b): &(u8, u8), &out: &u8| out == a + b,
        );
        assert!(stats.observed_panics > 0);
        assert!(stats.normal_returns > 0);
        assert!(stats.normal_mutants_killed > 0);
    }

    #[test]
    fn cfg_bfs_handles_cycles_and_out_of_bounds_successors() {
        let blocks = [
            MirBlockSummary::branch(&[1, 999]), // 999 is out of bounds -> ignored
            MirBlockSummary::call("crate::target", &[0, 1]), // cycle back to 0 and self-loop
        ];
        let verdict = verify_reachable_call_boundary(&blocks, &[], &[], "crate::target");
        assert_eq!(
            verdict,
            CallBoundaryVerdict::Preserved {
                observed_call_sites: 1,
                reachable_blocks: 2,
            }
        );
    }

    #[test]
    fn cfg_exceeding_capacity_fails_closed() {
        let blocks = [MirBlockSummary::ret(); MAX_MIR_BLOCKS + 1];
        let verdict = verify_reachable_call_boundary(&blocks, &[], &[], "crate::target");
        assert_eq!(
            verdict,
            CallBoundaryVerdict::CfgExceedsCapacity {
                block_count: MAX_MIR_BLOCKS + 1,
                max_blocks: MAX_MIR_BLOCKS,
            }
        );
    }
}
