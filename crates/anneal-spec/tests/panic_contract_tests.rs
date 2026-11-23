// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for `anneal_spec::panic_contract` exercising real
//! `std::panic::catch_unwind` execution, `#[spec]`/`#[embed_spec]`/`#[invariant]`
//! companions, `impl_spec_check_struct!`, all 17 `PanicFailureClass` variants,
//! Stage P3a/P3b mutant killing, stateful pre-panic `&mut` mutation guards,
//! deterministic replay, and `kani#5095` source/CFG call-boundary verifiers.

use anneal_spec::panic_contract::{
    AbortPolicy, AbortPolicyKind, CallBoundaryGuard, CallBoundaryVerdict, CalleeEntry,
    ExactPanicContract, InlineBoundaryVerdict, InlineScanOptions, MAX_MIR_BLOCKS,
    MirBlockSummary, NeverPanics, PanicCheckConfig, PanicContractMode, PanicExecOutcome,
    PanicFailureClass, PanicFailureDetail, PanicGuardMutant, PanicTrapKind, PanicsIf,
    PanicsOnlyIf, StatefulPanicContractSpec, TraitImplBinding, assert_panic_contract_strong,
    check_panic_contract, check_panic_contract_fallible, check_panic_guard_mutants,
    check_stateful_panic_contract_fallible, check_stateful_panic_guard_mutants, forbid_abort,
    forbid_abort_fallible, forbid_stateful_abort, invoke_boundary_guarded,
    invoke_stateful_boundary_guarded, replay_panic_trial_input,
    replay_stateful_panic_trial_input, verify_call_boundary, verify_call_chain_boundary,
    verify_callee_table_excludes, verify_counted_call_sites, verify_fn_inline_never_source,
    verify_fn_inline_never_source_with_options, verify_reachable_call_boundary,
    verify_reachable_call_sites, verify_traits_preserved, waive_abort_unchecked,
};
use anneal_spec::spec_check::{
    KILL_FREE_OVERSCAN, ProbeDomain, SpecCheckConfig, SplitMix64, SyntacticBindingHint,
};
use anneal_spec::*;

// ===========================================================================
// Test Fixtures
// ===========================================================================

#[inline(never)]
fn checked_add_u8(a: u8, b: u8) -> u8 {
    let sum = (a as u16) + (b as u16);
    assert!(sum <= u8::MAX as u16, "u8 addition overflow");
    sum as u8
}

#[inline(never)]
fn checked_div_u32(dividend: u32, divisor: u32) -> u32 {
    assert!(divisor != 0, "division by zero");
    dividend / divisor
}

#[inline(never)]
fn checked_slice_index(arr: [u8; 4], idx: usize) -> u8 {
    arr[idx]
}

#[spec(
    pure,
    total,
    requires: [a < 100, b < 100],
    ensures: |out| out == a + b,
)]
#[inline(never)]
fn spec_total_add_u32(a: u32, b: u32) -> u32 {
    a + b
}

#[embed_spec(
    pure,
    requires: divisor <= 1_000,
    ensures: |out| divisor != 0 && out == dividend / divisor,
)]
#[inline(never)]
fn embed_spec_checked_div(dividend: u32, divisor: u32) -> u32 {
    assert!(divisor != 0, "divisor must be nonzero");
    dividend / divisor
}

/// Custom non-`Copy` struct with an `#[invariant]` companion and
/// `impl_spec_check_struct!`. Capacity `3` aligns with `u8`'s deterministic
/// boundary corpus (`0, 1, 2, 3`), guaranteeing both empty (`len == 0`),
/// normal (`len in 1..3`), and full (`len == 3`) hits on every seed.
#[derive(Clone, Debug, PartialEq, Eq)]
#[invariant(self.len <= 3)]
struct BoundedStack {
    slots: [u8; 3],
    len: u8,
}

impl_spec_check_struct!(BoundedStack {
    slots: [u8; 3],
    len: u8,
});

impl BoundedStack {
    #[inline(never)]
    fn push_safe(&mut self, val: u8) -> u8 {
        assert!((self.len as usize) < self.slots.len(), "stack overflow");
        let idx = self.len as usize;
        self.slots[idx] = val;
        self.len += 1;
        self.len
    }

    #[inline(never)]
    fn push_corrupting(&mut self, val: u8) -> u8 {
        // Hazard (`kani#4230`): mutates `&mut self` BEFORE panicking!
        self.len = self.len.wrapping_add(1);
        assert!((self.len as usize) <= self.slots.len(), "stack overflow");
        let idx = (self.len - 1) as usize;
        self.slots[idx] = val;
        self.len
    }

    #[inline(never)]
    fn pop_safe(&mut self) -> u8 {
        assert!(self.len > 0, "stack underflow");
        self.len -= 1;
        self.slots[self.len as usize]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[invariant(self.lo <= self.hi)]
struct RangePair {
    lo: u8,
    hi: u8,
}

impl_spec_check_struct!(RangePair { lo: u8, hi: u8 });

#[inline(never)]
fn checked_range_span(pair: &RangePair) -> u8 {
    assert!(pair.lo < pair.hi, "degenerate empty range");
    pair.hi - pair.lo
}

// ===========================================================================
// 1. Positive Panic-Contract Tests (`Exact`, `OnlyIf`, `If`, `NeverPanics`)
// ===========================================================================

#[test]
fn positive_exact_checked_add_u8_with_catch_unwind() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    let stats = assert_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&(_a, _b): &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > u8::MAX as u16,
        |&(a, b): &(u8, u8)| invoke_boundary_guarded((a, b), |(x, y)| checked_add_u8(x, y)),
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
    );

    assert_eq!(stats.trials_run, 256);
    assert_eq!(stats.precondition_hits, 256);
    assert!(stats.observed_panics > 0);
    assert!(stats.normal_returns > 0);
    assert_eq!(stats.observed_aborts, 0);
    assert!(stats.is_normal_branch_pointwise_strong());

    // Also test via typed wrapper `ExactPanicContract`.
    let outcome = ExactPanicContract::new(
        |&(_a, _b): &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > u8::MAX as u16,
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
    )
    .check(cfg, panic_unwind_runner!(|&(a, b): &(u8, u8)| checked_add_u8(a, b)));
    assert!(outcome.is_strong());
}

#[test]
fn positive_exact_checked_div_u32_and_embed_spec_companions() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    let stats = assert_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&(dividend, divisor): &(u32, u32)| __anodized_fn_requires_embed_spec_checked_div(dividend, divisor),
        |&(_dividend, divisor): &(u32, u32)| divisor == 0,
        |&(dividend, divisor): &(u32, u32)| embed_spec_checked_div(dividend, divisor),
        |&(dividend, divisor): &(u32, u32), &out: &u32| {
            __anodized_fn_ensures_embed_spec_checked_div(dividend, divisor, out)
        },
    );
    assert!(stats.observed_panics > 0);
    assert!(stats.normal_returns > 0);
    assert!(stats.normal_mutants_killed > 0);

    // Direct standalone checked_div_u32 with PanicsOnlyIf & PanicsIf wrappers.
    let only_if = PanicsOnlyIf::new(
        |&(_n, _d): &(u32, u32)| true,
        |&(_n, d): &(u32, u32)| d == 0,
        |&(n, d): &(u32, u32), &q: &u32| d != 0 && q == n / d,
    )
    .check(cfg, panic_unwind_runner!(|&(n, d): &(u32, u32)| checked_div_u32(n, d)));
    assert!(only_if.is_strong());

    let panics_if = PanicsIf::new(
        |&(_n, _d): &(u32, u32)| true,
        |&(_n, d): &(u32, u32)| d == 0,
    )
    .check(cfg, panic_unwind_runner!(|&(n, d): &(u32, u32)| checked_div_u32(n, d)));
    assert!(panics_if.is_strong());
}

#[test]
fn positive_exact_bounds_checked_array_slice_access() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);
    let stats = assert_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&(_arr, _idx): &([u8; 4], usize)| true,
        |&(_arr, idx): &([u8; 4], usize)| idx >= 4,
        |&(arr, idx): &([u8; 4], usize)| checked_slice_index(arr, idx),
        |&(arr, idx): &([u8; 4], usize), &out: &u8| out == arr[idx],
    );
    assert!(stats.observed_panics > 0);
    assert!(stats.normal_returns > 0);
    assert!(stats.normal_mutants_killed > 0);
}

#[test]
fn positive_never_panics_bridges_total_spec_companions() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);
    let outcome = NeverPanics::new(
        |&(a, b): &(u32, u32)| __anodized_fn_requires_spec_total_add_u32(a, b),
        |&(a, b): &(u32, u32), &out: &u32| __anodized_fn_ensures_spec_total_add_u32(a, b, out),
    )
    .check(cfg, panic_unwind_runner!(|&(a, b): &(u32, u32)| spec_total_add_u32(a, b)));
    let stats = outcome.into_result().expect("NeverPanics contract must be strong");
    assert_eq!(stats.observed_panics, 0);
    assert_eq!(stats.panic_cond_hits, 0);
    assert!(stats.normal_returns > 0);
    assert!(stats.normal_mutants_killed > 0);
}

#[test]
fn positive_dual_panic_and_abort_policy_exact_and_only_if() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    // Region 1: x == 0 -> Aborted (e.g., fatal `-C panic=abort` nounwind check)
    // Region 2: x > 200 -> Panicked (unwinding panic)
    // Region 3: 1..=200 -> Returned(x * 2)
    let dual_body = |&x: &u8| -> PanicExecOutcome<u16> {
        if x == 0 {
            PanicExecOutcome::Aborted
        } else if x > 200 {
            PanicExecOutcome::Panicked
        } else {
            PanicExecOutcome::Returned((x as u16) * 2)
        }
    };

    let exact_dual = ExactPanicContract::new(
        |&_x: &u8| true,
        |&x: &u8| x > 200,
        |&x: &u8, &out: &u16| out == (x as u16) * 2,
    )
    .with_abort_only_if(|&x: &u8| x == 0)
    .check(cfg, dual_body);

    let stats = exact_dual.into_result().expect("dual panic+abort exact contract should pass");
    assert!(stats.observed_panics > 0);
    assert!(stats.observed_aborts > 0);
    assert!(stats.normal_returns > 0);
    assert!(stats.normal_mutants_killed > 0);

    // `OnlyIf` with explicit `WaiveAbortUnchecked` accepts aborts on any input.
    let waived = PanicsOnlyIf::new(
        |&_x: &u8| true,
        |&x: &u8| x > 200,
        |&x: &u8, &out: &u16| out == (x as u16) * 2,
    )
    .with_waive_abort_unchecked::<u8>()
    .check(cfg, dual_body);
    assert!(waived.is_strong());
}

#[test]
fn positive_custom_struct_with_invariant_and_stateful_bounded_stack() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    // Stateless custom struct using `#[invariant]` companion in `pre`.
    let range_stats = assert_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::Exact,
        |pair: &RangePair| pair.__anneal_type_invariant_range_pair(),
        |pair: &RangePair| pair.lo == pair.hi,
        |pair: &RangePair| checked_range_span(pair),
        |pair: &RangePair, &span: &u8| span == pair.hi - pair.lo && span > 0,
    );
    assert!(range_stats.observed_panics > 0);
    assert!(range_stats.normal_returns > 0);

    // Stateful non-`Copy` `BoundedStack::push_safe` with rollback invariant.
    let push_stats = assert_stateful_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::Exact,
        |s: &BoundedStack, _val: &u8| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _val: &u8| s.len == 3,
        |s: &mut BoundedStack, &val: &u8| {
            invoke_stateful_boundary_guarded(s, val, |st, v| st.push_safe(v))
        },
        |old_s: &BoundedStack, &val: &u8, new_s: &BoundedStack, &new_len: &u8| {
            new_s.__anneal_type_invariant_bounded_stack()
                && new_s.len == old_s.len + 1
                && new_len == new_s.len
                && new_s.slots[old_s.len as usize] == val
                && (0..old_s.len as usize).all(|i| new_s.slots[i] == old_s.slots[i])
        },
        |old_s: &BoundedStack, panicked_s: &BoundedStack| {
            panicked_s == old_s && panicked_s.__anneal_type_invariant_bounded_stack()
        },
    );
    assert!(push_stats.observed_panics > 0);
    assert!(push_stats.panic_state_inv_checks == push_stats.observed_panics);
    assert!(push_stats.normal_returns > 0);

    // Stateful `BoundedStack::pop_safe`.
    let pop_outcome = StatefulPanicContractSpec::exact::<BoundedStack, ()>(
        |s: &BoundedStack, _args: &()| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _args: &()| s.len == 0,
        |old_s: &BoundedStack, _args: &(), new_s: &BoundedStack, &popped: &u8| {
            new_s.__anneal_type_invariant_bounded_stack()
                && new_s.len + 1 == old_s.len
                && popped == old_s.slots[(old_s.len - 1) as usize]
                && new_s.slots == old_s.slots
        },
    )
    .with_panic_state_inv(|old_s: &BoundedStack, panicked_s: &BoundedStack| panicked_s == old_s)
    .check(
        cfg,
        stateful_panic_unwind_runner!(|s: &mut BoundedStack, _args: &()| s.pop_safe()),
    );
    assert!(pop_outcome.is_strong());
}

// ===========================================================================
// 2. Negative Soundness, Policy & Vacuity Refutations (All 17 Failure Classes)
// ===========================================================================

#[test]
fn negative_ub_or_fault_rejected_even_when_panic_or_abort_cond_is_true() {
    let cfg = PanicCheckConfig::default().with_max_trials(128);

    // UB on an input where `panic_cond == true` MUST still fail immediately!
    let outcome = check_panic_contract(
        cfg,
        PanicContractMode::Exact,
        |&_x: &u8| true,
        |&x: &u8| x >= 100,
        forbid_abort(),
        |&x: &u8| {
            if x == 128 {
                PanicExecOutcome::UbOrFault
            } else if x >= 100 {
                PanicExecOutcome::Panicked
            } else {
                PanicExecOutcome::Returned(x)
            }
        },
        |&x: &u8, &out: &u8| out == x,
    );
    let failure = outcome.failure().expect("UB on panic path must fail");
    assert_eq!(failure.class, PanicFailureClass::UbOrFaultOnExecution);
    let trial = failure.counterexample_trial().expect("must record trial");
    assert_eq!(replay_panic_trial_input::<u8>(cfg, trial), Some(128));

    // UB on an input where `abort_cond == true` MUST also fail immediately!
    let abort_ub = check_panic_contract(
        cfg,
        PanicContractMode::OnlyIf,
        |&_x: &u8| true,
        |&x: &u8| x > 200,
        AbortPolicy::AbortOnlyIf(|&x: &u8| x == 0),
        |&x: &u8| {
            if x == 0 {
                PanicExecOutcome::UbOrFault
            } else if x > 200 {
                PanicExecOutcome::Panicked
            } else {
                PanicExecOutcome::Returned(x)
            }
        },
        |&x: &u8, &out: &u8| out == x,
    );
    assert_eq!(
        abort_ub.failure_class(),
        Some(PanicFailureClass::UbOrFaultOnExecution)
    );
}

#[test]
fn negative_dead_conditions_and_dead_normal_branch() {
    let cfg = PanicCheckConfig::default().with_max_trials(128);

    // 1. DeadPrecondition
    let dead_pre = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&x: &u8| x > 100 && x < 50,
        |&x: &u8| x == 0,
        |&x: &u8| x,
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        dead_pre.failure_class(),
        Some(PanicFailureClass::DeadPrecondition)
    );

    // Degenerate config: max_trials == 0
    let zero_trials = check_panic_contract(
        cfg.with_max_trials(0),
        PanicContractMode::Exact,
        |&_x: &u8| true,
        |&x: &u8| x == 0,
        forbid_abort(),
        |&x: &u8| PanicExecOutcome::Returned(x),
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        zero_trials.failure_class(),
        Some(PanicFailureClass::DeadPrecondition)
    );
    assert_eq!(
        zero_trials.failure().unwrap().detail,
        PanicFailureDetail::DegenerateConfig
    );

    // 2. DeadPanicCondition
    let dead_panic = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&x: &u8| x < 100,
        |&x: &u8| x >= 200,
        |&x: &u8| x,
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        dead_panic.failure_class(),
        Some(PanicFailureClass::DeadPanicCondition)
    );

    // 3. DeadAbortCondition
    let dead_abort = ExactPanicContract::new(
        |&x: &u8| x < 200,
        |&x: &u8| x > 100,
        |&x: &u8, &r: &u8| r == x,
    )
    .with_abort_only_if(|&x: &u8| x >= 250)
    .check(
        cfg,
        |&x: &u8| {
            if x > 100 {
                PanicExecOutcome::Panicked
            } else {
                PanicExecOutcome::Returned(x)
            }
        },
    );
    assert_eq!(
        dead_abort.failure_class(),
        Some(PanicFailureClass::DeadAbortCondition)
    );

    // 4. DeadNormalBranch (default `require_normal_hits_in_exact = true`)
    let dead_normal = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&_x: &u8| true,
        |&_x: &u8| true,
        |&_x: &u8| -> u8 { panic!("always panics") },
        |&_x: &u8, &_r: &u8| true,
    );
    assert_eq!(
        dead_normal.failure_class(),
        Some(PanicFailureClass::DeadNormalBranch)
    );

    // Opting out of normal hits in Exact passes cleanly for always-panicking fn.
    let always_panics_ok = check_panic_contract_unwind!(
        cfg.with_require_normal_hits_in_exact(false),
        PanicContractMode::Exact,
        |&_x: &u8| true,
        |&_x: &u8| true,
        |&_x: &u8| -> u8 { panic!("always panics") },
        |&_x: &u8, &_r: &u8| true,
    );
    assert!(always_panics_ok.is_strong());
}

#[test]
fn negative_overlapping_panic_abort_and_waive_abort_in_exact_mode() {
    let cfg = PanicCheckConfig::default().with_max_trials(128);

    // Overlapping panic_cond and abort_cond in Exact mode.
    let overlap = ExactPanicContract::new(
        |&_x: &u8| true,
        |&x: &u8| x >= 10,
        |&x: &u8, &r: &u8| r == x,
    )
    .with_abort_only_if(|&x: &u8| x == 16)
    .check(cfg, |&x: &u8| {
        if x == 16 {
            PanicExecOutcome::Aborted
        } else if x >= 10 {
            PanicExecOutcome::Panicked
        } else {
            PanicExecOutcome::Returned(x)
        }
    });
    let fail = overlap.failure().expect("overlapping conditions must fail");
    assert_eq!(
        fail.class,
        PanicFailureClass::OverlappingPanicAndAbortConditions
    );
    let trial = fail.counterexample_trial().unwrap();
    assert_eq!(replay_panic_trial_input::<u8>(cfg, trial), Some(16));

    // WaiveAbortUnchecked rejected in Exact mode.
    let waive_exact = ExactPanicContract::new(
        |&_x: &u8| true,
        |&x: &u8| x > 100,
        |&x: &u8, &r: &u8| r == x,
    )
    .with_waive_abort_unchecked::<u8>()
    .check(cfg, |&x: &u8| PanicExecOutcome::Returned(x));
    assert_eq!(
        waive_exact.failure_class(),
        Some(PanicFailureClass::WaiveAbortIncompatibleWithExactContract)
    );
    assert_eq!(
        waive_exact.failure().unwrap().detail,
        PanicFailureDetail::WaiveAbortInExactMode
    );

    // Also via raw `check_panic_contract`
    let waive_raw = check_panic_contract(
        cfg,
        PanicContractMode::Exact,
        |&_x: &u8| true,
        |&x: &u8| x > 100,
        waive_abort_unchecked(),
        |&x: &u8| PanicExecOutcome::Returned(x),
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        waive_raw.failure_class(),
        Some(PanicFailureClass::WaiveAbortIncompatibleWithExactContract)
    );
}

#[test]
fn negative_unexpected_and_missed_panics_and_aborts() {
    let cfg = PanicCheckConfig::default().with_max_trials(128);

    // UnexpectedPanic under Exact
    let unexp_panic = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&_x: &u8| true,
        |&x: &u8| x > 200,
        |&x: &u8| {
            assert!(x < 100, "unexpected extra panic");
            x
        },
        |&x: &u8, &r: &u8| r == x,
    );
    let f = unexp_panic.failure().unwrap();
    assert_eq!(f.class, PanicFailureClass::UnexpectedPanic);
    let x_ce = replay_panic_trial_input::<u8>(cfg, f.counterexample_trial().unwrap()).unwrap();
    assert!((100..=200).contains(&x_ce));

    // UnexpectedPanic under NeverPanics
    let never_panics_viol = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::NeverPanics,
        |&_x: &u8| true,
        |&_x: &u8| false,
        |&x: &u8| {
            assert!(x != 42);
            x
        },
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        never_panics_viol.failure_class(),
        Some(PanicFailureClass::UnexpectedPanic)
    );

    // UnexpectedAbort under ForbidAbort (even on panic_cond == true)
    let unexp_abort_forbid = check_panic_contract(
        cfg,
        PanicContractMode::OnlyIf,
        |&_x: &u8| true,
        |&x: &u8| x > 100,
        forbid_abort(),
        |&x: &u8| {
            if x > 100 {
                PanicExecOutcome::Aborted
            } else {
                PanicExecOutcome::Returned(x)
            }
        },
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        unexp_abort_forbid.failure_class(),
        Some(PanicFailureClass::UnexpectedAbort)
    );

    // UnexpectedAbort under AbortOnlyIf when abort_cond == false
    let unexp_abort_cond = ExactPanicContract::new(
        |&_x: &u8| true,
        |&x: &u8| x > 200,
        |&x: &u8, &r: &u8| r == x,
    )
    .with_abort_only_if(|&x: &u8| x == 0)
    .check(cfg, |&x: &u8| {
        if x == 0 || x == 1 {
            PanicExecOutcome::Aborted
        } else if x > 200 {
            PanicExecOutcome::Panicked
        } else {
            PanicExecOutcome::Returned(x)
        }
    });
    assert_eq!(
        unexp_abort_cond.failure_class(),
        Some(PanicFailureClass::UnexpectedAbort)
    );

    // MissedExpectedPanic (dropped `assert!`)
    let missed_panic = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&(_a, _b): &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > 255,
        |&(a, b): &(u8, u8)| a.wrapping_add(b),
        |&(a, b): &(u8, u8), &r: &u8| r == a + b,
    );
    let mp = missed_panic.failure().unwrap();
    assert_eq!(mp.class, PanicFailureClass::MissedExpectedPanic);
    let (a, b) = replay_panic_trial_input::<(u8, u8)>(cfg, mp.counterexample_trial().unwrap()).unwrap();
    assert!((a as u16) + (b as u16) > 255);

    // MissedExpectedAbort (returned normally instead of aborting)
    let missed_abort = ExactPanicContract::new(
        |&_x: &u8| true,
        |&x: &u8| x > 200,
        |&x: &u8, &r: &u8| r == x,
    )
    .with_abort_only_if(|&x: &u8| x == 0)
    .check(cfg, |&x: &u8| {
        if x > 200 {
            PanicExecOutcome::Panicked
        } else {
            PanicExecOutcome::Returned(x)
        }
    });
    assert_eq!(
        missed_abort.failure_class(),
        Some(PanicFailureClass::MissedExpectedAbort)
    );

    // NormalPostconditionViolation
    let post_viol = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&_x: &u8| true,
        |&x: &u8| x > 200,
        |&x: &u8| {
            assert!(x <= 200);
            x.wrapping_add(1)
        },
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        post_viol.failure_class(),
        Some(PanicFailureClass::NormalPostconditionViolation)
    );

    // Predicate trap in `pre`, `panic_cond`, and live `post`
    let pre_trap = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&x: &u8| -> bool {
            assert!(x != 1, "pre trapped");
            true
        },
        |&x: &u8| x > 200,
        |&x: &u8| x,
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        pre_trap.failure().unwrap().detail,
        PanicFailureDetail::PredicateTrapped {
            trial_idx: 1,
            trap: PanicTrapKind::PreconditionPanicked,
        }
    );
}

#[test]
fn domain_safety_never_calls_predicates_outside_their_domain() {
    let cfg = PanicCheckConfig::default()
        .with_max_trials(128)
        .with_probe_domain(ProbeDomain::PreconditionOnly);

    // 1. Strong contract where `panic_cond`, `abort_cond`, and `post` panic if
    //    ever called outside their domain (`!pre`, or `post` on a panicking/aborting input).
    let strong = check_panic_contract(
        cfg,
        PanicContractMode::Exact,
        |&x: &u8| x < 100,
        |&x: &u8| {
            assert!(x < 100, "panic_cond called outside pre!");
            x >= 50
        },
        AbortPolicy::AbortOnlyIf(|&x: &u8| {
            assert!(x < 100, "abort_cond called outside pre!");
            x == 0
        }),
        |&x: &u8| {
            if x == 0 {
                PanicExecOutcome::Aborted
            } else if x >= 50 {
                PanicExecOutcome::Panicked
            } else {
                PanicExecOutcome::Returned(x * 2)
            }
        },
        |&x: &u8, &r: &u8| {
            assert!(x < 100, "post called outside pre!");
            assert!(x != 0, "post called on aborting input!");
            assert!(x < 50, "post called on panicking input!");
            r == x * 2
        },
    );
    assert!(strong.is_strong());

    // 2. Even when Stage P3a classification probes run (`mutants_killed == 0`),
    //    `PreconditionOnly` NEVER calls `panic_cond` outside `pre` and NEVER
    //    calls `post` outside `pre && !panic_cond && !abort_cond`!
    let trivial_probe = check_panic_contract(
        cfg,
        PanicContractMode::Exact,
        |&x: &u8| x < 100,
        |&x: &u8| {
            assert!(x < 100, "panic_cond called outside pre during probe!");
            x >= 50
        },
        AbortPolicy::AbortOnlyIf(|&x: &u8| {
            assert!(x < 100, "abort_cond called outside pre during probe!");
            x == 0
        }),
        |&x: &u8| {
            if x == 0 {
                PanicExecOutcome::Aborted
            } else if x >= 50 {
                PanicExecOutcome::Panicked
            } else {
                PanicExecOutcome::Returned(x)
            }
        },
        |&x: &u8, &_r: &u8| {
            assert!(x < 100, "post called outside pre during probe!");
            assert!(x != 0, "post called on aborting input during probe!");
            assert!(x < 50, "post called on panicking input during probe!");
            true
        },
    );
    assert_eq!(
        trivial_probe.failure_class(),
        Some(PanicFailureClass::TrivialNormalPostcondition)
    );
    match trivial_probe.failure().unwrap().detail {
        PanicFailureDetail::AllNormalMutantsSurvived {
            out_of_normal_domain_probes,
            skipped_out_of_normal_domain,
            ..
        } => {
            assert_eq!(out_of_normal_domain_probes, 0);
            assert!(skipped_out_of_normal_domain > 0);
        }
        other => panic!("unexpected detail: {other:?}"),
    }
}

#[test]
fn trapping_postcondition_on_wrong_mutant_output_counts_as_kill() {
    let cfg = PanicCheckConfig::default().with_max_trials(128);
    // `post` indexes into a fixed 4-element table using the return value, so
    // any perturbed mutant `r >= 4` panics! Under fallible/unwind execution,
    // that trap must count as rejecting the mutant without crashing the test.
    let table = [10u8, 20, 30, 40];
    let stats = assert_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&x: &u8| x < 8,
        |&x: &u8| x >= 4,
        |&x: &u8| {
            assert!(x < 4);
            x
        },
        |&x: &u8, &r: &u8| table[r as usize] == table[x as usize],
    );
    assert!(stats.normal_mutants_killed > 0);
    assert!(stats.normal_mutants_trapped > 0);
}

#[test]
fn normal_branch_vacuity_detection_and_kill_free_overscan() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    // 1. TrivialNormalPostcondition (`|_, _| true`)
    let trivial = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |&x: &u8| x < 100,
        |&x: &u8| x >= 80,
        |&x: &u8| {
            assert!(x < 80);
            x
        },
        |&_x: &u8, &_r: &u8| true,
    );
    assert_eq!(
        trivial.failure_class(),
        Some(PanicFailureClass::TrivialNormalPostcondition)
    );

    // 2. UnboundNormalReturnOutput (input-only postcondition under Unconstrained probe)
    let unbound = check_panic_contract_unwind!(
        cfg.with_probe_domain(ProbeDomain::Unconstrained),
        PanicContractMode::Exact,
        |&x: &u8| x < 80,
        |&x: &u8| x >= 60,
        |&x: &u8| {
            assert!(x < 60);
            x
        },
        |&x: &u8, &_r: &u8| x < 100,
    );
    assert_eq!(
        unbound.failure_class(),
        Some(PanicFailureClass::UnboundNormalReturnOutput)
    );

    // Syntactic hint override
    let hinted_unbound = check_panic_contract_unwind!(
        cfg.with_syntactic_hint(SyntacticBindingHint::ReturnUnused),
        PanicContractMode::Exact,
        |&x: &u8| x < 80,
        |&x: &u8| x >= 60,
        |&x: &u8| {
            assert!(x < 60);
            x
        },
        |&_x: &u8, &_r: &u8| true,
    );
    assert_eq!(
        hinted_unbound.failure_class(),
        Some(PanicFailureClass::UnboundNormalReturnOutput)
    );

    // 3. SurvivedAllNormalMutants (`x < 10 || r == 42` is vacuously satisfied on
    //    `pre && !panic_cond` = `x < 10`, yet genuinely depends on `r` outside!)
    let survived_all = check_panic_contract_unwind!(
        cfg.with_probe_domain(ProbeDomain::Unconstrained),
        PanicContractMode::Exact,
        |&x: &u8| x < 20,
        |&x: &u8| x >= 10,
        |&x: &u8| {
            assert!(x < 10);
            x
        },
        |&x: &u8, &r: &u8| x < 10 || r == 42,
    );
    assert_eq!(
        survived_all.failure_class(),
        Some(PanicFailureClass::SurvivedAllNormalMutants)
    );

    // 4. KILL_FREE_OVERSCAN verification: with tight `max_mutants_per_hit == 1`,
    //    `Option<u8>::visit_mutants` emits `Some(m)` FIRST (which survives
    //    `r.is_some()`), and `None` SECOND (which kills `r.is_some()`).
    //    Overscan ensures the hit does not stop at 1 and finds the kill!
    assert!(KILL_FREE_OVERSCAN >= 1);
    let overscan_ok = assert_panic_contract_strong_unwind!(
        cfg.with_max_mutants_per_hit(1),
        PanicContractMode::Exact,
        |&x: &u8| x < 100,
        |&x: &u8| x >= 80,
        |&x: &u8| -> Option<u8> {
            assert!(x < 80);
            Some(x)
        },
        |&_x: &u8, r: &Option<u8>| r.is_some(),
    );
    assert!(overscan_ok.normal_mutants_killed > 0);
    assert!(overscan_ok.is_normal_branch_pointwise_strong());

    // 5. Degenerate `max_mutants_per_hit == 0` fails closed.
    let zero_mut = check_panic_contract_unwind!(
        cfg.with_max_mutants_per_hit(0),
        PanicContractMode::Exact,
        |&x: &u8| x < 100,
        |&x: &u8| x >= 80,
        |&x: &u8| {
            assert!(x < 80);
            x
        },
        |&x: &u8, &r: &u8| r == x,
    );
    assert_eq!(
        zero_mut.failure_class(),
        Some(PanicFailureClass::SurvivedAllNormalMutants)
    );
    assert_eq!(
        zero_mut.failure().unwrap().detail,
        PanicFailureDetail::DegenerateConfig
    );
}

#[test]
fn stateful_pre_panic_mutation_hazard_caught_by_panic_state_inv() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    // `push_corrupting` increments `self.len` BEFORE asserting capacity, leaving
    // `panicked_s.len == 4 > 3` (violating both rollback `panicked_s == old_s`
    // and type invariant `panicked_s.len <= 3`)!
    let corrupt_outcome = check_stateful_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |s: &BoundedStack, _val: &u8| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _val: &u8| s.len == 3,
        |s: &mut BoundedStack, &val: &u8| s.push_corrupting(val),
        |old_s: &BoundedStack, &val: &u8, new_s: &BoundedStack, &new_len: &u8| {
            new_s.__anneal_type_invariant_bounded_stack()
                && new_s.len == old_s.len + 1
                && new_len == new_s.len
                && new_s.slots[old_s.len as usize] == val
        },
        |old_s: &BoundedStack, panicked_s: &BoundedStack| {
            panicked_s == old_s && panicked_s.__anneal_type_invariant_bounded_stack()
        },
    );
    let fail = corrupt_outcome
        .failure()
        .expect("pre-panic state corruption must be caught");
    assert_eq!(fail.class, PanicFailureClass::PanicStateInvariantViolation);
    let trial = fail.counterexample_trial().expect("must report trial");
    let (ce_stack, _ce_val) =
        replay_stateful_panic_trial_input::<BoundedStack, u8>(cfg, trial).unwrap();
    assert_eq!(ce_stack.len, 3);

    // Stateful normal-branch dual-axis check: a postcondition ignoring `new_s`
    // is caught even when `ret` kills mutants.
    let unbound_state = check_stateful_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |s: &BoundedStack, _val: &u8| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _val: &u8| s.len == 3,
        |s: &mut BoundedStack, &val: &u8| s.push_safe(val),
        |old_s: &BoundedStack, _val: &u8, _new_s: &BoundedStack, &new_len: &u8| {
            new_len == old_s.len + 1
        },
    );
    assert_eq!(
        unbound_state.failure_class(),
        Some(PanicFailureClass::UnboundNormalReturnOutput)
    );
    assert!(matches!(
        unbound_state.failure().unwrap().detail,
        PanicFailureDetail::StatefulNormalAxisUnconstrained {
            state_mutants_killed: 0,
            ..
        }
    ));
}

#[test]
fn stage_p3b_guard_mutant_kill_suite_stateless_and_stateful() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    // Four realistic behavioral/guard mutants of `checked_add_u8`:
    let mutants = [
        panic_guard_mutant_unwind!("dropped_overflow_guard", |&(a, b): &(u8, u8)| {
            a.wrapping_add(b)
        }),
        panic_guard_mutant_unwind!("off_by_one_strict_lt_255", |&(a, b): &(u8, u8)| {
            let sum = (a as u16) + (b as u16);
            assert!(sum < u8::MAX as u16, "too tight by 1");
            sum as u8
        }),
        panic_guard_mutant_unwind!("unexpected_zero_panic", |&(a, b): &(u8, u8)| {
            assert!(a != 0 || b != 0, "spurious panic on (0,0)");
            checked_add_u8(a, b)
        }),
        panic_guard_mutant_unwind!("wrong_normal_return", |&(a, b): &(u8, u8)| {
            checked_add_u8(a, b).wrapping_sub(1)
        }),
    ];

    // 1. ExactPanicContract kills ALL 4 mutants!
    let strong_res = ExactPanicContract::new(
        |&(_a, _b): &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > u8::MAX as u16,
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
    )
    .check_guard_mutants(
        cfg,
        panic_unwind_runner!(|&(a, b): &(u8, u8)| checked_add_u8(a, b)),
        &mutants,
    );
    let stats = strong_res
        .into_result()
        .expect("ExactPanicContract must kill all 4 guard mutants");
    assert_eq!(stats.guard_mutants_tested, 4);
    assert_eq!(stats.guard_mutants_killed, 4);

    // 2. Weak `OnlyIf` (`panic_cond: true`, wrapping postcondition) fails Stage
    //    P3b with `SurvivedGuardMutant` on mutant #0 (`dropped_overflow_guard`)!
    let weak_res = PanicsOnlyIf::new(
        |&(_a, _b): &(u8, u8)| true,
        |&(_a, _b): &(u8, u8)| true,
        |&(a, b): &(u8, u8), &out: &u8| out == a.wrapping_add(b),
    )
    .check_guard_mutants(
        cfg,
        panic_unwind_runner!(|&(a, b): &(u8, u8)| checked_add_u8(a, b)),
        &mutants,
    );
    let weak_fail = weak_res
        .failure()
        .expect("weak OnlyIf must fail because dropped_overflow_guard survives");
    assert_eq!(weak_fail.class, PanicFailureClass::SurvivedGuardMutant);
    assert!(matches!(
        weak_fail.detail,
        PanicFailureDetail::GuardMutantSurvived {
            mutant_idx: 0,
            mutant_name: "dropped_overflow_guard",
            ..
        }
    ));

    // 3. Empty mutant slice fails closed (`NoGuardMutantsProvided`).
    let empty_muts: [PanicGuardMutant<'_, (u8, u8), u8>; 0] = [];
    let empty_res = check_panic_guard_mutants(
        cfg,
        PanicContractMode::Exact,
        |&(_a, _b): &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > u8::MAX as u16,
        forbid_abort(),
        panic_unwind_runner!(|&(a, b): &(u8, u8)| checked_add_u8(a, b)),
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
        &empty_muts,
    );
    assert_eq!(
        empty_res.failure_class(),
        Some(PanicFailureClass::SurvivedGuardMutant)
    );
    assert_eq!(
        empty_res.failure().unwrap().detail,
        PanicFailureDetail::NoGuardMutantsProvided
    );

    // 4. Stateful Stage P3b mutant-kill suite kills dropped guard, wrong return,
    //    AND pre-panic state corruption (`push_corrupting`).
    let stateful_mutants = [
        stateful_panic_guard_mutant_unwind!("corrupts_state_before_panic", |s: &mut BoundedStack, &val: &u8| {
            s.push_corrupting(val)
        }),
        stateful_panic_guard_mutant_unwind!("saturating_no_panic", |s: &mut BoundedStack, &val: &u8| {
            if (s.len as usize) < s.slots.len() {
                s.push_safe(val)
            } else {
                s.len
            }
        }),
        stateful_panic_guard_mutant_unwind!("wrong_return_len", |s: &mut BoundedStack, &val: &u8| {
            s.push_safe(val).wrapping_sub(1)
        }),
    ];
    let stateful_kill = check_stateful_panic_guard_mutants(
        cfg,
        PanicContractMode::Exact,
        |s: &BoundedStack, _val: &u8| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _val: &u8| s.len == 3,
        forbid_stateful_abort(),
        stateful_panic_unwind_runner!(|s: &mut BoundedStack, &val: &u8| s.push_safe(val)),
        |old_s: &BoundedStack, &val: &u8, new_s: &BoundedStack, &new_len: &u8| {
            new_s.__anneal_type_invariant_bounded_stack()
                && new_s.len == old_s.len + 1
                && new_len == new_s.len
                && new_s.slots[old_s.len as usize] == val
        },
        Some(|old_s: &BoundedStack, panicked_s: &BoundedStack| panicked_s == old_s),
        &stateful_mutants,
    );
    let sk_stats = stateful_kill
        .into_result()
        .expect("stateful Exact + panic_state_inv must kill all 3 stateful mutants");
    assert_eq!(sk_stats.guard_mutants_tested, 3);
    assert_eq!(sk_stats.guard_mutants_killed, 3);
}

// ===========================================================================
// 3. `kani#5095` Source Attribute Scanner & Call-Boundary Guard Tests
// ===========================================================================

#[test]
fn kani5095_source_scanner_positive_cases() {
    // Direct `#[inline(never)]`
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\npub fn checked_add(a: u8, b: u8) -> u8 { a + b }", "checked_add"),
        InlineBoundaryVerdict::Verified
    );

    // Multi-item attribute `#[cold, inline(never)]`
    assert_eq!(
        verify_fn_inline_never_source("#[cold, inline(never)]\nfn target() {}", "target"),
        InlineBoundaryVerdict::Verified
    );

    // Doc comments before and after `#[inline(never)]`, plus `pub(crate) const unsafe extern "C" fn`
    let complex_sig = r#"
        /// Leading doc comment
        #[inline(never)]
        /// Trailing doc comment after inline(never)
        pub(crate) const unsafe extern "C" fn abi_boundary(x: u32) -> u32 {
            x
        }
    "#;
    assert_eq!(
        verify_fn_inline_never_source(complex_sig, "abi_boundary"),
        InlineBoundaryVerdict::Verified
    );

    // Generic bounds with `where` clauses pass default scanner, fail strict scanner.
    let generic_where = r#"
        #[inline(never)]
        pub fn generic_op<'a, T>(x: &'a T) -> &'a T
        where
            T: Copy + 'a,
        {
            x
        }
    "#;
    assert_eq!(
        verify_fn_inline_never_source(generic_where, "generic_op"),
        InlineBoundaryVerdict::Verified
    );
    assert_eq!(
        verify_fn_inline_never_source_with_options(
            generic_where,
            "generic_op",
            InlineScanOptions::strict()
        ),
        InlineBoundaryVerdict::ForbiddenPolymorphicOrTraitDefault
    );

    // Lifetime-only generic `fn<'a>` is NOT polymorphic — passes even strict options!
    let lifetime_only = r#"
        #[inline(never)]
        pub fn borrow_first<'a>(s: &'a [u8]) -> &'a u8
        where
            'a: 'static,
        {
            &s[0]
        }
    "#;
    assert_eq!(
        verify_fn_inline_never_source_with_options(
            lifetime_only,
            "borrow_first",
            InlineScanOptions::strict()
        ),
        InlineBoundaryVerdict::Verified
    );

    // Unconditional `#[cfg_attr(all(), inline(never))]`
    assert_eq!(
        verify_fn_inline_never_source("#[cfg_attr(all(), inline(never))]\nfn target() {}", "target"),
        InlineBoundaryVerdict::Verified
    );

    // Tricky char literals `'"'`, `'\''`, `'#'`, and lifetimes `'a` before target fn
    let tricky_literals = r####"
        const QUOTE: char = '"';
        const APOS: char = '\'';
        const HASH: char = '#';
        const BYTE_Q: u8 = b'"';
        const RAW_S: &str = r###"not an attr #[inline(always)]"###;
        fn helper<'a>(x: &'a str) -> &'a str { x }
        #[inline(never)]
        pub fn real_target<'a>(x: &'a u8) -> u8 { *x }
    "####;
    assert_eq!(
        verify_fn_inline_never_source(tricky_literals, "real_target"),
        InlineBoundaryVerdict::Verified
    );
}

#[test]
fn kani5095_source_scanner_adversarial_negative_cases() {
    // 1. Line comment decoy
    assert_eq!(
        verify_fn_inline_never_source("// #[inline(never)]\npub fn target() {}", "target"),
        InlineBoundaryVerdict::MissingInlineNever
    );

    // 2. Nested block comment decoy
    assert_eq!(
        verify_fn_inline_never_source(
            "/* outer /* #[inline(never)] */ still commented */\npub fn target() {}",
            "target"
        ),
        InlineBoundaryVerdict::MissingInlineNever
    );

    // 3. String literal & raw / raw-byte / raw-C string literal decoys
    assert_eq!(
        verify_fn_inline_never_source(
            "const S: &str = \"#[inline(never)] fn target() {}\";\nfn target() {}",
            "target"
        ),
        InlineBoundaryVerdict::MissingInlineNever
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "const R: &str = r#\"#[inline(never)] fn target() {}\"#;\nfn target() {}",
            "target"
        ),
        InlineBoundaryVerdict::MissingInlineNever
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "const BR: &[u8] = br##\"#[inline(never)] fn target() {}\"##;\nfn target() {}",
            "target"
        ),
        InlineBoundaryVerdict::MissingInlineNever
    );

    // 4. Forbidden `#[inline]` and `#[inline(always)]`
    assert_eq!(
        verify_fn_inline_never_source("#[inline]\nfn target() {}", "target"),
        InlineBoundaryVerdict::ForbiddenInlineHint
    );
    assert_eq!(
        verify_fn_inline_never_source("#[inline(always)]\nfn target() {}", "target"),
        InlineBoundaryVerdict::ForbiddenInlineHint
    );

    // 5. Conflicting `#[inline(never)]` + `#[inline(always)]` (direct & via `cfg_attr`)
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\n#[inline(always)]\nfn target() {}", "target"),
        InlineBoundaryVerdict::ConflictingInlineAttributes
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "#[inline(never)]\n#[cfg_attr(feature = \"fast\", inline(always))]\nfn target() {}",
            "target"
        ),
        InlineBoundaryVerdict::ConflictingInlineAttributes
    );

    // 6. Conditional-only `#[cfg_attr(test, inline(never))]`
    assert_eq!(
        verify_fn_inline_never_source("#[cfg_attr(test, inline(never))]\nfn target() {}", "target"),
        InlineBoundaryVerdict::ConditionalInlineNever
    );

    // 7. Inner attribute `#![inline(never)]` does NOT attach to `fn target`
    assert_eq!(
        verify_fn_inline_never_source("#![inline(never)]\nfn target() {}", "target"),
        InlineBoundaryVerdict::MissingInlineNever
    );

    // 8. Attribute attached to another fn or struct does NOT bleed onto `target`
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\nfn other() {}\nfn target() {}", "target"),
        InlineBoundaryVerdict::MissingInlineNever
    );
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\nstruct Dummy;\nfn target() {}", "target"),
        InlineBoundaryVerdict::MissingInlineNever
    );

    // 9. Duplicate-name functions across modules: ALL matches must pass!
    assert_eq!(
        verify_fn_inline_never_source(
            "mod a { #[inline(never)] pub fn target() {} }\nmod b { pub fn target() {} }",
            "target"
        ),
        InlineBoundaryVerdict::MissingInlineNever
    );

    // 10. Macro definition decoy does not spoof a real item
    assert_eq!(
        verify_fn_inline_never_source(
            "macro_rules! fake { () => { #[inline(never)] fn target() {} }; }\nfn target() {}",
            "target"
        ),
        InlineBoundaryVerdict::MissingInlineNever
    );

    // 11. Trait default method & generic `impl<T>` & `impl Trait` arg rejected under strict mode
    assert_eq!(
        verify_fn_inline_never_source_with_options(
            "trait Foo { #[inline(never)] fn target(&self) {} }",
            "target",
            InlineScanOptions::strict()
        ),
        InlineBoundaryVerdict::ForbiddenPolymorphicOrTraitDefault
    );
    assert_eq!(
        verify_fn_inline_never_source_with_options(
            "impl<T> Wrap<T> { #[inline(never)] fn target(&self) {} }",
            "target",
            InlineScanOptions::strict()
        ),
        InlineBoundaryVerdict::ForbiddenPolymorphicOrTraitDefault
    );
    assert_eq!(
        verify_fn_inline_never_source_with_options(
            "#[inline(never)]\nfn target(x: impl Copy) { let _ = x; }",
            "target",
            InlineScanOptions::strict()
        ),
        InlineBoundaryVerdict::ForbiddenPolymorphicOrTraitDefault
    );

    // 12. Missing function & malformed source
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\nfn other() {}", "target"),
        InlineBoundaryVerdict::TargetFunctionNotFound
    );
    assert_eq!(
        verify_fn_inline_never_source("/* unterminated comment\n#[inline(never)] fn target() {}", "target"),
        InlineBoundaryVerdict::MalformedSource
    );
}

#[test]
fn kani5095_mir_cfg_and_multi_hop_call_boundary_verifiers() {
    const TARGET: &str = "crate::math::checked_add_u8";
    const GUARD: CallBoundaryGuard =
        CallBoundaryGuard::new("crate::caller", TARGET).with_expected_call_sites(2);

    // 1. `CalleeTableExcludes`: absent vs present in `callees` vs present in `trait_impls`
    assert!(verify_callee_table_excludes(&[], &[], TARGET).is_preserved());

    let ret_only = [MirBlockSummary::ret()];
    let inlined_target = [CalleeEntry::new(TARGET, &ret_only)];
    assert_eq!(
        verify_callee_table_excludes(&inlined_target, &[], TARGET),
        CallBoundaryVerdict::TargetInCalleeTable
    );

    let caller_trait_override = [TraitImplBinding::new(TARGET, "crate::math::inlined_add")];
    assert_eq!(
        verify_callee_table_excludes(&[], &caller_trait_override, TARGET),
        CallBoundaryVerdict::TargetDispatchedByTraitImpl
    );

    let helper_with_trait = [CalleeEntry::with_trait_impls(
        "crate::helper",
        &ret_only,
        &caller_trait_override,
    )];
    assert_eq!(
        verify_callee_table_excludes(&helper_with_trait, &[], TARGET),
        CallBoundaryVerdict::TargetDispatchedByTraitImpl
    );

    // 2. `withTraitsPreserved`: catches Call 1 injecting a trait entry before Call 2!
    let before_traits: [TraitImplBinding<'_>; 0] = [];
    let after_traits_injected = [TraitImplBinding::new(TARGET, "crate::math::evil_inline")];
    assert!(verify_traits_preserved(&before_traits, &before_traits, &[], TARGET).is_preserved());
    assert_eq!(
        verify_traits_preserved(&before_traits, &after_traits_injected, &[], TARGET),
        CallBoundaryVerdict::TraitTableMutatedAcrossCall
    );

    // 3. Partial 1-of-2 inlining caught by `verify_counted_call_sites` & `CallBoundaryGuard`
    let two_site_caller = [
        MirBlockSummary::call(TARGET, &[1]),
        MirBlockSummary::call(TARGET, &[2]),
        MirBlockSummary::ret(),
    ];
    let one_of_two_inlined = [
        MirBlockSummary::call(TARGET, &[1]),
        MirBlockSummary::ret(),
    ];
    assert!(verify_call_boundary(&two_site_caller, &[], &[], TARGET).is_preserved());
    assert!(verify_counted_call_sites(&two_site_caller, &[], &[], TARGET, 2).is_preserved());
    assert!(GUARD.verify_reachable_sites(&two_site_caller, &[], &[]).is_preserved());

    // `verify_call_boundary` alone would pass 1-of-2, while `verify_counted_call_sites` catches it!
    assert!(verify_call_boundary(&one_of_two_inlined, &[], &[], TARGET).is_preserved());
    assert_eq!(
        verify_counted_call_sites(&one_of_two_inlined, &[], &[], TARGET, 2),
        CallBoundaryVerdict::CallSiteCountMismatch {
            expected: 2,
            observed: 1,
        }
    );

    // 4. Unreachable dead decoy call block `bb_dead` caught by `verify_reachable_call_boundary`
    let dead_decoy_caller = [
        MirBlockSummary::ret(),             // bb0 returns immediately (body was inlined!)
        MirBlockSummary::call(TARGET, &[0]), // bb1 is unreachable dead decoy call
    ];
    assert!(verify_call_boundary(&dead_decoy_caller, &[], &[], TARGET).is_preserved());
    assert_eq!(
        verify_reachable_call_boundary(&dead_decoy_caller, &[], &[], TARGET),
        CallBoundaryVerdict::NoReachableCallSite {
            syntactic_call_sites: 1,
        }
    );
    assert_eq!(
        verify_reachable_call_sites(&dead_decoy_caller, &[], &[], TARGET, 1),
        CallBoundaryVerdict::ReachableCallSiteCountMismatch {
            expected: 1,
            observed_reachable: 0,
            observed_syntactic: 1,
        }
    );

    // 5. 2-hop helper chain: `grand_caller -> outer_mid -> mid_helper -> checked_add_u8`
    let grand_caller = [
        MirBlockSummary::call("crate::outer_mid", &[1]),
        MirBlockSummary::ret(),
    ];
    let outer_mid_blocks = [
        MirBlockSummary::branch(&[1, 2]),
        MirBlockSummary::call("crate::mid_helper", &[2]),
        MirBlockSummary::ret(),
    ];
    let mid_helper_blocks = [MirBlockSummary::tail_call(TARGET)];
    let callees = [
        CalleeEntry::new("crate::outer_mid", &outer_mid_blocks),
        CalleeEntry::new("crate::mid_helper", &mid_helper_blocks),
    ];
    let chain = ["crate::outer_mid", "crate::mid_helper"];

    assert_eq!(
        verify_call_chain_boundary(&grand_caller, &callees, &[], &chain, TARGET),
        CallBoundaryVerdict::Preserved {
            observed_call_sites: 1,
            reachable_blocks: 6,
        }
    );

    // Broken link: `outer_mid` no longer calls `mid_helper`
    let broken_outer_mid = [MirBlockSummary::ret()];
    let broken_callees = [
        CalleeEntry::new("crate::outer_mid", &broken_outer_mid),
        CalleeEntry::new("crate::mid_helper", &mid_helper_blocks),
    ];
    assert_eq!(
        verify_call_chain_boundary(&grand_caller, &broken_callees, &[], &chain, TARGET),
        CallBoundaryVerdict::BrokenCallChainLink { hop_index: 1 }
    );

    // Missing hop body in `callees`
    let missing_hop_callees = [CalleeEntry::new("crate::outer_mid", &outer_mid_blocks)];
    assert_eq!(
        verify_call_chain_boundary(&grand_caller, &missing_hop_callees, &[], &chain, TARGET),
        CallBoundaryVerdict::MissingChainHopBody { hop_index: 1 }
    );

    // `ChainHopsNotTraitDispatched` (Episode 1 Pass A4): intermediate hop
    // `mid_helper` overridden in `trait_impls` -> rejected!
    let hop_override = [TraitImplBinding::new(
        "crate::mid_helper",
        "crate::inlined_mid_bypass",
    )];
    assert_eq!(
        verify_call_chain_boundary(&grand_caller, &callees, &hop_override, &chain, TARGET),
        CallBoundaryVerdict::ChainHopTraitDispatched { hop_index: 1 }
    );

    // Also caught when the trait override hides inside a linked callee's `trait_impls`!
    let hidden_override_callees = [
        CalleeEntry::with_trait_impls("crate::outer_mid", &outer_mid_blocks, &hop_override),
        CalleeEntry::new("crate::mid_helper", &mid_helper_blocks),
    ];
    assert_eq!(
        verify_call_chain_boundary(&grand_caller, &hidden_override_callees, &[], &chain, TARGET),
        CallBoundaryVerdict::ChainHopTraitDispatched { hop_index: 1 }
    );

    // Capacity overflow fails closed.
    let huge = [MirBlockSummary::ret(); MAX_MIR_BLOCKS + 1];
    assert_eq!(
        verify_reachable_call_sites(&huge, &[], &[], TARGET, 0),
        CallBoundaryVerdict::CfgExceedsCapacity {
            block_count: MAX_MIR_BLOCKS + 1,
            max_blocks: MAX_MIR_BLOCKS,
        }
    );
}

// ===========================================================================
// 4. Seed-Stability Sweeps & Deterministic Counterexample Replay
// ===========================================================================

#[test]
fn seed_stability_sweep_and_exact_counterexample_replay() {
    let seeds = [
        0u64,
        1,
        42,
        0xDEAD_BEEF_CAFE_BABE,
        SplitMix64::DEFAULT_SEED,
        u64::MAX,
    ];

    for seed in seeds {
        let cfg = PanicCheckConfig::from_spec_config(
            SpecCheckConfig::default().with_seed(seed).with_max_trials(128),
        );

        // Positive contract passes across every seed.
        let stats = assert_panic_contract_strong(
            cfg,
            PanicContractMode::Exact,
            |&(_a, _b): &(u8, u8)| true,
            |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > 255,
            forbid_abort(),
            panic_unwind_runner!(|&(a, b): &(u8, u8)| checked_add_u8(a, b)),
            |&(a, b): &(u8, u8), &out: &u8| out == a + b,
        );
        assert!(stats.observed_panics > 0);
        assert!(stats.normal_returns > 0);

        // Counterexample replay reproduces the EXACT violating input on every seed.
        let fail_outcome = check_panic_contract_fallible(
            cfg,
            PanicContractMode::Exact,
            |&(_a, _b): &(u8, u8)| Ok(true),
            |&(a, b): &(u8, u8)| Ok((a as u16) + (b as u16) > 255),
            forbid_abort_fallible(),
            panic_unwind_runner!(|&(a, b): &(u8, u8)| {
                // Bug: panics on `(a, b) == (42, 42)` too!
                assert!(!(a == 42 && b == 42), "injected bug");
                checked_add_u8(a, b)
            }),
            |&(a, b): &(u8, u8), &out: &u8| Ok(out == a + b),
        );
        let fail = fail_outcome
            .failure()
            .expect("injected (42, 42) panic must fail on every seed");
        assert_eq!(fail.class, PanicFailureClass::UnexpectedPanic);
        let idx = fail.counterexample_trial().unwrap();
        let replayed = replay_panic_trial_input::<(u8, u8)>(cfg, idx).unwrap();
        assert_eq!(replayed, (42, 42));

        // Out-of-range trial index returns `None`.
        assert_eq!(replay_panic_trial_input::<u8>(cfg, 128), None);
        assert_eq!(
            replay_stateful_panic_trial_input::<BoundedStack, u8>(cfg, 128),
            None
        );

        // Stateful replay matches across every seed too.
        let st_fail = check_stateful_panic_contract_fallible(
            cfg,
            PanicContractMode::Exact,
            |s: &BoundedStack, _v: &u8| Ok(s.__anneal_type_invariant_bounded_stack()),
            |s: &BoundedStack, _v: &u8| Ok(s.len == 3),
            forbid_stateful_abort::<BoundedStack, u8>().map_cond(|f| move |s: &BoundedStack, a: &u8| Ok(f(s, a))),
            stateful_panic_unwind_runner!(|s: &mut BoundedStack, &v: &u8| s.push_corrupting(v)),
            |old_s: &BoundedStack, &v: &u8, new_s: &BoundedStack, &ret: &u8| {
                Ok(new_s.len == old_s.len + 1
                    && ret == new_s.len
                    && new_s.slots[old_s.len as usize] == v)
            },
            Some(|old_s: &BoundedStack, post_s: &BoundedStack| Ok(post_s == old_s)),
        );
        let sf = st_fail.failure().expect("must catch pre-panic corruption on every seed");
        assert_eq!(sf.class, PanicFailureClass::PanicStateInvariantViolation);
        let s_idx = sf.counterexample_trial().unwrap();
        let (replayed_s, _) =
            replay_stateful_panic_trial_input::<BoundedStack, u8>(cfg, s_idx).unwrap();
        assert_eq!(replayed_s.len, 3);
    }

    // Verify `AbortPolicyKind` display formatting and `AbortPolicy` accessors.
    assert_eq!(AbortPolicyKind::ForbidAbort.canonical_name(), "forbidAbort");
    assert!(forbid_abort::<u8>().is_forbid());
    assert!(waive_abort_unchecked::<u8>().is_waived());
    assert!(AbortPolicy::AbortOnlyIf(|&x: &u8| x == 0).is_abort_only_if());
}
