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
    verify_call_frame_and_traits_preserved, verify_reachable_call_sites,
    verify_reachable_callees_call_sites, verify_traits_preserved, waive_abort_unchecked,
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
        verify_reachable_call_sites(&huge, &[], &[], TARGET, 1),
        CallBoundaryVerdict::CfgExceedsCapacity {
            block_count: MAX_MIR_BLOCKS + 1,
            max_blocks: MAX_MIR_BLOCKS,
        }
    );
}

// ===========================================================================
// 3b. `[adv ep2 B1]` Hardening: Nested / Macro-Hidden Targets, Lexer Corner
//     Cases, Vacuous Counted Guards, Callee-Table Frames & Transitive Guards
// ===========================================================================

#[test]
fn kani5095_source_scanner_rejects_nested_and_macro_hidden_targets() {
    use InlineBoundaryVerdict::*;
    let strict = InlineScanOptions::strict();
    let both = |src: &str| {
        (
            verify_fn_inline_never_source(src, "target"),
            verify_fn_inline_never_source_with_options(src, "target", strict),
        )
    };

    // An un-annotated duplicate nested in a function body, a `const` block,
    // a closure, a macro invocation, or a `macro_rules!` template can no
    // longer hide behind a correctly annotated item-level definition.
    for hidden in [
        "#[inline(never)] fn target() {}\nmod m { fn outer() { fn target() {} } }",
        "#[inline(never)] fn target() {}\nmod m { const _: () = { fn target() {} }; }",
        "#[inline(never)] fn target() {}\nfn g() { let c = || { fn target() {} }; }",
        "#[inline(never)] fn target() {}\nmod m { make! { fn target() {} } }",
        "macro_rules! m { () => { fn target() {} } }\n#[inline(never)] fn target() {}",
        "fn outer() { fn target() {} }",
    ] {
        assert_eq!(both(hidden), (MissingInlineNever, MissingInlineNever), "{hidden}");
    }
    // Nested occurrences get the full attribute analysis too.
    assert_eq!(
        both("fn outer() { #[inline(never)] #[inline(always)] fn target() {} }"),
        (ConflictingInlineAttributes, ConflictingInlineAttributes)
    );
    assert_eq!(
        both("fn outer() { #[cfg_attr(test, inline(never))] fn target() {} }"),
        (ConditionalInlineNever, ConditionalInlineNever)
    );

    // Annotated nested / macro-template occurrences are accepted.
    assert_eq!(both("fn outer() { #[inline(never)] fn target() {} }"), (Verified, Verified));
    assert_eq!(
        both(
            "macro_rules! m { () => { #[inline(never)] fn target() {} } }\n\
             #[inline(never)] fn target() {}"
        ),
        (Verified, Verified)
    );

    // Polymorphism inside bodies: nested generic `impl` / `trait` scopes are
    // tracked, while plain nested fns stay monomorphic (E0401).
    assert_eq!(
        both("fn g() { impl<T> Foo<T> { #[inline(never)] fn target(&self) {} } }"),
        (Verified, ForbiddenPolymorphicOrTraitDefault)
    );
    assert_eq!(
        both("fn g() { trait T { #[inline(never)] fn target(&self) {} } }"),
        (Verified, ForbiddenPolymorphicOrTraitDefault)
    );
    assert_eq!(
        both("fn g<T>() { #[inline(never)] fn target() {} }"),
        (Verified, Verified)
    );

    // Rust 2024 `safe fn` in `unsafe extern` blocks is a real target item.
    assert_eq!(
        both("unsafe extern \"C\" { safe fn target(); }"),
        (MissingInlineNever, MissingInlineNever)
    );
}

#[test]
fn kani5095_source_scanner_lexer_corner_cases_do_not_false_positive() {
    use InlineBoundaryVerdict::*;
    for ok in [
        // Legal token sequences previously rejected as `MalformedSource`.
        "auto trait Marker {}\n#[inline(never)] fn target() {}",
        "# ! [allow(dead_code)]\n#[inline(never)] fn target() {}",
        "#!/usr/bin/env run-cargo-script\n#[inline(never)] fn target() {}",
        "#![allow(dead_code)]\n#[inline(never)] fn target() {}",
        // Macro token trees with non-item structure.
        "macro_rules! m { ($n:ident) => { mod $n {} } }\n#[inline(never)] fn target() {}",
        "fn g() { quote! { impl<#generics> #name { fn #method() {} } } }\n\
         #[inline(never)] fn target() {}",
        // Lifetimes vs char literals, labels, raw byte strings with braces.
        "fn g<'a>(x: &'a u8) -> char { let _ = '{'; let _ = b'}'; 'a' }\n\
         #[inline(never)] fn target() {}",
        "fn g() { 'outer: loop { break 'outer; } }\n#[inline(never)] fn target() {}",
        "const S: &[u8] = br#\"} fn target() {\"#;\n#[inline(never)] fn target() {}",
        // `impl Trait` in return / type-alias position and fn-pointer types.
        "type X = impl Sized;\nfn g() -> impl Fn() { || {} }\n\
         fn h() { let f: fn(u8) -> u8 = k; }\n#[inline(never)] fn target() {}",
        "#[unsafe(no_mangle)]\n#[inline(never)] fn target() {}",
    ] {
        assert_eq!(verify_fn_inline_never_source(ok, "target"), Verified, "{ok}");
    }

    // Dogfooding on real, macro- and literal-heavy Rust sources.
    assert_eq!(
        verify_fn_inline_never_source(include_str!("panic_contract_tests.rs"), "checked_add_u8"),
        Verified
    );
    let lib_src = include_str!("../src/panic_contract.rs");
    assert_eq!(verify_fn_inline_never_source(lib_src, "invoke_boundary_guarded"), Verified);
    assert_eq!(
        verify_fn_inline_never_source_with_options(
            lib_src,
            "invoke_boundary_guarded",
            InlineScanOptions::strict(),
        ),
        ForbiddenPolymorphicOrTraitDefault
    );
    assert_eq!(verify_fn_inline_never_source(lib_src, "check_panic_contract"), MissingInlineNever);
}

#[test]
fn kani5095_vacuous_guards_callee_frames_and_transitive_callee_sites() {
    const TARGET: &str = "crate::math::checked_add_u8";
    let fully_inlined_caller = [MirBlockSummary::ret()];

    // A counted guard expecting ZERO sites would accept a fully inlined caller.
    assert_eq!(
        verify_counted_call_sites(&fully_inlined_caller, &[], &[], TARGET, 0),
        CallBoundaryVerdict::ZeroExpectedCallSites
    );
    assert_eq!(
        verify_reachable_call_sites(&fully_inlined_caller, &[], &[], TARGET, 0),
        CallBoundaryVerdict::ZeroExpectedCallSites
    );
    const ZERO_GUARD: CallBoundaryGuard =
        CallBoundaryGuard::new("crate::caller", TARGET).with_expected_call_sites(0);
    assert_eq!(
        ZERO_GUARD.verify_reachable_sites(&fully_inlined_caller, &[], &[]),
        CallBoundaryVerdict::ZeroExpectedCallSites
    );
    assert_eq!(
        ZERO_GUARD
            .with_forbid_trait_dispatch(false)
            .verify_reachable_sites(&fully_inlined_caller, &[], &[]),
        CallBoundaryVerdict::ZeroExpectedCallSites
    );

    // `callFrameAndTraitsPreserved`: Call 1 injecting the target's body into
    // `callees` is caught even when the post-call trait table is unchanged.
    let helper_blocks = [MirBlockSummary::call(TARGET, &[1]), MirBlockSummary::ret()];
    let ret_only = [MirBlockSummary::ret()];
    let before_callees = [CalleeEntry::new("crate::helper", &helper_blocks)];
    let after_injected = [
        CalleeEntry::new("crate::helper", &helper_blocks),
        CalleeEntry::new(TARGET, &ret_only),
    ];
    assert!(
        verify_call_frame_and_traits_preserved(&before_callees, &before_callees, &[], &[], TARGET)
            .is_preserved()
    );
    assert_eq!(
        verify_call_frame_and_traits_preserved(&before_callees, &after_injected, &[], &[], TARGET),
        CallBoundaryVerdict::CalleeTableMutatedAcrossCall
    );
    // Even a body swap that keeps the same `def_path` is a frame violation.
    let after_swapped = [CalleeEntry::new("crate::helper", &ret_only)];
    assert_eq!(
        verify_call_frame_and_traits_preserved(&before_callees, &after_swapped, &[], &[], TARGET),
        CallBoundaryVerdict::CalleeTableMutatedAcrossCall
    );
    let injected_trait = [TraitImplBinding::new(TARGET, "crate::evil")];
    assert_eq!(
        verify_call_frame_and_traits_preserved(
            &before_callees,
            &before_callees,
            &[],
            &injected_trait,
            TARGET
        ),
        CallBoundaryVerdict::TraitTableMutatedAcrossCall
    );

    // Transitive `ReachableCalleesCallSitesPreserved` inside linked helpers.
    let two_site_helper = [
        MirBlockSummary::call(TARGET, &[1]),
        MirBlockSummary::call(TARGET, &[2]),
        MirBlockSummary::ret(),
    ];
    let half_inlined_helper = [MirBlockSummary::call(TARGET, &[1]), MirBlockSummary::ret()];
    let dead_decoy_helper = [MirBlockSummary::ret(), MirBlockSummary::call(TARGET, &[0])];
    let callees = [
        CalleeEntry::new("crate::outer_helper", &two_site_helper),
        CalleeEntry::new("crate::inner_helper", &helper_blocks),
    ];
    assert_eq!(
        verify_reachable_callees_call_sites(
            &callees,
            &[],
            &[("crate::outer_helper", 2), ("crate::inner_helper", 1)],
            TARGET
        ),
        CallBoundaryVerdict::Preserved {
            observed_call_sites: 3,
            reachable_blocks: 5,
        }
    );
    let half = [CalleeEntry::new("crate::outer_helper", &half_inlined_helper)];
    assert_eq!(
        verify_reachable_callees_call_sites(&half, &[], &[("crate::outer_helper", 2)], TARGET),
        CallBoundaryVerdict::CalleeReachableCallSiteCountMismatch {
            caller_index: 0,
            expected: 2,
            observed: 1,
        }
    );
    let decoy = [CalleeEntry::new("crate::outer_helper", &dead_decoy_helper)];
    assert_eq!(
        verify_reachable_callees_call_sites(&decoy, &[], &[("crate::outer_helper", 1)], TARGET),
        CallBoundaryVerdict::CalleeReachableCallSiteCountMismatch {
            caller_index: 0,
            expected: 1,
            observed: 0,
        }
    );
    // Duplicate bodies for one path must ALL satisfy the expectation.
    let dup = [
        CalleeEntry::new("crate::outer_helper", &helper_blocks),
        CalleeEntry::new("crate::outer_helper", &dead_decoy_helper),
    ];
    assert_eq!(
        verify_reachable_callees_call_sites(&dup, &[], &[("crate::outer_helper", 1)], TARGET),
        CallBoundaryVerdict::CalleeReachableCallSiteCountMismatch {
            caller_index: 0,
            expected: 1,
            observed: 0,
        }
    );
    assert_eq!(
        verify_reachable_callees_call_sites(&callees, &[], &[("crate::missing", 1)], TARGET),
        CallBoundaryVerdict::MissingExpectedCaller { caller_index: 0 }
    );
    assert_eq!(
        verify_reachable_callees_call_sites(&callees, &[], &[], TARGET),
        CallBoundaryVerdict::ZeroExpectedCallSites
    );
    assert_eq!(
        verify_reachable_callees_call_sites(&callees, &[], &[("crate::outer_helper", 0)], TARGET),
        CallBoundaryVerdict::ZeroExpectedCallSites
    );
    assert_eq!(
        verify_reachable_callees_call_sites(
            &after_injected,
            &[],
            &[("crate::helper", 1)],
            TARGET
        ),
        CallBoundaryVerdict::TargetInCalleeTable
    );
    assert_eq!(
        verify_reachable_callees_call_sites(
            &callees,
            &injected_trait,
            &[("crate::outer_helper", 2)],
            TARGET
        ),
        CallBoundaryVerdict::TargetDispatchedByTraitImpl
    );
}

#[test]
fn panics_if_mode_triggers_abort_interplay_and_degenerate_config() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);
    let pre = |_: &(u8, u8)| Ok(true);
    let overflow = |&(a, b): &(u8, u8)| Ok((a as u16) + (b as u16) > 255);
    let post = |_: &(u8, u8), _: &u8| Ok(true);

    // `PanicsIf` tolerates extra panics outside `panic_cond`.
    let over_panicky = |&(a, b): &(u8, u8)| {
        if a > 200 || (a as u16) + (b as u16) > 255 {
            PanicExecOutcome::Panicked
        } else {
            PanicExecOutcome::Returned(a.wrapping_add(b))
        }
    };
    assert!(
        check_panic_contract_fallible(
            cfg,
            PanicContractMode::If,
            pre,
            overflow,
            forbid_abort_fallible(),
            over_panicky,
            post
        )
        .is_strong()
    );

    // Dropped guard: missed panic in `If` mode.
    let dropped = |&(a, b): &(u8, u8)| PanicExecOutcome::Returned(a.wrapping_add(b));
    assert_eq!(
        check_panic_contract_fallible(
            cfg,
            PanicContractMode::If,
            pre,
            overflow,
            forbid_abort_fallible(),
            dropped,
            post
        )
        .failure_class(),
        Some(PanicFailureClass::MissedExpectedPanic)
    );

    // `WaiveAbortUnchecked` does not let an abort discharge a panic trigger.
    let aborts_instead = |&(a, b): &(u8, u8)| {
        if (a as u16) + (b as u16) > 255 {
            PanicExecOutcome::Aborted
        } else {
            PanicExecOutcome::Returned(a.wrapping_add(b))
        }
    };
    assert_eq!(
        check_panic_contract_fallible(
            cfg,
            PanicContractMode::If,
            pre,
            overflow,
            AbortPolicy::<fn(&(u8, u8)) -> Result<bool, ()>>::WaiveAbortUnchecked,
            aborts_instead,
            post
        )
        .failure_class(),
        Some(PanicFailureClass::MissedExpectedPanic)
    );

    // Under `AbortOnlyIf`, panicking where an abort is required is rejected.
    let zero_aborts = |&(a, _b): &(u8, u8)| Ok(a == 0);
    let panics_on_zero = |&(a, b): &(u8, u8)| {
        if a == 0 || (a as u16) + (b as u16) > 255 {
            PanicExecOutcome::Panicked
        } else {
            PanicExecOutcome::Returned(a.wrapping_add(b))
        }
    };
    assert_eq!(
        check_panic_contract_fallible(
            cfg,
            PanicContractMode::If,
            pre,
            overflow,
            AbortPolicy::AbortOnlyIf(zero_aborts),
            panics_on_zero,
            post
        )
        .failure_class(),
        Some(PanicFailureClass::MissedExpectedAbort)
    );

    // `min_panic_hits == 0` in `If` mode is vacuous (no `post`, no trigger
    // evidence) and fails closed before running any trial...
    let outcome = check_panic_contract_fallible(
        cfg.with_min_panic_hits(0),
        PanicContractMode::If,
        pre,
        |_: &(u8, u8)| Ok(false),
        forbid_abort_fallible(),
        dropped,
        post,
    );
    let failure = outcome.failure().expect("vacuous PanicsIf must fail closed");
    assert_eq!(failure.class, PanicFailureClass::DeadPanicCondition);
    assert_eq!(failure.detail, PanicFailureDetail::DegenerateConfig);
    assert_eq!(failure.stats.trials_run, 0);

    // ...unless an abort trigger still demands evidence.
    let abort_only = |&(a, _b): &(u8, u8)| {
        if a == 0 {
            PanicExecOutcome::Aborted
        } else {
            PanicExecOutcome::Returned(a)
        }
    };
    assert!(
        check_panic_contract_fallible(
            cfg.with_min_panic_hits(0),
            PanicContractMode::If,
            pre,
            |_: &(u8, u8)| Ok(false),
            AbortPolicy::AbortOnlyIf(zero_aborts),
            abort_only,
            post
        )
        .is_strong()
    );
}

#[test]
fn unwind_macros_accept_explicit_abort_policy() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    // `OnlyIf` + `AbortOnlyIf` via the unwind macro (aborts permitted, not
    // required, so an unwinding runner passes).
    let stats = assert_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::OnlyIf,
        |_: &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > 255,
        abort_policy = AbortPolicy::AbortOnlyIf(|&(a, _b): &(u8, u8)| a == 255),
        |&(a, b): &(u8, u8)| checked_add_u8(a, b),
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
    );
    assert!(stats.abort_cond_hits > 0);
    assert_eq!(stats.observed_aborts, 0);

    // A trapping `abort_cond` is reported as a predicate trap, not a crash.
    let trapped = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::OnlyIf,
        |_: &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > 255,
        abort_policy = AbortPolicy::AbortOnlyIf(|&(a, _b): &(u8, u8)| {
            assert!(a != 0, "abort_cond trap");
            false
        }),
        |&(a, b): &(u8, u8)| checked_add_u8(a, b),
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
    );
    let failure = trapped.failure().expect("trapping abort_cond must fail");
    assert_eq!(failure.class, PanicFailureClass::UnexpectedPanic);
    assert!(matches!(
        failure.detail,
        PanicFailureDetail::PredicateTrapped {
            trap: PanicTrapKind::AbortConditionPanicked,
            ..
        }
    ));
    let idx = failure.counterexample_trial().unwrap();
    assert_eq!(replay_panic_trial_input::<(u8, u8)>(cfg, idx).unwrap().0, 0);

    // `Exact` + `AbortOnlyIf` cannot be discharged by an unwinding runner:
    // `catch_unwind` never yields `Aborted`, so the abort trigger is missed.
    let missed = check_panic_contract_unwind!(
        cfg,
        PanicContractMode::Exact,
        |_: &(u8, u8)| true,
        |&(a, b): &(u8, u8)| a != 255 && (a as u16) + (b as u16) > 255,
        abort_policy = AbortPolicy::AbortOnlyIf(|&(a, _b): &(u8, u8)| a == 255),
        |&(a, b): &(u8, u8)| if a == 255 { a } else { checked_add_u8(a, b) },
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
    );
    assert_eq!(missed.failure_class(), Some(PanicFailureClass::MissedExpectedAbort));
}

// ===========================================================================
// 3c. `[adv ep2 A1]` Hardening: Deep Delimiter Scanning, Prelude Attrs,
//     UTF-8 Escapes, CallBoundaryGuard Enforcement, WaiveAbort Domain Safety,
//     Stateful Conjunctive Axis Probing & Stateful `abort_policy` Macros
// ===========================================================================

#[test]
fn kani5095_deep_scanner_catches_targets_hidden_in_params_generics_and_macro_headers() {
    use InlineBoundaryVerdict::*;
    let strict = InlineScanOptions::strict();

    // Hidden un-annotated `fn target` inside parameter const blocks, `impl`
    // generic bounds, and `macro_rules!` arms starting with `impl` / `trait`.
    for hidden in [
        "#[inline(never)] fn target() {}\nfn sneaky(_: [u8; { fn target() {} 1 }]) {}",
        "#[inline(never)] fn target() {}\nmacro_rules! mk { (impl $t:ty) => (fn target() {}); }",
        "#[inline(never)] fn target() {}\nmacro_rules! mk { (trait $t:ident) => (fn target() {}); }",
        "#[inline(never)] fn target() {}\nimpl Foo<[u8; { fn target() {} 1 }]> {}",
        "#[inline(never)] fn target() {}\nimpl<const N: usize = { fn target() {} 1 }> Foo<N> {}",
    ] {
        assert_eq!(
            verify_fn_inline_never_source(hidden, "target"),
            MissingInlineNever,
            "{hidden}"
        );
        assert_eq!(
            verify_fn_inline_never_source_with_options(hidden, "target", strict),
            MissingInlineNever,
            "{hidden}"
        );
    }

    // Prelude-qualified `inline` and `cfg_attr` attributes cannot bypass checks.
    assert_eq!(
        verify_fn_inline_never_source(
            "#[inline(never)]\n#[core::prelude::v1::inline(always)]\nfn target() {}",
            "target"
        ),
        ConflictingInlineAttributes
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "#[::core::prelude::v1::inline(always)]\nfn target() {}",
            "target"
        ),
        ForbiddenInlineHint
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "#[::std::prelude::rust_2024::inline(never)]\nfn target() {}",
            "target"
        ),
        Verified
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "#[core::prelude::v1::cfg_attr(all(), core::prelude::v1::inline(never))]\nfn target() {}",
            "target"
        ),
        Verified
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "#[core::prelude::v1::cfg_attr(test, inline(never))]\nfn target() {}",
            "target"
        ),
        ConditionalInlineNever
    );

    // Symmetric raw-identifier normalization (`r#match` <-> `match`, `r#target` <-> `target`).
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\nfn r#match() {}", "match"),
        Verified
    );
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\nfn r#match() {}", "r#match"),
        Verified
    );
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\nfn target() {}", "r#target"),
        Verified
    );
    assert_eq!(
        verify_fn_inline_never_source("#[inline(never)]\nfn target() {}", "r#"),
        TargetFunctionNotFound
    );

    // Non-ASCII UTF-8 bytes immediately after backslash escapes never panic on
    // UTF-8 char-boundary slicing!
    assert_eq!(
        verify_fn_inline_never_source(
            "const S: &str = \"\\🦀\";\n#[inline(never)]\nfn target() {}",
            "target"
        ),
        Verified
    );
    assert_eq!(
        verify_fn_inline_never_source(
            "const C: char = '\\🦀';\n#[inline(never)]\nfn target() {}",
            "target"
        ),
        Verified
    );
    assert_eq!(
        verify_fn_inline_never_source("const BAD: char = '\\x🦀'; fn target() {}", "target"),
        MalformedSource
    );

    // Deeply nested parameter groups fail closed instead of overflowing the stack.
    let mut deeply_nested = String::from("#[inline(never)] fn target(x: ");
    for _ in 0..40 {
        deeply_nested.push('(');
    }
    deeply_nested.push_str("u8");
    for _ in 0..40 {
        deeply_nested.push(')');
    }
    deeply_nested.push_str(") { let _ = x; }");
    assert_eq!(
        verify_fn_inline_never_source(&deeply_nested, "target"),
        MalformedSource
    );
}

#[test]
fn kani5095_call_boundary_guard_and_syntactic_capacity_hardening() {
    const CALLER: &str = "crate::api::safe_add";
    const TARGET: &str = "crate::math::checked_add_u8";

    // `require_inline_never = false` still checks existence, forbidden inline
    // hints, malformed source, and `forbid_trait_dispatch`!
    let relaxed = CallBoundaryGuard::new(CALLER, TARGET).with_require_inline_never(false);
    assert_eq!(
        relaxed.verify_target_source("fn other() {}", "checked_add_u8"),
        InlineBoundaryVerdict::TargetFunctionNotFound
    );
    assert_eq!(
        relaxed.verify_target_source("#[inline(always)] fn checked_add_u8() {}", "checked_add_u8"),
        InlineBoundaryVerdict::ForbiddenInlineHint
    );
    assert_eq!(
        relaxed.verify_target_source("fn checked_add_u8<T>(x: T) -> T { x }", "checked_add_u8"),
        InlineBoundaryVerdict::ForbiddenPolymorphicOrTraitDefault
    );
    assert_eq!(
        relaxed.verify_target_source("fn checked_add_u8() {}", "checked_add_u8"),
        InlineBoundaryVerdict::Verified
    );

    // `CallBoundaryGuard::verify_caller_in_callees` enforces `caller_path`!
    let guard = CallBoundaryGuard::new(CALLER, TARGET).with_expected_call_sites(2);
    let caller_blocks = [
        MirBlockSummary::call(TARGET, &[1]),
        MirBlockSummary::call(TARGET, &[2]),
        MirBlockSummary::ret(),
    ];
    let callees_ok = [CalleeEntry::new(CALLER, &caller_blocks)];
    assert_eq!(
        guard.verify_caller_in_callees(&callees_ok, &[]),
        CallBoundaryVerdict::Preserved {
            observed_call_sites: 2,
            reachable_blocks: 3,
        }
    );
    let wrong_caller = [CalleeEntry::new("crate::api::other_fn", &caller_blocks)];
    assert_eq!(
        guard.verify_caller_in_callees(&wrong_caller, &[]),
        CallBoundaryVerdict::MissingExpectedCaller { caller_index: 0 }
    );

    // `CallBoundaryGuard::verify_call_chain` enforces `forbid_trait_dispatch`.
    let hop_blocks = [MirBlockSummary::tail_call(TARGET)];
    let root_blocks = [MirBlockSummary::call("crate::mid", &[1]), MirBlockSummary::ret()];
    let chain_callees = [CalleeEntry::new("crate::mid", &hop_blocks)];
    let hop_trait = [TraitImplBinding::new("crate::mid", "crate::evil_mid")];
    assert_eq!(
        guard.verify_call_chain(&root_blocks, &chain_callees, &hop_trait, &["crate::mid"]),
        CallBoundaryVerdict::ChainHopTraitDispatched { hop_index: 0 }
    );
    assert!(
        guard
            .with_forbid_trait_dispatch(false)
            .verify_call_chain(&root_blocks, &chain_callees, &hop_trait, &["crate::mid"])
            .is_preserved()
    );

    // Syntactic checkers enforce `MAX_MIR_BLOCKS` and report `reachable_blocks: 0`.
    assert_eq!(
        verify_call_boundary(&caller_blocks, &[], &[], TARGET),
        CallBoundaryVerdict::Preserved {
            observed_call_sites: 2,
            reachable_blocks: 0,
        }
    );
    assert_eq!(
        verify_counted_call_sites(&caller_blocks, &[], &[], TARGET, 2),
        CallBoundaryVerdict::Preserved {
            observed_call_sites: 2,
            reachable_blocks: 0,
        }
    );
    let oversized = [MirBlockSummary::call(TARGET, &[]); MAX_MIR_BLOCKS + 1];
    assert_eq!(
        verify_call_boundary(&oversized, &[], &[], TARGET),
        CallBoundaryVerdict::CfgExceedsCapacity {
            block_count: MAX_MIR_BLOCKS + 1,
            max_blocks: MAX_MIR_BLOCKS,
        }
    );
    assert_eq!(
        verify_counted_call_sites(&oversized, &[], &[], TARGET, 1),
        CallBoundaryVerdict::CfgExceedsCapacity {
            block_count: MAX_MIR_BLOCKS + 1,
            max_blocks: MAX_MIR_BLOCKS,
        }
    );
}

#[test]
fn stage_p3a_waive_abort_domain_safety_and_stateful_conjunctive_axis_probe() {
    let cfg = PanicCheckConfig::default()
        .with_max_trials(128)
        .with_probe_domain(ProbeDomain::PreconditionOnly);

    // Under `OnlyIf` + `WaiveAbortUnchecked`, `x < 20` aborts. Even when
    // `post` is vacuous (`true` on `20..80`) and triggers Stage P3a
    // classification probes, `PreconditionOnly` MUST NOT pass unsampled
    // potentially-aborting inputs (`x < 20`) to `post`!
    let waived_probe = PanicsOnlyIf::new(
        |&x: &u8| x < 100,
        |&x: &u8| x >= 80,
        |&x: &u8, &_r: &u8| {
            assert!(x >= 20 && x < 80, "post called on aborting/panicking input {x}!");
            true
        },
    )
    .with_waive_abort_unchecked::<u8>()
    .check(cfg, |&x: &u8| {
        if x < 20 {
            PanicExecOutcome::Aborted
        } else if x >= 80 {
            PanicExecOutcome::Panicked
        } else {
            PanicExecOutcome::Returned(x)
        }
    });
    assert_eq!(
        waived_probe.failure_class(),
        Some(PanicFailureClass::TrivialNormalPostcondition)
    );
    match waived_probe.failure().unwrap().detail {
        PanicFailureDetail::AllNormalMutantsSurvived {
            probed_inputs,
            out_of_normal_domain_probes,
            skipped_out_of_normal_domain,
            ..
        } => {
            assert_eq!(probed_inputs, 1); // anchor input only!
            assert_eq!(out_of_normal_domain_probes, 0);
            assert!(skipped_out_of_normal_domain > 0);
        }
        other => panic!("unexpected detail: {other:?}"),
    }

    // Stateful conjunctive postcondition where `ret` kills mutants on live hits
    // (`old_s < 10`), while `new_s` is only constrained outside `old_s < 10`:
    // `(ret == old_s.wrapping_add(1)) && (old_s < 10 || new_s == 2)`.
    // On `old_s >= 10`, `anchor_ret == 1` never satisfies `ret == old_s + 1`, so
    // `probe_stateful_normal_state_axis` MUST probe `anchor_ret` mutants (e.g.
    // `probe_ret = 255` at `old_s = 254`) to discover `new_s` sensitivity and
    // report `SurvivedAllNormalMutants` instead of `UnboundNormalReturnOutput`!
    let conj_outcome = StatefulPanicContractSpec::exact::<u8, ()>(
        |&s: &u8, _: &()| s < 20,
        |&s: &u8, _: &()| s >= 10,
        |&old_s: &u8, _: &(), &new_s: &u8, &ret: &u8| {
            ret == old_s.wrapping_add(1) && (old_s < 10 || new_s == 2)
        },
    )
    .check(
        cfg.with_probe_domain(ProbeDomain::Unconstrained),
        |s: &mut u8, _: &()| {
            if *s >= 10 {
                PanicExecOutcome::Panicked
            } else {
                *s += 1;
                PanicExecOutcome::Returned(*s)
            }
        },
    );
    assert_eq!(
        conj_outcome.failure_class(),
        Some(PanicFailureClass::SurvivedAllNormalMutants)
    );
    assert!(matches!(
        conj_outcome.failure().unwrap().detail,
        PanicFailureDetail::StatefulNormalAxisUnconstrained {
            state_mutants_killed: 0,
            return_mutants_killed,
            ..
        } if return_mutants_killed > 0
    ));

    // Also verify mutant-chain flip reaches point predicate `new_s == 42` on
    // the state axis when `ret` is satisfied by `anchor_ret`.
    let chain_outcome = StatefulPanicContractSpec::exact::<u8, ()>(
        |&s: &u8, _: &()| s < 20,
        |&s: &u8, _: &()| s >= 10,
        |&old_s: &u8, _: &(), &new_s: &u8, &ret: &u8| {
            (ret <= 10) && (old_s < 10 || new_s == 42)
        },
    )
    .check(
        cfg.with_probe_domain(ProbeDomain::Unconstrained),
        |s: &mut u8, _: &()| {
            if *s >= 10 {
                PanicExecOutcome::Panicked
            } else {
                *s += 1;
                PanicExecOutcome::Returned(*s)
            }
        },
    );
    assert_eq!(
        chain_outcome.failure_class(),
        Some(PanicFailureClass::SurvivedAllNormalMutants)
    );
}

#[test]
fn stateful_unwind_macros_with_explicit_abort_policy_and_fallible_wrappers() {
    let cfg = PanicCheckConfig::default().with_max_trials(256);

    // Non-`Copy` struct with `check_panic_contract_unwind!` `abort_policy = ...`
    // and unannotated closure parameter verifying HRTB inference.
    let range_stats = assert_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::OnlyIf,
        |pair: &RangePair| pair.__anneal_type_invariant_range_pair(),
        |pair: &RangePair| pair.lo == pair.hi,
        abort_policy = AbortPolicy::AbortOnlyIf(|pair: &RangePair| pair.lo == 0),
        |pair: &RangePair| checked_range_span(pair),
        |pair: &RangePair, &span: &u8| span == pair.hi - pair.lo && span > 0,
    );
    assert!(range_stats.abort_cond_hits > 0);
    assert!(range_stats.observed_panics > 0);

    // Stateful `assert_stateful_panic_contract_strong_unwind!` with
    // `abort_policy = ...` both without and with `panic_state_inv`.
    let st_stats = assert_stateful_panic_contract_strong_unwind!(
        cfg,
        PanicContractMode::OnlyIf,
        |s: &BoundedStack, _v: &u8| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _v: &u8| s.len == 3,
        abort_policy = AbortPolicy::AbortOnlyIf(|s: &BoundedStack, _v: &u8| s.len == 0),
        |s: &mut BoundedStack, &v: &u8| s.push_safe(v),
        |old_s: &BoundedStack, &v: &u8, new_s: &BoundedStack, &new_len: &u8| {
            new_s.__anneal_type_invariant_bounded_stack()
                && new_s.len == old_s.len + 1
                && new_len == new_s.len
                && new_s.slots[old_s.len as usize] == v
        },
        |old_s: &BoundedStack, post_s: &BoundedStack| post_s == old_s,
    );
    assert!(st_stats.abort_cond_hits > 0);
    assert!(st_stats.panic_state_inv_checks > 0);

    // Stateful `check_stateful_panic_contract_unwind!` without `panic_state_inv`
    // catches a trapping `abort_cond` cleanly as `AbortConditionPanicked`.
    let st_trapped = check_stateful_panic_contract_unwind!(
        cfg,
        PanicContractMode::OnlyIf,
        |s: &BoundedStack, _v: &u8| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _v: &u8| s.len == 3,
        abort_policy = AbortPolicy::AbortOnlyIf(|s: &BoundedStack, _v: &u8| {
            assert!(s.len != 0, "stateful abort_cond trap");
            false
        }),
        |s: &mut BoundedStack, &v: &u8| s.push_safe(v),
        |old_s: &BoundedStack, &v: &u8, new_s: &BoundedStack, &new_len: &u8| {
            new_s.len == old_s.len + 1 && new_len == new_s.len && new_s.slots[old_s.len as usize] == v
        },
    );
    assert!(matches!(
        st_trapped.failure().unwrap().detail,
        PanicFailureDetail::PredicateTrapped {
            trap: PanicTrapKind::AbortConditionPanicked,
            ..
        }
    ));

    // Typed wrapper `check_fallible` parity on `NeverPanics`, `PanicsOnlyIf`,
    // `PanicsIf`, `ExactPanicContract`, and `StatefulPanicContractSpec::with_waive_abort_unchecked`.
    assert!(
        NeverPanics::new(
            |&x: &u8| Ok(x < 100),
            |&x: &u8, &r: &u8| Ok(r == x),
        )
        .check_fallible(cfg, |&x: &u8| PanicExecOutcome::Returned(x))
        .is_strong()
    );
    assert!(
        ExactPanicContract::new(
            |&x: &u8| Ok(x < 100),
            |&x: &u8| Ok(x >= 50),
            |&x: &u8, &r: &u8| Ok(r == x),
        )
        .check_fallible(cfg, |&x: &u8| {
            if x >= 50 {
                PanicExecOutcome::Panicked
            } else {
                PanicExecOutcome::Returned(x)
            }
        })
        .is_strong()
    );
    assert!(
        PanicsOnlyIf::new(
            |&x: &u8| Ok(x < 100),
            |&x: &u8| Ok(x >= 50),
            |&x: &u8, &r: &u8| Ok(r == x),
        )
        .check_fallible(cfg, |&x: &u8| PanicExecOutcome::Returned(x))
        .is_strong()
    );
    assert!(
        PanicsIf::new(|&x: &u8| Ok(x < 100), |&x: &u8| Ok(x >= 50))
            .check_fallible(cfg, |&x: &u8| {
                if x >= 50 {
                    PanicExecOutcome::Panicked
                } else {
                    PanicExecOutcome::Returned(x)
                }
            })
            .is_strong()
    );
    assert!(
        StatefulPanicContractSpec::only_if::<u8, ()>(
            |&s: &u8, _: &()| s < 100,
            |&s: &u8, _: &()| s >= 80,
            |&old_s: &u8, _: &(), &new_s: &u8, &r: &u8| new_s == old_s + 1 && r == new_s,
        )
        .with_waive_abort_unchecked()
        .check(cfg, |s: &mut u8, _: &()| {
            if *s == 0 {
                PanicExecOutcome::Aborted
            } else if *s >= 80 {
                PanicExecOutcome::Panicked
            } else {
                *s += 1;
                PanicExecOutcome::Returned(*s)
            }
        })
        .is_strong()
    );
}

#[test]
fn kani5095_raw_ident_attrs_fn_body_inner_attrs_and_attribute_macro_args() {
    use InlineBoundaryVerdict::*;
    let v = |src: &str| verify_fn_inline_never_source(src, "target");

    // rustc resolves raw-identifier attribute paths to the same builtin
    // (`#[r#inline(always)]` IS `#[inline(always)]`; the FIRST of duplicate
    // inline attributes wins), so these must not slip past the scanner.
    assert_eq!(
        v("#[r#inline(always)]\n#[inline(never)] fn target() {}"),
        ConflictingInlineAttributes
    );
    assert_eq!(
        v("#[r#cfg_attr(r#all(), inline(always))]\n#[inline(never)] fn target() {}"),
        ConflictingInlineAttributes
    );
    assert_eq!(
        v("#[r#core::r#prelude::v1::r#inline(always)] #[inline(never)] fn target() {}"),
        ConflictingInlineAttributes
    );
    assert_eq!(v("#[r#inline]\nfn target() {}"), ForbiddenInlineHint);
    assert_eq!(v("#[r#inline(r#never)] fn target() {}"), Verified);
    assert_eq!(v("#[cfg_attr(r#all(), inline(never))] fn target() {}"), Verified);

    // Inner attributes at the start of a function body apply to the function.
    assert_eq!(
        v("#[inline(never)] fn target() { #![inline(always)] }"),
        ConflictingInlineAttributes
    );
    assert_eq!(
        v("#[inline(never)] fn target() -> u8 { #![allow(unused)] #![inline] 3 }"),
        ConflictingInlineAttributes
    );
    assert_eq!(v("fn target() -> u8 { #![inline(never)] 3 }"), Verified);
    assert_eq!(
        v("fn target() where [(); { 1 }]: Sized { # ! [cfg_attr(all(), inline(never))] }"),
        Verified
    );
    assert_eq!(
        v("fn target() { #![cfg_attr(test, inline(never))] }"),
        ConditionalInlineNever
    );
    // Only *leading* inner attributes count; statement attributes do not.
    assert_eq!(v("fn target() { #[inline(never)] let _x = 1; }"), MissingInlineNever);
    assert_eq!(
        v("fn g() { fn target() { #![inline(always)] } }\n#[inline(never)] fn target() {}"),
        ForbiddenInlineHint
    );
    assert_eq!(
        verify_fn_inline_never_source_with_options(
            "#[inline] fn target() { #![inline(always)] }",
            "target",
            InlineScanOptions {
                require_inline_never: false,
                ..InlineScanOptions::default()
            },
        ),
        ForbiddenInlineHint
    );

    // Attribute-macro arguments are token trees that may expand to items.
    assert_eq!(
        v("#[inline(never)] fn target() {}\n#[gen_items { fn target() {} }] struct S;"),
        MissingInlineNever
    );
    assert_eq!(
        v("#![gen_items(fn target() {})]\n#[inline(never)] fn target() {}"),
        MissingInlineNever
    );
    assert_eq!(
        v("#[gen_items { #[inline(never)] fn target() {} }] struct S;"),
        Verified
    );
}

// ===========================================================================
// 3d. `[adv ep2 A2]` Hardening: `peek_fn_body_inner` Macro Pattern Leak,
//     Static `cfg`/`cfg_attr` Dead-Item Filtering, Opaque Proc-Macro Attrs,
//     Guard-Mutant Macro Temporary Lifetime Extension & Transitive Caller
//     Trait-Dispatch Guards
// ===========================================================================

#[test]
fn kani5095_macro_pattern_lookahead_and_static_cfg_dead_decoy_hardening() {
    use InlineBoundaryVerdict::*;
    let v = |src: &str| verify_fn_inline_never_source(src, "target");

    // 1. `peek_fn_body_inner` MUST NOT look past `)`, `]`, or `=` into a macro
    //    arm's RHS block `{ #![inline(never)] }`!
    assert_eq!(
        v("macro_rules! m { (fn target()) => { #![inline(never)] }; }"),
        MissingInlineNever
    );
    assert_eq!(
        v("macro_rules! m { [fn target()] => { #![inline(never)] }; }"),
        MissingInlineNever
    );
    assert_eq!(
        v("macro_rules! m { fn target() => { #![inline(never)] }; }"),
        MissingInlineNever
    );
    // And a `#[cfg(any())]` inside a macro pattern arm must not leak past `)`
    // into the RHS `(fn target() {})`.
    assert_eq!(
        v("macro_rules! mk { (#[cfg(any())] impl $t:ty) => (fn target() {}); }"),
        MissingInlineNever
    );
    assert_eq!(
        v("macro_rules! mk { (#[cfg(any())] fn helper()) => { fn target() {} }; }"),
        MissingInlineNever
    );

    // 2. Statically disabled `#[cfg(any())]`, `#[cfg(false)]`, `#[cfg(not(all()))]`,
    //    and Kleene `#[cfg(all(test, any()))]` items/scopes are compiled out by
    //    rustc and MUST NOT satisfy target existence (`TargetFunctionNotFound`)!
    for dead_decoy in [
        "#[cfg(any())] #[inline(never)] fn target() {}",
        "#[cfg(false)] #[inline(never)] fn target() {}",
        "#[cfg(not(all()))] #[inline(never)] fn target() {}",
        "#[cfg(not(true))] #[inline(never)] fn target() {}",
        "#[cfg(all(feature = \"x\", any()))] #[inline(never)] fn target() {}",
        "#[cfg(all(test, false))] #[inline(never)] fn target() {}",
        "#[core::prelude::v1::cfg(any())] #[inline(never)] fn target() {}",
        "#[r#cfg(r#any())] #[inline(never)] fn target() {}",
        "#[cfg_attr(all(), cfg(any()))] #[inline(never)] fn target() {}",
        "#[cfg(any())] mod dead { #[inline(never)] pub fn target() {} }",
        "mod dead { #![cfg(any())] #[inline(never)] pub fn target() {} }",
        "#![cfg(any())]\n#[inline(never)] pub fn target() {}",
        "#[cfg(any())] impl Foo { #[inline(never)] fn target(&self) {} }",
        "#[cfg(any())] trait T { #[inline(never)] fn target(&self) {} }",
        "#[cfg(any())] extern \"C\" { #[inline(never)] fn target(); }",
        "#[cfg(any())] fn outer() { #[inline(never)] fn target() {} }",
        "fn target() { #![cfg(any())] #![inline(never)] }",
        "#[cfg(any())] const _: () = { #[inline(never)] fn target() {} };",
        "#[cfg(any())] gen_items! { #[inline(never)] fn target() {} }",
    ] {
        assert_eq!(v(dead_decoy), TargetFunctionNotFound, "{dead_decoy}");
    }

    // A dead un-annotated decoy alongside a live `#[inline(never)]` target is
    // cleanly ignored rather than causing false rejection.
    assert_eq!(
        v("#[cfg(any())] fn target() {}\n#[inline(never)] fn target() {}"),
        Verified
    );
    assert_eq!(
        v("#[cfg(any())] mod dead { fn target() {} }\n#[inline(never)] fn target() {}"),
        Verified
    );

    // 3. Generalized static `cfg` / `cfg_attr` Kleene evaluation:
    assert_eq!(v("#[cfg(true)] #[inline(never)] fn target() {}"), Verified);
    assert_eq!(v("#[cfg(not(any()))] #[inline(never)] fn target() {}"), Verified);
    assert_eq!(v("#[cfg_attr(true, inline(never))] fn target() {}"), Verified);
    assert_eq!(v("#[cfg_attr(not(any()), inline(never))] fn target() {}"), Verified);
    assert_eq!(v("#[cfg_attr(not(false), inline(never))] fn target() {}"), Verified);
    assert_eq!(
        v("#[cfg_attr(any(test, all()), inline(never))] fn target() {}"),
        Verified
    );
    // Statically false `cfg_attr` arm never applies `inline(never)` ->
    // `MissingInlineNever` (NOT `ConditionalInlineNever`) and never applies
    // `inline(always)`.
    assert_eq!(
        v("#[cfg_attr(any(), inline(never))] fn target() {}"),
        MissingInlineNever
    );
    assert_eq!(
        v("#[cfg_attr(false, inline(never))] fn target() {}"),
        MissingInlineNever
    );
    assert_eq!(
        v("#[cfg_attr(false, inline(always))] #[inline(never)] fn target() {}"),
        Verified
    );
    // Conditional `cfg_attr(feature = "x", cfg(any()))` does NOT disable the item.
    assert_eq!(
        v("#[cfg_attr(feature = \"x\", cfg(any()))] fn target() {}"),
        MissingInlineNever
    );
    // Unknown `any(feature = "x", false)` is NOT statically disabled.
    assert_eq!(
        v("#[cfg(any(feature = \"x\", false))] fn target() {}"),
        MissingInlineNever
    );
    // Malformed `cfg` predicates (`not()`, `not(a, b)`, `cfg()`) fail closed.
    assert_eq!(v("#[cfg(not())] #[inline(never)] fn target() {}"), MalformedSource);
    assert_eq!(v("#[cfg(not(a, b))] #[inline(never)] fn target() {}"), MalformedSource);
    assert_eq!(v("#[cfg()] #[inline(never)] fn target() {}"), MalformedSource);

    // 4. Opt-in `forbid_unknown_attributes`: rejects potential rewriting
    //    proc-macro attributes (`OpaqueAttributeMacro`) while permitting
    //    built-in non-rewriting rustc/tool attributes.
    let no_macros = InlineScanOptions::strict().with_forbid_unknown_attributes(true);
    let check_strict_attrs =
        |src: &str| verify_fn_inline_never_source_with_options(src, "target", no_macros);

    assert_eq!(
        check_strict_attrs("#[my_rewrite]\n#[inline(never)] fn target() {}"),
        OpaqueAttributeMacro
    );
    assert_eq!(
        check_strict_attrs("#[my_crate::rewrite(inline = \"always\")]\n#[inline(never)] fn target() {}"),
        OpaqueAttributeMacro
    );
    assert_eq!(
        check_strict_attrs("#[cfg_attr(all(), my_rewrite)]\n#[inline(never)] fn target() {}"),
        OpaqueAttributeMacro
    );
    assert_eq!(
        check_strict_attrs("#[inline(never)] fn target() { #![my_rewrite] }"),
        OpaqueAttributeMacro
    );
    assert_eq!(
        check_strict_attrs("#[unsafe(unknown_attr)]\n#[inline(never)] fn target() {}"),
        OpaqueAttributeMacro
    );
    assert_eq!(
        check_strict_attrs("#[unsafe(no_mangle, evil)]\n#[inline(never)] fn target() {}"),
        OpaqueAttributeMacro
    );
    // Default (`forbid_unknown_attributes: false`) still allows custom attrs.
    assert_eq!(
        v("#[spec(requires = true)]\n#[inline(never)] fn target() {}"),
        Verified
    );
    // Built-in non-rewriting rustc/tool attrs pass even with `forbid_unknown_attributes: true`.
    assert_eq!(
        check_strict_attrs(
            "#[doc = \"audited\"]\n\
             #[allow(dead_code)]\n\
             #[clippy::allow_attributes]\n\
             #[rustfmt::skip]\n\
             #[cold]\n\
             #[must_use]\n\
             #[track_caller]\n\
             #[unsafe(no_mangle)]\n\
             #[unsafe(export_name = \"target_sym\")]\n\
             #[cfg(true)]\n\
             #[cfg_attr(false, my_dead_proc_macro)]\n\
             #[inline(never)]\n\
             pub fn target() -> u8 { 1 }"
        ),
        Verified
    );
}

#[test]
fn guard_mutant_unwind_macros_extend_lifetime_for_capturing_non_copy_closures() {
    let cfg = PanicCheckConfig::default().with_max_trials(128);
    let msg1 = String::from("dropped_guard_capture");
    let msg2 = String::from("spurious_zero_capture");

    // Both single `let` bindings AND array literals MUST extend the temporary
    // lifetime of capturing non-`Copy` closures cleanly (no E0716 / E0507).
    let single_mutant = panic_guard_mutant_unwind!("single_capturing", move |&(a, b): &(u8, u8)| {
        let _ = msg1.len();
        a.wrapping_add(b)
    });
    let array_mutants = [
        single_mutant,
        panic_guard_mutant_unwind!("array_capturing", move |&(a, b): &(u8, u8)| {
            assert!(a != 0 || b != 0, "{}", msg2);
            checked_add_u8(a, b)
        }),
    ];
    let res = ExactPanicContract::new(
        |&(_a, _b): &(u8, u8)| true,
        |&(a, b): &(u8, u8)| (a as u16) + (b as u16) > u8::MAX as u16,
        |&(a, b): &(u8, u8), &out: &u8| out == a + b,
    )
    .check_guard_mutants(
        cfg,
        panic_unwind_runner!(|&(a, b): &(u8, u8)| checked_add_u8(a, b)),
        &array_mutants,
    );
    let stats = res
        .into_result()
        .expect("capturing guard mutants must compile and all be killed");
    assert_eq!(stats.guard_mutants_killed, 2);

    // Stateful counterpart with capturing non-`Copy` `String`s in `let` & `[...]`.
    let smsg1 = String::from("stateful_corrupt_capture");
    let smsg2 = String::from("stateful_wrong_ret_capture");
    let single_st = stateful_panic_guard_mutant_unwind!(
        "stateful_single_capturing",
        move |s: &mut BoundedStack, &val: &u8| {
            let _ = smsg1.len();
            s.push_corrupting(val)
        }
    );
    let array_st = [
        single_st,
        stateful_panic_guard_mutant_unwind!(
            "stateful_array_capturing",
            move |s: &mut BoundedStack, &val: &u8| {
                let _ = smsg2.len();
                s.push_safe(val).wrapping_sub(1)
            }
        ),
    ];
    let st_res = StatefulPanicContractSpec::exact::<BoundedStack, u8>(
        |s: &BoundedStack, _v: &u8| s.__anneal_type_invariant_bounded_stack(),
        |s: &BoundedStack, _v: &u8| s.len == 3,
        |old_s: &BoundedStack, &val: &u8, new_s: &BoundedStack, &new_len: &u8| {
            new_s.__anneal_type_invariant_bounded_stack()
                && new_s.len == old_s.len + 1
                && new_len == new_s.len
                && new_s.slots[old_s.len as usize] == val
        },
    )
    .with_panic_state_inv(|old_s: &BoundedStack, post_s: &BoundedStack| post_s == old_s)
    .check_guard_mutants(
        cfg,
        stateful_panic_unwind_runner!(|s: &mut BoundedStack, &val: &u8| s.push_safe(val)),
        &array_st,
    );
    let st_stats = st_res
        .into_result()
        .expect("capturing stateful guard mutants must compile and all be killed");
    assert_eq!(st_stats.guard_mutants_killed, 2);
}

#[test]
fn kani5095_verify_reachable_callees_rejects_trait_dispatched_expected_caller() {
    const CALLER: &str = "crate::api::wrapper_caller";
    const TARGET: &str = "crate::math::checked_add_u8";

    let caller_blocks = [MirBlockSummary::call(TARGET, &[1]), MirBlockSummary::ret()];
    let callees = [CalleeEntry::new(CALLER, &caller_blocks)];
    let caller_override = [TraitImplBinding::new(CALLER, "crate::api::inlined_wrapper")];

    // Direct `verify_reachable_callees_call_sites` rejects trait-dispatched expected caller
    // whether the override lives in `caller_trait_impls` or inside a callee's `trait_impls`.
    assert_eq!(
        verify_reachable_callees_call_sites(&callees, &caller_override, &[(CALLER, 1)], TARGET),
        CallBoundaryVerdict::ExpectedCallerTraitDispatched { caller_index: 0 }
    );
    let hidden_callees = [CalleeEntry::with_trait_impls(
        CALLER,
        &caller_blocks,
        &caller_override,
    )];
    assert_eq!(
        verify_reachable_callees_call_sites(&hidden_callees, &[], &[(CALLER, 1)], TARGET),
        CallBoundaryVerdict::ExpectedCallerTraitDispatched { caller_index: 0 }
    );

    // `CallBoundaryGuard::verify_caller_in_callees` respects `forbid_trait_dispatch`.
    let guard = CallBoundaryGuard::new(CALLER, TARGET);
    assert_eq!(
        guard.verify_caller_in_callees(&callees, &caller_override),
        CallBoundaryVerdict::ExpectedCallerTraitDispatched { caller_index: 0 }
    );
    assert!(
        guard
            .with_forbid_trait_dispatch(false)
            .verify_caller_in_callees(&callees, &caller_override)
            .is_preserved()
    );
}

// ===========================================================================
// 3c. `[adv ep2 B3]` Disabled-cfg skipping must never swallow live items
// ===========================================================================

#[test]
fn kani5095_disabled_cfg_inline_const_block_does_not_swallow_live_items() {
    use InlineBoundaryVerdict::*;
    let v = |src: &str| verify_fn_inline_never_source(src, "target");
    let wrap = |body: &str| {
        format!("#[inline(never)] pub fn target() {{}}\nmod m {{ {body} }}\n")
    };

    // An inline `const { .. }` block statement is block-like (no trailing
    // `;`). Skipping a disabled one "to the next `;`" swallowed the live,
    // un-annotated `fn target` that follows. All of these compile with rustc.
    for live_hidden in [
        "fn g() { #[cfg(any())] const { } fn target() {} }",
        "fn g() { #[cfg(any())] const { fn inner() {} } fn target() {} }",
        "fn g() { #[cfg(false)] const { 1 }; fn target() {} }",
        "fn g() { #[cfg(any())] unsafe { } #[cfg(any())] const { } fn target() {} }",
        "fn g() { let _ = const { 1 }; #[cfg(any())] const { } fn target() {} }",
        "fn g() { #[cfg(any())] const _: () = (); fn target() {} }",
        "fn g() { const { fn target() {} } }",
    ] {
        assert_eq!(v(&wrap(live_hidden)), MissingInlineNever, "{live_hidden}");
    }

    // A genuinely disabled inline-const block is brace-matched exactly, so
    // dead un-annotated decoys inside it are still ignored.
    assert_eq!(
        v(&wrap("fn g() { #[cfg(any())] const { fn target() {} } }")),
        Verified
    );
    assert_eq!(
        v(&wrap("fn g() { #[cfg(not(all()))] unsafe { fn target() {} } }")),
        Verified
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
