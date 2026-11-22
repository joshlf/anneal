// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for `anneal_spec::spec_check` exercising real `#[spec]`,
//! `#[embed_spec]`, and `#[external_spec]` macro-generated companions.

use core::num::Wrapping;

use anneal_spec::spec_check::{
    FailureDetail, ProbeDomain, ReturnMutants, SampleInput, SpecCheckConfig, SpecCheckOutcome,
    SplitMix64, SyntacticBindingHint, TrapKind, VacuityClass, ViolationKind,
    assert_contract_strong, assert_stateful_contract_strong, check_contract,
    check_contract_fallible, check_contract_with_mutants, check_stateful_contract,
    check_stateful_contract_fallible,
};
use anneal_spec::*;

// ---------------------------------------------------------------------------
// Strong contract fixtures
// ---------------------------------------------------------------------------

#[external_spec(
    for = u32::checked_add,
    pure,
    total,
    ensures: |ret| match ret {
        Some(sum) => (a as u64) + (b as u64) == (sum as u64),
        None => (a as u64) + (b as u64) > (u32::MAX as u64),
    },
)]
fn spec_u32_checked_add(a: u32, b: u32) -> Option<u32>;

#[external_spec(
    for = <[u32]>::is_empty,
    pure,
    total,
    ensures: |empty| empty == (slice.len() == 0),
)]
fn spec_slice_u32_is_empty(slice: &[u32]) -> bool;

#[external_spec(
    for = <[u32]>::len,
    pure,
    total,
    ensures: |len| [
        len == slice.len(),
        (len == 0) == slice.is_empty(),
    ],
)]
fn spec_slice_u32_len(slice: &[u32]) -> usize;

#[spec(
    pure,
    total,
    requires: lo <= hi,
    ensures: |ret| [
        ret >= lo,
        ret <= hi,
        (val < lo && ret == lo)
            || (val > hi && ret == hi)
            || (val >= lo && val <= hi && ret == val),
    ],
)]
fn clamp_u32(val: u32, lo: u32, hi: u32) -> u32 {
    if val < lo {
        lo
    } else if val > hi {
        hi
    } else {
        val
    }
}

#[spec(
    pure,
    total,
    ensures: |ret| match ret {
        Ok(q) => divisor != 0 && q == dividend / divisor,
        Err(code) => divisor == 0 && code == 1,
    },
)]
fn checked_div_u32(dividend: u32, divisor: u32) -> Result<u32, u8> {
    if divisor == 0 {
        Err(1)
    } else {
        Ok(dividend / divisor)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Counter {
    value: u32,
    limit: u32,
}

impl SampleInput for Counter {
    const BOUNDARY_COUNT: usize = <(u32, u32) as SampleInput>::BOUNDARY_COUNT;

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        let (value, limit) = <(u32, u32) as SampleInput>::sample_at(trial_idx, rng);
        Self { value, limit }
    }
}

impl ReturnMutants for Counter {
    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        (self.value, self.limit).visit_mutants(rng, |(value, limit)| {
            emit(Self { value, limit });
        });
    }
}

#[embed_spec]
impl Counter {
    #[embed_spec(
        requires: self.value < self.limit,
        maintains: self.value <= self.limit,
        captures: prev = self.value,
        ensures: |out| prev.checked_add(1) == Some(out),
    )]
    fn step(&mut self) -> u32 {
        self.value += 1;
        self.value
    }
}

#[spec(
    requires: x < 100,
    ensures: |_unit| x < 100,
)]
fn stateless_unit_fn(x: u32) {
    let _ = x;
}

#[spec(
    requires: *x < u32::MAX,
    ensures: |_unit| *x > 0,
)]
fn inc_in_place(x: &mut u32) {
    *x += 1;
}

// ---------------------------------------------------------------------------
// Vacuous / violating contract fixtures (covering all 5 VacuityClass variants)
// ---------------------------------------------------------------------------

#[spec(
    requires: [x > 100, x < 50],
    ensures: |r| r == x,
)]
fn dead_precondition_fn(x: u32) -> u32 {
    x
}

#[external_spec(
    for = u32::wrapping_add,
    pure,
    total,
    requires: [a < 1_000, b < 1_000],
    ensures: |r| r == a.wrapping_add(b).wrapping_add(1),
)]
fn spec_dishonest_u32_wrapping_add(a: u32, b: u32) -> u32;

#[spec(
    requires: x < 100,
    ensures: |r| r == x,
)]
fn panicking_body_fn(x: u32) -> u32 {
    if x == 1 {
        panic!("simulated body panic on admissible input");
    }
    x
}

#[spec(
    requires: if x == 1 { panic!("simulated requires panic") } else { x < 100 },
    ensures: |r| r == x,
)]
fn panicking_requires_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 100,
    ensures: |r| if r == 1 { panic!("simulated ensures panic") } else { r == x },
)]
fn panicking_ensures_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 100,
    ensures: |_r| true,
)]
fn trivial_const_true_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 100,
    ensures: |r| r == r,
)]
fn trivial_reflexive_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 100,
    ensures: |r| r <= u32::MAX,
)]
fn trivial_type_bound_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 100,
    ensures: |_r| x < 500,
)]
fn unbound_return_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 100,
    ensures: |r| {
        let _ = r;
        true
    },
)]
fn hinted_return_unused_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 10,
    ensures: |r| x < 10 || r == 42,
)]
fn vacuous_under_requires_fn(x: u32) -> u32 {
    x
}

// `x + 100` overflows for `x > u32::MAX - 100`, far outside `requires: x < 100`,
// so this postcondition is only total on precondition-admissible inputs.
#[spec(
    requires: x < 100,
    ensures: |_r| x + 100 < 500,
)]
fn overflow_guarded_fn(x: u32) -> u32 {
    x
}

#[spec(
    requires: x < 100,
    ensures: |r| r > 0,
)]
fn loose_positive_fn(x: u32) -> u32 {
    x + 1
}

#[spec(
    requires: x < 100,
    ensures: |r| r == 7,
)]
fn const_seven_fn(x: u32) -> u32 {
    let _ = x;
    7
}

#[spec(
    requires: x > i32::MIN,
    ensures: |r| r == -x,
)]
fn negate_i32_fn(x: i32) -> i32 {
    -x
}

#[spec(
    ensures: |r| r.0 == x.0.wrapping_add(1),
)]
fn wrapping_inc_fn(x: Wrapping<u32>) -> Wrapping<u32> {
    Wrapping(x.0.wrapping_add(1))
}

#[spec(
    ensures: |r| r == [a[0].wrapping_add(1), a[1], a[2], a[3]],
)]
fn bump_first_elem(a: [u32; 4]) -> [u32; 4] {
    [a[0].wrapping_add(1), a[1], a[2], a[3]]
}

// ---------------------------------------------------------------------------
// 1. Strong specs pass
// ---------------------------------------------------------------------------

#[test]
fn strong_external_spec_u32_checked_add_covers_some_and_none() {
    let mut saw_some = false;
    let mut saw_none = false;

    let stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(a, b): &(u32, u32)| __anodized_fn_requires_spec_u32_checked_add(a, b),
        |&(a, b)| {
            let res = a.checked_add(b);
            if res.is_some() {
                saw_some = true;
            } else {
                saw_none = true;
            }
            res
        },
        |&(a, b), &ret| __anodized_fn_ensures_spec_u32_checked_add(a, b, ret),
    );

    assert!(saw_some, "expected non-overflowing Some(a + b) trials");
    assert!(saw_none, "expected overflowing None trials");
    assert_eq!(stats.trials_run, 256);
    assert_eq!(stats.precondition_hits, 256);
    assert!(stats.mutants_killed > 0);
    assert!(!stats.subsingleton_return);
}

#[test]
fn strong_external_spec_slice_is_empty_and_len() {
    let mut saw_empty = false;
    let mut saw_non_empty = false;

    let empty_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(arr, prefix_len): &([u32; 4], usize)| {
            prefix_len <= 4 && __anodized_fn_requires_spec_slice_u32_is_empty(&arr[..prefix_len])
        },
        |&(arr, prefix_len)| {
            let slice = &arr[..prefix_len];
            let empty = slice.is_empty();
            if empty {
                saw_empty = true;
            } else {
                saw_non_empty = true;
            }
            empty
        },
        |&(arr, prefix_len), &ret| {
            __anodized_fn_ensures_spec_slice_u32_is_empty(&arr[..prefix_len], ret)
        },
    );

    assert!(saw_empty, "expected empty slice trials");
    assert!(saw_non_empty, "expected non-empty slice trials");
    assert!(empty_stats.mutants_killed > 0);

    let len_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(arr, prefix_len): &([u32; 4], usize)| {
            prefix_len <= 4 && __anodized_fn_requires_spec_slice_u32_len(&arr[..prefix_len])
        },
        |&(arr, prefix_len)| arr[..prefix_len].len(),
        |&(arr, prefix_len), &ret| {
            __anodized_fn_ensures_spec_slice_u32_len(&arr[..prefix_len], ret)
        },
    );
    assert!(len_stats.precondition_hits > 0);
    assert!(len_stats.mutants_killed > 0);
}

#[test]
fn strong_spec_clamp_u32_covers_all_regions() {
    let mut saw_below = false;
    let mut saw_in_range = false;
    let mut saw_above = false;
    let mut saw_eq_bounds = false;

    let stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(val, lo, hi): &(u32, u32, u32)| __anodized_fn_requires_clamp_u32(val, lo, hi),
        |&(val, lo, hi)| {
            if lo == hi {
                saw_eq_bounds = true;
            }
            if val < lo {
                saw_below = true;
            } else if val > hi {
                saw_above = true;
            } else {
                saw_in_range = true;
            }
            clamp_u32(val, lo, hi)
        },
        |&(val, lo, hi), &ret| __anodized_fn_ensures_clamp_u32(val, lo, hi, ret),
    );

    assert!(saw_below, "expected val < lo trials");
    assert!(saw_in_range, "expected lo <= val <= hi trials");
    assert!(saw_above, "expected val > hi trials");
    assert!(saw_eq_bounds, "expected lo == hi trials");
    assert!(stats.precondition_hits > 0);
    assert!(stats.mutants_killed > 0);
}

#[test]
fn strong_spec_checked_div_result_covers_ok_and_err() {
    let mut saw_ok = false;
    let mut saw_err = false;

    let stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(dividend, divisor): &(u32, u32)| {
            __anodized_fn_requires_checked_div_u32(dividend, divisor)
        },
        |&(dividend, divisor)| {
            let res = checked_div_u32(dividend, divisor);
            match res {
                Ok(_) => saw_ok = true,
                Err(_) => saw_err = true,
            }
            res
        },
        |&(dividend, divisor), &ret| __anodized_fn_ensures_checked_div_u32(dividend, divisor, ret),
    );

    assert!(saw_ok, "expected Ok quotient trials");
    assert!(saw_err, "expected Err divide-by-zero trials");
    assert!(stats.mutants_killed > 0);
}

#[test]
fn strong_stateful_counter_step_and_half_weak_detection() {
    let stats = assert_stateful_contract_strong(
        SpecCheckConfig::default(),
        |old: &Counter, &()| old.clone().__anodized_fn_requires_step(),
        |counter: &mut Counter, &()| counter.step(),
        |old: &Counter, &(), new: &Counter, ret: &u32| {
            old.clone().__anodized_fn_ensures_step(*ret)
                && new.value == *ret
                && new.limit == old.limit
        },
    );
    assert!(stats.precondition_hits > 0);
    assert!(stats.mutants_killed > 0);
    assert!(!stats.subsingleton_return);

    // Ignoring `ret` while constraining only `new` state must fail.
    let missing_ret_check = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &Counter, &()| old.clone().__anodized_fn_requires_step(),
        |counter: &mut Counter, &()| counter.step(),
        |old: &Counter, &(), new: &Counter, _ret: &u32| {
            old.value.checked_add(1) == Some(new.value) && new.limit == old.limit
        },
    );
    assert_eq!(
        missing_ret_check.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
    assert!(matches!(
        missing_ret_check.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed: 0,
            state_mutants_killed,
            ..
        }) if state_mutants_killed > 0
    ));

    // Ignoring `new` state while constraining only `ret` must fail.
    let missing_state_check = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &Counter, &()| old.clone().__anodized_fn_requires_step(),
        |counter: &mut Counter, &()| counter.step(),
        |old: &Counter, &(), _new: &Counter, ret: &u32| {
            old.clone().__anodized_fn_ensures_step(*ret)
        },
    );
    assert_eq!(
        missing_state_check.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
    assert!(matches!(
        missing_state_check.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed,
            state_mutants_killed: 0,
            ..
        }) if return_mutants_killed > 0
    ));
}

#[test]
fn subsingleton_stateless_unit_exempt_vs_stateful_unit_state_revert_caught() {
    // Stateless `-> ()` with satisfiable `requires` is exempt from output-mutant dichotomy.
    let stateless_outcome = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_stateless_unit_fn(x),
        |&x| stateless_unit_fn(x),
        |&x, &unit| __anodized_fn_ensures_stateless_unit_fn(x, unit),
    );
    assert!(stateless_outcome.is_strong());
    assert_eq!(stateless_outcome.vacuity_class(), None);
    let stateless_stats = stateless_outcome.stats();
    assert!(stateless_stats.subsingleton_return);
    assert_eq!(stateless_stats.mutants_tested, 0);

    // Explicit `SyntacticallyTautological` hint still flags a tautological unit postcondition.
    let hinted_unit = check_contract(
        SpecCheckConfig::default()
            .with_syntactic_hint(SyntacticBindingHint::SyntacticallyTautological),
        |&x: &u32| __anodized_fn_requires_stateless_unit_fn(x),
        |&x| stateless_unit_fn(x),
        |&x, &unit| __anodized_fn_ensures_stateless_unit_fn(x, unit),
    );
    assert_eq!(
        hinted_unit.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );

    // Stateful `&mut u32 -> ()`: strong postcondition kills the pre-state revert `bad_s = old_s`.
    let stateful_stats = assert_stateful_contract_strong(
        SpecCheckConfig::default(),
        |old: &u32, &()| {
            let mut copy = *old;
            __anodized_fn_requires_inc_in_place(&mut copy)
        },
        |x: &mut u32, &()| inc_in_place(x),
        |old: &u32, &(), new: &u32, &()| {
            let mut copy = *new;
            __anodized_fn_ensures_inc_in_place(&mut copy, ()) && old.checked_add(1) == Some(*new)
        },
    );
    assert!(stateful_stats.subsingleton_return);
    assert!(stateful_stats.mutants_killed > 0);

    // Stateful `&mut u32 -> ()` with a vacuous postcondition is NOT exempt!
    let vacuous_stateful = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < u32::MAX,
        |x: &mut u32, &()| inc_in_place(x),
        |_old: &u32, &(), _new: &u32, &()| true,
    );
    assert_eq!(
        vacuous_stateful.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );

    // Stateful `&mut u32 -> ()` with a no-op buggy body violates the strong postcondition.
    let noop_bug = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < u32::MAX,
        |_x: &mut u32, &()| {},
        |old: &u32, &(), new: &u32, &()| old.checked_add(1) == Some(*new),
    );
    assert_eq!(noop_bug.vacuity_class(), Some(VacuityClass::SpecViolation));
}

// ---------------------------------------------------------------------------
// 2. All 5 Vacuity / Failure Classes Caught with Exact Variant
// ---------------------------------------------------------------------------

#[test]
fn catches_dead_precondition() {
    let outcome = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_dead_precondition_fn(x),
        |&x| dead_precondition_fn(x),
        |&x, &r| __anodized_fn_ensures_dead_precondition_fn(x, r),
    );
    assert!(!outcome.is_strong());
    assert_eq!(
        outcome.vacuity_class(),
        Some(VacuityClass::DeadPrecondition)
    );
    let failure = outcome.into_result().unwrap_err();
    assert_eq!(failure.stats.precondition_hits, 0);
    assert_eq!(failure.stats.trials_run, 256);
    assert_eq!(
        failure.detail,
        FailureDetail::InsufficientPreconditionHits {
            required: 1,
            observed: 0,
        }
    );
}

#[test]
fn catches_spec_violation_dishonest_external_spec() {
    let outcome = check_contract(
        SpecCheckConfig::default(),
        |&(a, b): &(u32, u32)| __anodized_fn_requires_spec_dishonest_u32_wrapping_add(a, b),
        |&(a, b)| a.wrapping_add(b),
        |&(a, b), &r| __anodized_fn_ensures_spec_dishonest_u32_wrapping_add(a, b, r),
    );
    assert_eq!(outcome.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert!(matches!(
        outcome.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(
            ViolationKind::PostconditionFalse { .. }
        ))
    ));
}

#[test]
fn catches_spec_violation_panics_never_swallowed() {
    // 1. Panicking body is reported as SpecViolation(BodyPanicked), never skipped.
    let body_panic = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| {
            std::panic::catch_unwind(move || __anodized_fn_requires_panicking_body_fn(x))
                .map_err(|_| ())
        },
        |&x| std::panic::catch_unwind(move || panicking_body_fn(x)).map_err(|_| ()),
        |&x, &r| {
            std::panic::catch_unwind(move || __anodized_fn_ensures_panicking_body_fn(x, r))
                .map_err(|_| ())
        },
    );
    assert_eq!(
        body_panic.vacuity_class(),
        Some(VacuityClass::SpecViolation)
    );
    assert!(matches!(
        body_panic.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trap: TrapKind::BodyPanicked,
            ..
        }))
    ));

    // 2. Panicking requires is reported as SpecViolation(PreconditionPanicked), never false.
    let pre_panic = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| {
            std::panic::catch_unwind(move || __anodized_fn_requires_panicking_requires_fn(x))
                .map_err(|_| ())
        },
        |&x| std::panic::catch_unwind(move || panicking_requires_fn(x)).map_err(|_| ()),
        |&x, &r| {
            std::panic::catch_unwind(move || __anodized_fn_ensures_panicking_requires_fn(x, r))
                .map_err(|_| ())
        },
    );
    assert_eq!(pre_panic.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert!(matches!(
        pre_panic.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trap: TrapKind::PreconditionPanicked,
            ..
        }))
    ));

    // 3. Panicking ensures on live output is reported as SpecViolation(PostconditionPanicked).
    let post_panic = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| {
            std::panic::catch_unwind(move || __anodized_fn_requires_panicking_ensures_fn(x))
                .map_err(|_| ())
        },
        |&x| std::panic::catch_unwind(move || panicking_ensures_fn(x)).map_err(|_| ()),
        |&x, &r| {
            std::panic::catch_unwind(move || __anodized_fn_ensures_panicking_ensures_fn(x, r))
                .map_err(|_| ())
        },
    );
    assert_eq!(
        post_panic.vacuity_class(),
        Some(VacuityClass::SpecViolation)
    );
    assert!(matches!(
        post_panic.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trap: TrapKind::PostconditionPanicked,
            ..
        }))
    ));
}

#[test]
fn catches_trivial_postcondition_variants() {
    let const_true = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_trivial_const_true_fn(x),
        |&x| trivial_const_true_fn(x),
        |&x, &r| __anodized_fn_ensures_trivial_const_true_fn(x, r),
    );
    assert_eq!(
        const_true.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );

    let reflexive = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_trivial_reflexive_fn(x),
        |&x| trivial_reflexive_fn(x),
        |&x, &r| __anodized_fn_ensures_trivial_reflexive_fn(x, r),
    );
    assert_eq!(
        reflexive.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );

    let type_bound = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_trivial_type_bound_fn(x),
        |&x| trivial_type_bound_fn(x),
        |&x, &r| __anodized_fn_ensures_trivial_type_bound_fn(x, r),
    );
    assert_eq!(
        type_bound.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
}

#[test]
fn catches_unbound_return_output_dynamic_and_hinted() {
    // `x < 500` is total, so the probe may leave `requires: x < 100`: it is false for
    // `x >= 500`, yet independent of `r`.
    let dynamic_outcome = check_contract(
        SpecCheckConfig::default().with_probe_domain(ProbeDomain::Unconstrained),
        |&x: &u32| __anodized_fn_requires_unbound_return_fn(x),
        |&x| unbound_return_fn(x),
        |&x, &r| __anodized_fn_ensures_unbound_return_fn(x, r),
    );
    assert_eq!(
        dynamic_outcome.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
    assert!(matches!(
        dynamic_outcome.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            out_of_precondition_probes,
            saw_any_false: true,
            saw_output_sensitivity: false,
            ..
        }) if out_of_precondition_probes > 0
    ));

    // Inside `requires: x < 100` the same postcondition never rejects anything, so the
    // default precondition-only probe still fails closed, reports it as trivially true
    // on its domain, and records that inputs were withheld from `post`.
    let default_outcome = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_unbound_return_fn(x),
        |&x| unbound_return_fn(x),
        |&x, &r| __anodized_fn_ensures_unbound_return_fn(x, r),
    );
    assert!(!default_outcome.is_strong());
    assert_eq!(
        default_outcome.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(matches!(
        default_outcome.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            out_of_precondition_probes: 0,
            skipped_out_of_precondition,
            saw_any_false: false,
            saw_output_sensitivity: false,
            ..
        }) if skipped_out_of_precondition > 0
    ));

    // Syntactically hinted detection on `let _ = r; true`.
    let hinted_outcome = check_contract(
        SpecCheckConfig::default().with_syntactic_hint(SyntacticBindingHint::ReturnUnused),
        |&x: &u32| __anodized_fn_requires_hinted_return_unused_fn(x),
        |&x| hinted_return_unused_fn(x),
        |&x, &r| __anodized_fn_ensures_hinted_return_unused_fn(x, r),
    );
    assert_eq!(
        hinted_outcome.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
}

#[test]
fn catches_survived_all_mutants_under_requires_and_weak_bank() {
    // `x < 10 || r == 42` is total and output-sensitive when `x >= 10`, yet every mutant
    // survives under `x < 10`.
    let vacuous_under_req = check_contract(
        SpecCheckConfig::default().with_probe_domain(ProbeDomain::Unconstrained),
        |&x: &u32| __anodized_fn_requires_vacuous_under_requires_fn(x),
        |&x| vacuous_under_requires_fn(x),
        |&x, &r| __anodized_fn_ensures_vacuous_under_requires_fn(x, r),
    );
    assert_eq!(
        vacuous_under_req.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert!(matches!(
        vacuous_under_req.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            saw_any_false: true,
            saw_output_sensitivity: true,
            ..
        })
    ));

    // The default precondition-only probe never leaves `x < 10`, where the postcondition
    // is identically true; it still fails closed.
    let default_under_req = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_vacuous_under_requires_fn(x),
        |&x| vacuous_under_requires_fn(x),
        |&x, &r| __anodized_fn_ensures_vacuous_under_requires_fn(x, r),
    );
    assert!(!default_under_req.is_strong());
    assert_eq!(
        default_under_req.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(matches!(
        default_under_req.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            out_of_precondition_probes: 0,
            saw_any_false: false,
            ..
        })
    ));

    // Custom weak mutant bank where every candidate satisfies `r > 0`.
    let weak_bank = check_contract_with_mutants(
        SpecCheckConfig::default(),
        &[1u32, 2, 3, 5, 10],
        |&x: &u32| __anodized_fn_requires_loose_positive_fn(x),
        |&x| loose_positive_fn(x),
        |&x, &r| __anodized_fn_ensures_loose_positive_fn(x, r),
    );
    assert_eq!(
        weak_bank.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert!(weak_bank.stats().mutants_tested > 0);
    assert_eq!(weak_bank.stats().mutants_killed, 0);

    // By contrast, the default mutant generator emits `0` and kills `r > 0`.
    let default_strong = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_loose_positive_fn(x),
        |&x| loose_positive_fn(x),
        |&x, &r| __anodized_fn_ensures_loose_positive_fn(x, r),
    );
    assert!(default_strong.is_strong());
}

// ---------------------------------------------------------------------------
// 3. Zero-Trial & Degenerate Config Guards (Fail-Closed)
// ---------------------------------------------------------------------------

#[test]
fn degenerate_configs_and_duplicate_mutant_slices_fail_closed() {
    let zero_trials = check_contract(
        SpecCheckConfig::default().with_max_trials(0),
        |&x: &u32| __anodized_fn_requires_const_seven_fn(x),
        |&x| const_seven_fn(x),
        |&x, &r| __anodized_fn_ensures_const_seven_fn(x, r),
    );
    assert!(!zero_trials.is_strong());
    assert_eq!(
        zero_trials.vacuity_class(),
        Some(VacuityClass::DeadPrecondition)
    );
    assert_eq!(
        zero_trials.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::DegenerateConfig))
    );

    let zero_min_hits = check_contract(
        SpecCheckConfig::default().with_min_precondition_hits(0),
        |&x: &u32| __anodized_fn_requires_const_seven_fn(x),
        |&x| const_seven_fn(x),
        |&x, &r| __anodized_fn_ensures_const_seven_fn(x, r),
    );
    assert!(!zero_min_hits.is_strong());
    assert_eq!(
        zero_min_hits.vacuity_class(),
        Some(VacuityClass::DeadPrecondition)
    );
    assert_eq!(
        zero_min_hits.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::DegenerateConfig))
    );

    let zero_mutants = check_contract(
        SpecCheckConfig::default().with_max_mutants_per_hit(0),
        |&x: &u32| __anodized_fn_requires_const_seven_fn(x),
        |&x| const_seven_fn(x),
        |&x, &r| __anodized_fn_ensures_const_seven_fn(x, r),
    );
    assert!(!zero_mutants.is_strong());
    assert_eq!(
        zero_mutants.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert_eq!(zero_mutants.stats().mutants_tested, 0);

    // Duplicate-only custom mutant slice `&[ret_ok]` must skip equals and fail closed.
    let dup_only = check_contract_with_mutants(
        SpecCheckConfig::default(),
        &[7u32, 7u32],
        |&x: &u32| __anodized_fn_requires_const_seven_fn(x),
        |&x| const_seven_fn(x),
        |&x, &r| __anodized_fn_ensures_const_seven_fn(x, r),
    );
    assert!(!dup_only.is_strong());
    assert_eq!(
        dup_only.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert_eq!(dup_only.stats().mutants_tested, 0);
    assert_eq!(
        dup_only.failure().map(|f| f.detail),
        Some(FailureDetail::NoDistinctMutantsTested)
    );

    // Stateful degenerate config guards also fail closed.
    let stateful_zero_trials = check_stateful_contract(
        SpecCheckConfig::default().with_max_trials(0),
        |old: &u32, &()| *old < u32::MAX,
        |x: &mut u32, &()| inc_in_place(x),
        |old: &u32, &(), new: &u32, &()| old.checked_add(1) == Some(*new),
    );
    assert_eq!(
        stateful_zero_trials.vacuity_class(),
        Some(VacuityClass::DeadPrecondition)
    );

    let stateful_zero_mutants = check_stateful_contract(
        SpecCheckConfig::default().with_max_mutants_per_hit(0),
        |old: &u32, &()| *old < u32::MAX,
        |x: &mut u32, &()| inc_in_place(x),
        |old: &u32, &(), new: &u32, &()| old.checked_add(1) == Some(*new),
    );
    assert_eq!(
        stateful_zero_mutants.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
}

#[test]
#[should_panic(expected = "DeadPrecondition")]
fn assert_contract_strong_panics_with_canonical_name() {
    assert_contract_strong(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_dead_precondition_fn(x),
        |&x| dead_precondition_fn(x),
        |&x, &r| __anodized_fn_ensures_dead_precondition_fn(x, r),
    );
}

// ---------------------------------------------------------------------------
// 4. Determinism, Taxonomy Names, and Composite Type Coverage
// ---------------------------------------------------------------------------

#[test]
fn vacuity_class_canonical_names_and_determinism() {
    assert_eq!(
        VacuityClass::DeadPrecondition.canonical_name(),
        "DeadPrecondition"
    );
    assert_eq!(
        VacuityClass::SpecViolation.canonical_name(),
        "SpecViolation"
    );
    assert_eq!(
        VacuityClass::TrivialPostcondition.canonical_name(),
        "TrivialPostcondition"
    );
    assert_eq!(
        VacuityClass::UnboundReturnOutput.canonical_name(),
        "UnboundReturnOutput"
    );
    assert_eq!(
        VacuityClass::SurvivedAllMutants.canonical_name(),
        "SurvivedAllMutants"
    );

    let cfg = SpecCheckConfig::default().with_seed(0xDEAD_BEEF_CAFE_BABE);
    let run1 = check_contract(
        cfg,
        |&(val, lo, hi): &(u32, u32, u32)| __anodized_fn_requires_clamp_u32(val, lo, hi),
        |&(val, lo, hi)| clamp_u32(val, lo, hi),
        |&(val, lo, hi), &ret| __anodized_fn_ensures_clamp_u32(val, lo, hi, ret),
    );
    let run2 = check_contract(
        cfg,
        |&(val, lo, hi): &(u32, u32, u32)| __anodized_fn_requires_clamp_u32(val, lo, hi),
        |&(val, lo, hi)| clamp_u32(val, lo, hi),
        |&(val, lo, hi), &ret| __anodized_fn_ensures_clamp_u32(val, lo, hi, ret),
    );
    assert_eq!(run1, run2);
    assert!(matches!(run1, SpecCheckOutcome::Strong(_)));
}

#[test]
fn signed_wrapping_option_unit_tuples_and_arrays_supported() {
    // Signed integer negation (`i32::MIN` rejected by `requires: x > i32::MIN`).
    let neg_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&x: &i32| __anodized_fn_requires_negate_i32_fn(x),
        |&x| negate_i32_fn(x),
        |&x, &r| __anodized_fn_ensures_negate_i32_fn(x, r),
    );
    assert!(neg_stats.precondition_hits > 0);
    assert!(neg_stats.mutants_killed > 0);

    // `core::num::Wrapping<u32>`.
    let wrap_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&x: &Wrapping<u32>| __anodized_fn_requires_wrapping_inc_fn(x),
        |&x| wrapping_inc_fn(x),
        |&x, &r| __anodized_fn_ensures_wrapping_inc_fn(x, r),
    );
    assert!(wrap_stats.mutants_killed > 0);

    // `Option<()>` has TWO inhabitants (`None`, `Some(())`), so it is NOT subsingleton.
    assert!(!<Option<()> as ReturnMutants>::IS_SUBSINGLETON);
    assert!(<[u32; 0] as ReturnMutants>::IS_SUBSINGLETON);
    assert!(<[(); 4] as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<[u32; 4] as ReturnMutants>::IS_SUBSINGLETON);

    let opt_unit_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&b: &bool| {
            let _ = b;
            true
        },
        |&b| if b { Some(()) } else { None },
        |&b, &ret| ret.is_some() == b,
    );
    assert!(!opt_unit_stats.subsingleton_return);
    assert!(opt_unit_stats.mutants_killed > 0);

    // Fixed-size array `[u32; 4]` input and return mutants.
    let arr_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&a: &[u32; 4]| __anodized_fn_requires_bump_first_elem(a),
        |&a| bump_first_elem(a),
        |&a, &r| __anodized_fn_ensures_bump_first_elem(a, r),
    );
    assert!(arr_stats.mutants_killed > 0);

    // 1-tuple and 4-tuple input sampling + 3-tuple return mutants.
    let tuple4_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(a, b, c, d): &(u8, i8, u16, bool)| {
            let _ = (a, b, c, d);
            true
        },
        |&(a, b, c, d)| (a, b, if d { c } else { 0 }),
        |&(a, b, c, d), &(ra, rb, rc)| ra == a && rb == b && rc == if d { c } else { 0 },
    );
    assert!(tuple4_stats.mutants_killed > 0);

    let tuple1_stats = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(x,): &(u64,)| x < u64::MAX,
        |&(x,)| (x + 1,),
        |&(x,), &(r,)| r == x + 1,
    );
    assert!(tuple1_stats.mutants_killed > 0);
}

// ---------------------------------------------------------------------------
// 5. Precondition-Domain Safety of the Classification Probes
// ---------------------------------------------------------------------------

#[test]
fn probe_domain_defaults_to_precondition_only() {
    assert_eq!(ProbeDomain::default(), ProbeDomain::PreconditionOnly);
    assert_eq!(
        SpecCheckConfig::default().probe_domain,
        ProbeDomain::PreconditionOnly
    );
    assert_eq!(
        SpecCheckConfig::default()
            .with_probe_domain(ProbeDomain::Unconstrained)
            .probe_domain,
        ProbeDomain::Unconstrained
    );
}

#[test]
fn classification_probe_never_evaluates_spec_ensures_outside_requires() {
    // The real `#[spec]` companion computes `x + 100`, which overflows (and panics under
    // overflow checks) on the probe's boundary inputs near `u32::MAX`. The companion is
    // called without any guard: the checker itself must keep it inside `requires`.
    let unguarded = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_overflow_guarded_fn(x),
        |&x| overflow_guarded_fn(x),
        |&x, &r| __anodized_fn_ensures_overflow_guarded_fn(x, r),
    );
    assert!(!unguarded.is_strong());
    assert_eq!(
        unguarded.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );

    // Independently of overflow checks, count every evaluation outside `requires`.
    let mut ensures_calls_outside_requires = 0usize;
    let counted = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_overflow_guarded_fn(x),
        |&x| overflow_guarded_fn(x),
        |&x, &r| {
            if !__anodized_fn_requires_overflow_guarded_fn(x) {
                ensures_calls_outside_requires += 1;
                return true;
            }
            __anodized_fn_ensures_overflow_guarded_fn(x, r)
        },
    );
    assert_eq!(ensures_calls_outside_requires, 0);
    assert_eq!(
        counted.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(matches!(
        counted.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            probed_inputs,
            out_of_precondition_probes: 0,
            skipped_out_of_precondition,
            saw_any_false: false,
            saw_output_sensitivity: false,
        }) if probed_inputs > 0 && skipped_out_of_precondition > 0
    ));
}

#[test]
fn stateless_probe_stays_inside_precondition_for_partial_postconditions() {
    const TABLE: [u32; 4] = [10, 20, 30, 40];

    // Input-only postcondition that indexes with the input: out of bounds (a panic in
    // every build profile) for any `x` violating `requires: x < TABLE.len()`.
    let indexing = check_contract(
        SpecCheckConfig::default(),
        |&x: &usize| x < TABLE.len(),
        |&x| TABLE[x],
        |&x, _r: &u32| TABLE[x] >= 10,
    );
    assert_eq!(
        indexing.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );

    // Postcondition that divides by a quantity which is zero outside `requires: x > 0`.
    let dividing = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| x > 0,
        |&x| x,
        |&x, _r: &u32| 100 / x <= 100,
    );
    assert_eq!(
        dividing.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );

    // Postcondition that asserts its own precondition, with a custom mutant bank.
    let asserting = check_contract_with_mutants(
        SpecCheckConfig::default(),
        &[1u32, 2, 3, 5, 10],
        |&x: &u32| x < 10,
        |&x| x,
        |&x, &r: &u32| {
            assert!(x < 10, "postcondition evaluated outside its precondition");
            x < 10 || r == 42
        },
    );
    assert_eq!(
        asserting.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(asserting.stats().mutants_tested > 0);
    assert_eq!(asserting.stats().mutants_killed, 0);

    // A precondition admitting a single non-boundary-adjacent value still yields probe
    // evidence, because the live anchor input is always probed.
    let narrow = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| x == 1_000,
        |&x| x,
        |&x, _r: &u32| {
            assert!(
                x == 1_000,
                "postcondition evaluated outside its precondition"
            );
            true
        },
    );
    assert_eq!(
        narrow.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(matches!(
        narrow.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            probed_inputs,
            out_of_precondition_probes: 0,
            ..
        }) if probed_inputs >= 1
    ));
}

#[test]
fn precondition_only_probe_still_finds_output_sensitivity_under_requires() {
    // `r != 100` rejects exactly one output. No first-order mutant of the outputs `0..10`
    // equals `100`, but the mutant chain walked on the admissible anchor input reaches it.
    let outcome = check_contract_with_mutants(
        SpecCheckConfig::default(),
        &[1u32, 2, 3, 5, 7],
        |&x: &u32| x < 10,
        |&x| x,
        |&x, &r: &u32| {
            assert!(x < 10, "postcondition evaluated outside its precondition");
            r != 100
        },
    );
    assert_eq!(
        outcome.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert!(matches!(
        outcome.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            out_of_precondition_probes: 0,
            saw_any_false: true,
            saw_output_sensitivity: true,
            ..
        })
    ));
}

#[test]
fn unconstrained_probe_domain_refines_classification_for_total_postconditions() {
    let unconstrained = SpecCheckConfig::default().with_probe_domain(ProbeDomain::Unconstrained);

    // `true` everywhere: trivial on the whole sampled domain.
    let trivial = check_contract(
        unconstrained,
        |&x: &u32| x < 100,
        |&x| x,
        |_x: &u32, _r: &u32| true,
    );
    assert_eq!(
        trivial.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(matches!(
        trivial.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            out_of_precondition_probes,
            skipped_out_of_precondition: 0,
            saw_any_false: false,
            ..
        }) if out_of_precondition_probes > 0
    ));

    // Input-only: false outside the precondition, never output-sensitive.
    let input_only = check_contract(
        unconstrained,
        |&x: &u32| x < 100,
        |&x| x,
        |&x, _r: &u32| x < 500,
    );
    assert_eq!(
        input_only.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );

    // Output-sensitive only outside the precondition.
    let outside_only = check_contract(
        unconstrained,
        |&x: &u32| x < 10,
        |&x| x,
        |&x, &r: &u32| x < 10 || r == 42,
    );
    assert_eq!(
        outside_only.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );

    // Through the fallible entry point a trap outside the precondition is tolerated and
    // carries no evidence: the postcondition is still trivial where it is defined.
    let partial = check_contract_fallible(
        unconstrained,
        |&x: &u32| Ok(x < 100),
        |&x| Ok(x),
        |&x, _r: &u32| if x < 100 { Ok(true) } else { Err(()) },
    );
    assert_eq!(
        partial.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(matches!(
        partial.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            out_of_precondition_probes,
            saw_any_false: false,
            saw_output_sensitivity: false,
            ..
        }) if out_of_precondition_probes > 0
    ));
}

#[test]
fn stateful_probes_stay_inside_precondition_by_default() {
    // Every postcondition below panics, in every build profile, when it is evaluated on a
    // pre-state violating `requires: *old < 100`.
    fn next(old: &u32) -> u32 {
        assert!(
            *old < 100,
            "stateful postcondition evaluated outside its precondition"
        );
        *old + 1
    }

    // (1) Vacuous along both output axes: the joint classification probe runs.
    let vacuous = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < 100,
        |state: &mut u32, &()| {
            *state += 1;
            *state
        },
        |old: &u32, &(), _new: &u32, _ret: &u32| next(old) > 0,
    );
    assert_eq!(
        vacuous.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(matches!(
        vacuous.failure().map(|f| f.detail),
        Some(FailureDetail::AllMutantsSurvived {
            probed_inputs,
            out_of_precondition_probes: 0,
            skipped_out_of_precondition,
            saw_any_false: false,
            ..
        }) if probed_inputs >= 1 && skipped_out_of_precondition > 0
    ));

    // (2) Return value unbound: the return-axis probe runs.
    let ret_unbound = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < 100,
        |state: &mut u32, &()| {
            *state += 1;
            *state
        },
        |old: &u32, &(), new: &u32, _ret: &u32| *new == next(old),
    );
    assert_eq!(
        ret_unbound.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
    assert!(matches!(
        ret_unbound.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed: 0,
            state_mutants_killed,
            ..
        }) if state_mutants_killed > 0
    ));

    // (3) Post-state unbound: the state-axis probe runs.
    let state_unbound = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < 100,
        |state: &mut u32, &()| {
            *state += 1;
            *state
        },
        |old: &u32, &(), _new: &u32, ret: &u32| *ret == next(old),
    );
    assert_eq!(
        state_unbound.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
    assert!(matches!(
        state_unbound.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed,
            state_mutants_killed: 0,
            ..
        }) if return_mutants_killed > 0
    ));

    // (4) The fully constraining contract is strong and likewise never leaves `requires`.
    let strong = assert_stateful_contract_strong(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < 100,
        |state: &mut u32, &()| {
            *state += 1;
            *state
        },
        |old: &u32, &(), new: &u32, ret: &u32| *new == next(old) && *ret == *new,
    );
    assert!(strong.mutants_killed > 0);
}

// ---------------------------------------------------------------------------
// 6. Trapping Postconditions and Fallible Stateful Contracts
// ---------------------------------------------------------------------------

#[test]
fn trapping_postcondition_rejects_mutants() {
    // Assertion-style postcondition: it traps on every wrong output instead of returning
    // `false`. Each trap rejects that mutant, so the contract is strong.
    let asserting = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| Ok(x < 100),
        |&x| Ok(x.wrapping_mul(3)),
        |&x, &r: &u32| {
            if r == x.wrapping_mul(3) {
                Ok(true)
            } else {
                Err(())
            }
        },
    );
    assert!(asserting.is_strong());
    let stats = asserting.stats();
    assert!(stats.mutants_tested > 0);
    assert_eq!(stats.mutants_killed, stats.mutants_tested);
    assert_eq!(stats.mutants_trapped, stats.mutants_killed);

    // The same holds for a real unwinding panic intercepted by `catch_unwind`: indexing
    // with an out-of-range mutant of the returned index panics.
    const SORTED: [u32; 4] = [10, 20, 30, 40];
    let indexing = check_contract_fallible(
        SpecCheckConfig::default()
            .with_max_trials(8)
            .with_max_mutants_per_hit(4),
        |&x: &usize| Ok(x < SORTED.len()),
        |&x| Ok(x),
        |&x, &r: &usize| std::panic::catch_unwind(move || SORTED[r] == SORTED[x]).map_err(|_| ()),
    );
    assert!(indexing.is_strong());
    assert!(indexing.stats().mutants_killed > 0);

    // A postcondition that returns `false` is unaffected and reports no trapped mutants.
    let plain = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| Ok(x < 100),
        |&x| Ok(x),
        |&x, &r: &u32| Ok(r == x),
    );
    assert!(plain.is_strong());
    assert_eq!(plain.stats().mutants_trapped, 0);

    // A trap on the live output is still a specification violation, never a kill.
    let live_trap = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| Ok(x < 100),
        |&x| Ok(x),
        |_x: &u32, _r: &u32| Err(()),
    );
    assert_eq!(live_trap.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert_eq!(live_trap.stats().mutants_tested, 0);
}

#[test]
fn stateful_fallible_reports_traps_and_discards_partial_mutation() {
    // The body mutates its state and only then traps, on the admissible pre-state `3`.
    let mut observed_partial_state = false;
    let body_trap = check_stateful_contract_fallible(
        SpecCheckConfig::default(),
        |old: &u32, &()| Ok(*old < 100),
        |state: &mut u32, &()| {
            *state += 1;
            if *state == 4 { Err(()) } else { Ok(*state) }
        },
        |old: &u32, &(), new: &u32, ret: &u32| {
            if *old == 3 {
                observed_partial_state = true;
            }
            Ok(*new == *old + 1 && *ret == *new)
        },
    );
    assert_eq!(body_trap.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert!(matches!(
        body_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trap: TrapKind::BodyPanicked,
            ..
        }))
    ));
    assert!(
        !observed_partial_state,
        "postcondition must never observe the state left behind by a trapping body"
    );

    let pre_trap = check_stateful_contract_fallible(
        SpecCheckConfig::default(),
        |old: &u32, &()| if *old == 2 { Err(()) } else { Ok(*old < 100) },
        |state: &mut u32, &()| {
            *state += 1;
            Ok(*state)
        },
        |old: &u32, &(), new: &u32, ret: &u32| Ok(*new == *old + 1 && *ret == *new),
    );
    assert_eq!(pre_trap.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert!(matches!(
        pre_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trap: TrapKind::PreconditionPanicked,
            ..
        }))
    ));

    let post_trap = check_stateful_contract_fallible(
        SpecCheckConfig::default(),
        |old: &u32, &()| Ok(*old < 100),
        |state: &mut u32, &()| {
            *state += 1;
            Ok(*state)
        },
        |old: &u32, &(), new: &u32, ret: &u32| {
            if *old == 1 && *new == 2 && *ret == 2 {
                Err(())
            } else {
                Ok(*new == *old + 1 && *ret == *new)
            }
        },
    );
    assert_eq!(post_trap.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert!(matches!(
        post_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trap: TrapKind::PostconditionPanicked,
            ..
        }))
    ));

    // A strong contract passes through the fallible entry point, and a postcondition that
    // rejects perturbed post-states and return values by trapping kills every mutant.
    let trapping_strong = check_stateful_contract_fallible(
        SpecCheckConfig::default(),
        |old: &u32, &()| Ok(*old < 100),
        |state: &mut u32, &()| {
            *state += 1;
            Ok(*state)
        },
        |old: &u32, &(), new: &u32, ret: &u32| {
            if *new == *old + 1 && *ret == *new {
                Ok(true)
            } else {
                Err(())
            }
        },
    );
    assert!(trapping_strong.is_strong());
    let stats = trapping_strong.stats();
    assert!(stats.mutants_killed > 0);
    assert_eq!(stats.mutants_trapped, stats.mutants_killed);

    // Half-weak detection is unchanged through the fallible entry point.
    let ret_ignored = check_stateful_contract_fallible(
        SpecCheckConfig::default(),
        |old: &u32, &()| Ok(*old < 100),
        |state: &mut u32, &()| {
            *state += 1;
            Ok(*state)
        },
        |old: &u32, &(), new: &u32, _ret: &u32| Ok(*new == *old + 1),
    );
    assert_eq!(
        ret_ignored.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
}

// ---------------------------------------------------------------------------
// 7. Sampler and Mutant-Generator Edge Cases
// ---------------------------------------------------------------------------

#[test]
fn array_return_mutants_reach_interior_positions() {
    // The output array is all-equal, so the structural mutants (swap, reverse, rotate) are
    // no-ops, and the postcondition pins only an interior element.
    let interior_4 = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u32| true,
        |&x| [x; 4],
        |&x, r: &[u32; 4]| r[1] == x,
    );
    assert!(interior_4.mutants_killed > 0);

    let interior_8 = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u32| true,
        |&x| [x; 8],
        |&x, r: &[u32; 8]| r[5] == x,
    );
    assert!(interior_8.mutants_killed > 0);

    // An array postcondition that ignores every element is still caught.
    let ignores_elements = check_contract(
        SpecCheckConfig::default(),
        |_x: &u32| true,
        |&x| [x; 4],
        |_x: &u32, r: &[u32; 4]| r.len() == 4,
    );
    assert_eq!(
        ignores_elements.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
}

#[test]
fn zero_and_short_arrays_never_index_out_of_bounds() {
    let mut rng = SplitMix64::new(7);

    // `[T; 0]` is a subsingleton: sampling it and visiting its mutants must not index.
    for trial_idx in 0..256 {
        let empty: [u32; 0] = SampleInput::sample_at(trial_idx, &mut rng);
        let mut emitted = 0usize;
        empty.visit_mutants(&mut rng, |_mutant| emitted += 1);
        assert_eq!(emitted, 0);
    }
    assert_eq!(<[u32; 0] as SampleInput>::BOUNDARY_COUNT, 1);

    // `[T; 1]`, `[T; 2]`, and `[T; 3]` exercise every position-selection branch.
    for trial_idx in 0..256 {
        let one: [u8; 1] = SampleInput::sample_at(trial_idx, &mut rng);
        let mut distinct = 0usize;
        one.visit_mutants(&mut rng, |mutant| distinct += usize::from(mutant != one));
        assert!(distinct > 0);

        let two: [i8; 2] = SampleInput::sample_at(trial_idx, &mut rng);
        let mut distinct = 0usize;
        two.visit_mutants(&mut rng, |mutant| distinct += usize::from(mutant != two));
        assert!(distinct > 0);

        let three: [bool; 3] = SampleInput::sample_at(trial_idx, &mut rng);
        let mut distinct = 0usize;
        three.visit_mutants(&mut rng, |mutant| distinct += usize::from(mutant != three));
        assert!(distinct > 0);
    }

    // A unit-returning contract over a zero-length array input is exempt, not a panic.
    let empty_input = check_contract(
        SpecCheckConfig::default(),
        |_a: &[u32; 0]| true,
        |_a| [0u8; 0],
        |_a, _r: &[u8; 0]| true,
    );
    assert!(empty_input.is_strong());
    assert!(empty_input.stats().subsingleton_return);
}

#[test]
fn integer_samplers_and_mutants_cover_extremes_without_overflow() {
    // Under overflow checks any non-wrapping arithmetic in a sampler or mutant generator
    // panics at the extremes exercised here.
    macro_rules! check_int {
        ($ty:ty, [$($extreme:expr),+ $(,)?]) => {{
            let mut rng = SplitMix64::new(0x5EED);
            let mut saw_min = false;
            let mut saw_max = false;
            for trial_idx in 0..512 {
                let value = <$ty as SampleInput>::sample_at(trial_idx, &mut rng);
                saw_min |= value == <$ty>::MIN;
                saw_max |= value == <$ty>::MAX;
            }
            assert!(saw_min && saw_max, "boundary corpus must contain MIN and MAX");

            for extreme in [$($extreme),+] {
                let extreme: $ty = extreme;
                let mut distinct = 0usize;
                extreme.visit_mutants(&mut rng, |mutant| {
                    distinct += usize::from(mutant != extreme);
                });
                assert!(distinct > 0, "every integer value must have a distinct mutant");
            }
        }};
    }

    check_int!(u8, [u8::MIN, 1, u8::MAX - 1, u8::MAX]);
    check_int!(u16, [u16::MIN, 1, u16::MAX - 1, u16::MAX]);
    check_int!(u32, [u32::MIN, 1, u32::MAX - 1, u32::MAX]);
    check_int!(u64, [u64::MIN, 1, u64::MAX - 1, u64::MAX]);
    check_int!(u128, [u128::MIN, 1, u128::MAX - 1, u128::MAX]);
    check_int!(usize, [usize::MIN, 1, usize::MAX - 1, usize::MAX]);
    check_int!(i8, [i8::MIN, i8::MIN + 1, -1, 0, 1, i8::MAX - 1, i8::MAX]);
    check_int!(
        i16,
        [i16::MIN, i16::MIN + 1, -1, 0, 1, i16::MAX - 1, i16::MAX]
    );
    check_int!(
        i32,
        [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX]
    );
    check_int!(
        i64,
        [i64::MIN, i64::MIN + 1, -1, 0, 1, i64::MAX - 1, i64::MAX]
    );
    check_int!(
        i128,
        [i128::MIN, i128::MIN + 1, -1, 0, 1, i128::MAX - 1, i128::MAX]
    );
    check_int!(
        isize,
        [
            isize::MIN,
            isize::MIN + 1,
            -1,
            0,
            1,
            isize::MAX - 1,
            isize::MAX
        ]
    );

    // Signed boundary corpora lead with `0`, `1`, `-1`.
    let mut rng = SplitMix64::default();
    assert_eq!(<i8 as SampleInput>::sample_at(0, &mut rng), 0);
    assert_eq!(<i8 as SampleInput>::sample_at(1, &mut rng), 1);
    assert_eq!(<i8 as SampleInput>::sample_at(2, &mut rng), -1);
    assert_eq!(<i128 as SampleInput>::sample_at(2, &mut rng), -1);

    // Negation of `i8::MIN` wraps to itself and is skipped as a non-distinct mutant, so a
    // contract over the full `i8` domain stays strong at the extreme.
    let wrapping_neg = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &i8| true,
        |&x| x.wrapping_neg(),
        |&x, &r: &i8| r == x.wrapping_neg(),
    );
    assert!(wrapping_neg.mutants_killed > 0);

    // `Option` and `Result` returns flip variants in both directions.
    let option_flip = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u8| true,
        |&x| x.checked_add(1),
        |&x, &r: &Option<u8>| r == x.checked_add(1),
    );
    assert!(option_flip.mutants_killed > 0);

    let result_flip = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &i8| true,
        |&x| if x < 0 { Err(x) } else { Ok(x as u8) },
        |&x, &r: &Result<u8, i8>| r == if x < 0 { Err(x) } else { Ok(x as u8) },
    );
    assert!(result_flip.mutants_killed > 0);
}

// ---------------------------------------------------------------------------
// 8. Subsingleton Bounds, Deduplicated Mutants, Tight Budgets & Stateful Axes
// ---------------------------------------------------------------------------

#[test]
fn subsingleton_flags_and_deduplicated_variant_mutants() {
    // `Option<()>` and `Result<(), ()>` each have two distinct inhabitants.
    assert!(!<Option<()> as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<Result<(), ()> as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<Result<(), u8> as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<Result<u8, ()> as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<Option<Option<u8>> as ReturnMutants>::IS_SUBSINGLETON);
    assert!(<[(); 0] as ReturnMutants>::IS_SUBSINGLETON);
    assert!(<[(); 4] as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<([u8; 0], u8) as ReturnMutants>::IS_SUBSINGLETON);
    assert!(<([u8; 0], ()) as ReturnMutants>::IS_SUBSINGLETON);

    let mut rng = SplitMix64::new(0xC0DE);

    // Subsingleton inner payloads must emit their opposite variant exactly once.
    let mut opt_unit_muts = Vec::new();
    None::<()>.visit_mutants(&mut rng, |m| opt_unit_muts.push(m));
    assert_eq!(opt_unit_muts, vec![Some(())]);

    let mut res_ok_unit_muts = Vec::new();
    Ok::<(), ()>(()).visit_mutants(&mut rng, |m| res_ok_unit_muts.push(m));
    assert_eq!(res_ok_unit_muts, vec![Err(())]);

    let mut res_err_unit_muts = Vec::new();
    Err::<(), ()>(()).visit_mutants(&mut rng, |m| res_err_unit_muts.push(m));
    assert_eq!(res_err_unit_muts, vec![Ok(())]);

    // With a tight mutant budget of 2, `Result<u32, ()>` and `Result<(), u32>` must cover
    // both payload mutation and opposite-variant flip without starving on duplicates.
    let tight = SpecCheckConfig::default().with_max_mutants_per_hit(2);

    let res_ok_payload = assert_contract_strong(
        tight,
        |_x: &u32| true,
        |&x| Ok::<u32, ()>(x),
        |&x, r: &Result<u32, ()>| r.is_err() || *r == Ok(x),
    );
    assert!(res_ok_payload.mutants_killed > 0);

    let res_ok_variant = assert_contract_strong(
        tight,
        |_x: &u32| true,
        |&x| Ok::<u32, ()>(x),
        |_x, r: &Result<u32, ()>| r.is_ok(),
    );
    assert!(res_ok_variant.mutants_killed > 0);

    let res_err_payload = assert_contract_strong(
        tight,
        |_x: &u32| true,
        |&x| Err::<(), u32>(x),
        |&x, r: &Result<(), u32>| r.is_ok() || *r == Err(x),
    );
    assert!(res_err_payload.mutants_killed > 0);

    // Integer mutant generators must never emit `self` or duplicate candidates.
    macro_rules! assert_no_int_dups {
        ($val:expr) => {{
            let val = $val;
            let mut emitted = Vec::new();
            val.visit_mutants(&mut rng, |m| {
                assert_ne!(m, val, "integer visit_mutants must not emit self");
                assert!(
                    !emitted.contains(&m),
                    "integer visit_mutants must not emit duplicates"
                );
                emitted.push(m);
            });
            assert!(!emitted.is_empty());
        }};
    }

    assert_no_int_dups!(0u32);
    assert_no_int_dups!(u32::MAX);
    assert_no_int_dups!(0i8);
    assert_no_int_dups!(i8::MIN);
    assert_no_int_dups!(i128::MIN);
}

#[test]
fn array_roving_index_kills_interior_under_tight_mutant_budget() {
    // Placing the roving index first ensures even `max_mutants_per_hit = 4` visits
    // interior indices of `[u32; 8]` instead of exhausting its budget on `0`, `N/2`, `N-1`.
    let tight = SpecCheckConfig::default().with_max_mutants_per_hit(4);
    let interior = assert_contract_strong(
        tight,
        |_x: &u32| true,
        |&x| [x; 8],
        |&x, r: &[u32; 8]| r[5] == x,
    );
    assert!(interior.mutants_killed > 0);

    // For `N = 2`, both index `0` and index `1` (`last == N / 2`) must remain covered.
    let pair_first = assert_contract_strong(
        tight,
        |_x: &u32| true,
        |&x| [x, x],
        |&x, r: &[u32; 2]| r[0] == x,
    );
    assert!(pair_first.mutants_killed > 0);

    let pair_second = assert_contract_strong(
        tight,
        |_x: &u32| true,
        |&x| [x, x],
        |&x, r: &[u32; 2]| r[1] == x,
    );
    assert!(pair_second.mutants_killed > 0);

    let mut rng = SplitMix64::new(0x1234);
    for _ in 0..16 {
        let base = [0u32, 0u32];
        let mut saw_idx0 = false;
        let mut saw_idx1 = false;
        base.visit_mutants(&mut rng, |m| {
            if m[0] != 0 && m[1] == 0 {
                saw_idx0 = true;
            }
            if m[0] == 0 && m[1] != 0 {
                saw_idx1 = true;
            }
        });
        assert!(
            saw_idx0 && saw_idx1,
            "`[T; 2]::visit_mutants` must perturb both indices"
        );
    }
}

#[test]
fn result_mutant_chain_and_nested_option_classify_cleanly() {
    // `Result<u32, u32>` mutant chains advance monotonically through `Ok(0), Ok(1), ...`
    // rather than bouncing `Ok <-> Err`, reaching `Ok(42)` under `ProbeDomain::Unconstrained`.
    let outcome = check_contract(
        SpecCheckConfig::default().with_probe_domain(ProbeDomain::Unconstrained),
        |&x: &u32| x < 10,
        |&x| Ok::<u32, u32>(x),
        |&x, r: &Result<u32, u32>| x < 10 || *r == Ok(42),
    );
    assert_eq!(
        outcome.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );

    // Nested `Option<Option<u8>>` covers `None`, `Some(None)`, and `Some(Some(_))`.
    let nested_opt = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u8| true,
        |&x| {
            if x == 0 {
                None
            } else if x == 1 {
                Some(None)
            } else {
                Some(Some(x))
            }
        },
        |&x, &r: &Option<Option<u8>>| {
            r == if x == 0 {
                None
            } else if x == 1 {
                Some(None)
            } else {
                Some(Some(x))
            }
        },
    );
    assert!(nested_opt.mutants_killed > 0);
}

#[test]
fn stateful_pure_read_and_conjunctive_axis_probes() {
    // Pure read via `&mut S` leaving `*state == old_state` intentionally: with the frame
    // condition `*new == *old`, both state and return axes kill mutants.
    let pure_read_strong = assert_stateful_contract_strong(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < 100,
        |state: &mut u32, &()| *state,
        |old: &u32, &(), new: &u32, ret: &u32| *new == *old && *ret == *old,
    );
    assert!(pure_read_strong.mutants_killed > 0);

    // Omitting the frame condition `*new == *old` on a pure read is caught on the state axis.
    let pure_read_missing_frame = check_stateful_contract(
        SpecCheckConfig::default(),
        |old: &u32, &()| *old < 100,
        |state: &mut u32, &()| *state,
        |old: &u32, &(), _new: &u32, ret: &u32| *ret == *old,
    );
    assert_eq!(
        pure_read_missing_frame.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );
    assert!(matches!(
        pure_read_missing_frame.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed,
            state_mutants_killed: 0,
            ..
        }) if return_mutants_killed > 0
    ));

    // Conjunctive `requires`-vacuous return axis: `*new == old.wrapping_add(1)` pins `new`
    // while `(*old < 100 || *ret == 42)` varies with `ret` outside `requires`.
    let unconstrained = SpecCheckConfig::default().with_probe_domain(ProbeDomain::Unconstrained);
    let conj_ret_vacuous = check_stateful_contract(
        unconstrained,
        |old: &u32, &()| *old < 100,
        |state: &mut u32, &()| {
            *state += 1;
            *state
        },
        |old: &u32, &(), new: &u32, ret: &u32| {
            *new == old.wrapping_add(1) && (*old < 100 || *ret == 42)
        },
    );
    assert_eq!(
        conj_ret_vacuous.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert!(matches!(
        conj_ret_vacuous.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed: 0,
            state_mutants_killed,
            ..
        }) if state_mutants_killed > 0
    ));

    // Conjunctive `requires`-vacuous state axis: `*ret == old.wrapping_add(1)` pins `ret`
    // while `(*old == 0 || *new == 42)` varies with `new` outside `requires`.
    let conj_state_vacuous = check_stateful_contract(
        unconstrained,
        |old: &u32, &()| *old == 0,
        |state: &mut u32, &()| {
            *state += 1;
            *state
        },
        |old: &u32, &(), new: &u32, ret: &u32| {
            *ret == old.wrapping_add(1) && (*old == 0 || *new == 42)
        },
    );
    assert_eq!(
        conj_state_vacuous.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert!(matches!(
        conj_state_vacuous.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed,
            state_mutants_killed: 0,
            ..
        }) if return_mutants_killed > 0
    ));
}

/// Asserts the `SpecCheckStats` accounting invariants that every outcome must satisfy,
/// whether the check ran to completion or returned early.
fn assert_stats_invariants(outcome: &SpecCheckOutcome) {
    let stats = outcome.stats();
    assert!(
        stats.precondition_hits <= stats.trials_run,
        "precondition_hits exceeds trials_run: {outcome:?}"
    );
    assert!(
        stats.hits_with_kill <= stats.precondition_hits,
        "hits_with_kill exceeds precondition_hits: {outcome:?}"
    );
    assert!(
        stats.hits_with_kill <= stats.mutants_killed,
        "hits_with_kill exceeds mutants_killed: {outcome:?}"
    );
    assert_eq!(
        stats.hits_with_kill > 0,
        stats.mutants_killed > 0,
        "hits_with_kill and mutants_killed disagree on non-zero kills: {outcome:?}"
    );
    assert_eq!(
        stats.hits_with_kill + stats.hits_without_kill(),
        stats.precondition_hits,
        "hits_with_kill + hits_without_kill != precondition_hits: {outcome:?}"
    );
    assert!(
        stats.mutants_killed <= stats.mutants_tested,
        "mutants_killed exceeds mutants_tested: {outcome:?}"
    );
    assert!(
        stats.mutants_trapped <= stats.mutants_killed,
        "mutants_trapped exceeds mutants_killed: {outcome:?}"
    );
    if let Some(FailureDetail::StatefulAxisUnconstrained {
        return_mutants_tested,
        return_mutants_killed,
        state_mutants_tested,
        state_mutants_killed,
    }) = outcome.failure().map(|f| f.detail)
    {
        assert!(return_mutants_killed <= return_mutants_tested);
        assert!(state_mutants_killed <= state_mutants_tested);
        assert_eq!(
            return_mutants_tested + state_mutants_tested,
            stats.mutants_tested
        );
        assert_eq!(
            return_mutants_killed + state_mutants_killed,
            stats.mutants_killed
        );
    }
}

#[test]
fn stats_invariants_hold_on_every_early_return_path() {
    let cfg = SpecCheckConfig::default();

    // Degenerate configuration: fails closed before sampling any input.
    let degenerate = check_contract(
        cfg.with_max_trials(0),
        |_x: &u32| true,
        |&x| x,
        |&x, &r: &u32| r == x,
    );
    assert_stats_invariants(&degenerate);
    assert_eq!(
        degenerate.vacuity_class(),
        Some(VacuityClass::DeadPrecondition)
    );
    assert_eq!(degenerate.stats().trials_run, 0);

    // Dead precondition: every trial is sampled and none is admissible.
    let dead = check_contract(cfg, |_x: &u32| false, |&x| x, |&x, &r: &u32| r == x);
    assert_stats_invariants(&dead);
    assert_eq!(dead.vacuity_class(), Some(VacuityClass::DeadPrecondition));
    assert_eq!(dead.stats().trials_run, cfg.max_trials);
    assert_eq!(dead.stats().precondition_hits, 0);

    // Live postcondition violation on the very first admissible trial.
    let violated = check_contract(cfg, |_x: &u32| true, |&x| x, |&x, &r: &u32| r != x);
    assert_stats_invariants(&violated);
    assert_eq!(violated.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert_eq!(violated.stats().trials_run, 1);
    assert_eq!(violated.stats().precondition_hits, 1);
    assert_eq!(violated.stats().mutants_tested, 0);

    // Live postcondition violation after an earlier trial already killed mutants.
    let late_violation = check_contract(
        cfg,
        |_x: &u32| true,
        |&x| x,
        |&x, &r: &u32| r == x && x != 1,
    );
    assert_stats_invariants(&late_violation);
    assert_eq!(
        late_violation.vacuity_class(),
        Some(VacuityClass::SpecViolation)
    );

    // Trapping `pre`, `body`, and live `post` each fail closed immediately.
    let pre_trap = check_contract_fallible(
        cfg,
        |_x: &u32| Err(()),
        |&x| Ok(x),
        |&x, &r: &u32| Ok(r == x),
    );
    assert_stats_invariants(&pre_trap);
    assert!(matches!(
        pre_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 0,
            trap: TrapKind::PreconditionPanicked,
        }))
    ));
    assert_eq!(pre_trap.stats().trials_run, 1);
    assert_eq!(pre_trap.stats().precondition_hits, 0);

    let body_trap = check_contract_fallible(
        cfg,
        |_x: &u32| Ok(true),
        |_x| Err::<u32, ()>(()),
        |&x, &r: &u32| Ok(r == x),
    );
    assert_stats_invariants(&body_trap);
    assert!(matches!(
        body_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 0,
            trap: TrapKind::BodyPanicked,
        }))
    ));
    assert_eq!(body_trap.stats().precondition_hits, 1);

    let post_trap =
        check_contract_fallible(cfg, |_x: &u32| Ok(true), |&x| Ok(x), |_x, _r: &u32| Err(()));
    assert_stats_invariants(&post_trap);
    assert!(matches!(
        post_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 0,
            trap: TrapKind::PostconditionPanicked,
        }))
    ));
    assert_eq!(post_trap.stats().mutants_tested, 0);

    // Zero mutant budget on a non-subsingleton return fails closed after all trials.
    let no_budget = check_contract(
        cfg.with_max_mutants_per_hit(0),
        |_x: &u32| true,
        |&x| x,
        |&x, &r: &u32| r == x,
    );
    assert_stats_invariants(&no_budget);
    assert_eq!(
        no_budget.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert_eq!(no_budget.stats().mutants_tested, 0);

    // Every mutant survives a constant-true postcondition.
    let survived = check_contract(cfg, |_x: &u32| true, |&x| x, |_x, _r: &u32| true);
    assert_stats_invariants(&survived);
    assert_eq!(
        survived.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert!(survived.stats().mutants_tested > 0);
    assert_eq!(survived.stats().mutants_killed, 0);

    // Strong contract: the invariants also hold on success.
    let strong = check_contract(cfg, |_x: &u32| true, |&x| x, |&x, &r: &u32| r == x);
    assert_stats_invariants(&strong);
    assert!(strong.is_strong());
    assert!(strong.stats().mutants_killed > 0);

    // Stateful: an unconstrained post-state axis reports consistent per-axis counters.
    let half_weak = check_stateful_contract(
        cfg,
        |_old: &u32, &()| true,
        |state: &mut u32, &()| {
            *state = state.wrapping_add(1);
            *state
        },
        |old: &u32, &(), _new: &u32, ret: &u32| *ret == old.wrapping_add(1),
    );
    assert_stats_invariants(&half_weak);
    assert!(matches!(
        half_weak.failure().map(|f| f.detail),
        Some(FailureDetail::StatefulAxisUnconstrained {
            return_mutants_killed,
            state_mutants_killed: 0,
            ..
        }) if return_mutants_killed > 0
    ));

    // Stateful: a trapping body fails closed with consistent counters.
    let stateful_body_trap = check_stateful_contract_fallible(
        cfg,
        |_old: &u32, &()| Ok(true),
        |_state: &mut u32, &()| Err::<u32, ()>(()),
        |_old: &u32, &(), _new: &u32, _ret: &u32| Ok(true),
    );
    assert_stats_invariants(&stateful_body_trap);
    assert!(matches!(
        stateful_body_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 0,
            trap: TrapKind::BodyPanicked,
        }))
    ));

    // Stateful: an assertion-style postcondition traps on every mutant of both axes.
    let stateful_trapping = check_stateful_contract_fallible(
        cfg,
        |_old: &u32, &()| Ok(true),
        |state: &mut u32, &()| {
            *state = state.wrapping_add(1);
            Ok(*state)
        },
        |old: &u32, &(), new: &u32, ret: &u32| {
            if *new == old.wrapping_add(1) && *ret == *new {
                Ok(true)
            } else {
                Err(())
            }
        },
    );
    assert_stats_invariants(&stateful_trapping);
    assert!(stateful_trapping.is_strong());
    let trapped = stateful_trapping.stats();
    assert!(trapped.mutants_tested > 0);
    assert_eq!(trapped.mutants_killed, trapped.mutants_tested);
    assert_eq!(trapped.mutants_trapped, trapped.mutants_killed);
}

#[test]
fn min_precondition_hits_exceeding_max_trials_fails_closed() {
    let impossible = SpecCheckConfig::default()
        .with_max_trials(10)
        .with_min_precondition_hits(11);

    let mut stateless_pre_calls = 0usize;
    let stateless = check_contract(
        impossible,
        |_x: &u32| {
            stateless_pre_calls += 1;
            true
        },
        |&x| x,
        |&x, &r: &u32| r == x,
    );
    assert_stats_invariants(&stateless);
    assert_eq!(stateless_pre_calls, 0);
    assert_eq!(stateless.stats().trials_run, 0);
    assert_eq!(
        stateless.vacuity_class(),
        Some(VacuityClass::DeadPrecondition)
    );
    assert_eq!(
        stateless.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::DegenerateConfig))
    );

    let mut stateful_pre_calls = 0usize;
    let stateful = check_stateful_contract(
        impossible,
        |_old: &u32, &()| {
            stateful_pre_calls += 1;
            true
        },
        |state: &mut u32, &()| {
            *state = state.wrapping_add(1);
            *state
        },
        |old: &u32, &(), new: &u32, ret: &u32| *new == old.wrapping_add(1) && *ret == *new,
    );
    assert_stats_invariants(&stateful);
    assert_eq!(stateful_pre_calls, 0);
    assert_eq!(stateful.stats().trials_run, 0);
    assert_eq!(
        stateful.vacuity_class(),
        Some(VacuityClass::DeadPrecondition)
    );
    assert_eq!(
        stateful.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::DegenerateConfig))
    );
}

#[test]
fn multi_branch_existential_dichotomy_and_pointwise_stats() {
    // Full `u32::checked_add` kills mutants on every admissible trial (pointwise strong).
    let full = check_contract(
        SpecCheckConfig::default(),
        |&(a, b): &(u32, u32)| __anodized_fn_requires_spec_u32_checked_add(a, b),
        |&(a, b)| a.checked_add(b),
        |&(a, b), &ret| __anodized_fn_ensures_spec_u32_checked_add(a, b, ret),
    );
    assert_stats_invariants(&full);
    assert!(full.is_strong());
    let full_stats = full.stats();
    assert!(full_stats.is_pointwise_strong());
    assert_eq!(full_stats.hits_without_kill(), 0);
    assert_eq!(full_stats.hits_with_kill, full_stats.precondition_hits);

    // Multi-branch `u32::checked_add` whose overflow branch accepts any `Option<u32>`:
    // existential `PostconditionDichotomy` still holds (`Strong`), while `SpecCheckStats`
    // surfaces the unconstrained overflow hits via `hits_without_kill() > 0`.
    let partial_checked_add = check_contract(
        SpecCheckConfig::default(),
        |_ab: &(u32, u32)| true,
        |&(a, b)| a.checked_add(b),
        |&(a, b), &ret: &Option<u32>| {
            if (a as u64) + (b as u64) > (u32::MAX as u64) {
                true
            } else {
                ret == Some(a + b)
            }
        },
    );
    assert_stats_invariants(&partial_checked_add);
    assert!(partial_checked_add.is_strong());
    let partial_stats = partial_checked_add.stats();
    assert!(partial_stats.hits_with_kill > 0);
    assert!(partial_stats.hits_without_kill() > 0);
    assert!(!partial_stats.is_pointwise_strong());

    // Multi-branch `Result` contract leaving the divide-by-zero branch unconstrained:
    // still existentially `Strong`, with non-zero `hits_without_kill()`.
    let partial_div = check_contract(
        SpecCheckConfig::default(),
        |_dd: &(u32, u32)| true,
        |&(dividend, divisor)| checked_div_u32(dividend, divisor),
        |&(dividend, divisor), &ret: &Result<u32, u8>| {
            if divisor == 0 {
                true
            } else {
                ret == Ok(dividend / divisor)
            }
        },
    );
    assert_stats_invariants(&partial_div);
    assert!(partial_div.is_strong());
    let div_stats = partial_div.stats();
    assert!(div_stats.hits_with_kill > 0);
    assert!(div_stats.hits_without_kill() > 0);
    assert!(!div_stats.is_pointwise_strong());
}

#[test]
fn splitmix64_seed_zero_and_four_tuple_return_mutants() {
    // Seed `0` must yield a non-degenerate, deterministic stream distinct from `DEFAULT_SEED`.
    let mut z0 = SplitMix64::new(0);
    let mut z0_again = SplitMix64::new(0);
    let mut z_def = SplitMix64::default();
    let a = z0.next_u64();
    let b = z0.next_u64();
    assert_ne!(a, 0);
    assert_ne!(a, b);
    assert_eq!(a, z0_again.next_u64());
    assert_ne!(a, z_def.next_u64());

    let seed_zero_cfg = SpecCheckConfig::default().with_seed(0);
    let run1 = check_contract(
        seed_zero_cfg,
        |&(val, lo, hi): &(u32, u32, u32)| __anodized_fn_requires_clamp_u32(val, lo, hi),
        |&(val, lo, hi)| clamp_u32(val, lo, hi),
        |&(val, lo, hi), &ret| __anodized_fn_ensures_clamp_u32(val, lo, hi, ret),
    );
    let run2 = check_contract(
        seed_zero_cfg,
        |&(val, lo, hi): &(u32, u32, u32)| __anodized_fn_requires_clamp_u32(val, lo, hi),
        |&(val, lo, hi)| clamp_u32(val, lo, hi),
        |&(val, lo, hi), &ret| __anodized_fn_ensures_clamp_u32(val, lo, hi, ret),
    );
    assert_eq!(run1, run2);
    assert!(run1.is_strong());
    assert_stats_invariants(&run1);

    // 4-tuple `ReturnMutants` subsingleton flags and per-axis coverage within default budget.
    assert!(<((), (), (), ()) as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<((), (), (), bool) as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<(u8, i8, u16, bool) as ReturnMutants>::IS_SUBSINGLETON);

    let pin_axis_0 = assert_contract_strong(
        SpecCheckConfig::default(),
        |_t: &(u8, i8, u16, bool)| true,
        |&t| t,
        |&(a, _, _, _), &(ra, _, _, _): &(u8, i8, u16, bool)| ra == a,
    );
    assert!(pin_axis_0.is_pointwise_strong());

    let pin_axis_3 = assert_contract_strong(
        SpecCheckConfig::default(),
        |_t: &(u8, i8, u16, bool)| true,
        |&t| t,
        |&(_, _, _, d), &(_, _, _, rd): &(u8, i8, u16, bool)| rd == d,
    );
    assert!(pin_axis_3.is_pointwise_strong());

    // Extremal boundary flips for `Option<u32>` (`Some(u32::MAX)`) and `Result<u32, u32>`
    // (`Err(u32::MAX)` / `Ok(u32::MAX)`) kill specs that only forbid `MAX` on the opposite variant.
    let opt_forbids_max = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u32| true,
        |_x| None::<u32>,
        |_x, &r: &Option<u32>| r != Some(u32::MAX),
    );
    assert!(opt_forbids_max.mutants_killed > 0);

    let res_forbids_err_max = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u32| true,
        |&x| Ok::<u32, u32>(x),
        |_x, &r: &Result<u32, u32>| r != Err(u32::MAX),
    );
    assert!(res_forbids_err_max.mutants_killed > 0);
}

// ---------------------------------------------------------------------------
// Struct plug-in macro and counterexample replay
// ---------------------------------------------------------------------------

/// Invariant-carrying range (`lo <= hi`) wired into the checker by one macro call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Span {
    lo: u16,
    hi: u16,
}

anneal_spec::impl_spec_check_struct!(Span { lo: u16, hi: u16 });

/// Newtype wired through the tuple-struct arm of the macro.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Meters(u32);

anneal_spec::impl_spec_check_struct!(Meters(u32));

#[test]
fn struct_macro_plugs_custom_types_into_sampling_and_mutation() {
    // The generated impls mirror the tuple (or inner-type) impls exactly.
    assert_eq!(
        <Span as SampleInput>::BOUNDARY_COUNT,
        <(u16, u16) as SampleInput>::BOUNDARY_COUNT
    );
    assert_eq!(
        <Meters as SampleInput>::BOUNDARY_COUNT,
        <u32 as SampleInput>::BOUNDARY_COUNT
    );
    assert!(!<Span as ReturnMutants>::IS_SUBSINGLETON);
    assert!(!<Meters as ReturnMutants>::IS_SUBSINGLETON);

    let mut struct_rng = SplitMix64::new(7);
    let mut tuple_rng = SplitMix64::new(7);
    for idx in 0..96 {
        let span = <Span as SampleInput>::sample_at(idx, &mut struct_rng);
        let (lo, hi) = <(u16, u16) as SampleInput>::sample_at(idx, &mut tuple_rng);
        assert_eq!(span, Span { lo, hi });
    }

    let mut struct_mutants = 0usize;
    let mut tuple_mutants = 0usize;
    let origin = Span { lo: 3, hi: 9 };
    origin.visit_mutants(&mut SplitMix64::new(11), |m| {
        assert_ne!(m, origin);
        struct_mutants += 1;
    });
    (3u16, 9u16).visit_mutants(&mut SplitMix64::new(11), |_| tuple_mutants += 1);
    assert!(struct_mutants > 0);
    assert_eq!(struct_mutants, tuple_mutants);

    // Stateless return type: a span normalizer must return the ordered endpoints.
    let normalize = assert_contract_strong(
        SpecCheckConfig::default(),
        |_s: &Span| true,
        |s| Span {
            lo: s.lo.min(s.hi),
            hi: s.lo.max(s.hi),
        },
        |s, r: &Span| r.lo == s.lo.min(s.hi) && r.hi == s.lo.max(s.hi),
    );
    assert!(normalize.is_pointwise_strong());

    // The invariant alone (`lo <= hi`) is a weaker but still output-binding
    // postcondition: mutants that break the invariant are legitimate wrong answers.
    let invariant_only = assert_contract_strong(
        SpecCheckConfig::default(),
        |_s: &Span| true,
        |s| Span {
            lo: s.lo.min(s.hi),
            hi: s.lo.max(s.hi),
        },
        |_s, r: &Span| r.lo <= r.hi,
    );
    assert!(invariant_only.mutants_killed > 0);

    // Stateful `&mut Span`: the invariant is part of `pre`, so samples violating it
    // are rejected as inadmissible inputs rather than filtered by the sampler.
    let widen = assert_stateful_contract_strong(
        SpecCheckConfig::default(),
        |old: &Span, &()| old.lo <= old.hi && old.hi < u16::MAX,
        |span: &mut Span, &()| {
            span.hi += 1;
            span.hi
        },
        |old: &Span, &(), new: &Span, ret: &u16| {
            new.lo == old.lo && new.lo <= new.hi && new.hi == old.hi + 1 && *ret == new.hi
        },
    );
    assert!(widen.precondition_hits > 0);
    assert!(widen.precondition_hits < widen.trials_run);
    assert!(widen.is_pointwise_strong());

    // Newtype input and output.
    let double = assert_contract_strong(
        SpecCheckConfig::default(),
        |m: &Meters| m.0 <= u32::MAX / 2,
        |m| Meters(m.0 * 2),
        |m, r: &Meters| r.0 == m.0 * 2,
    );
    assert!(double.is_pointwise_strong());
}

#[test]
fn counterexample_trial_replays_the_exact_failing_input() {
    use anneal_spec::spec_check::{replay_stateful_trial_input, replay_trial_input};

    let cfg = SpecCheckConfig::default().with_seed(0x00C0_FFEE);

    // Record every sampled input so the replay is compared against ground truth.
    let mut seen = [(0u32, 0u32); 256];
    let mut seen_len = 0usize;
    let outcome = check_contract(
        cfg,
        |&(a, b): &(u32, u32)| {
            if seen_len < seen.len() {
                seen[seen_len] = (a, b);
            }
            seen_len += 1;
            true
        },
        |&(a, b)| a.wrapping_add(b),
        // Wrong whenever the sum overflows `u32`.
        |&(a, b), &r: &u32| u64::from(r) == u64::from(a) + u64::from(b),
    );
    let failure = *outcome
        .failure()
        .expect("an overflowing sum violates the spec");
    assert_eq!(failure.class, VacuityClass::SpecViolation);
    let trial_idx = failure
        .counterexample_trial()
        .expect("a live violation carries its trial index");
    assert_eq!(
        failure.detail,
        FailureDetail::Violation(ViolationKind::PostconditionFalse { trial_idx })
    );
    assert_eq!(failure.stats.trials_run, trial_idx + 1);
    assert_eq!(seen_len, trial_idx + 1);

    let (a, b): (u32, u32) = replay_trial_input(cfg, trial_idx).expect("the trial ran");
    assert_eq!((a, b), seen[trial_idx]);
    assert!(a.checked_add(b).is_none());
    // Every earlier trial replays as well, and trials past the budget never ran.
    for (idx, expected) in seen.iter().enumerate().take(trial_idx) {
        assert_eq!(replay_trial_input::<(u32, u32)>(cfg, idx), Some(*expected));
    }
    assert_eq!(replay_trial_input::<(u32, u32)>(cfg, cfg.max_trials), None);
    // A different seed samples a different stream past the boundary corpus.
    let other = cfg.with_seed(cfg.seed ^ 1);
    let prng_idx = <(u32, u32) as SampleInput>::BOUNDARY_COUNT + 3;
    assert!(prng_idx < cfg.max_trials);
    assert_ne!(
        replay_trial_input::<(u32, u32)>(cfg, prng_idx),
        replay_trial_input::<(u32, u32)>(other, prng_idx)
    );

    // Stateful trap: the replayed `(old_state, args)` pair is the one whose body trapped.
    let stateful = check_stateful_contract_fallible(
        cfg,
        |_old: &u8, _delta: &u8| Ok(true),
        |state: &mut u8, delta: &u8| match state.checked_add(*delta) {
            Some(sum) => {
                *state = sum;
                Ok(sum)
            }
            None => Err(()),
        },
        |old: &u8, delta: &u8, new: &u8, ret: &u8| {
            Ok(old.checked_add(*delta) == Some(*new) && ret == new)
        },
    );
    let trapped = *stateful.failure().expect("an overflowing add traps");
    let trapped_idx = trapped
        .counterexample_trial()
        .expect("a trap carries its trial index");
    assert_eq!(
        trapped.detail,
        FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: trapped_idx,
            trap: TrapKind::BodyPanicked,
        })
    );
    let (old, delta): (u8, u8) =
        replay_stateful_trial_input(cfg, trapped_idx).expect("the trial ran");
    assert!(old.checked_add(delta).is_none());
    for idx in 0..trapped_idx {
        let (s, d): (u8, u8) = replay_stateful_trial_input(cfg, idx).expect("the trial ran");
        assert!(s.checked_add(d).is_some());
    }
    assert_eq!(
        replay_stateful_trial_input::<u8, u8>(cfg, cfg.max_trials),
        None
    );

    // Failures that are not tied to one trial report no counterexample trial.
    let vacuous = check_contract(cfg, |_x: &u32| true, |&x| x, |_x, _r: &u32| true);
    assert_eq!(
        vacuous.vacuity_class(),
        Some(VacuityClass::TrivialPostcondition)
    );
    assert_eq!(
        vacuous.failure().and_then(|f| f.counterexample_trial()),
        None
    );
    let dead = check_contract(cfg, |_x: &u32| false, |&x| x, |&x, &r: &u32| r == x);
    assert_eq!(dead.vacuity_class(), Some(VacuityClass::DeadPrecondition));
    assert_eq!(dead.failure().and_then(|f| f.counterexample_trial()), None);
}

// ---------------------------------------------------------------------------
// Tight-budget multi-axis interleaving, `#[invariant]` integration, full
// struct arities, and exhaustive width/array zero-panic audit
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct QuadNamed {
    a: u8,
    b: i8,
    c: u16,
    d: bool,
}

anneal_spec::impl_spec_check_struct!(QuadNamed {
    a: u8,
    b: i8,
    c: u16,
    d: bool,
});

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PairTuple(u16, u16);

anneal_spec::impl_spec_check_struct!(PairTuple(u16, u16));

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TripleTuple(u8, i16, bool);

anneal_spec::impl_spec_check_struct!(TripleTuple(u8, i16, bool));

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct QuadTuple(u8, i8, u16, bool);

anneal_spec::impl_spec_check_struct!(QuadTuple(u8, i8, u16, bool));

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct UnitMarker;

anneal_spec::impl_spec_check_struct!(UnitMarker);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EmptyBrace {}

anneal_spec::impl_spec_check_struct!(EmptyBrace {});

/// Intentionally non-`Clone` single-field struct proving 1-field macro arms
/// require neither `Clone` nor `Copy`.
#[derive(Debug, PartialEq, Eq)]
struct NonCloneWrap {
    inner: u32,
}

anneal_spec::impl_spec_check_struct!(NonCloneWrap { inner: u32 });

#[derive(Debug, PartialEq, Eq)]
struct NonCloneNewtype(u32);

anneal_spec::impl_spec_check_struct!(NonCloneNewtype(u32,));

#[invariant(self.lo <= self.hi, self.hi < 1_000)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CheckedWindow {
    lo: u16,
    hi: u16,
}

anneal_spec::impl_spec_check_struct!(CheckedWindow { lo: u16, hi: u16 });

#[test]
fn tight_budget_multi_axis_interleaving_for_tuples_structs_and_arrays() {
    // 2-tuple and 2-field tuple struct reach axis 1 even with `max_mutants_per_hit = 2`.
    let cfg2 = SpecCheckConfig::default().with_max_mutants_per_hit(2);
    let tuple2_last = assert_contract_strong(
        cfg2,
        |_t: &(u16, u16)| true,
        |&t| t,
        |&(_, b), &(_, rb): &(u16, u16)| rb == b,
    );
    assert!(tuple2_last.is_pointwise_strong());

    let pair_last = assert_contract_strong(
        cfg2,
        |_p: &PairTuple| true,
        |&p| p,
        |p, r: &PairTuple| r.1 == p.1,
    );
    assert!(pair_last.is_pointwise_strong());

    // 3-tuple and 3-field tuple struct reach axis 2 even with `max_mutants_per_hit = 3`.
    let cfg3 = SpecCheckConfig::default().with_max_mutants_per_hit(3);
    let tuple3_last = assert_contract_strong(
        cfg3,
        |_t: &(u8, i16, bool)| true,
        |&t| t,
        |&(_, _, c), &(_, _, rc): &(u8, i16, bool)| rc == c,
    );
    assert!(tuple3_last.is_pointwise_strong());

    let triple_last = assert_contract_strong(
        cfg3,
        |_t: &TripleTuple| true,
        |&t| t,
        |t, r: &TripleTuple| r.2 == t.2,
    );
    assert!(triple_last.is_pointwise_strong());

    // 4-tuple, 4-field named struct, and 4-field tuple struct reach axis 3 even
    // with `max_mutants_per_hit = 4`.
    let cfg4 = SpecCheckConfig::default().with_max_mutants_per_hit(4);
    let tuple4_last = assert_contract_strong(
        cfg4,
        |_t: &(u8, i8, u16, bool)| true,
        |&t| t,
        |&(_, _, _, d), &(_, _, _, rd): &(u8, i8, u16, bool)| rd == d,
    );
    assert!(tuple4_last.is_pointwise_strong());

    let quad_named_last = assert_contract_strong(
        cfg4,
        |_q: &QuadNamed| true,
        |&q| q,
        |q, r: &QuadNamed| r.d == q.d,
    );
    assert!(quad_named_last.is_pointwise_strong());

    let quad_tuple_last = assert_contract_strong(
        cfg4,
        |_q: &QuadTuple| true,
        |&q| q,
        |q, r: &QuadTuple| r.3 == q.3,
    );
    assert!(quad_tuple_last.is_pointwise_strong());

    // `[u16; 8]` interleaves positions so even `max_mutants_per_hit = 4` hits `last`
    // (`index 7`) on every hit.
    let arr8_last = assert_contract_strong(
        cfg4,
        |_a: &[u16; 8]| true,
        |&a| a,
        |a, r: &[u16; 8]| r[7] == a[7],
    );
    assert!(arr8_last.is_pointwise_strong());

    // Structural permutation deduplication: `[1, 2]` emits `[2, 1]` once (not 3x),
    // and `[1, 2, 3]` emits `[3, 2, 1]` and `[2, 3, 1]` once each (not duplicated).
    let mut swapped_2_count = 0usize;
    [1u8, 2u8].visit_mutants(&mut SplitMix64::new(19), |m| {
        if m == [2, 1] {
            swapped_2_count += 1;
        }
    });
    assert_eq!(swapped_2_count, 1);

    let mut swapped_3_count = 0usize;
    let mut rotated_3_count = 0usize;
    [1u8, 2u8, 3u8].visit_mutants(&mut SplitMix64::new(19), |m| {
        if m == [3, 2, 1] {
            swapped_3_count += 1;
        }
        if m == [2, 3, 1] {
            rotated_3_count += 1;
        }
    });
    assert_eq!(swapped_3_count, 1);
    assert_eq!(rotated_3_count, 1);
}

#[test]
fn invariant_attribute_and_full_struct_arities_integrate_with_spec_check() {
    // Unit and empty-braced structs are subsingletons with 1 boundary sample.
    assert!(<UnitMarker as ReturnMutants>::IS_SUBSINGLETON);
    assert!(<EmptyBrace as ReturnMutants>::IS_SUBSINGLETON);
    assert_eq!(<UnitMarker as SampleInput>::BOUNDARY_COUNT, 1);
    assert_eq!(<EmptyBrace as SampleInput>::BOUNDARY_COUNT, 1);

    let unit_ok = assert_contract_strong(
        SpecCheckConfig::default(),
        |_u: &UnitMarker| true,
        |_| EmptyBrace {},
        |_u, _e: &EmptyBrace| true,
    );
    assert!(unit_ok.subsingleton_return);

    // Non-`Clone` 1-field named and tuple structs work end-to-end.
    let wrap_ok = assert_contract_strong(
        SpecCheckConfig::default(),
        |w: &NonCloneWrap| w.inner < u32::MAX,
        |w| NonCloneWrap { inner: w.inner + 1 },
        |w, r: &NonCloneWrap| r.inner == w.inner + 1,
    );
    assert!(wrap_ok.is_pointwise_strong());

    let newtype_ok = assert_contract_strong(
        SpecCheckConfig::default(),
        |n: &NonCloneNewtype| n.0 > 0,
        |n| NonCloneNewtype(n.0 - 1),
        |n, r: &NonCloneNewtype| r.0 == n.0 - 1,
    );
    assert!(newtype_ok.is_pointwise_strong());

    // `#[invariant]` companion method wired into stateless and stateful contracts.
    let inv_stateless = assert_contract_strong(
        SpecCheckConfig::default(),
        |w: &CheckedWindow| w.__anneal_type_invariant_checked_window(),
        |w| CheckedWindow { lo: w.lo, hi: w.hi },
        |w, r: &CheckedWindow| {
            r.__anneal_type_invariant_checked_window() && r.lo == w.lo && r.hi == w.hi
        },
    );
    assert!(inv_stateless.precondition_hits > 0);
    assert!(inv_stateless.precondition_hits < inv_stateless.trials_run);
    assert!(inv_stateless.is_pointwise_strong());

    // Even the `#[invariant]` check alone kills output mutants that break `lo <= hi`
    // or `hi < 1_000`.
    let inv_only = assert_contract_strong(
        SpecCheckConfig::default(),
        |w: &CheckedWindow| w.__anneal_type_invariant_checked_window(),
        |w| CheckedWindow { lo: w.lo, hi: w.hi },
        |_w, r: &CheckedWindow| r.__anneal_type_invariant_checked_window(),
    );
    assert!(inv_only.mutants_killed > 0);

    let inv_stateful = assert_stateful_contract_strong(
        SpecCheckConfig::default(),
        |old: &CheckedWindow, &step: &u16| {
            old.__anneal_type_invariant_checked_window()
                && step <= 10
                && old.hi.saturating_add(step) < 1_000
        },
        |w: &mut CheckedWindow, &step: &u16| {
            w.hi += step;
            w.hi - w.lo
        },
        |old: &CheckedWindow, &step: &u16, new: &CheckedWindow, &width: &u16| {
            new.__anneal_type_invariant_checked_window()
                && new.lo == old.lo
                && new.hi == old.hi + step
                && width == new.hi - new.lo
        },
    );
    assert!(inv_stateful.precondition_hits > 0);
    assert!(inv_stateful.is_pointwise_strong());
}

#[test]
fn zero_panic_all_primitive_widths_wrapping_signed_and_array_lengths() {
    fn exercise_type<T: SampleInput + ReturnMutants + PartialEq>(seed: u64) {
        let mut rng = SplitMix64::new(seed);
        let mut mrng = rng.fork();
        let mut distinct_mutants = 0usize;
        let total = T::BOUNDARY_COUNT + 32;
        for idx in 0..total {
            let val = T::sample_at(idx, &mut rng);
            val.visit_mutants(&mut mrng, |m| {
                if m != val {
                    distinct_mutants += 1;
                }
            });
        }
        assert!(T::IS_SUBSINGLETON || distinct_mutants > 0);
    }

    // All unsigned and signed primitive widths (`8..=128` plus pointer-width).
    exercise_type::<u8>(1);
    exercise_type::<u16>(2);
    exercise_type::<u32>(3);
    exercise_type::<u64>(4);
    exercise_type::<u128>(5);
    exercise_type::<usize>(6);
    exercise_type::<i8>(7);
    exercise_type::<i16>(8);
    exercise_type::<i32>(9);
    exercise_type::<i64>(10);
    exercise_type::<i128>(11);
    exercise_type::<isize>(12);

    // `Wrapping<T>` across every unsigned and signed primitive width.
    exercise_type::<Wrapping<u8>>(13);
    exercise_type::<Wrapping<u16>>(14);
    exercise_type::<Wrapping<u32>>(15);
    exercise_type::<Wrapping<u64>>(16);
    exercise_type::<Wrapping<u128>>(17);
    exercise_type::<Wrapping<usize>>(18);
    exercise_type::<Wrapping<i8>>(19);
    exercise_type::<Wrapping<i16>>(20);
    exercise_type::<Wrapping<i32>>(21);
    exercise_type::<Wrapping<i64>>(22);
    exercise_type::<Wrapping<i128>>(23);
    exercise_type::<Wrapping<isize>>(24);

    // Every array length `0..=8` across unsigned, signed, and subsingleton elements.
    exercise_type::<[u8; 0]>(30);
    exercise_type::<[u8; 1]>(31);
    exercise_type::<[u8; 2]>(32);
    exercise_type::<[u8; 3]>(33);
    exercise_type::<[u8; 4]>(34);
    exercise_type::<[u8; 5]>(35);
    exercise_type::<[u8; 6]>(36);
    exercise_type::<[u8; 7]>(37);
    exercise_type::<[u8; 8]>(38);

    exercise_type::<[i8; 0]>(40);
    exercise_type::<[i8; 1]>(41);
    exercise_type::<[i8; 2]>(42);
    exercise_type::<[i8; 3]>(43);
    exercise_type::<[i8; 4]>(44);
    exercise_type::<[i8; 5]>(45);
    exercise_type::<[i8; 6]>(46);
    exercise_type::<[i8; 7]>(47);
    exercise_type::<[i8; 8]>(48);

    exercise_type::<[(); 0]>(50);
    exercise_type::<[(); 1]>(51);
    exercise_type::<[(); 8]>(52);

    // Signed `Wrapping<i8>` and `Wrapping<i128>` extremal boundary contracts
    // (`MIN`, `MAX`, `-1`, `0`) exercise two's-complement wrap-around without panicking.
    let mut saw_i8_min = false;
    let wrap_i8_neg = assert_contract_strong(
        SpecCheckConfig::default(),
        |&x: &Wrapping<i8>| {
            if x.0 == i8::MIN {
                saw_i8_min = true;
            }
            true
        },
        |&x| Wrapping(x.0.wrapping_neg()),
        |&x, &r: &Wrapping<i8>| r.0 == x.0.wrapping_neg(),
    );
    assert!(saw_i8_min);
    assert!(wrap_i8_neg.is_pointwise_strong());

    let mut saw_i128_min = false;
    let wrap_i128_add = assert_contract_strong(
        SpecCheckConfig::default(),
        |&(a, _b): &(Wrapping<i128>, Wrapping<i128>)| {
            if a.0 == i128::MIN {
                saw_i128_min = true;
            }
            true
        },
        |&(a, b)| a + b,
        |&(a, b), &r: &Wrapping<i128>| r.0 == a.0.wrapping_add(b.0),
    );
    assert!(saw_i128_min);
    assert!(wrap_i128_add.is_pointwise_strong());
}

// ---------------------------------------------------------------------------
// 4-tuple joint mutants across subsingleton components
// ---------------------------------------------------------------------------

/// Named 4-field struct with a subsingleton marker between its live fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TaggedTriple {
    head: u8,
    tag: UnitMarker,
    mid: u8,
    tail: u8,
}

anneal_spec::impl_spec_check_struct!(TaggedTriple {
    head: u8,
    tag: UnitMarker,
    mid: u8,
    tail: u8,
});

#[test]
fn quad_joint_mutants_span_non_adjacent_axes_around_subsingleton_components() {
    // The joint mutant perturbs every component that has a mutant and keeps a
    // subsingleton component as is, so it exists even when a `()` separates
    // the live components.
    let mut joint_count = 0usize;
    let mut total = 0usize;
    (10u8, (), 20u8, 30u8).visit_mutants(&mut SplitMix64::new(7), |m| {
        total += 1;
        if m.0 != 10 && m.2 != 20 && m.3 != 30 {
            joint_count += 1;
        }
    });
    assert_eq!(joint_count, 1);
    assert!(total <= 16);

    // Two live components that are not adjacent still get one joint mutant.
    let mut far_joint_count = 0usize;
    (10u8, (), (), 30u8).visit_mutants(&mut SplitMix64::new(7), |m| {
        if m.0 != 10 && m.3 != 30 {
            far_joint_count += 1;
        }
    });
    assert_eq!(far_joint_count, 1);

    // An adjacent live pair is perturbed jointly exactly once, not twice.
    let mut near_joint_count = 0usize;
    (10u8, 20u8, (), ()).visit_mutants(&mut SplitMix64::new(7), |m| {
        if m.0 != 10 && m.1 != 20 {
            near_joint_count += 1;
        }
    });
    assert_eq!(near_joint_count, 1);

    // With all four components live the mutant set stays within the default
    // 16-mutant budget and still ends round 0 with the all-axes joint.
    let mut full_total = 0usize;
    let mut full_joint_count = 0usize;
    (10u8, 20u8, 30u8, 40u8).visit_mutants(&mut SplitMix64::new(7), |m| {
        full_total += 1;
        if m.0 != 10 && m.1 != 20 && m.2 != 30 && m.3 != 40 {
            full_joint_count += 1;
        }
    });
    assert_eq!(full_total, 16);
    assert_eq!(full_joint_count, 1);

    // A disjunction over two components is a genuine (if loose) contract: each
    // single-component mutant survives because the other disjunct still holds,
    // so only a joint perturbation can falsify it. It must not be reported as
    // vacuous merely because a subsingleton sits between the two components.
    let across_unit = assert_contract_strong(
        SpecCheckConfig::default(),
        |_i: &(u8, u8)| true,
        |&(a, b)| (a, (), b, 0u8),
        |&(a, b), r: &(u8, (), u8, u8)| r.0 == a || r.2 == b,
    );
    assert!(across_unit.mutants_killed > 0);

    let across_two_units = assert_contract_strong(
        SpecCheckConfig::default(),
        |_i: &(u8, u8)| true,
        |&(a, b)| (a, (), (), b),
        |&(a, b), r: &(u8, (), (), u8)| r.0 == a || r.3 == b,
    );
    assert!(across_two_units.mutants_killed > 0);

    // The same holds for a struct that delegates to the 4-tuple of its fields.
    let tagged = assert_contract_strong(
        SpecCheckConfig::default(),
        |_i: &(u8, u8)| true,
        |&(a, b)| TaggedTriple {
            head: a,
            tag: UnitMarker,
            mid: b,
            tail: 0,
        },
        |&(a, b), r: &TaggedTriple| r.head == a || r.mid == b,
    );
    assert!(tagged.mutants_killed > 0);

    // A postcondition that ignores the output is still caught: the wider joint
    // adds a mutant to test, never a way to pass.
    let ignores_output = check_contract(
        SpecCheckConfig::default(),
        |_i: &(u8, u8)| true,
        |&(a, b)| (a, (), b, 0u8),
        |_i, _r: &(u8, (), u8, u8)| true,
    );
    assert!(matches!(ignores_output, SpecCheckOutcome::Failed(_)));
}

// ---------------------------------------------------------------------------
// Final negative controls & false-positive guards (Episode 1 closeout)
// ---------------------------------------------------------------------------

#[test]
fn array_both_ends_joint_mutant_and_false_positive_guards() {
    // `[0, 1]` has `m0 = 1 == self[1]`, so `both_ends` must use each end's own
    // first mutant (`[1, 2]`) rather than collapsing to a single-element mutant.
    let mut saw_distinct_ends_2 = false;
    [0u8, 1u8].visit_mutants(&mut SplitMix64::new(11), |m| {
        if m[0] != 0 && m[1] != 1 && m != [1, 0] {
            saw_distinct_ends_2 = true;
        }
    });
    assert!(saw_distinct_ends_2);

    let mut saw_distinct_ends_3 = false;
    [0u8, 5u8, 1u8].visit_mutants(&mut SplitMix64::new(11), |m| {
        if m[0] != 0 && m[1] == 5 && m[2] != 1 && m != [1, 5, 0] {
            saw_distinct_ends_3 = true;
        }
    });
    assert!(saw_distinct_ends_3);

    // Genuine disjunctive array postcondition over both ends must pass even
    // when `orig[last] == orig[0].wrapping_add(1)`.
    let array_disj = assert_contract_strong(
        SpecCheckConfig::default(),
        |_a: &u8| true,
        |&a| [a, 5u8, a.wrapping_add(1)],
        |&a, r: &[u8; 3]| r[0] == a || r[2] == a.wrapping_add(1),
    );
    assert!(array_disj.mutants_killed > 0);

    // Negative controls: genuine multi-branch `Option<()>` and `Result<(), u8>`
    // contracts (where one variant carries a subsingleton payload) must never
    // be false-flagged.
    let opt_unit = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u8| true,
        |&x| if x % 2 == 0 { Some(()) } else { None },
        |&x, r: &Option<()>| match r {
            Some(()) => x % 2 == 0,
            None => x % 2 != 0,
        },
    );
    assert!(opt_unit.is_pointwise_strong());

    let res_unit_err = assert_contract_strong(
        SpecCheckConfig::default(),
        |_x: &u8| true,
        |&x| if x < 100 { Ok(()) } else { Err(x - 100) },
        |&x, r: &Result<(), u8>| match r {
            Ok(()) => x < 100,
            Err(excess) => x >= 100 && *excess == x - 100,
        },
    );
    assert!(res_unit_err.is_pointwise_strong());

    // Negative control: genuine asymmetric multi-branch `Result<u16, u8>` where
    // the `Ok` branch only enforces a loose bound and the `Err` branch pins the
    // error code.
    let asym_res = assert_contract_strong(
        SpecCheckConfig::default(),
        |_p: &(u16, u16)| true,
        |&(a, b)| if b == 0 { Err(1u8) } else { Ok(a / b) },
        |&(a, b), r: &Result<u16, u8>| match r {
            Ok(q) => b != 0 && *q <= a,
            Err(code) => b == 0 && *code == 1,
        },
    );
    assert!(asym_res.is_pointwise_strong());

    // Negative control: genuine conditional frame-dependent stateful contract
    // (frame unchanged when `flag == false`, incremented when `flag == true`).
    let cond_stateful = assert_stateful_contract_strong(
        SpecCheckConfig::default(),
        |_old: &u16, _flag: &bool| true,
        |state: &mut u16, &flag: &bool| {
            let prev = *state;
            if flag {
                *state = state.wrapping_add(1);
            }
            (prev, flag)
        },
        |old: &u16, &flag: &bool, new: &u16, &(ret_prev, ret_flag): &(u16, bool)| {
            let expected = if flag { old.wrapping_add(1) } else { *old };
            ret_prev == *old && ret_flag == flag && *new == expected
        },
    );
    assert!(cond_stateful.is_pointwise_strong());
}

// ---------------------------------------------------------------------------
// Adversarial bypass hardening: padded mutant banks, narrow-equality
// preconditions, late traps, and degenerate configurations
// ---------------------------------------------------------------------------

#[test]
fn padded_custom_mutant_banks_are_deduplicated() {
    // A bank repeating one distinct wrong answer tests it once per hit, so duplicates
    // cannot inflate `mutants_tested` or `mutants_killed`.
    let repeated = check_contract_with_mutants(
        SpecCheckConfig::default(),
        &[9u32, 9, 9, 9],
        |&x: &u32| __anodized_fn_requires_const_seven_fn(x),
        |&x| const_seven_fn(x),
        |&x, &r| __anodized_fn_ensures_const_seven_fn(x, r),
    );
    assert!(repeated.is_strong());
    let repeated_stats = repeated.stats();
    assert!(repeated_stats.precondition_hits > 0);
    assert_eq!(
        repeated_stats.mutants_tested,
        repeated_stats.precondition_hits
    );
    assert_eq!(
        repeated_stats.mutants_killed,
        repeated_stats.precondition_hits
    );

    // Duplicates do not spend the per-hit budget ahead of a distinct candidate: with a
    // budget of two, `0` is still reached behind three copies of `1` and kills `r > 0`.
    let padded = check_contract_with_mutants(
        SpecCheckConfig::default().with_max_mutants_per_hit(2),
        &[1u32, 1, 1, 0],
        |&x: &u32| __anodized_fn_requires_loose_positive_fn(x),
        |&x| loose_positive_fn(x),
        |&x, &r| __anodized_fn_ensures_loose_positive_fn(x, r),
    );
    assert!(padded.is_strong());
    let padded_stats = padded.stats();
    assert!(padded_stats.is_pointwise_strong());
    assert!(padded_stats.mutants_tested <= 2 * padded_stats.precondition_hits);

    // A bank that only repeats the actual output tests nothing, however long it is.
    let only_output = check_contract_with_mutants(
        SpecCheckConfig::default(),
        &[7u32; 8],
        |&x: &u32| __anodized_fn_requires_const_seven_fn(x),
        |&x| const_seven_fn(x),
        |&x, &r| __anodized_fn_ensures_const_seven_fn(x, r),
    );
    assert_eq!(
        only_output.vacuity_class(),
        Some(VacuityClass::SurvivedAllMutants)
    );
    assert_eq!(only_output.stats().mutants_tested, 0);
    assert_eq!(
        only_output.failure().map(|f| f.detail),
        Some(FailureDetail::NoDistinctMutantsTested)
    );
}

/// Index of the first deterministic boundary trial whose sampled input satisfies `pre`.
fn first_boundary_hit<I: SampleInput, P: Fn(&I) -> bool>(pre: P) -> Option<usize> {
    let config = SpecCheckConfig::default();
    (0..I::BOUNDARY_COUNT).find(|&trial_idx| {
        anneal_spec::spec_check::replay_trial_input::<I>(config, trial_idx)
            .is_some_and(|input| pre(&input))
    })
}

#[test]
fn narrow_equality_preconditions_are_hit_within_the_boundary_corpus() {
    // Each narrow equality is first satisfied by a deterministic boundary trial, never
    // left to a seeded draw.
    assert_eq!(
        first_boundary_hit::<(u32, u32), _>(|&(a, b)| a == b),
        Some(0)
    );
    assert_eq!(
        first_boundary_hit::<(u32, u32, u32), _>(|&(_, lo, hi)| lo == hi),
        Some(0)
    );
    assert_eq!(first_boundary_hit::<u32, _>(|&x| x == 0), Some(0));
    assert!(first_boundary_hit::<u32, _>(|&x| x == u32::MAX).is_some());
    assert!(
        first_boundary_hit::<(u32, u32), _>(|&(a, b)| a == u32::MAX && b == u32::MAX).is_some()
    );
    assert!(first_boundary_hit::<(u32, u32), _>(|&(a, b)| a.checked_add(1) == Some(b)).is_some());

    // Restricted to the boundary corpus alone, each contract is still reached and strong.
    let eq_pair = check_contract(
        SpecCheckConfig::default().with_max_trials(<(u32, u32) as SampleInput>::BOUNDARY_COUNT),
        |&(a, b): &(u32, u32)| a == b,
        |&(a, b)| a ^ b,
        |_, &r| r == 0,
    );
    assert!(eq_pair.is_strong());
    assert!(eq_pair.stats().precondition_hits >= 2);

    let eq_bounds = check_contract(
        SpecCheckConfig::default()
            .with_max_trials(<(u32, u32, u32) as SampleInput>::BOUNDARY_COUNT),
        |&(_, lo, hi): &(u32, u32, u32)| lo == hi,
        |&(val, lo, hi)| clamp_u32(val, lo, hi),
        |&(_, lo, _), &r| r == lo,
    );
    assert!(eq_bounds.is_strong());
    assert!(eq_bounds.stats().precondition_hits >= 2);

    let at_zero = check_contract(
        SpecCheckConfig::default().with_max_trials(<u32 as SampleInput>::BOUNDARY_COUNT),
        |&x: &u32| x == 0,
        |&x| x.checked_sub(1),
        |_, r: &Option<u32>| r.is_none(),
    );
    assert!(at_zero.is_strong());
    assert_eq!(at_zero.stats().precondition_hits, 1);

    let at_max = check_contract(
        SpecCheckConfig::default().with_max_trials(<u32 as SampleInput>::BOUNDARY_COUNT),
        |&x: &u32| x == u32::MAX,
        |&x| x.checked_add(1),
        |_, r: &Option<u32>| r.is_none(),
    );
    assert!(at_max.is_strong());
    assert_eq!(at_max.stats().precondition_hits, 1);
}

#[test]
fn traps_after_strong_evidence_are_never_swallowed() {
    // By trial 3 the contract already has three precondition hits and killed mutants, yet
    // a trapping precondition is still reported, never skipped as a missed precondition.
    let pre_trap = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| if x == 3 { Err(()) } else { Ok(x < 3) },
        |&x| Ok(x),
        |&x, &r: &u32| Ok(r == x),
    );
    assert_eq!(pre_trap.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert_eq!(
        pre_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 3,
            trap: TrapKind::PreconditionPanicked,
        }))
    );
    assert_eq!(pre_trap.stats().trials_run, 4);
    assert_eq!(pre_trap.stats().precondition_hits, 3);
    assert!(pre_trap.stats().mutants_killed > 0);

    // A body that traps on a later admissible input.
    let body_trap = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| Ok(x < 100),
        |&x| if x == 2 { Err(()) } else { Ok(x) },
        |&x, &r: &u32| Ok(r == x),
    );
    assert_eq!(body_trap.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert_eq!(
        body_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 2,
            trap: TrapKind::BodyPanicked,
        }))
    );
    assert_eq!(body_trap.stats().precondition_hits, 3);
    assert!(body_trap.stats().mutants_killed > 0);

    // A postcondition that traps on the live output of a later admissible input, after
    // rejecting mutants normally on earlier ones.
    let post_trap = check_contract_fallible(
        SpecCheckConfig::default(),
        |&x: &u32| Ok(x < 100),
        |&x| Ok(x),
        |&x, &r: &u32| {
            if x == 2 && r == x {
                Err(())
            } else {
                Ok(r == x)
            }
        },
    );
    assert_eq!(post_trap.vacuity_class(), Some(VacuityClass::SpecViolation));
    assert_eq!(
        post_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 2,
            trap: TrapKind::PostconditionPanicked,
        }))
    );
    assert!(post_trap.stats().mutants_killed > 0);

    // The stateful entry point reports a late precondition trap the same way.
    let stateful_pre_trap = check_stateful_contract_fallible(
        SpecCheckConfig::default(),
        |old: &u32, &()| if *old == 2 { Err(()) } else { Ok(*old < 100) },
        |state: &mut u32, &()| {
            *state += 1;
            Ok(*state)
        },
        |old: &u32, &(), new: &u32, ret: &u32| Ok(*new == *old + 1 && *ret == *new),
    );
    assert_eq!(
        stateful_pre_trap.vacuity_class(),
        Some(VacuityClass::SpecViolation)
    );
    assert_eq!(
        stateful_pre_trap.failure().map(|f| f.detail),
        Some(FailureDetail::Violation(ViolationKind::ExecutionTrapped {
            trial_idx: 2,
            trap: TrapKind::PreconditionPanicked,
        }))
    );
    assert_eq!(stateful_pre_trap.stats().precondition_hits, 2);
}

#[test]
fn degenerate_configs_fail_closed_before_any_callback_runs() {
    let degenerate = [
        SpecCheckConfig::default().with_max_trials(0),
        SpecCheckConfig::default().with_min_precondition_hits(0),
        SpecCheckConfig::default()
            .with_max_trials(8)
            .with_min_precondition_hits(9),
    ];

    for config in degenerate {
        let stateless = check_contract_fallible(
            config,
            |_: &u32| -> Result<bool, ()> { panic!("`pre` ran under a degenerate config") },
            |_: &u32| -> Result<u32, ()> { panic!("`body` ran under a degenerate config") },
            |_: &u32, _: &u32| -> Result<bool, ()> {
                panic!("`post` ran under a degenerate config")
            },
        );
        assert_eq!(
            stateless.vacuity_class(),
            Some(VacuityClass::DeadPrecondition)
        );
        assert_eq!(
            stateless.failure().map(|f| f.detail),
            Some(FailureDetail::Violation(ViolationKind::DegenerateConfig))
        );
        assert_eq!(stateless.stats().trials_run, 0);

        let stateful = check_stateful_contract_fallible(
            config,
            |_: &u32, _: &()| -> Result<bool, ()> { panic!("`pre` ran under a degenerate config") },
            |_: &mut u32, _: &()| -> Result<u32, ()> {
                panic!("`body` ran under a degenerate config")
            },
            |_: &u32, _: &(), _: &u32, _: &u32| -> Result<bool, ()> {
                panic!("`post` ran under a degenerate config")
            },
        );
        assert_eq!(
            stateful.vacuity_class(),
            Some(VacuityClass::DeadPrecondition)
        );
        assert_eq!(
            stateful.failure().map(|f| f.detail),
            Some(FailureDetail::Violation(ViolationKind::DegenerateConfig))
        );
        assert_eq!(stateful.stats().trials_run, 0);
    }
}

// ---------------------------------------------------------------------------
// Cross-language 1:1 vacuity parity suite
// ---------------------------------------------------------------------------

/// Cross-Language Vacuity Parity Benchmark Matrix.
///
/// Each row is one contract, stated once here as a real `#[spec]`,
/// `#[external_spec]`, or `#[embed_spec]` companion and once in
/// `tests/mir/SpecRealizabilityTests.lean` (namespace `CrossLanguageParitySuite`)
/// over `Nat` models of the same types. Both files use the canonical benchmark
/// ID verbatim as the name of the row.
///
/// | Benchmark ID                       | Verdict in both languages |
/// |------------------------------------|---------------------------|
/// | `CL_POS_01_checked_add_u32`        | strong                    |
/// | `CL_POS_02_slice_bounds_and_empty` | strong                    |
/// | `CL_POS_03_saturating_clamp_u32`   | strong                    |
/// | `CL_POS_04_stateful_bounded_step`  | strong                    |
/// | `CL_VAC_01_dead_precondition`      | `DeadPrecondition`        |
/// | `CL_VAC_02_spec_violation`         | `SpecViolation`           |
/// | `CL_VAC_03_trivial_postcondition`  | `TrivialPostcondition`    |
/// | `CL_VAC_04_unbound_return_output`  | `UnboundReturnOutput`     |
/// | `CL_VAC_05_survived_all_mutants`   | `SurvivedAllMutants`      |
///
/// Lean reaches each verdict statically; this module reaches it dynamically.
/// Every check runs under `parity_config`, which lets the classification
/// probe leave the precondition: the static analysis reasons about `ensures`
/// on every input, and every postcondition below is total.
mod cross_language_parity_suite {
    use super::*;

    /// Canonical IDs of the 4 shared strong contracts, in matrix order.
    const POSITIVE_BENCHMARK_IDS: [&str; 4] = [
        "CL_POS_01_checked_add_u32",
        "CL_POS_02_slice_bounds_and_empty",
        "CL_POS_03_saturating_clamp_u32",
        "CL_POS_04_stateful_bounded_step",
    ];

    /// Canonical IDs of the 5 shared intentional vacuity mutants, in matrix order.
    const VACUITY_BENCHMARK_IDS: [&str; 5] = [
        "CL_VAC_01_dead_precondition",
        "CL_VAC_02_spec_violation",
        "CL_VAC_03_trivial_postcondition",
        "CL_VAC_04_unbound_return_output",
        "CL_VAC_05_survived_all_mutants",
    ];

    /// The class names `CL_VAC_01..CL_VAC_05` must emit, in order. The Lean suite
    /// pins the same list (`expectedClassNames`).
    const EXPECTED_CLASS_NAMES: [&str; 5] = [
        "DeadPrecondition",
        "SpecViolation",
        "TrivialPostcondition",
        "UnboundReturnOutput",
        "SurvivedAllMutants",
    ];

    /// Shared checker configuration of the parity suite.
    fn parity_config() -> SpecCheckConfig {
        SpecCheckConfig::default().with_probe_domain(ProbeDomain::Unconstrained)
    }

    // `CL_POS_02_slice_bounds_and_empty`: `ret.0` is `is_empty` and `ret.1` is whether
    // `idx` is a valid index. `CL_POS_01`, `CL_POS_03`, and `CL_POS_04` reuse the
    // `spec_u32_checked_add`, `clamp_u32`, and `Counter::step` companions above.
    #[spec(
        requires: idx <= slice.len(),
        ensures: |ret| [
            ret.0 == (slice.len() == 0),
            ret.1 == (idx < slice.len()),
        ],
    )]
    fn cl_pos_02_slice_bounds_and_empty_fn(slice: &[u32], idx: usize) -> (bool, bool) {
        (slice.is_empty(), slice.get(idx).is_some())
    }

    // `CL_VAC_01_dead_precondition`: contradictory `requires`.
    #[spec(
        requires: [x > 100, x < 50],
        ensures: |ret| ret == x,
    )]
    fn cl_vac_01_dead_precondition_fn(x: u32) -> u32 {
        x
    }

    // `CL_VAC_02_spec_violation`: dishonest off-by-one clamp, claimed to lie in
    // `[lo, hi]` and to equal `hi + 1`.
    #[spec(
        requires: lo <= hi,
        ensures: |ret| [
            ret >= lo,
            ret <= hi,
            (ret as u64) == (hi as u64) + 1,
        ],
    )]
    fn cl_vac_02_spec_violation_fn(val: u32, lo: u32, hi: u32) -> u32 {
        clamp_u32(val, lo, hi)
    }

    // `CL_VAC_03_trivial_postcondition`: disguised reflexive tautology.
    #[spec(
        ensures: |ret| ret == ret || ret == 0,
    )]
    fn cl_vac_03_trivial_postcondition_fn(x: u32) -> u32 {
        x
    }

    // `CL_VAC_04_unbound_return_output`: the output is bound and discarded.
    #[spec(
        requires: lo <= hi,
        ensures: |ret| {
            let _ = ret;
            lo <= hi
        },
    )]
    fn cl_vac_04_unbound_return_output_fn(val: u32, lo: u32, hi: u32) -> u32 {
        clamp_u32(val, lo, hi)
    }

    // `CL_VAC_05_survived_all_mutants`: postcondition masked by its own `requires`.
    #[spec(
        requires: x < 10,
        ensures: |ret| x < 10 || ret == 42,
    )]
    fn cl_vac_05_survived_all_mutants_fn(x: u32) -> u32 {
        x
    }

    fn cl_vac_01_outcome() -> SpecCheckOutcome {
        check_contract(
            parity_config(),
            |&x: &u32| __anodized_fn_requires_cl_vac_01_dead_precondition_fn(x),
            |&x| cl_vac_01_dead_precondition_fn(x),
            |&x, &ret| __anodized_fn_ensures_cl_vac_01_dead_precondition_fn(x, ret),
        )
    }

    fn cl_vac_02_outcome() -> SpecCheckOutcome {
        check_contract(
            parity_config(),
            |&(val, lo, hi): &(u32, u32, u32)| {
                __anodized_fn_requires_cl_vac_02_spec_violation_fn(val, lo, hi)
            },
            |&(val, lo, hi)| cl_vac_02_spec_violation_fn(val, lo, hi),
            |&(val, lo, hi), &ret| {
                __anodized_fn_ensures_cl_vac_02_spec_violation_fn(val, lo, hi, ret)
            },
        )
    }

    fn cl_vac_03_outcome() -> SpecCheckOutcome {
        check_contract(
            parity_config(),
            |&x: &u32| __anodized_fn_requires_cl_vac_03_trivial_postcondition_fn(x),
            |&x| cl_vac_03_trivial_postcondition_fn(x),
            |&x, &ret| __anodized_fn_ensures_cl_vac_03_trivial_postcondition_fn(x, ret),
        )
    }

    fn cl_vac_04_outcome() -> SpecCheckOutcome {
        check_contract(
            parity_config(),
            |&(val, lo, hi): &(u32, u32, u32)| {
                __anodized_fn_requires_cl_vac_04_unbound_return_output_fn(val, lo, hi)
            },
            |&(val, lo, hi)| cl_vac_04_unbound_return_output_fn(val, lo, hi),
            |&(val, lo, hi), &ret| {
                __anodized_fn_ensures_cl_vac_04_unbound_return_output_fn(val, lo, hi, ret)
            },
        )
    }

    fn cl_vac_05_outcome() -> SpecCheckOutcome {
        check_contract(
            parity_config(),
            |&x: &u32| __anodized_fn_requires_cl_vac_05_survived_all_mutants_fn(x),
            |&x| cl_vac_05_survived_all_mutants_fn(x),
            |&x, &ret| __anodized_fn_ensures_cl_vac_05_survived_all_mutants_fn(x, ret),
        )
    }

    /// The 5 vacuity mutants paired with their canonical IDs, in matrix order.
    fn vacuity_matrix() -> [(&'static str, SpecCheckOutcome); 5] {
        [
            (VACUITY_BENCHMARK_IDS[0], cl_vac_01_outcome()),
            (VACUITY_BENCHMARK_IDS[1], cl_vac_02_outcome()),
            (VACUITY_BENCHMARK_IDS[2], cl_vac_03_outcome()),
            (VACUITY_BENCHMARK_IDS[3], cl_vac_04_outcome()),
            (VACUITY_BENCHMARK_IDS[4], cl_vac_05_outcome()),
        ]
    }

    #[test]
    fn cl_pos_01_checked_add_u32() {
        let mut saw_some = false;
        let mut saw_none = false;

        let stats = assert_contract_strong(
            parity_config(),
            |&(a, b): &(u32, u32)| __anodized_fn_requires_spec_u32_checked_add(a, b),
            |&(a, b)| {
                let ret = a.checked_add(b);
                if ret.is_some() {
                    saw_some = true;
                } else {
                    saw_none = true;
                }
                ret
            },
            |&(a, b), &ret| __anodized_fn_ensures_spec_u32_checked_add(a, b, ret),
        );

        assert!(
            saw_some,
            "{}: no `Some(a + b)` trial",
            POSITIVE_BENCHMARK_IDS[0]
        );
        assert!(
            saw_none,
            "{}: no overflowing `None` trial",
            POSITIVE_BENCHMARK_IDS[0]
        );
        assert!(stats.is_pointwise_strong());
    }

    #[test]
    fn cl_pos_02_slice_bounds_and_empty() {
        let mut saw_empty = false;
        let mut saw_in_bounds = false;
        let mut saw_one_past_end = false;

        let bounds_stats = assert_contract_strong(
            parity_config(),
            |&(arr, prefix_len, idx): &([u32; 4], usize, usize)| {
                prefix_len <= 4
                    && __anodized_fn_requires_cl_pos_02_slice_bounds_and_empty_fn(
                        &arr[..prefix_len],
                        idx,
                    )
            },
            |&(arr, prefix_len, idx)| {
                if prefix_len == 0 {
                    saw_empty = true;
                } else if idx < prefix_len {
                    saw_in_bounds = true;
                } else {
                    saw_one_past_end = true;
                }
                cl_pos_02_slice_bounds_and_empty_fn(&arr[..prefix_len], idx)
            },
            |&(arr, prefix_len, idx), &ret| {
                __anodized_fn_ensures_cl_pos_02_slice_bounds_and_empty_fn(
                    &arr[..prefix_len],
                    idx,
                    ret,
                )
            },
        );

        assert!(
            saw_empty,
            "{}: no empty slice trial",
            POSITIVE_BENCHMARK_IDS[1]
        );
        assert!(
            saw_in_bounds,
            "{}: no `idx < len` trial",
            POSITIVE_BENCHMARK_IDS[1]
        );
        assert!(
            saw_one_past_end,
            "{}: no `idx == len` trial",
            POSITIVE_BENCHMARK_IDS[1]
        );
        assert!(bounds_stats.is_pointwise_strong());

        // The standard-library contracts behind the same row: `len == 0 <-> is_empty`.
        let len_stats = assert_contract_strong(
            parity_config(),
            |&(arr, prefix_len): &([u32; 4], usize)| {
                prefix_len <= 4 && __anodized_fn_requires_spec_slice_u32_len(&arr[..prefix_len])
            },
            |&(arr, prefix_len)| arr[..prefix_len].len(),
            |&(arr, prefix_len), &ret| {
                __anodized_fn_ensures_spec_slice_u32_len(&arr[..prefix_len], ret)
            },
        );
        assert!(len_stats.is_pointwise_strong());

        let empty_stats = assert_contract_strong(
            parity_config(),
            |&(arr, prefix_len): &([u32; 4], usize)| {
                prefix_len <= 4
                    && __anodized_fn_requires_spec_slice_u32_is_empty(&arr[..prefix_len])
            },
            |&(arr, prefix_len)| arr[..prefix_len].is_empty(),
            |&(arr, prefix_len), &ret| {
                __anodized_fn_ensures_spec_slice_u32_is_empty(&arr[..prefix_len], ret)
            },
        );
        assert!(empty_stats.is_pointwise_strong());
    }

    #[test]
    fn cl_pos_03_saturating_clamp_u32() {
        let mut saw_below = false;
        let mut saw_in_range = false;
        let mut saw_above = false;
        let mut saw_eq_bounds = false;

        let stats = assert_contract_strong(
            parity_config(),
            |&(val, lo, hi): &(u32, u32, u32)| __anodized_fn_requires_clamp_u32(val, lo, hi),
            |&(val, lo, hi)| {
                if lo == hi {
                    saw_eq_bounds = true;
                }
                if val < lo {
                    saw_below = true;
                } else if val > hi {
                    saw_above = true;
                } else {
                    saw_in_range = true;
                }
                clamp_u32(val, lo, hi)
            },
            |&(val, lo, hi), &ret| __anodized_fn_ensures_clamp_u32(val, lo, hi, ret),
        );

        assert!(
            saw_below,
            "{}: no `val < lo` trial",
            POSITIVE_BENCHMARK_IDS[2]
        );
        assert!(
            saw_in_range,
            "{}: no in-range trial",
            POSITIVE_BENCHMARK_IDS[2]
        );
        assert!(
            saw_above,
            "{}: no `val > hi` trial",
            POSITIVE_BENCHMARK_IDS[2]
        );
        assert!(
            saw_eq_bounds,
            "{}: no `lo == hi` trial",
            POSITIVE_BENCHMARK_IDS[2]
        );
        assert!(stats.is_pointwise_strong());
    }

    #[test]
    fn cl_pos_04_stateful_bounded_step() {
        // Both output axes (the return value and the `&mut` post-state) must kill mutants
        // independently, as `require_both_state_and_return_kills` demands by default.
        let stats = assert_stateful_contract_strong(
            parity_config(),
            |old: &Counter, &()| old.clone().__anodized_fn_requires_step(),
            |counter: &mut Counter, &()| counter.step(),
            |old: &Counter, &(), new: &Counter, ret: &u32| {
                old.clone().__anodized_fn_ensures_step(*ret)
                    && new.value == *ret
                    && new.limit == old.limit
            },
        );
        assert!(
            stats.precondition_hits > 0,
            "{}: precondition never hit",
            POSITIVE_BENCHMARK_IDS[3]
        );
        assert!(stats.is_pointwise_strong());
        assert!(!stats.subsingleton_return);
    }

    #[test]
    fn cl_vac_01_dead_precondition() {
        let outcome = cl_vac_01_outcome();
        assert_eq!(
            outcome.vacuity_class(),
            Some(VacuityClass::DeadPrecondition)
        );
        assert_eq!(
            outcome.failure().map(|f| f.detail),
            Some(FailureDetail::InsufficientPreconditionHits {
                required: 1,
                observed: 0,
            })
        );
    }

    #[test]
    fn cl_vac_02_spec_violation() {
        let outcome = cl_vac_02_outcome();
        assert_eq!(outcome.vacuity_class(), Some(VacuityClass::SpecViolation));
        assert_eq!(
            outcome.failure().map(|f| f.detail),
            Some(FailureDetail::Violation(
                ViolationKind::PostconditionFalse { trial_idx: 0 }
            ))
        );
        // The counterexample is the very first boundary trial.
        assert_eq!(
            anneal_spec::spec_check::replay_trial_input::<(u32, u32, u32)>(parity_config(), 0),
            Some((0, 0, 0))
        );
    }

    #[test]
    fn cl_vac_03_trivial_postcondition() {
        let outcome = cl_vac_03_outcome();
        assert_eq!(
            outcome.vacuity_class(),
            Some(VacuityClass::TrivialPostcondition)
        );
        assert!(matches!(
            outcome.failure().map(|f| f.detail),
            Some(FailureDetail::AllMutantsSurvived {
                saw_any_false: false,
                saw_output_sensitivity: false,
                ..
            })
        ));
    }

    #[test]
    fn cl_vac_04_unbound_return_output() {
        let outcome = cl_vac_04_outcome();
        assert_eq!(
            outcome.vacuity_class(),
            Some(VacuityClass::UnboundReturnOutput)
        );
        assert!(matches!(
            outcome.failure().map(|f| f.detail),
            Some(FailureDetail::AllMutantsSurvived {
                out_of_precondition_probes,
                saw_any_false: true,
                saw_output_sensitivity: false,
                ..
            }) if out_of_precondition_probes > 0
        ));
    }

    #[test]
    fn cl_vac_05_survived_all_mutants() {
        let outcome = cl_vac_05_outcome();
        assert_eq!(
            outcome.vacuity_class(),
            Some(VacuityClass::SurvivedAllMutants)
        );
        assert!(matches!(
            outcome.failure().map(|f| f.detail),
            Some(FailureDetail::AllMutantsSurvived {
                saw_any_false: true,
                saw_output_sensitivity: true,
                ..
            })
        ));
    }

    #[test]
    fn cl_vacuity_class_names_match_the_lean_matrix_in_exact_order() {
        let matrix = vacuity_matrix();
        assert_eq!(matrix.map(|(id, _)| id), VACUITY_BENCHMARK_IDS);

        let emitted = matrix.map(|(id, outcome)| match outcome.vacuity_class() {
            Some(class) => class.canonical_name(),
            None => panic!("{id}: expected a vacuity verdict, got a strong contract"),
        });
        assert_eq!(emitted, EXPECTED_CLASS_NAMES);

        // The frozen taxonomy enumerates the classes in the same order, and every
        // canonical name parses back to its class.
        assert_eq!(
            VacuityClass::ALL.map(VacuityClass::canonical_name),
            EXPECTED_CLASS_NAMES
        );
        for class in VacuityClass::ALL {
            assert_eq!(
                VacuityClass::from_canonical_name(class.canonical_name()),
                Some(class)
            );
        }
        assert_eq!(VacuityClass::from_canonical_name("NotAVacuityClass"), None);
        assert_eq!(VacuityClass::from_canonical_name("deadprecondition"), None);
    }
}
