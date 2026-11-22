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
    FailureDetail, ReturnMutants, SampleInput, SpecCheckConfig, SpecCheckOutcome, SplitMix64,
    SyntacticBindingHint, TrapKind, VacuityClass, ViolationKind, assert_contract_strong,
    assert_stateful_contract_strong, check_contract, check_contract_fallible,
    check_contract_with_mutants, check_stateful_contract,
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
    // Purely dynamic detection (`x < 500` is false for `x >= 500`, yet independent of `r`).
    let dynamic_outcome = check_contract(
        SpecCheckConfig::default(),
        |&x: &u32| __anodized_fn_requires_unbound_return_fn(x),
        |&x| unbound_return_fn(x),
        |&x, &r| __anodized_fn_ensures_unbound_return_fn(x, r),
    );
    assert_eq!(
        dynamic_outcome.vacuity_class(),
        Some(VacuityClass::UnboundReturnOutput)
    );

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
    // `x < 10 || r == 42`: output-sensitive when `x >= 10`, yet every mutant survives under `x < 10`.
    let vacuous_under_req = check_contract(
        SpecCheckConfig::default(),
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
