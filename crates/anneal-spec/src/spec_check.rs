// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `#![no_std]` deterministic dynamic contract and output-mutant vacuity checker.
//!
//! This module provides zero-allocation (`core`-only) runtime checking of Anneal
//! `#[spec]`, `#[embed_spec]`, and `#[external_spec]` contracts against the
//! frozen 5-class cross-language vacuity taxonomy ([`VacuityClass`]):
//!
//! 1. **Stage D1 (Boundary + Seeded Sampling)**: Draws inputs via [`SampleInput`]
//!    starting with deterministic boundary values and cross-products before
//!    stratified [`SplitMix64`] draws, verifying that preconditions are actually
//!    satisfiable ([`VacuityClass::DeadPrecondition`]).
//! 2. **Stage D2 (Live Conformance)**: Executes the target function on
//!    precondition-admissible inputs and checks that the postcondition holds
//!    without panicking ([`VacuityClass::SpecViolation`]).
//! 3. **Stage D3 (Output-Mutant Killing)**: Perturbs the actual output (and
//!    post-state for stateful `&mut S` contracts) via [`ReturnMutants`] to verify
//!    postcondition dichotomy and distinguish [`VacuityClass::TrivialPostcondition`],
//!    [`VacuityClass::UnboundReturnOutput`], and [`VacuityClass::SurvivedAllMutants`].
//!
//! # Domain safety
//!
//! A postcondition is only required to be meaningful on inputs its
//! precondition admits: outside `pre` it may overflow, index out of bounds,
//! loop for an impractical number of iterations, or rely on `unsafe` code whose
//! safety argument is the precondition itself. The checker therefore upholds
//! one invariant in every stage and in every entry point:
//!
//! > `post(input, output)` is evaluated only when `pre(input)` returned `true`.
//!
//! The single exception is the opt-in [`ProbeDomain::Unconstrained`]
//! classification probe, by which a caller asserts that `post` is total on
//! every sampled input. Under the default [`ProbeDomain::PreconditionOnly`],
//! a postcondition that never rejects an output on precondition-admissible
//! inputs is reported as [`VacuityClass::TrivialPostcondition`], and
//! [`FailureDetail::AllMutantsSurvived::skipped_out_of_precondition`] records
//! how many sampled inputs were withheld from `post`; refining that verdict
//! into [`VacuityClass::UnboundReturnOutput`] or
//! [`VacuityClass::SurvivedAllMutants`] requires either a
//! [`SyntacticBindingHint`] or [`ProbeDomain::Unconstrained`].
//!
//! Stage D3 necessarily evaluates `post` on perturbed outputs. The infallible
//! entry points ([`check_contract`], [`check_contract_with_mutants`], and
//! [`check_stateful_contract`]) cannot intercept a panic in `core`-only code,
//! so a postcondition that can trap on a wrong output (for example by indexing
//! with the return value) must be checked through [`check_contract_fallible`]
//! or [`check_stateful_contract_fallible`], which count a trapping mutant
//! evaluation as that mutant being rejected.
//!
//! # Reproducing a failure
//!
//! Every check is a pure function of its [`SpecCheckConfig`] and callbacks: the
//! same seed samples the same inputs and mutants on every run. A live violation
//! or trap reports the index of the offending trial
//! ([`SpecCheckFailure::counterexample_trial`]); [`replay_trial_input`] and
//! [`replay_stateful_trial_input`] rebuild the exact input sampled at that
//! index, without requiring inputs to be `Copy` or `Debug`.
//!
//! # Custom types
//!
//! A struct or newtype becomes a checkable input, output, or `&mut` state with
//! one `impl_spec_check_struct!` invocation, which delegates [`SampleInput`]
//! and [`ReturnMutants`] to the field types. Types with an invariant need no
//! special sampler: state the invariant in the precondition.

use core::array;
use core::fmt;
use core::num::Wrapping;

/// Frozen 5-class cross-language vacuity and conformance failure taxonomy.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VacuityClass {
    /// Precondition was never satisfied (or fell below `min_precondition_hits`).
    DeadPrecondition,
    /// Live execution violated the postcondition or trapped during evaluation.
    SpecViolation,
    /// Postcondition accepted every probed `(input, output)` pair. The probed
    /// inputs are the precondition-admissible ones unless
    /// [`ProbeDomain::Unconstrained`] is selected.
    TrivialPostcondition,
    /// Postcondition depends on inputs (rejects every probed output for some
    /// probed input) yet appears independent of the output (or mutated
    /// post-state).
    UnboundReturnOutput,
    /// Postcondition varies with the output somewhere in the probed domain (or
    /// no distinct mutants were tested), yet every tested mutant survived on
    /// precondition-admissible inputs.
    SurvivedAllMutants,
}

impl VacuityClass {
    /// All five classes in their frozen cross-language order, the order in
    /// which the Lean static analysis enumerates them (`VacuityClass.all`).
    pub const ALL: [Self; 5] = [
        Self::DeadPrecondition,
        Self::SpecViolation,
        Self::TrivialPostcondition,
        Self::UnboundReturnOutput,
        Self::SurvivedAllMutants,
    ];

    /// Returns the canonical cross-language diagnostic identifier for this class.
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::DeadPrecondition => "DeadPrecondition",
            Self::SpecViolation => "SpecViolation",
            Self::TrivialPostcondition => "TrivialPostcondition",
            Self::UnboundReturnOutput => "UnboundReturnOutput",
            Self::SurvivedAllMutants => "SurvivedAllMutants",
        }
    }

    /// Parses a canonical cross-language identifier back into its class, the
    /// inverse of [`Self::canonical_name`]. Returns `None` for any other
    /// string; matching is exact and case-sensitive.
    pub fn from_canonical_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|class| class.canonical_name() == name)
    }
}

impl fmt::Display for VacuityClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.canonical_name())
    }
}

/// Deterministic 64-bit SplitMix64 pseudo-random number generator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    /// Default deterministic seed (golden-ratio 64-bit increment).
    pub const DEFAULT_SEED: u64 = 0x9E37_79B9_7F4A_7C15;

    /// Constructs a new generator from `seed`.
    ///
    /// SplitMix64 advances its internal counter by `0x9E37_79B9_7F4A_7C15`
    /// prior to mixing, so even `seed == 0` yields a non-degenerate stream.
    pub const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    /// Generates the next 64-bit unsigned integer.
    pub const fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Generates the next 32-bit unsigned integer from the upper 32 bits.
    pub const fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 32) as u32
    }

    /// Generates the next 128-bit unsigned integer from two 64-bit draws.
    pub const fn next_u128(&mut self) -> u128 {
        let hi = self.next_u64() as u128;
        let lo = self.next_u64() as u128;
        (hi << 64) | lo
    }

    /// Generates the next `usize`.
    pub const fn next_usize(&mut self) -> usize {
        self.next_u64() as usize
    }

    /// Generates the next `bool`.
    pub const fn next_bool(&mut self) -> bool {
        (self.next_u64() & 1) != 0
    }

    /// Forks an independent child generator seeded from the current stream.
    pub const fn fork(&mut self) -> Self {
        Self::new(self.next_u64())
    }
}

impl Default for SplitMix64 {
    fn default() -> Self {
        Self::new(Self::DEFAULT_SEED)
    }
}

/// Deterministic boundary-first input sampler for dynamic contract checking.
pub trait SampleInput: Sized {
    /// Number of deterministic boundary trials before switching to seeded
    /// pseudo-random generation.
    const BOUNDARY_COUNT: usize;

    /// Produces the candidate input for `trial_idx`.
    ///
    /// Indices `0..Self::BOUNDARY_COUNT` should deterministically cover edge
    /// cases (extremes, small integers, variant flips, and tuple cross-pairs);
    /// indices `>= Self::BOUNDARY_COUNT` draw from `rng`.
    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self;
}

impl SampleInput for () {
    const BOUNDARY_COUNT: usize = 1;

    fn sample_at(_trial_idx: usize, _rng: &mut SplitMix64) -> Self {}
}

impl SampleInput for bool {
    const BOUNDARY_COUNT: usize = 2;

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        match trial_idx {
            0 => false,
            1 => true,
            _ => rng.next_bool(),
        }
    }
}

macro_rules! impl_sample_input_unsigned {
    ($ty:ty, $boundaries:expr, $med_mask:expr, $full_draw:expr) => {
        impl SampleInput for $ty {
            const BOUNDARY_COUNT: usize = $boundaries.len();

            fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
                const BOUNDARIES: &[$ty] = &$boundaries;
                if trial_idx < BOUNDARIES.len() {
                    BOUNDARIES[trial_idx]
                } else {
                    let bucket = rng.next_u64() & 3;
                    let raw: $ty = $full_draw(rng);
                    match bucket {
                        // Small range `0..=63` to hit narrow small-integer preconditions.
                        0 => raw & (0x3F as $ty),
                        // Medium range `0..=1023` (or full width for `u8`).
                        1 => raw & ($med_mask as $ty),
                        // Near-MAX range to exercise overflow/saturation preconditions.
                        2 => <$ty>::MAX.wrapping_sub(raw & (0xFF as $ty)),
                        // Full-width uniform draw.
                        _ => raw,
                    }
                }
            }
        }
    };
}

impl_sample_input_unsigned!(
    u8,
    [0, 1, 2, 3, 10, 16, 42, 64, 0x7F, 0x80, u8::MAX - 1, u8::MAX],
    0xFF,
    |rng: &mut SplitMix64| rng.next_u64() as u8
);
impl_sample_input_unsigned!(
    u16,
    [
        0,
        1,
        2,
        3,
        10,
        16,
        42,
        0x7F,
        0x80,
        0xFF,
        0x100,
        u16::MAX / 2,
        u16::MAX - 1,
        u16::MAX,
    ],
    0x3FF,
    |rng: &mut SplitMix64| rng.next_u64() as u16
);
impl_sample_input_unsigned!(
    u32,
    [
        0,
        1,
        2,
        3,
        10,
        16,
        42,
        0x7F,
        0x80,
        0xFF,
        0x100,
        1_000,
        u32::MAX / 2,
        u32::MAX - 1,
        u32::MAX,
    ],
    0x3FF,
    |rng: &mut SplitMix64| rng.next_u32()
);
impl_sample_input_unsigned!(
    u64,
    [
        0,
        1,
        2,
        3,
        10,
        16,
        42,
        0x7F,
        0x80,
        0xFF,
        0x100,
        1_000,
        u32::MAX as u64,
        u64::MAX / 2,
        u64::MAX - 1,
        u64::MAX,
    ],
    0x3FF,
    |rng: &mut SplitMix64| rng.next_u64()
);
impl_sample_input_unsigned!(
    u128,
    [
        0,
        1,
        2,
        3,
        10,
        16,
        42,
        0x7F,
        0x80,
        0xFF,
        0x100,
        1_000,
        u64::MAX as u128,
        u128::MAX / 2,
        u128::MAX - 1,
        u128::MAX,
    ],
    0x3FF,
    |rng: &mut SplitMix64| rng.next_u128()
);
impl_sample_input_unsigned!(
    usize,
    [
        0,
        1,
        2,
        3,
        10,
        16,
        42,
        0x7F,
        0x80,
        0xFF,
        0x100,
        1_000,
        usize::MAX / 2,
        usize::MAX - 1,
        usize::MAX,
    ],
    0x3FF,
    |rng: &mut SplitMix64| rng.next_usize()
);

macro_rules! impl_sample_input_signed {
    ($ty:ty, $boundaries:expr, $med_draw:expr, $full_draw:expr) => {
        impl SampleInput for $ty {
            const BOUNDARY_COUNT: usize = $boundaries.len();

            fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
                const BOUNDARIES: &[$ty] = &$boundaries;
                if trial_idx < BOUNDARIES.len() {
                    BOUNDARIES[trial_idx]
                } else {
                    let bucket = rng.next_u64() & 3;
                    let raw64 = rng.next_u64();
                    match bucket {
                        // Small centered range `-64..=63`.
                        0 => ((raw64 & 0x7F) as $ty).wrapping_sub(64),
                        // Medium centered range `-512..=511` (or full `i8`).
                        1 => $med_draw(raw64),
                        // Near `MIN` or `MAX` (offset `0..=127`, always non-negative).
                        2 => {
                            let delta = ((raw64 >> 1) & 0x7F) as $ty;
                            if (raw64 & 1) == 0 {
                                <$ty>::MAX.wrapping_sub(delta)
                            } else {
                                <$ty>::MIN.wrapping_add(delta)
                            }
                        }
                        // Full-width uniform draw.
                        _ => $full_draw(rng),
                    }
                }
            }
        }
    };
}

// Note: `MIN` is placed at `len() / 2` so tuple cross-products using the
// representative boundary indices `[0, 1, 2, count / 2, count - 2, count - 1]`
// deterministically cover `0`, `1`, `-1`, `MIN`, `MAX - 1`, and `MAX`.
impl_sample_input_signed!(
    i8,
    [
        0,
        1,
        -1,
        2,
        -2,
        10,
        i8::MIN,
        -10,
        42,
        -42,
        i8::MIN + 1,
        i8::MAX - 1,
        i8::MAX,
    ],
    |raw64: u64| raw64 as i8,
    |rng: &mut SplitMix64| rng.next_u64() as i8
);
impl_sample_input_signed!(
    i16,
    [
        0,
        1,
        -1,
        2,
        -2,
        10,
        -10,
        i16::MIN,
        i16::MIN + 1,
        42,
        127,
        -128,
        i16::MAX / 2,
        i16::MAX - 1,
        i16::MAX,
    ],
    |raw64: u64| ((raw64 & 0x3FF) as i16).wrapping_sub(512),
    |rng: &mut SplitMix64| rng.next_u64() as i16
);
impl_sample_input_signed!(
    i32,
    [
        0,
        1,
        -1,
        2,
        -2,
        10,
        -10,
        i32::MIN,
        i32::MIN + 1,
        42,
        127,
        -128,
        i32::MAX / 2,
        i32::MAX - 1,
        i32::MAX,
    ],
    |raw64: u64| ((raw64 & 0x3FF) as i32).wrapping_sub(512),
    |rng: &mut SplitMix64| rng.next_u32() as i32
);
impl_sample_input_signed!(
    i64,
    [
        0,
        1,
        -1,
        2,
        -2,
        10,
        -10,
        i64::MIN,
        i64::MIN + 1,
        42,
        127,
        -128,
        i64::MAX / 2,
        i64::MAX - 1,
        i64::MAX,
    ],
    |raw64: u64| ((raw64 & 0x3FF) as i64).wrapping_sub(512),
    |rng: &mut SplitMix64| rng.next_u64() as i64
);
impl_sample_input_signed!(
    i128,
    [
        0,
        1,
        -1,
        2,
        -2,
        10,
        -10,
        i128::MIN,
        i128::MIN + 1,
        42,
        127,
        -128,
        i128::MAX / 2,
        i128::MAX - 1,
        i128::MAX,
    ],
    |raw64: u64| ((raw64 & 0x3FF) as i128).wrapping_sub(512),
    |rng: &mut SplitMix64| rng.next_u128() as i128
);
impl_sample_input_signed!(
    isize,
    [
        0,
        1,
        -1,
        2,
        -2,
        10,
        -10,
        isize::MIN,
        isize::MIN + 1,
        42,
        127,
        -128,
        isize::MAX / 2,
        isize::MAX - 1,
        isize::MAX,
    ],
    |raw64: u64| ((raw64 & 0x3FF) as isize).wrapping_sub(512),
    |rng: &mut SplitMix64| rng.next_usize() as isize
);

impl<T: SampleInput> SampleInput for Wrapping<T> {
    const BOUNDARY_COUNT: usize = T::BOUNDARY_COUNT;

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        Wrapping(T::sample_at(trial_idx, rng))
    }
}

impl<T: SampleInput> SampleInput for Option<T> {
    const BOUNDARY_COUNT: usize = T::BOUNDARY_COUNT.saturating_add(1);

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        if trial_idx == 0 {
            None
        } else {
            let inner = trial_idx - 1;
            if inner < T::BOUNDARY_COUNT {
                Some(T::sample_at(inner, rng))
            } else if (rng.next_u64() & 3) == 0 {
                None
            } else {
                Some(T::sample_at(trial_idx.max(T::BOUNDARY_COUNT), rng))
            }
        }
    }
}

impl<T: SampleInput, E: SampleInput> SampleInput for Result<T, E> {
    const BOUNDARY_COUNT: usize = T::BOUNDARY_COUNT.saturating_add(E::BOUNDARY_COUNT);

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        let pair_min = min_usize(T::BOUNDARY_COUNT, E::BOUNDARY_COUNT);
        let interleaved = pair_min.saturating_mul(2);
        if trial_idx < interleaved {
            if trial_idx % 2 == 0 {
                Ok(T::sample_at(trial_idx / 2, rng))
            } else {
                Err(E::sample_at(trial_idx / 2, rng))
            }
        } else if trial_idx < Self::BOUNDARY_COUNT {
            let idx = pair_min.saturating_add(trial_idx - interleaved);
            if T::BOUNDARY_COUNT > E::BOUNDARY_COUNT {
                Ok(T::sample_at(idx, rng))
            } else {
                Err(E::sample_at(idx, rng))
            }
        } else if rng.next_bool() {
            Ok(T::sample_at(trial_idx.max(T::BOUNDARY_COUNT), rng))
        } else {
            Err(E::sample_at(trial_idx.max(E::BOUNDARY_COUNT), rng))
        }
    }
}

const fn min_usize(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

const fn max_usize(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

/// Maps slot `k` (`0..min(count, 6)`) into a representative boundary index in
/// `0..count` spanning the start (`0, 1, 2`), middle (`count / 2`), and end
/// (`count - 2, count - 1`) of a component's boundary corpus.
const fn key_boundary_idx_6(k: usize, count: usize) -> usize {
    if count <= 6 {
        k
    } else {
        match k {
            0 => 0,
            1 => 1,
            2 => 2,
            3 => count / 2,
            4 => count - 2,
            _ => count - 1,
        }
    }
}

/// Maps slot `k` (`0..min(count, 4)`) into a representative boundary index in
/// `0..count` spanning `0`, `1`, `count / 2`, and `count - 1`.
const fn key_boundary_idx_4(k: usize, count: usize) -> usize {
    if count <= 4 {
        k
    } else {
        match k {
            0 => 0,
            1 => 1,
            2 => count / 2,
            _ => count - 1,
        }
    }
}

/// Maps slot `k` (`0..min(count, 3)`) into a representative boundary index in
/// `0..count` spanning `0`, `1`, and `count - 1`.
const fn key_boundary_idx_3(k: usize, count: usize) -> usize {
    if count <= 3 {
        k
    } else {
        match k {
            0 => 0,
            1 => 1,
            _ => count - 1,
        }
    }
}

impl<A: SampleInput> SampleInput for (A,) {
    const BOUNDARY_COUNT: usize = A::BOUNDARY_COUNT;

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        (A::sample_at(trial_idx, rng),)
    }
}

impl<A: SampleInput, B: SampleInput> SampleInput for (A, B) {
    // Up to 6x6 = 36 representative cross-pairs (covering `(0, 0)`, `(0, 1)`,
    // `(1, 0)`, `(0, MAX)`, `(1, MAX)`, `(MAX, MAX)`, etc.) followed by full
    // diagonal `(i, i)` pairs when either component has >6 boundaries.
    const BOUNDARY_COUNT: usize = {
        let ka = min_usize(A::BOUNDARY_COUNT, 6);
        let kb = min_usize(B::BOUNDARY_COUNT, 6);
        let cross = ka * kb;
        let max_ab = max_usize(A::BOUNDARY_COUNT, B::BOUNDARY_COUNT);
        let diag = if ka > 0 && kb > 0 && max_ab > 6 {
            max_ab
        } else {
            0
        };
        cross.saturating_add(diag)
    };

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        let ka = min_usize(A::BOUNDARY_COUNT, 6);
        let kb = min_usize(B::BOUNDARY_COUNT, 6);
        let cross = ka * kb;
        if trial_idx < cross && kb > 0 {
            let ia = key_boundary_idx_6(trial_idx / kb, A::BOUNDARY_COUNT);
            let ib = key_boundary_idx_6(trial_idx % kb, B::BOUNDARY_COUNT);
            (A::sample_at(ia, rng), B::sample_at(ib, rng))
        } else if trial_idx < Self::BOUNDARY_COUNT && A::BOUNDARY_COUNT > 0 && B::BOUNDARY_COUNT > 0
        {
            let d = trial_idx - cross;
            (
                A::sample_at(d % A::BOUNDARY_COUNT, rng),
                B::sample_at(d % B::BOUNDARY_COUNT, rng),
            )
        } else {
            (
                A::sample_at(trial_idx.max(A::BOUNDARY_COUNT), rng),
                B::sample_at(trial_idx.max(B::BOUNDARY_COUNT), rng),
            )
        }
    }
}

impl<A: SampleInput, B: SampleInput, C: SampleInput> SampleInput for (A, B, C) {
    // Up to 4x4x4 = 64 representative triples (deterministically covering all
    // ordering regions such as `lo == hi`, `val < lo`, `lo <= val <= hi`, and
    // `val > hi`) followed by full diagonal `(i, i, i)` triples.
    const BOUNDARY_COUNT: usize = {
        let ka = min_usize(A::BOUNDARY_COUNT, 4);
        let kb = min_usize(B::BOUNDARY_COUNT, 4);
        let kc = min_usize(C::BOUNDARY_COUNT, 4);
        let cross = ka * kb * kc;
        let max_abc = max_usize(
            A::BOUNDARY_COUNT,
            max_usize(B::BOUNDARY_COUNT, C::BOUNDARY_COUNT),
        );
        let diag = if ka > 0 && kb > 0 && kc > 0 && max_abc > 4 {
            max_abc
        } else {
            0
        };
        cross.saturating_add(diag)
    };

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        let ka = min_usize(A::BOUNDARY_COUNT, 4);
        let kb = min_usize(B::BOUNDARY_COUNT, 4);
        let kc = min_usize(C::BOUNDARY_COUNT, 4);
        let cross = ka * kb * kc;
        if trial_idx < cross && kb > 0 && kc > 0 {
            let bc = kb * kc;
            let ia = key_boundary_idx_4(trial_idx / bc, A::BOUNDARY_COUNT);
            let rem = trial_idx % bc;
            let ib = key_boundary_idx_4(rem / kc, B::BOUNDARY_COUNT);
            let ic = key_boundary_idx_4(rem % kc, C::BOUNDARY_COUNT);
            (
                A::sample_at(ia, rng),
                B::sample_at(ib, rng),
                C::sample_at(ic, rng),
            )
        } else if trial_idx < Self::BOUNDARY_COUNT
            && A::BOUNDARY_COUNT > 0
            && B::BOUNDARY_COUNT > 0
            && C::BOUNDARY_COUNT > 0
        {
            let d = trial_idx - cross;
            (
                A::sample_at(d % A::BOUNDARY_COUNT, rng),
                B::sample_at(d % B::BOUNDARY_COUNT, rng),
                C::sample_at(d % C::BOUNDARY_COUNT, rng),
            )
        } else {
            (
                A::sample_at(trial_idx.max(A::BOUNDARY_COUNT), rng),
                B::sample_at(trial_idx.max(B::BOUNDARY_COUNT), rng),
                C::sample_at(trial_idx.max(C::BOUNDARY_COUNT), rng),
            )
        }
    }
}

impl<A: SampleInput, B: SampleInput, C: SampleInput, D: SampleInput> SampleInput for (A, B, C, D) {
    // Up to 3^4 = 81 representative 4-tuples, followed by diagonal `(i, i, i, i)`
    // tuples and 4 axis-isolated midpoint (`BOUNDARY_COUNT / 2`, holding `MIN` for
    // every signed integer type) probes so 4-argument signed contracts hit `MIN`
    // off-diagonal deterministically on the boundary corpus.
    const BOUNDARY_COUNT: usize = {
        let ka = min_usize(A::BOUNDARY_COUNT, 3);
        let kb = min_usize(B::BOUNDARY_COUNT, 3);
        let kc = min_usize(C::BOUNDARY_COUNT, 3);
        let kd = min_usize(D::BOUNDARY_COUNT, 3);
        let cross = ka * kb * kc * kd;
        let max_abcd = max_usize(
            max_usize(A::BOUNDARY_COUNT, B::BOUNDARY_COUNT),
            max_usize(C::BOUNDARY_COUNT, D::BOUNDARY_COUNT),
        );
        let diag = if ka > 0 && kb > 0 && kc > 0 && kd > 0 && max_abcd > 3 {
            max_abcd
        } else {
            0
        };
        let mid_probes = if ka > 0 && kb > 0 && kc > 0 && kd > 0 && max_abcd > 3 {
            4
        } else {
            0
        };
        cross.saturating_add(diag).saturating_add(mid_probes)
    };

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        let ka = min_usize(A::BOUNDARY_COUNT, 3);
        let kb = min_usize(B::BOUNDARY_COUNT, 3);
        let kc = min_usize(C::BOUNDARY_COUNT, 3);
        let kd = min_usize(D::BOUNDARY_COUNT, 3);
        let cross = ka * kb * kc * kd;
        let max_abcd = max_usize(
            max_usize(A::BOUNDARY_COUNT, B::BOUNDARY_COUNT),
            max_usize(C::BOUNDARY_COUNT, D::BOUNDARY_COUNT),
        );
        let diag = if ka > 0 && kb > 0 && kc > 0 && kd > 0 && max_abcd > 3 {
            max_abcd
        } else {
            0
        };
        let diag_end = cross.saturating_add(diag);
        if trial_idx < cross && kb > 0 && kc > 0 && kd > 0 {
            let cd = kc * kd;
            let bcd = kb * cd;
            let ia = key_boundary_idx_3(trial_idx / bcd, A::BOUNDARY_COUNT);
            let rem1 = trial_idx % bcd;
            let ib = key_boundary_idx_3(rem1 / cd, B::BOUNDARY_COUNT);
            let rem2 = rem1 % cd;
            let ic = key_boundary_idx_3(rem2 / kd, C::BOUNDARY_COUNT);
            let id = key_boundary_idx_3(rem2 % kd, D::BOUNDARY_COUNT);
            (
                A::sample_at(ia, rng),
                B::sample_at(ib, rng),
                C::sample_at(ic, rng),
                D::sample_at(id, rng),
            )
        } else if trial_idx < diag_end
            && A::BOUNDARY_COUNT > 0
            && B::BOUNDARY_COUNT > 0
            && C::BOUNDARY_COUNT > 0
            && D::BOUNDARY_COUNT > 0
        {
            let d = trial_idx - cross;
            (
                A::sample_at(d % A::BOUNDARY_COUNT, rng),
                B::sample_at(d % B::BOUNDARY_COUNT, rng),
                C::sample_at(d % C::BOUNDARY_COUNT, rng),
                D::sample_at(d % D::BOUNDARY_COUNT, rng),
            )
        } else if trial_idx < Self::BOUNDARY_COUNT
            && A::BOUNDARY_COUNT > 0
            && B::BOUNDARY_COUNT > 0
            && C::BOUNDARY_COUNT > 0
            && D::BOUNDARY_COUNT > 0
        {
            let a0 = 0;
            let a1 = min_usize(1, A::BOUNDARY_COUNT - 1);
            let b1 = min_usize(1, B::BOUNDARY_COUNT - 1);
            let c0 = 0;
            let d_last = D::BOUNDARY_COUNT - 1;
            let (ia, ib, ic, id) = match trial_idx - diag_end {
                0 => (A::BOUNDARY_COUNT / 2, b1, c0, d_last),
                1 => (a0, B::BOUNDARY_COUNT / 2, c0, d_last),
                2 => (a0, b1, C::BOUNDARY_COUNT / 2, d_last),
                _ => (a1, b1, c0, D::BOUNDARY_COUNT / 2),
            };
            (
                A::sample_at(ia, rng),
                B::sample_at(ib, rng),
                C::sample_at(ic, rng),
                D::sample_at(id, rng),
            )
        } else {
            (
                A::sample_at(trial_idx.max(A::BOUNDARY_COUNT), rng),
                B::sample_at(trial_idx.max(B::BOUNDARY_COUNT), rng),
                C::sample_at(trial_idx.max(C::BOUNDARY_COUNT), rng),
                D::sample_at(trial_idx.max(D::BOUNDARY_COUNT), rng),
            )
        }
    }
}

impl<T: SampleInput, const N: usize> SampleInput for [T; N] {
    const BOUNDARY_COUNT: usize = if N == 0 {
        1
    } else if N >= 2 && T::BOUNDARY_COUNT >= 2 {
        T::BOUNDARY_COUNT.saturating_add(4)
    } else {
        T::BOUNDARY_COUNT
    };

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        if N == 0 {
            return array::from_fn(|_| T::sample_at(trial_idx, rng));
        }
        if trial_idx < T::BOUNDARY_COUNT {
            // All-equal boundary array `[b_i; N]` without requiring `T: Clone`.
            let snapshot = *rng;
            let _ = rng.next_u64();
            array::from_fn(|_| {
                let mut local = snapshot;
                T::sample_at(trial_idx, &mut local)
            })
        } else if N >= 2 && T::BOUNDARY_COUNT >= 2 && trial_idx < Self::BOUNDARY_COUNT {
            let extra = trial_idx - T::BOUNDARY_COUNT;
            let last_b = T::BOUNDARY_COUNT - 1;
            match extra {
                // Ascending cycle of boundaries.
                0 => array::from_fn(|i| T::sample_at(i % T::BOUNDARY_COUNT, rng)),
                // Descending cycle of boundaries.
                1 => array::from_fn(|i| T::sample_at(last_b - (i % T::BOUNDARY_COUNT), rng)),
                // Single-element spike at index 0.
                2 => array::from_fn(|i| T::sample_at(if i == 0 { 1 } else { 0 }, rng)),
                // Single-element extremal spike at index `N - 1`.
                _ => array::from_fn(|i| T::sample_at(if i == N - 1 { last_b } else { 0 }, rng)),
            }
        } else {
            let prng_idx = trial_idx.max(T::BOUNDARY_COUNT);
            array::from_fn(|_| T::sample_at(prng_idx, rng))
        }
    }
}

/// Output perturbation generator for dynamic postcondition-dichotomy testing.
pub trait ReturnMutants: Sized {
    /// True iff the type has at most one inhabitant (e.g., `()`), where
    /// postcondition dichotomy on the return value alone is impossible.
    const IS_SUBSINGLETON: bool = false;

    /// Emit candidate perturbed outputs to `emit`. Implementations should emit
    /// diverse boundary and local perturbations (`+1`, `-1`, `^1`, `!x`, `0`,
    /// `1`, `MIN`, `MAX`, variant flips, and component perturbations).
    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, emit: F);
}

impl ReturnMutants for () {
    const IS_SUBSINGLETON: bool = true;

    fn visit_mutants<F: FnMut(Self)>(&self, _rng: &mut SplitMix64, _emit: F) {}
}

impl ReturnMutants for bool {
    const IS_SUBSINGLETON: bool = false;

    fn visit_mutants<F: FnMut(Self)>(&self, _rng: &mut SplitMix64, mut emit: F) {
        emit(!*self);
    }
}

macro_rules! impl_return_mutants_unsigned {
    ($ty:ty, $full_draw:expr) => {
        impl ReturnMutants for $ty {
            const IS_SUBSINGLETON: bool = false;

            fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
                let v = *self;
                // Stratified small PRNG draw + full-width PRNG draw.
                let r1: $ty = $full_draw(rng);
                let r2: $ty = $full_draw(rng);
                let candidates: [$ty; 14] = [
                    v.wrapping_add(1),
                    v.wrapping_sub(1),
                    v ^ 1,
                    !v,
                    0,
                    1,
                    <$ty>::MAX,
                    <$ty>::MAX.wrapping_sub(1),
                    v.wrapping_add(2),
                    v.wrapping_sub(2),
                    v >> 1,
                    v.wrapping_mul(2),
                    r1 & (0x3F as $ty),
                    r2,
                ];
                let mut seen = [v; 15];
                let mut seen_len = 1usize;
                for cand in candidates {
                    let mut dup = false;
                    let mut i = 0usize;
                    while i < seen_len {
                        if seen[i] == cand {
                            dup = true;
                            break;
                        }
                        i += 1;
                    }
                    if !dup {
                        seen[seen_len] = cand;
                        seen_len += 1;
                        emit(cand);
                    }
                }
            }
        }
    };
}

impl_return_mutants_unsigned!(u8, |rng: &mut SplitMix64| rng.next_u64() as u8);
impl_return_mutants_unsigned!(u16, |rng: &mut SplitMix64| rng.next_u64() as u16);
impl_return_mutants_unsigned!(u32, |rng: &mut SplitMix64| rng.next_u32());
impl_return_mutants_unsigned!(u64, |rng: &mut SplitMix64| rng.next_u64());
impl_return_mutants_unsigned!(u128, |rng: &mut SplitMix64| rng.next_u128());
impl_return_mutants_unsigned!(usize, |rng: &mut SplitMix64| rng.next_usize());

macro_rules! impl_return_mutants_signed {
    ($ty:ty, $full_draw:expr) => {
        impl ReturnMutants for $ty {
            const IS_SUBSINGLETON: bool = false;

            fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
                let v = *self;
                let r1 = rng.next_u64();
                let r2: $ty = $full_draw(rng);
                let candidates: [$ty; 15] = [
                    v.wrapping_add(1),
                    v.wrapping_sub(1),
                    v ^ 1,
                    !v,
                    v.wrapping_neg(),
                    0,
                    1,
                    -1,
                    <$ty>::MIN,
                    <$ty>::MAX,
                    <$ty>::MAX.wrapping_sub(1),
                    v >> 1,
                    v.wrapping_mul(2),
                    ((r1 & 0x7F) as $ty).wrapping_sub(64),
                    r2,
                ];
                let mut seen = [v; 16];
                let mut seen_len = 1usize;
                for cand in candidates {
                    let mut dup = false;
                    let mut i = 0usize;
                    while i < seen_len {
                        if seen[i] == cand {
                            dup = true;
                            break;
                        }
                        i += 1;
                    }
                    if !dup {
                        seen[seen_len] = cand;
                        seen_len += 1;
                        emit(cand);
                    }
                }
            }
        }
    };
}

impl_return_mutants_signed!(i8, |rng: &mut SplitMix64| rng.next_u64() as i8);
impl_return_mutants_signed!(i16, |rng: &mut SplitMix64| rng.next_u64() as i16);
impl_return_mutants_signed!(i32, |rng: &mut SplitMix64| rng.next_u32() as i32);
impl_return_mutants_signed!(i64, |rng: &mut SplitMix64| rng.next_u64() as i64);
impl_return_mutants_signed!(i128, |rng: &mut SplitMix64| rng.next_u128() as i128);
impl_return_mutants_signed!(isize, |rng: &mut SplitMix64| rng.next_usize() as isize);

impl<T: ReturnMutants> ReturnMutants for Wrapping<T> {
    const IS_SUBSINGLETON: bool = T::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        self.0.visit_mutants(rng, |m| emit(Wrapping(m)));
    }
}

impl<T: SampleInput + ReturnMutants> ReturnMutants for Option<T> {
    // Because `T: SampleInput` is inhabited, `Option<T>` always has at least
    // two distinct inhabitants (`None` and `Some(...)`), even when `T = ()`.
    const IS_SUBSINGLETON: bool = false;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        match self {
            Some(v) => {
                let mut emitted_none = false;
                if !T::IS_SUBSINGLETON {
                    v.visit_mutants(rng, |m| {
                        emit(Some(m));
                        if !emitted_none {
                            emitted_none = true;
                            // Emit `None` right after the first payload mutant so
                            // small budgets (`>= 2`) test both axes and mutant
                            // chains advance monotonically within `Some(...)`
                            // instead of resetting through `None`. A budget of 1
                            // tests the `Some` payload first; if that mutant
                            // survives, Stage D3 goes on to this `None` flip,
                            // because a kill-free hit is never truncated.
                            emit(None);
                        }
                    });
                }
                if !emitted_none {
                    emit(None);
                }
            }
            None => {
                emit(Some(T::sample_at(0, rng)));
                if !T::IS_SUBSINGLETON {
                    if T::BOUNDARY_COUNT >= 2 {
                        emit(Some(T::sample_at(1, rng)));
                    }
                    if T::BOUNDARY_COUNT >= 3 {
                        emit(Some(T::sample_at(2, rng)));
                    }
                    if T::BOUNDARY_COUNT >= 6 {
                        // Index `BOUNDARY_COUNT / 2` holds `MIN` for every signed
                        // integer type (`i8..=isize`) and is strictly distinct from
                        // `0`, `1`, `2`, and `BOUNDARY_COUNT - 1` whenever
                        // `BOUNDARY_COUNT >= 6`.
                        emit(Some(T::sample_at(T::BOUNDARY_COUNT / 2, rng)));
                    }
                    if T::BOUNDARY_COUNT >= 4 {
                        emit(Some(T::sample_at(T::BOUNDARY_COUNT - 1, rng)));
                    }
                    if T::BOUNDARY_COUNT != 2 {
                        emit(Some(T::sample_at(T::BOUNDARY_COUNT, rng)));
                        emit(Some(T::sample_at(T::BOUNDARY_COUNT.saturating_add(1), rng)));
                    }
                }
            }
        }
    }
}

/// Emits representative opposite-variant payloads of type `U` covering `0`,
/// `1`, the signed-`MIN` midpoint (`BOUNDARY_COUNT / 2`), `BOUNDARY_COUNT - 1`,
/// and one PRNG draw, wrapped via `wrap`.
fn emit_variant_flip_samples<U, R, W, F>(rng: &mut SplitMix64, mut wrap: W, emit: &mut F)
where
    U: SampleInput + ReturnMutants,
    W: FnMut(U) -> R,
    F: FnMut(R),
{
    emit(wrap(U::sample_at(0, rng)));
    if !U::IS_SUBSINGLETON {
        if U::BOUNDARY_COUNT >= 2 {
            emit(wrap(U::sample_at(1, rng)));
        }
        if U::BOUNDARY_COUNT >= 4 {
            // Strictly distinct from `0`, `1`, and `BOUNDARY_COUNT - 1`; covers
            // `MIN` for every signed integer type (`i8..=isize`).
            emit(wrap(U::sample_at(U::BOUNDARY_COUNT / 2, rng)));
        }
        if U::BOUNDARY_COUNT >= 3 {
            emit(wrap(U::sample_at(U::BOUNDARY_COUNT - 1, rng)));
        }
        if U::BOUNDARY_COUNT != 2 {
            emit(wrap(U::sample_at(U::BOUNDARY_COUNT, rng)));
        }
    }
}

impl<T: SampleInput + ReturnMutants, E: SampleInput + ReturnMutants> ReturnMutants
    for Result<T, E>
{
    // Because `T` and `E` are inhabited via `SampleInput`, `Result<T, E>`
    // always has both `Ok` and `Err` inhabitants.
    const IS_SUBSINGLETON: bool = false;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        let mut flip_rng = rng.fork();
        match self {
            Ok(v) => {
                let mut emitted_flips = false;
                if !T::IS_SUBSINGLETON {
                    v.visit_mutants(rng, |m| {
                        emit(Ok(m));
                        if !emitted_flips {
                            emitted_flips = true;
                            // Emit opposite-variant flips right after the first payload
                            // mutant so small budgets test both axes without duplicating
                            // subsingleton payloads and mutant chains advance within `Ok`.
                            emit_variant_flip_samples(&mut flip_rng, Err, &mut emit);
                        }
                    });
                }
                if !emitted_flips {
                    emit_variant_flip_samples(&mut flip_rng, Err, &mut emit);
                }
            }
            Err(e) => {
                let mut emitted_flips = false;
                if !E::IS_SUBSINGLETON {
                    e.visit_mutants(rng, |m| {
                        emit(Err(m));
                        if !emitted_flips {
                            emitted_flips = true;
                            emit_variant_flip_samples(&mut flip_rng, Ok, &mut emit);
                        }
                    });
                }
                if !emitted_flips {
                    emit_variant_flip_samples(&mut flip_rng, Ok, &mut emit);
                }
            }
        }
    }
}

impl<A: ReturnMutants> ReturnMutants for (A,) {
    const IS_SUBSINGLETON: bool = A::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        self.0.visit_mutants(rng, |a| emit((a,)));
    }
}

/// Collects up to `CAP` mutants from `value` into a fixed-size stack buffer
/// without heap allocation, returning `(buffer, count)`.
fn collect_axis_mutants<T: ReturnMutants, const CAP: usize>(
    value: &T,
    rng: &mut SplitMix64,
) -> ([Option<T>; CAP], usize) {
    let mut buf: [Option<T>; CAP] = array::from_fn(|_| None);
    let mut len = 0usize;
    if !T::IS_SUBSINGLETON {
        value.visit_mutants(rng, |m| {
            if len < CAP {
                buf[len] = Some(m);
                len += 1;
            }
        });
    }
    (buf, len)
}

impl<A: ReturnMutants + Clone, B: ReturnMutants + Clone> ReturnMutants for (A, B) {
    const IS_SUBSINGLETON: bool = A::IS_SUBSINGLETON && B::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        if Self::IS_SUBSINGLETON {
            return;
        }
        if B::IS_SUBSINGLETON {
            let mut emitted = 0usize;
            self.0.visit_mutants(rng, |a_mut| {
                if emitted < 16 {
                    emit((a_mut, self.1.clone()));
                    emitted += 1;
                }
            });
            return;
        }
        if A::IS_SUBSINGLETON {
            let mut emitted = 0usize;
            self.1.visit_mutants(rng, |b_mut| {
                if emitted < 16 {
                    emit((self.0.clone(), b_mut));
                    emitted += 1;
                }
            });
            return;
        }

        const CAP: usize = 5;
        let (a_muts, a_len) = collect_axis_mutants::<A, CAP>(&self.0, rng);
        let (b_muts, _) = collect_axis_mutants::<B, CAP>(&self.1, rng);

        // Interleave axes round-robin so tight `max_mutants_per_hit` budgets
        // (even `max_mutants_per_hit == 2`) perturb every active component.
        for k in 0..CAP {
            if let Some(a_mut) = a_muts[k].as_ref() {
                emit((a_mut.clone(), self.1.clone()));
            }
            if let Some(b_mut) = b_muts[k].as_ref() {
                emit((self.0.clone(), b_mut.clone()));
            }
            // Emit joint two-axis perturbations early (rounds 0..3) while
            // staying within the default 16-mutant budget (`5 + 5 + 3 = 13`).
            if k < 3
                && a_len > 0
                && let Some(b_mut) = b_muts[k].as_ref()
            {
                let a_idx = if k == 1 && a_len > 1 { 1 } else { 0 };
                if let Some(a_mut) = a_muts[a_idx].as_ref() {
                    emit((a_mut.clone(), b_mut.clone()));
                }
            }
        }
    }
}

impl<A: ReturnMutants + Clone, B: ReturnMutants + Clone, C: ReturnMutants + Clone> ReturnMutants
    for (A, B, C)
{
    const IS_SUBSINGLETON: bool = A::IS_SUBSINGLETON && B::IS_SUBSINGLETON && C::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        if Self::IS_SUBSINGLETON {
            return;
        }
        let active_axes = (!A::IS_SUBSINGLETON as usize)
            + (!B::IS_SUBSINGLETON as usize)
            + (!C::IS_SUBSINGLETON as usize);
        if active_axes == 1 {
            let mut emitted = 0usize;
            if !A::IS_SUBSINGLETON {
                self.0.visit_mutants(rng, |a_mut| {
                    if emitted < 16 {
                        emit((a_mut, self.1.clone(), self.2.clone()));
                        emitted += 1;
                    }
                });
            } else if !B::IS_SUBSINGLETON {
                self.1.visit_mutants(rng, |b_mut| {
                    if emitted < 16 {
                        emit((self.0.clone(), b_mut, self.2.clone()));
                        emitted += 1;
                    }
                });
            } else {
                self.2.visit_mutants(rng, |c_mut| {
                    if emitted < 16 {
                        emit((self.0.clone(), self.1.clone(), c_mut));
                        emitted += 1;
                    }
                });
            }
            return;
        }

        const CAP: usize = 4;
        let (a_muts, _) = collect_axis_mutants::<A, CAP>(&self.0, rng);
        let (b_muts, _) = collect_axis_mutants::<B, CAP>(&self.1, rng);
        let (c_muts, _) = collect_axis_mutants::<C, CAP>(&self.2, rng);

        // Interleave axes round-robin so tight budgets (`max_mutants_per_hit >= 3`)
        // perturb every active component on every hit.
        for k in 0..CAP {
            if let Some(a_mut) = a_muts[k].as_ref() {
                emit((a_mut.clone(), self.1.clone(), self.2.clone()));
            }
            if let Some(b_mut) = b_muts[k].as_ref() {
                emit((self.0.clone(), b_mut.clone(), self.2.clone()));
            }
            if let Some(c_mut) = c_muts[k].as_ref() {
                emit((self.0.clone(), self.1.clone(), c_mut.clone()));
            }
            if k == 0 {
                if let (Some(a0), Some(b0)) = (a_muts[0].as_ref(), b_muts[0].as_ref()) {
                    emit((a0.clone(), b0.clone(), self.2.clone()));
                }
                if let (Some(b0), Some(c0)) = (b_muts[0].as_ref(), c_muts[0].as_ref()) {
                    emit((self.0.clone(), b0.clone(), c0.clone()));
                }
                if let (Some(a0), Some(c0)) = (a_muts[0].as_ref(), c_muts[0].as_ref()) {
                    if let Some(b0) = b_muts[0].as_ref() {
                        emit((a0.clone(), b0.clone(), c0.clone()));
                    } else {
                        emit((a0.clone(), self.1.clone(), c0.clone()));
                    }
                }
            }
        }
    }
}

impl<
    A: ReturnMutants + Clone,
    B: ReturnMutants + Clone,
    C: ReturnMutants + Clone,
    D: ReturnMutants + Clone,
> ReturnMutants for (A, B, C, D)
{
    const IS_SUBSINGLETON: bool =
        A::IS_SUBSINGLETON && B::IS_SUBSINGLETON && C::IS_SUBSINGLETON && D::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        if Self::IS_SUBSINGLETON {
            return;
        }
        let active_axes = (!A::IS_SUBSINGLETON as usize)
            + (!B::IS_SUBSINGLETON as usize)
            + (!C::IS_SUBSINGLETON as usize)
            + (!D::IS_SUBSINGLETON as usize);
        if active_axes == 1 {
            let mut emitted = 0usize;
            if !A::IS_SUBSINGLETON {
                self.0.visit_mutants(rng, |a_mut| {
                    if emitted < 16 {
                        emit((a_mut, self.1.clone(), self.2.clone(), self.3.clone()));
                        emitted += 1;
                    }
                });
            } else if !B::IS_SUBSINGLETON {
                self.1.visit_mutants(rng, |b_mut| {
                    if emitted < 16 {
                        emit((self.0.clone(), b_mut, self.2.clone(), self.3.clone()));
                        emitted += 1;
                    }
                });
            } else if !C::IS_SUBSINGLETON {
                self.2.visit_mutants(rng, |c_mut| {
                    if emitted < 16 {
                        emit((self.0.clone(), self.1.clone(), c_mut, self.3.clone()));
                        emitted += 1;
                    }
                });
            } else {
                self.3.visit_mutants(rng, |d_mut| {
                    if emitted < 16 {
                        emit((self.0.clone(), self.1.clone(), self.2.clone(), d_mut));
                        emitted += 1;
                    }
                });
            }
            return;
        }

        const CAP: usize = 3;
        let (a_muts, _) = collect_axis_mutants::<A, CAP>(&self.0, rng);
        let (b_muts, _) = collect_axis_mutants::<B, CAP>(&self.1, rng);
        let (c_muts, _) = collect_axis_mutants::<C, CAP>(&self.2, rng);
        let (d_muts, _) = collect_axis_mutants::<D, CAP>(&self.3, rng);

        // Interleave axes round-robin so tight budgets (`max_mutants_per_hit >= 4`)
        // perturb every active component on every hit.
        for k in 0..CAP {
            if let Some(a_mut) = a_muts[k].as_ref() {
                emit((
                    a_mut.clone(),
                    self.1.clone(),
                    self.2.clone(),
                    self.3.clone(),
                ));
            }
            if let Some(b_mut) = b_muts[k].as_ref() {
                emit((
                    self.0.clone(),
                    b_mut.clone(),
                    self.2.clone(),
                    self.3.clone(),
                ));
            }
            if let Some(c_mut) = c_muts[k].as_ref() {
                emit((
                    self.0.clone(),
                    self.1.clone(),
                    c_mut.clone(),
                    self.3.clone(),
                ));
            }
            if let Some(d_mut) = d_muts[k].as_ref() {
                emit((
                    self.0.clone(),
                    self.1.clone(),
                    self.2.clone(),
                    d_mut.clone(),
                ));
            }
            if k == 0 {
                let a0 = a_muts[0].as_ref();
                let b0 = b_muts[0].as_ref();
                let c0 = c_muts[0].as_ref();
                let d0 = d_muts[0].as_ref();
                if let (Some(a0), Some(b0)) = (a0, b0) {
                    emit((a0.clone(), b0.clone(), self.2.clone(), self.3.clone()));
                }
                if let (Some(b0), Some(c0)) = (b0, c0) {
                    emit((self.0.clone(), b0.clone(), c0.clone(), self.3.clone()));
                }
                if let (Some(c0), Some(d0)) = (c0, d0) {
                    emit((self.0.clone(), self.1.clone(), c0.clone(), d0.clone()));
                }
                // Jointly perturb every axis that produced a mutant, keeping the
                // original component on an axis that produced none (a
                // subsingleton field such as `()`). A postcondition that is a
                // disjunction over two components (`r.0 == a || r.2 == b`) is
                // only ever falsified by perturbing both at once; requiring all
                // four axes to be active would leave such a genuine contract
                // with no killable mutant whenever the tuple carries a
                // subsingleton component. The joint is skipped when it would
                // repeat the single adjacent pair emitted just above.
                let joint_axes = usize::from(a0.is_some())
                    + usize::from(b0.is_some())
                    + usize::from(c0.is_some())
                    + usize::from(d0.is_some());
                let repeats_adjacent_pair = joint_axes == 2
                    && ((a0.is_some() && b0.is_some())
                        || (b0.is_some() && c0.is_some())
                        || (c0.is_some() && d0.is_some()));
                if joint_axes >= 2 && !repeats_adjacent_pair {
                    emit((
                        a0.cloned().unwrap_or_else(|| self.0.clone()),
                        b0.cloned().unwrap_or_else(|| self.1.clone()),
                        c0.cloned().unwrap_or_else(|| self.2.clone()),
                        d0.cloned().unwrap_or_else(|| self.3.clone()),
                    ));
                }
            }
        }
    }
}

impl<T: ReturnMutants + Clone, const N: usize> ReturnMutants for [T; N] {
    const IS_SUBSINGLETON: bool = (N == 0) || T::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        if Self::IS_SUBSINGLETON {
            return;
        }

        // Place one PRNG-selected roving index first, followed by the fixed
        // representative positions `0`, `N / 2` (when `N >= 3`), and `N - 1`
        // (when `N >= 2`), deduplicated. Interleaving rounds across these
        // positions guarantees that even tight budgets (`max_mutants_per_hit <= 4`)
        // probe every selected position on every hit while roving covers all
        // interior indices across hits. `N >= 1` here because `[T; 0]` is a
        // subsingleton.
        let last = N - 1;
        let mid = N / 2;
        let roving = (rng.next_u64() % (N as u64)) as usize;
        let indices: [Option<usize>; 4] = [
            Some(roving),
            if roving != 0 { Some(0) } else { None },
            if N >= 3 && mid != roving {
                Some(mid)
            } else {
                None
            },
            if N >= 2 && last != roving {
                Some(last)
            } else {
                None
            },
        ];
        let active_positions = indices.iter().filter(|idx| idx.is_some()).count();
        if active_positions <= 1 {
            let mut emitted = 0usize;
            self[0].visit_mutants(rng, |elem_mut| {
                if emitted < 16 {
                    let mut mutated = self.clone();
                    mutated[0] = elem_mut;
                    emit(mutated);
                    emitted += 1;
                }
            });
            return;
        }

        // Leave room for the structural mutants below within the default
        // `max_mutants_per_hit` budget of 16.
        let per_pos_cap = match active_positions {
            2 | 3 => 4,
            _ => 3,
        };

        let mut pos_muts: [[Option<T>; 4]; 4] = array::from_fn(|_| array::from_fn(|_| None));
        let mut front_mut: Option<T> = None;
        let mut back_mut: Option<T> = None;
        for (slot, maybe_pos) in indices.iter().enumerate() {
            let Some(pos) = *maybe_pos else {
                continue;
            };
            let mut collected = 0usize;
            self[pos].visit_mutants(rng, |elem_mut| {
                if collected < per_pos_cap {
                    if pos == 0 && front_mut.is_none() {
                        front_mut = Some(elem_mut.clone());
                    }
                    if pos == last && back_mut.is_none() {
                        back_mut = Some(elem_mut.clone());
                    }
                    pos_muts[slot][collected] = Some(elem_mut);
                    collected += 1;
                }
            });
        }

        // Interleave rounds across active positions, emitting distinct
        // structural permutations after round 0 so tight budgets see both
        // single-element and permutation mutants without duplicate work.
        for round in 0..per_pos_cap {
            for (slot, maybe_pos) in indices.iter().enumerate() {
                let Some(pos) = *maybe_pos else {
                    continue;
                };
                if let Some(elem_mut) = pos_muts[slot][round].as_ref() {
                    let mut mutated = self.clone();
                    mutated[pos] = elem_mut.clone();
                    emit(mutated);
                }
            }
            if round == 0 && N >= 2 {
                // For `N == 2`, `swap(0, 1)`, `reverse()`, and `rotate_left(1)`
                // coincide; for `N == 3`, `swap(0, 2)` and `reverse()` coincide.
                let mut swapped = self.clone();
                swapped.swap(0, last);
                emit(swapped);

                if N >= 3 {
                    let mut rotated = self.clone();
                    rotated.rotate_left(1);
                    emit(rotated);
                }

                if N >= 4 {
                    let mut reversed = self.clone();
                    reversed.reverse();
                    emit(reversed);
                }

                // Perturb both ends using each end's own first mutant so `both_ends`
                // never degenerates to a single-element mutant when `m0 == self[last]`.
                if let (Some(m0), Some(mlast)) = (front_mut.as_ref(), back_mut.as_ref()) {
                    let mut both_ends = self.clone();
                    both_ends[0] = m0.clone();
                    both_ends[last] = mlast.clone();
                    emit(both_ends);
                }
            }
        }
    }
}

/// Optional syntactic hint supplied by a macro or static analyzer to refine
/// vacuity diagnosis when all output mutants survive.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SyntacticBindingHint {
    /// The postcondition binder does not syntactically reference the return value.
    ReturnUnused,
    /// The postcondition expression is syntactically tautological (e.g. `true`).
    SyntacticallyTautological,
}

/// Domain over which a vacuity-classification probe may evaluate a
/// postcondition once every tested mutant has survived.
///
/// Stages D2 and D3 always stay inside the precondition. The classification
/// probe gathers further evidence about how `post` behaves, and this policy
/// decides whether that evidence may come from inputs that violate `pre`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ProbeDomain {
    /// Evaluate `post` only on inputs satisfying `pre`.
    ///
    /// This is always safe and is the default: a postcondition is only
    /// required to be total, terminating, and free of undefined behavior on
    /// inputs its precondition admits.
    #[default]
    PreconditionOnly,
    /// Additionally evaluate `post` on sampled inputs that violate `pre`.
    ///
    /// Selecting this domain asserts that `post` neither panics, diverges, nor
    /// exhibits undefined behavior on any sampled input, admissible or not. It
    /// lets the probe distinguish a postcondition that is `true` everywhere
    /// ([`VacuityClass::TrivialPostcondition`]) from one that is input-only
    /// ([`VacuityClass::UnboundReturnOutput`]) or that binds the output only
    /// outside the precondition ([`VacuityClass::SurvivedAllMutants`]). Through
    /// the fallible entry points, a trap on a precondition-violating input is
    /// tolerated and carries no evidence.
    Unconstrained,
}

/// Configuration parameters controlling dynamic contract checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpecCheckConfig {
    /// Deterministic PRNG seed for [`SplitMix64`].
    pub seed: u64,
    /// Total number of input trials to execute (must be `>= 1`).
    ///
    /// Also bounds failure classification: once every tested mutant survived,
    /// the vacuity-classification probe samples at most
    /// `min(max_trials, MAX_PROBE_INPUTS)` further inputs (see
    /// [`MAX_PROBE_INPUTS`]). A budget below the input type's
    /// [`SampleInput::BOUNDARY_COUNT`] therefore classifies from a truncated
    /// boundary corpus, exactly as it checks from one.
    pub max_trials: usize,
    /// Minimum number of precondition-admissible trials required (must be `>= 1`).
    pub min_precondition_hits: usize,
    /// Number of distinct output mutants evaluated per precondition hit (per
    /// output axis in stateful checks).
    ///
    /// The budget is soft for a kill-free hit: a hit (or axis) whose budgeted
    /// mutants all survived keeps testing further distinct mutants, at most
    /// [`KILL_FREE_OVERSCAN`] beyond the budget, until its first kill. A tight
    /// budget therefore never reports a contract that rejects a first-order
    /// mutant as [`VacuityClass::SurvivedAllMutants`], and never makes
    /// [`SpecCheckStats::is_pointwise_strong`] under-report.
    pub max_mutants_per_hit: usize,
    /// Optional syntactic hint refining `mutants_killed == 0` diagnostics.
    pub syntactic_hint: Option<SyntacticBindingHint>,
    /// For [`check_stateful_contract`], require both non-subsingleton axes
    /// (mutated post-state `S` and return value `R`) to independently kill at
    /// least one mutant.
    pub require_both_state_and_return_kills: bool,
    /// Inputs on which the vacuity-classification probe may evaluate `post`.
    pub probe_domain: ProbeDomain,
}

impl Default for SpecCheckConfig {
    fn default() -> Self {
        Self {
            seed: SplitMix64::DEFAULT_SEED,
            max_trials: 256,
            min_precondition_hits: 1,
            max_mutants_per_hit: 16,
            syntactic_hint: None,
            require_both_state_and_return_kills: true,
            probe_domain: ProbeDomain::PreconditionOnly,
        }
    }
}

impl SpecCheckConfig {
    /// Sets the PRNG seed.
    pub const fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Sets the maximum number of input trials.
    pub const fn with_max_trials(mut self, max_trials: usize) -> Self {
        self.max_trials = max_trials;
        self
    }

    /// Sets the minimum required number of precondition-admissible hits.
    pub const fn with_min_precondition_hits(mut self, min_precondition_hits: usize) -> Self {
        self.min_precondition_hits = min_precondition_hits;
        self
    }

    /// Sets the maximum number of distinct mutants tested per precondition hit.
    pub const fn with_max_mutants_per_hit(mut self, max_mutants_per_hit: usize) -> Self {
        self.max_mutants_per_hit = max_mutants_per_hit;
        self
    }

    /// Attaches (or clears) a [`SyntacticBindingHint`].
    pub fn with_syntactic_hint(mut self, hint: impl Into<Option<SyntacticBindingHint>>) -> Self {
        self.syntactic_hint = hint.into();
        self
    }

    /// Sets whether stateful contract checks require killing mutants along both
    /// the post-state and return-value axes independently.
    pub const fn with_require_both_state_and_return_kills(mut self, require_both: bool) -> Self {
        self.require_both_state_and_return_kills = require_both;
        self
    }

    /// Sets the [`ProbeDomain`] of the vacuity-classification probe.
    pub const fn with_probe_domain(mut self, probe_domain: ProbeDomain) -> Self {
        self.probe_domain = probe_domain;
        self
    }
}

/// Identifies which phase trapped during a fallible contract check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TrapKind {
    /// Precondition evaluation panicked or returned `Err(())`.
    PreconditionPanicked,
    /// Target function body panicked or returned `Err(())`.
    BodyPanicked,
    /// Postcondition evaluation on the actual return value panicked or returned `Err(())`.
    PostconditionPanicked,
}

/// Alias for [`TrapKind`] naming an execution trap phase.
pub type ExecutionTrap = TrapKind;

/// Concrete conformance or configuration violation detail.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ViolationKind {
    /// Live postcondition returned `false` on the actual return value at `trial_idx`.
    PostconditionFalse { trial_idx: usize },
    /// Live execution trapped during `trap` at `trial_idx`.
    ExecutionTrapped { trial_idx: usize, trap: TrapKind },
    /// Checker configuration had a zero trial/hit/mutant budget or an
    /// unsatisfiable `min_precondition_hits > max_trials` requirement
    /// (fail-closed).
    DegenerateConfig,
}

/// Detailed diagnostic payload carried by [`SpecCheckFailure`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureDetail {
    /// Fewer than `required` inputs satisfied the precondition.
    InsufficientPreconditionHits { required: usize, observed: usize },
    /// Live conformance violation or fail-closed degenerate configuration.
    Violation(ViolationKind),
    /// Zero distinct mutants were tested (e.g. an empty custom mutant bank,
    /// every custom mutant equaled the actual output however often the bank
    /// repeats it, or a custom [`ReturnMutants`] implementation emitted no
    /// distinct mutant).
    NoDistinctMutantsTested,
    /// All tested mutants satisfied the postcondition; includes probe telemetry.
    AllMutantsSurvived {
        /// Number of inputs on which the classification probe evaluated `post`:
        /// the live anchor input plus at most
        /// `min(max_trials, MAX_PROBE_INPUTS)` sampled inputs (see
        /// [`MAX_PROBE_INPUTS`]). `0` when a [`SyntacticBindingHint`] decided
        /// the class without probing.
        probed_inputs: usize,
        /// Number of those inputs that violated `pre`. Always `0` under
        /// [`ProbeDomain::PreconditionOnly`].
        out_of_precondition_probes: usize,
        /// Number of sampled probe inputs withheld from `post` because they
        /// violated `pre` (or `pre` trapped on them). A nonzero count under
        /// [`ProbeDomain::PreconditionOnly`] means the verdict describes `post`
        /// relative to the precondition only.
        skipped_out_of_precondition: usize,
        /// Whether `post` rejected any probed `(input, output)` pair.
        saw_any_false: bool,
        /// Whether `post` both accepted and rejected outputs for one input.
        saw_output_sensitivity: bool,
    },
    /// In a stateful contract check, at least one required non-subsingleton
    /// output axis (return value or mutated post-state) failed to kill any mutant.
    StatefulAxisUnconstrained {
        return_mutants_tested: usize,
        return_mutants_killed: usize,
        state_mutants_tested: usize,
        state_mutants_killed: usize,
    },
}

/// Execution statistics collected during a dynamic contract check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct SpecCheckStats {
    /// Number of input trials sampled.
    pub trials_run: usize,
    /// Number of trials satisfying the precondition.
    pub precondition_hits: usize,
    /// Number of precondition-admissible trials on which at least one output
    /// (or mutated post-state) mutant was killed.
    ///
    /// Satisfies `hits_with_kill <= precondition_hits`,
    /// `hits_with_kill <= mutants_killed`, and
    /// `(hits_with_kill > 0) == (mutants_killed > 0)`.
    pub hits_with_kill: usize,
    /// Total number of distinct output/state mutants evaluated.
    pub mutants_tested: usize,
    /// Total number of mutants rejected (`post == false` or `post` trapped).
    pub mutants_killed: usize,
    /// Number of killed mutants rejected by a trapping postcondition
    /// (`Err(())` through a fallible entry point); a subset of
    /// `mutants_killed`.
    pub mutants_trapped: usize,
    /// True iff the return type `R` is a subsingleton (`R::IS_SUBSINGLETON`).
    pub subsingleton_return: bool,
}

impl SpecCheckStats {
    /// Number of precondition-admissible trials on which zero mutants were
    /// killed (for example, an unconstrained branch of a multi-branch contract,
    /// or a subsingleton return type).
    pub const fn hits_without_kill(&self) -> usize {
        self.precondition_hits.saturating_sub(self.hits_with_kill)
    }

    /// Returns `true` iff at least one precondition-admissible trial ran and
    /// every such trial killed at least one mutant (the dynamic counterpart of
    /// pointwise postcondition dichotomy).
    pub const fn is_pointwise_strong(&self) -> bool {
        self.precondition_hits > 0 && self.hits_with_kill == self.precondition_hits
    }

    /// Number of tested mutants that the postcondition accepted.
    pub const fn mutants_survived(&self) -> usize {
        self.mutants_tested.saturating_sub(self.mutants_killed)
    }

    /// Returns `true` iff at least one mutant was tested and the postcondition
    /// rejected every tested mutant.
    ///
    /// This is the strict, component-wise reading of the mutant gate. The
    /// default gates only require one kill (per output axis in stateful
    /// checks), so a postcondition that pins one field of a composite output
    /// or post-state and leaves another unverified still passes them, while
    /// the single-field mutants of the unverified field survive and make this
    /// method return `false`. A contract that determines its output and
    /// post-state exactly kills every mutant.
    pub const fn kills_every_mutant(&self) -> bool {
        self.mutants_tested > 0 && self.mutants_killed == self.mutants_tested
    }
}

/// Structured failure report emitted when a contract fails strength checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpecCheckFailure {
    /// Exact frozen 5-class vacuity/conformance classification.
    pub class: VacuityClass,
    /// Execution statistics accumulated up to failure.
    pub stats: SpecCheckStats,
    /// Specific diagnostic context for the failure.
    pub detail: FailureDetail,
}

impl SpecCheckFailure {
    /// Returns the index of the trial whose live execution violated the
    /// postcondition or trapped, or `None` for failures that are not tied to
    /// one trial (dead precondition, surviving mutants, degenerate
    /// configuration).
    ///
    /// Pass the index to [`replay_trial_input`] (or
    /// [`replay_stateful_trial_input`]) with the same [`SpecCheckConfig`] to
    /// reconstruct the exact counterexample input.
    pub const fn counterexample_trial(&self) -> Option<usize> {
        match self.detail {
            FailureDetail::Violation(
                ViolationKind::PostconditionFalse { trial_idx }
                | ViolationKind::ExecutionTrapped { trial_idx, .. },
            ) => Some(trial_idx),
            _ => None,
        }
    }
}

/// Outcome of a dynamic contract and mutant check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecCheckOutcome {
    /// Contract passed reachability, live conformance, and mutant-killing gates.
    Strong(SpecCheckStats),
    /// Contract failed with an exact [`VacuityClass`] diagnosis.
    Failed(SpecCheckFailure),
}

impl SpecCheckOutcome {
    /// Returns `true` iff the contract passed all strength gates.
    pub const fn is_strong(&self) -> bool {
        matches!(self, Self::Strong(_))
    }

    /// Returns the failing [`VacuityClass`], or `None` when [`Self::Strong`].
    pub const fn vacuity_class(&self) -> Option<VacuityClass> {
        match self {
            Self::Strong(_) => None,
            Self::Failed(failure) => Some(failure.class),
        }
    }

    /// Returns the accumulated [`SpecCheckStats`].
    pub const fn stats(&self) -> SpecCheckStats {
        match self {
            Self::Strong(stats) => *stats,
            Self::Failed(failure) => failure.stats,
        }
    }

    /// Returns the [`SpecCheckFailure`] when failed, or `None` when strong.
    pub const fn failure(&self) -> Option<&SpecCheckFailure> {
        match self {
            Self::Strong(_) => None,
            Self::Failed(failure) => Some(failure),
        }
    }

    /// Converts the outcome into a standard `Result`.
    pub const fn into_result(self) -> Result<SpecCheckStats, SpecCheckFailure> {
        match self {
            Self::Strong(stats) => Ok(stats),
            Self::Failed(failure) => Err(failure),
        }
    }
}

/// Verdict of one probe evaluation of a postcondition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProbeVerdict {
    /// The postcondition accepted the candidate output.
    Accepted,
    /// The postcondition rejected the candidate output.
    Rejected,
    /// The postcondition trapped on a precondition-violating input, where it
    /// is not required to be defined.
    Undefined,
}

/// Interprets one evaluation of `post` on an input whose precondition
/// admissibility is `admissible`.
///
/// On a precondition-admissible input a trapping postcondition rejects the
/// candidate output, exactly as it would at run time. Outside the precondition
/// a trap carries no evidence.
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

/// Decides whether a sampled probe input may be handed to `post`.
///
/// Returns `Some(true)` for a precondition-admissible input, `Some(false)` for
/// a precondition-violating input under [`ProbeDomain::Unconstrained`], and
/// `None` when `post` must not be evaluated on the input (it violates `pre`
/// under [`ProbeDomain::PreconditionOnly`], or `pre` itself trapped so its
/// admissibility is unknown).
const fn probe_admission(domain: ProbeDomain, pre_outcome: Result<bool, ()>) -> Option<bool> {
    match pre_outcome {
        Ok(true) => Some(true),
        Ok(false) => match domain {
            ProbeDomain::Unconstrained => Some(false),
            ProbeDomain::PreconditionOnly => None,
        },
        Err(()) => None,
    }
}

/// Maps a [`SyntacticBindingHint`] to the class it asserts.
const fn hint_class(hint: SyntacticBindingHint) -> VacuityClass {
    match hint {
        SyntacticBindingHint::ReturnUnused => VacuityClass::UnboundReturnOutput,
        SyntacticBindingHint::SyntacticallyTautological => VacuityClass::TrivialPostcondition,
    }
}

/// Records one Stage D3 mutant evaluation in `stats`, returning `true` iff the
/// mutant was rejected. A trapping postcondition rejects the mutant.
fn record_mutant(stats: &mut SpecCheckStats, outcome: Result<bool, ()>) -> bool {
    stats.mutants_tested += 1;
    match outcome {
        Ok(true) => false,
        Ok(false) => {
            stats.mutants_killed += 1;
            true
        }
        Err(()) => {
            stats.mutants_killed += 1;
            stats.mutants_trapped += 1;
            true
        }
    }
}

/// Builds the fail-closed outcome for a live execution trap.
const fn execution_trapped(
    stats: SpecCheckStats,
    trial_idx: usize,
    trap: TrapKind,
) -> SpecCheckOutcome {
    SpecCheckOutcome::Failed(SpecCheckFailure {
        class: VacuityClass::SpecViolation,
        stats,
        detail: FailureDetail::Violation(ViolationKind::ExecutionTrapped { trial_idx, trap }),
    })
}

/// Accumulates one accept/reject observation for a single probed input.
fn note_verdict(verdict: ProbeVerdict, accepted: &mut bool, rejected: &mut bool) {
    match verdict {
        ProbeVerdict::Accepted => *accepted = true,
        ProbeVerdict::Rejected => *rejected = true,
        ProbeVerdict::Undefined => {}
    }
}

/// Evidence accumulated by a vacuity-classification probe.
#[derive(Clone, Copy, Debug, Default)]
struct ProbeEvidence {
    probed_inputs: usize,
    out_of_precondition_probes: usize,
    skipped_out_of_precondition: usize,
    saw_any_false: bool,
    saw_output_sensitivity: bool,
}

impl ProbeEvidence {
    /// Records the outputs observed for one probed input.
    fn record_input(&mut self, admissible: bool, accepted: bool, rejected: bool) {
        self.probed_inputs += 1;
        if !admissible {
            self.out_of_precondition_probes += 1;
        }
        if rejected {
            self.saw_any_false = true;
        }
        if accepted && rejected {
            self.saw_output_sensitivity = true;
        }
    }

    /// Records that a witness input accepted one output and rejected another.
    fn record_flip(&mut self) {
        self.saw_any_false = true;
        self.saw_output_sensitivity = true;
    }

    /// Classifies the accumulated evidence.
    const fn class(&self) -> VacuityClass {
        if !self.saw_any_false {
            VacuityClass::TrivialPostcondition
        } else if !self.saw_output_sensitivity {
            VacuityClass::UnboundReturnOutput
        } else {
            VacuityClass::SurvivedAllMutants
        }
    }

    /// Renders the accumulated evidence as probe telemetry.
    const fn detail(&self) -> FailureDetail {
        FailureDetail::AllMutantsSurvived {
            probed_inputs: self.probed_inputs,
            out_of_precondition_probes: self.out_of_precondition_probes,
            skipped_out_of_precondition: self.skipped_out_of_precondition,
            saw_any_false: self.saw_any_false,
            saw_output_sensitivity: self.saw_output_sensitivity,
        }
    }
}

/// Maximum number of mutant-of-mutant steps taken by [`mutant_chain_finds_flip`].
const MUTANT_CHAIN_STEPS: usize = 128;

/// Walks a bounded chain of mutants-of-mutants starting at `start`, handing
/// every candidate to `flips` until it reports that some witness input flipped
/// its verdict. Returns `true` iff a flip was reported.
///
/// The chain lets point constraints such as `x < 10 || r == 42` be classified
/// deterministically: successive `+1` perturbations reach `42` from any small
/// anchor well within [`MUTANT_CHAIN_STEPS`].
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

/// Evaluates `post(x, r)` across `anchor_ret`, `extra_outputs`, and the
/// first-order mutants of `anchor_ret`, stopping once both an accepted and a
/// rejected output were observed. Returns `(accepted, rejected)`.
fn observe_outputs_at<I, R, Post>(
    x: &I,
    admissible: bool,
    anchor_ret: &R,
    extra_outputs: &[R],
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

    for r in extra_outputs {
        if accepted && rejected {
            break;
        }
        note_verdict(
            probe_verdict(post(x, r), admissible),
            &mut accepted,
            &mut rejected,
        );
    }

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

/// Minimum number of deterministic PRNG probe inputs drawn beyond the input
/// type's `BOUNDARY_COUNT` whenever the caller's trial budget allows.
const MIN_PROBE_PRNG_DRAWS: usize = 16;

/// Upper cap on the number of sampled inputs evaluated by a vacuity
/// classification probe, so very large [`SpecCheckConfig::max_trials`] budgets
/// do not turn failure classification into an unbounded scan.
///
/// The probe additionally evaluates the live anchor input that exposed the
/// failure, so [`FailureDetail::AllMutantsSurvived::probed_inputs`] is at most
/// `MAX_PROBE_INPUTS + 1`.
pub const MAX_PROBE_INPUTS: usize = 256;

/// Scales a vacuity-classification probe's sampled-input budget
/// deterministically with both `boundary_count` and `max_trials`:
///
/// - Never exceeds `max_trials`, so shrinking `max_trials` to bound callback
///   cost also bounds the inputs a classification probe samples. The live
///   anchor input and the [`MUTANT_CHAIN_STEPS`]-bounded mutant chain are
///   evaluated on top of this budget and do not scale with `max_trials`.
/// - Covers the entire boundary corpus plus at least [`MIN_PROBE_PRNG_DRAWS`]
///   PRNG draws whenever `max_trials` and [`MAX_PROBE_INPUTS`] permit, so
///   3-tuple, 4-tuple, and compound stateful inputs whose `BOUNDARY_COUNT >= 64`
///   neither truncate their boundary corpus nor draw zero PRNG samples.
/// - Scales smoothly with larger `max_trials` (`max_trials / 4`) up to
///   [`MAX_PROBE_INPUTS`].
/// - Is monotone in `max_trials` and nonzero whenever `max_trials >= 1`.
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

// Compile-time regression checks pinning `probe_input_budget` at the default
// budget, at tight and wide budgets, and at its saturating extremes.
const _: () = {
    // Default `max_trials == 256`: 64 inputs for a scalar corpus, the full
    // corpus plus `MIN_PROBE_PRNG_DRAWS` draws for compound inputs.
    assert!(probe_input_budget(15, 256) == 64);
    assert!(probe_input_budget(79, 256) == 79 + MIN_PROBE_PRNG_DRAWS);
    assert!(probe_input_budget(87, 256) == 87 + MIN_PROBE_PRNG_DRAWS);
    // Tight budgets bound the probe and never starve it entirely.
    assert!(probe_input_budget(15, 1) == 1);
    assert!(probe_input_budget(79, 8) == 8);
    assert!(probe_input_budget(79, 79) == 79);
    // Wide budgets scale as `max_trials / 4` up to the cap.
    assert!(probe_input_budget(15, 512) == 128);
    assert!(probe_input_budget(15, 1024) == MAX_PROBE_INPUTS);
    assert!(probe_input_budget(15, usize::MAX) == MAX_PROBE_INPUTS);
    // An oversized corpus is capped rather than overflowing.
    assert!(probe_input_budget(usize::MAX, usize::MAX) == MAX_PROBE_INPUTS);
    assert!(probe_input_budget(usize::MAX, 0) == 0);
};

/// Runs the deterministic classification probe once
/// `mutants_tested > 0 && mutants_killed == 0` on a non-subsingleton return.
///
/// `(anchor_input, anchor_ret)` is a live precondition-admissible pair that
/// satisfied `post`. Every other probe input is first submitted to `pre`, and
/// `post` is evaluated on it only when [`probe_admission`] allows.
fn classify_all_mutants_survived<I, R, Pre, Post>(
    config: SpecCheckConfig,
    anchor_input: I,
    anchor_ret: R,
    extra_outputs: &[R],
    pre: &mut Pre,
    post: &mut Post,
) -> (VacuityClass, FailureDetail)
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.syntactic_hint {
        return (hint_class(hint), ProbeEvidence::default().detail());
    }

    let mut probe_rng = SplitMix64::new(config.seed ^ 0xA5A5_5A5A_C3C3_3C3C);
    let probe_input_count = probe_input_budget(I::BOUNDARY_COUNT, config.max_trials);

    let mut evidence = ProbeEvidence::default();
    let mut rejected_witness: Option<(I, bool)> = None;
    let mut accepted_witness: Option<(I, bool)> = None;

    // The anchor input is admissible by construction, so it is always safe to
    // probe and guarantees at least one probed input however narrow `pre` is.
    let (accepted, rejected) = observe_outputs_at(
        &anchor_input,
        true,
        &anchor_ret,
        extra_outputs,
        &mut probe_rng,
        post,
    );
    evidence.record_input(true, accepted, rejected);

    if !evidence.saw_output_sensitivity {
        for idx in 0..probe_input_count {
            let x_probe = I::sample_at(idx, &mut probe_rng);
            let Some(admissible) = probe_admission(config.probe_domain, pre(&x_probe)) else {
                evidence.skipped_out_of_precondition += 1;
                continue;
            };

            let (accepted, rejected) = observe_outputs_at(
                &x_probe,
                admissible,
                &anchor_ret,
                extra_outputs,
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

    // Walk a bounded mutant chain from `anchor_ret` looking for an output that
    // flips the verdict of the anchor input or of a recorded witness input.
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

/// Seeds the streams of a stateless check: the input-sampling stream and the
/// Stage D3 mutant stream. Sampling draws only from the first, so the input of
/// a trial never depends on how many mutants earlier trials consumed.
const fn stateless_streams(seed: u64) -> (SplitMix64, SplitMix64) {
    let mut rng = SplitMix64::new(seed);
    let mutant_rng = rng.fork();
    (rng, mutant_rng)
}

/// Seeds the streams of a stateful check: the input-sampling stream, the
/// return-value mutant stream, and the post-state mutant stream.
const fn stateful_streams(seed: u64) -> (SplitMix64, SplitMix64, SplitMix64) {
    let mut rng = SplitMix64::new(seed);
    let ret_mutant_rng = rng.fork();
    let state_mutant_rng = rng.fork();
    (rng, ret_mutant_rng, state_mutant_rng)
}

/// Reconstructs the input that [`check_contract`],
/// [`check_contract_with_mutants`], or [`check_contract_fallible`] sampled at
/// `trial_idx` under `config`.
///
/// A failure reports only a trial index (see
/// [`SpecCheckFailure::counterexample_trial`]) because the checker is
/// allocation-free and does not require inputs to be `Copy` or `Debug`. The
/// sampling stream is a pure function of `config.seed` and the input type, so
/// replaying it yields the exact counterexample for inspection or for a
/// regression test. Returns `None` when `trial_idx >= config.max_trials`, a
/// trial the checker never runs. The cost is `trial_idx + 1` samples.
pub fn replay_trial_input<I: SampleInput>(config: SpecCheckConfig, trial_idx: usize) -> Option<I> {
    if trial_idx >= config.max_trials {
        return None;
    }
    let (mut rng, _) = stateless_streams(config.seed);
    for earlier in 0..trial_idx {
        let _ = I::sample_at(earlier, &mut rng);
    }
    Some(I::sample_at(trial_idx, &mut rng))
}

/// Reconstructs the `(old_state, args)` pair that [`check_stateful_contract`]
/// or [`check_stateful_contract_fallible`] sampled at `trial_idx` under
/// `config`.
///
/// The stateful counterpart of [`replay_trial_input`]: returns `None` when
/// `trial_idx >= config.max_trials`.
pub fn replay_stateful_trial_input<S: SampleInput, A: SampleInput>(
    config: SpecCheckConfig,
    trial_idx: usize,
) -> Option<(S, A)> {
    if trial_idx >= config.max_trials {
        return None;
    }
    let (mut rng, _, _) = stateful_streams(config.seed);
    for earlier in 0..trial_idx {
        let _ = <(S, A) as SampleInput>::sample_at(earlier, &mut rng);
    }
    Some(<(S, A) as SampleInput>::sample_at(trial_idx, &mut rng))
}

/// Fixed stack capacity for zero-allocation Stage D3 mutant deduplication
/// (large enough to hold every built-in `ReturnMutants` candidate emitted by
/// `Option<T>` and `Result<T, E>` over signed/unsigned integers).
const STAGE_D3_DEDUP_CAP: usize = 24;

/// Maximum number of distinct mutants Stage D3 tests beyond
/// [`SpecCheckConfig::max_mutants_per_hit`] on a hit (or stateful output axis)
/// that has not killed any mutant yet.
pub const KILL_FREE_OVERSCAN: usize = 64;

/// Decides whether Stage D3 stops testing mutants of the current hit (or
/// stateful output axis) once `tested` distinct mutants were evaluated.
///
/// Within the budget every distinct mutant is tested. Past it, testing stops
/// at once if the hit already killed a mutant, and otherwise continues until
/// the first kill or until [`KILL_FREE_OVERSCAN`] further mutants survived.
/// Truncating a kill-free hit would report a postcondition that rejects a
/// later first-order mutant (for example the `None` flip of a `Some` output
/// under `r.is_some()`) as having survived every mutant.
const fn stage_d3_budget_spent(tested: usize, killed_this_hit: bool, budget: usize) -> bool {
    tested >= budget && (killed_this_hit || tested >= budget.saturating_add(KILL_FREE_OVERSCAN))
}

/// Shared fallible core powering [`check_contract`],
/// [`check_contract_with_mutants`], and [`check_contract_fallible`].
fn check_contract_core<I, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    custom_mutants: Option<&[R]>,
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> SpecCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    Body: FnMut(&I) -> Result<R, ()>,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    let mut stats = SpecCheckStats {
        subsingleton_return: R::IS_SUBSINGLETON,
        ..SpecCheckStats::default()
    };

    // Fail-closed guard against zero or unsatisfiable trial/hit budgets.
    if config.max_trials == 0
        || config.min_precondition_hits == 0
        || config.min_precondition_hits > config.max_trials
    {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::DeadPrecondition,
            stats,
            detail: FailureDetail::Violation(ViolationKind::DegenerateConfig),
        });
    }

    let (mut rng, mut mutant_rng) = stateless_streams(config.seed);
    let mut anchor: Option<(I, R)> = None;

    for trial_idx in 0..config.max_trials {
        let input = I::sample_at(trial_idx, &mut rng);
        stats.trials_run += 1;

        let pre_holds = match pre(&input) {
            Ok(holds) => holds,
            Err(()) => {
                return execution_trapped(stats, trial_idx, TrapKind::PreconditionPanicked);
            }
        };

        if !pre_holds {
            continue;
        }

        stats.precondition_hits += 1;

        let ret_ok = match body(&input) {
            Ok(ret) => ret,
            Err(()) => return execution_trapped(stats, trial_idx, TrapKind::BodyPanicked),
        };

        let post_ok = match post(&input, &ret_ok) {
            Ok(holds) => holds,
            Err(()) => {
                return execution_trapped(stats, trial_idx, TrapKind::PostconditionPanicked);
            }
        };

        if !post_ok {
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class: VacuityClass::SpecViolation,
                stats,
                detail: FailureDetail::Violation(ViolationKind::PostconditionFalse { trial_idx }),
            });
        }

        let kills_before = stats.mutants_killed;
        if !R::IS_SUBSINGLETON && config.max_mutants_per_hit > 0 {
            let mut tested_this_hit = 0usize;
            if let Some(slice) = custom_mutants {
                for (bank_idx, ret_bad) in slice.iter().enumerate() {
                    if stage_d3_budget_spent(
                        tested_this_hit,
                        stats.mutants_killed > kills_before,
                        config.max_mutants_per_hit,
                    ) {
                        break;
                    }
                    // Skip the actual output and every repeat of an earlier
                    // bank entry: a bank padded with duplicates must neither
                    // inflate `mutants_tested` nor spend the per-hit budget
                    // before a distinct candidate is reached.
                    if ret_bad == &ret_ok || slice[..bank_idx].contains(ret_bad) {
                        continue;
                    }
                    tested_this_hit += 1;
                    record_mutant(&mut stats, post(&input, ret_bad));
                }
            } else {
                let mut seen: [Option<R>; STAGE_D3_DEDUP_CAP] = array::from_fn(|_| None);
                let mut seen_len = 0usize;
                ret_ok.visit_mutants(&mut mutant_rng, |ret_bad| {
                    let spent = stage_d3_budget_spent(
                        tested_this_hit,
                        stats.mutants_killed > kills_before,
                        config.max_mutants_per_hit,
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
                    record_mutant(&mut stats, post(&input, &ret_bad));
                    if seen_len < STAGE_D3_DEDUP_CAP {
                        seen[seen_len] = Some(ret_bad);
                        seen_len += 1;
                    }
                });
            }
        }
        if stats.mutants_killed > kills_before {
            stats.hits_with_kill += 1;
        }

        if anchor.is_none() {
            anchor = Some((input, ret_ok));
        }
    }

    if stats.precondition_hits < config.min_precondition_hits {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::DeadPrecondition,
            stats,
            detail: FailureDetail::InsufficientPreconditionHits {
                required: config.min_precondition_hits,
                observed: stats.precondition_hits,
            },
        });
    }

    if R::IS_SUBSINGLETON {
        if config.syntactic_hint == Some(SyntacticBindingHint::SyntacticallyTautological) {
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class: VacuityClass::TrivialPostcondition,
                stats,
                detail: ProbeEvidence::default().detail(),
            });
        }
        return SpecCheckOutcome::Strong(stats);
    }

    if config.max_mutants_per_hit == 0 {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::SurvivedAllMutants,
            stats,
            detail: FailureDetail::Violation(ViolationKind::DegenerateConfig),
        });
    }

    if stats.mutants_tested == 0 {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::SurvivedAllMutants,
            stats,
            detail: FailureDetail::NoDistinctMutantsTested,
        });
    }

    if stats.mutants_killed == 0 {
        let extra = custom_mutants.unwrap_or(&[]);
        let (class, detail) = match anchor {
            Some((anchor_input, anchor_ret)) => classify_all_mutants_survived(
                config,
                anchor_input,
                anchor_ret,
                extra,
                &mut pre,
                &mut post,
            ),
            None => (
                VacuityClass::SurvivedAllMutants,
                FailureDetail::NoDistinctMutantsTested,
            ),
        };
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class,
            stats,
            detail,
        });
    }

    SpecCheckOutcome::Strong(stats)
}

/// Checks a stateless contract `(pre, body, post)` using [`SampleInput`] and
/// [`ReturnMutants`].
///
/// `post` is evaluated only on inputs satisfying `pre` (see the module-level
/// *Domain safety* section), but Stage D3 evaluates it on perturbed outputs.
/// Because a panic cannot be intercepted in `core`-only code, a `post` that can
/// panic on a wrong output must be checked through [`check_contract_fallible`].
pub fn check_contract<I, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> SpecCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    Body: FnMut(&I) -> R,
    Post: FnMut(&I, &R) -> bool,
{
    check_contract_core(
        config,
        None,
        |input| Ok(pre(input)),
        |input| Ok(body(input)),
        |input, ret| Ok(post(input, ret)),
    )
}

/// Checks a stateless contract `(pre, body, post)` using an explicit custom
/// mutant slice `mutants` during Stage D3.
///
/// Any candidate in `mutants` equal to the actual output `ret_ok`, or equal to
/// an earlier candidate in `mutants`, is skipped: it is never counted toward
/// `mutants_tested` and never spends the `max_mutants_per_hit` budget, so a
/// bank padded with duplicates behaves exactly like its distinct entries. If
/// zero distinct mutants are tested on a non-subsingleton return type, the
/// check fails closed with [`VacuityClass::SurvivedAllMutants`].
pub fn check_contract_with_mutants<I, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    mutants: &[R],
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> SpecCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    Body: FnMut(&I) -> R,
    Post: FnMut(&I, &R) -> bool,
{
    check_contract_core(
        config,
        Some(mutants),
        |input| Ok(pre(input)),
        |input| Ok(body(input)),
        |input, ret| Ok(post(input, ret)),
    )
}

/// Checks a stateless contract whose `pre`, `body`, and `post` callbacks may
/// trap (for example, when wrapped in `std::panic::catch_unwind` in tests).
///
/// An `Err(())` in `pre`, `body`, or live `post(&input, &ret_ok)` ALWAYS fails
/// immediately with [`VacuityClass::SpecViolation`] and the corresponding
/// [`TrapKind`]; panics are never silently swallowed as precondition rejection
/// or skipped trials.
///
/// An `Err(())` from `post` on a perturbed output of a precondition-admissible
/// input means the postcondition rejected that mutant by trapping, so it is
/// counted in both `mutants_killed` and `mutants_trapped`.
pub fn check_contract_fallible<I, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    pre: Pre,
    body: Body,
    post: Post,
) -> SpecCheckOutcome
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    Body: FnMut(&I) -> Result<R, ()>,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    check_contract_core(config, None, pre, body, post)
}

/// Panics if [`check_contract`] does not return [`SpecCheckOutcome::Strong`],
/// returning the collected [`SpecCheckStats`] on success.
pub fn assert_contract_strong<I, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    pre: Pre,
    body: Body,
    post: Post,
) -> SpecCheckStats
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    Body: FnMut(&I) -> R,
    Post: FnMut(&I, &R) -> bool,
{
    match check_contract(config, pre, body, post) {
        SpecCheckOutcome::Strong(stats) => stats,
        SpecCheckOutcome::Failed(failure) => {
            panic!(
                "contract failed dynamic strength check ({}): {:?}",
                failure.class.canonical_name(),
                failure
            );
        }
    }
}

/// Live precondition-admissible execution `(old_s, args) -> (new_s, ret)` of a
/// stateful contract that satisfied its postcondition.
struct StatefulAnchor<S, A, R> {
    old_s: S,
    args: A,
    new_s: S,
    ret: R,
}

/// Probes whether `post` varies with `ret` (holding `(old_s, args, new_s)` fixed).
fn probe_stateful_return_axis<S, A, R, Pre, Post>(
    config: SpecCheckConfig,
    anchor: StatefulAnchor<S, A, R>,
    pre: &mut Pre,
    post: &mut Post,
) -> VacuityClass
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.syntactic_hint {
        return hint_class(hint);
    }

    let StatefulAnchor {
        old_s: anchor_old_s,
        args: anchor_args,
        new_s: anchor_new_s,
        ret: anchor_ret,
    } = anchor;

    let mut probe_rng = SplitMix64::new(config.seed ^ 0x51A7_E001_C3C3_3C3C);
    let mut state_probe_rng = probe_rng.fork();
    let mut ret_probe_rng = probe_rng.fork();
    let mut saw_sensitivity = false;
    // Stratified witness slots indexed by `(admissible as usize) * 3 + kind`
    // (`kind`: 0 = `anchor_new_s`/`old_s`, 1 = first mutant of `old_s`, 2 = second mutant)
    // so an early state-clause rejection on `old_s` cannot shadow a state-matching
    // witness (such as `old_s + 1` or `old_s - 1`) in conjunctive postconditions.
    let mut rejected_witnesses: [Option<(S, A, S, bool)>; 6] = [None, None, None, None, None, None];
    let mut accepted_witnesses: [Option<(S, A, S, bool)>; 2] = [None, None];

    let probe_input_count =
        probe_input_budget(<(S, A) as SampleInput>::BOUNDARY_COUNT, config.max_trials);
    for idx in 0..probe_input_count {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
        let Some(admissible) = probe_admission(config.probe_domain, pre(&old_s, &args)) else {
            continue;
        };

        let mut state_cands: [Option<(S, usize)>; 5] = [None, None, None, None, None];
        if idx % 2 == 0 {
            state_cands[0] = Some((anchor_new_s.clone(), 0));
            state_cands[1] = Some((old_s.clone(), 0));
        } else {
            state_cands[0] = Some((old_s.clone(), 0));
            state_cands[1] = Some((anchor_new_s.clone(), 0));
        }
        if !S::IS_SUBSINGLETON {
            let mut m_slot = 2usize;
            old_s.visit_mutants(&mut state_probe_rng, |cand_s| {
                if m_slot < state_cands.len() && cand_s != old_s {
                    let kind = if m_slot == 2 { 1 } else { 2 };
                    state_cands[m_slot] = Some((cand_s, kind));
                    m_slot += 1;
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
                let verdict = probe_verdict(post(&old_s, &args, &probe_new_s, &cand), admissible);
                if verdict != ProbeVerdict::Undefined && verdict != base {
                    varied = true;
                }
            });
            if varied {
                saw_sensitivity = true;
                break;
            }

            if base == ProbeVerdict::Rejected {
                let rej_slot = acc_slot * 3 + kind;
                let prefer = match &best_rej {
                    None => true,
                    Some((prev_slot, _)) => *prev_slot < rej_slot,
                };
                if rejected_witnesses[rej_slot].is_none() && prefer {
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
            let live = post(&anchor_old_s, &anchor_args, &anchor_new_s, cand);
            if probe_verdict(live, true) == ProbeVerdict::Rejected {
                return true;
            }
            for witness in accepted_witnesses.iter().flatten() {
                let (os, a, ns, admissible) = witness;
                if probe_verdict(post(os, a, ns, cand), *admissible) == ProbeVerdict::Rejected {
                    return true;
                }
            }
            for witness in rejected_witnesses.iter().flatten() {
                let (os, a, ns, admissible) = witness;
                if probe_verdict(post(os, a, ns, cand), *admissible) == ProbeVerdict::Accepted {
                    return true;
                }
            }
            false
        });
    }

    if saw_sensitivity {
        VacuityClass::SurvivedAllMutants
    } else {
        VacuityClass::UnboundReturnOutput
    }
}

/// Probes whether `post` varies with `new_s` (holding `(old_s, args, ret)` fixed).
fn probe_stateful_state_axis<S, A, R, Pre, Post>(
    config: SpecCheckConfig,
    anchor: StatefulAnchor<S, A, R>,
    pre: &mut Pre,
    post: &mut Post,
) -> VacuityClass
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.syntactic_hint {
        return hint_class(hint);
    }

    let StatefulAnchor {
        old_s: anchor_old_s,
        args: anchor_args,
        new_s: anchor_new_s,
        ret: anchor_ret,
    } = anchor;

    let mut probe_rng = SplitMix64::new(config.seed ^ 0x51A7_E002_C3C3_3C3C);
    let mut state_probe_rng = probe_rng.fork();
    let mut ret_probe_rng = probe_rng.fork();
    let mut saw_sensitivity = false;
    // Stratified witness slots indexed by `(admissible as usize) * 2 + (mutated_ret as usize)`
    // (`None` in the third field means borrow `&anchor_ret`, avoiding any `R: Clone` bound).
    let mut rejected_witnesses: [Option<(S, A, Option<R>, bool)>; 4] = [None, None, None, None];
    let mut accepted_witnesses: [Option<(S, A, Option<R>, bool)>; 4] = [None, None, None, None];

    let probe_input_count =
        probe_input_budget(<(S, A) as SampleInput>::BOUNDARY_COUNT, config.max_trials);
    for idx in 0..probe_input_count {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
        let Some(admissible) = probe_admission(config.probe_domain, pre(&old_s, &args)) else {
            continue;
        };

        let acc_slot = usize::from(admissible);
        let mut base_anchor = ProbeVerdict::Undefined;

        // First probe while holding `anchor_ret` fixed.
        let base = probe_verdict(post(&old_s, &args, &anchor_new_s, &anchor_ret), admissible);
        if base != ProbeVerdict::Undefined {
            base_anchor = base;
            let revert = probe_verdict(post(&old_s, &args, &old_s, &anchor_ret), admissible);
            let mut varied = revert != ProbeVerdict::Undefined && revert != base;
            if !varied {
                anchor_new_s.visit_mutants(&mut state_probe_rng, |cand_s| {
                    if varied {
                        return;
                    }
                    let verdict =
                        probe_verdict(post(&old_s, &args, &cand_s, &anchor_ret), admissible);
                    if verdict != ProbeVerdict::Undefined && verdict != base {
                        varied = true;
                    }
                });
            }
            if varied {
                saw_sensitivity = true;
                break;
            }
        }

        // Also probe up to 5 mutants of `anchor_ret` (still holding each candidate fixed
        // while varying `new_s`) so conjunctive constraints pairing `ret` with `old_s`
        // do not hide state-axis sensitivity.
        let mut best_rej_mut: Option<R> = None;
        let mut best_acc_mut: Option<R> = None;
        if !R::IS_SUBSINGLETON {
            let mut ret_cands: [Option<R>; 5] = [None, None, None, None, None];
            let mut r_slot = 0usize;
            anchor_ret.visit_mutants(&mut ret_probe_rng, |cand_r| {
                if r_slot < ret_cands.len() && cand_r != anchor_ret {
                    ret_cands[r_slot] = Some(cand_r);
                    r_slot += 1;
                }
            });

            for probe_ret in ret_cands.into_iter().flatten() {
                let b = probe_verdict(post(&old_s, &args, &anchor_new_s, &probe_ret), admissible);
                if b == ProbeVerdict::Undefined {
                    continue;
                }
                let rev = probe_verdict(post(&old_s, &args, &old_s, &probe_ret), admissible);
                let mut varied = rev != ProbeVerdict::Undefined && rev != b;
                if !varied {
                    anchor_new_s.visit_mutants(&mut state_probe_rng, |cand_s| {
                        if varied {
                            return;
                        }
                        let verdict =
                            probe_verdict(post(&old_s, &args, &cand_s, &probe_ret), admissible);
                        if verdict != ProbeVerdict::Undefined && verdict != b {
                            varied = true;
                        }
                    });
                }
                if varied {
                    saw_sensitivity = true;
                    break;
                }
                if b == ProbeVerdict::Rejected
                    && rejected_witnesses[acc_slot * 2 + 1].is_none()
                    && best_rej_mut.is_none()
                {
                    best_rej_mut = Some(probe_ret);
                } else if b == ProbeVerdict::Accepted
                    && accepted_witnesses[acc_slot * 2 + 1].is_none()
                    && best_acc_mut.is_none()
                {
                    best_acc_mut = Some(probe_ret);
                }
            }
            if saw_sensitivity {
                break;
            }
        }

        if let Some(probe_ret) = best_rej_mut {
            rejected_witnesses[acc_slot * 2 + 1] = Some((old_s, args, Some(probe_ret), admissible));
        } else if base_anchor == ProbeVerdict::Rejected
            && rejected_witnesses[acc_slot * 2].is_none()
        {
            rejected_witnesses[acc_slot * 2] = Some((old_s, args, None, admissible));
        } else if let Some(probe_ret) = best_acc_mut {
            accepted_witnesses[acc_slot * 2 + 1] = Some((old_s, args, Some(probe_ret), admissible));
        } else if base_anchor == ProbeVerdict::Accepted
            && accepted_witnesses[acc_slot * 2].is_none()
        {
            accepted_witnesses[acc_slot * 2] = Some((old_s, args, None, admissible));
        }
    }

    if !saw_sensitivity {
        saw_sensitivity = mutant_chain_finds_flip(anchor_new_s, &mut probe_rng, |cand_s| {
            let live = post(&anchor_old_s, &anchor_args, cand_s, &anchor_ret);
            if probe_verdict(live, true) == ProbeVerdict::Rejected {
                return true;
            }
            for witness in accepted_witnesses.iter().flatten() {
                let (os, a, opt_r, admissible) = witness;
                let r_ref = opt_r.as_ref().unwrap_or(&anchor_ret);
                if probe_verdict(post(os, a, cand_s, r_ref), *admissible) == ProbeVerdict::Rejected
                {
                    return true;
                }
            }
            for witness in rejected_witnesses.iter().flatten() {
                let (os, a, opt_r, admissible) = witness;
                let r_ref = opt_r.as_ref().unwrap_or(&anchor_ret);
                if probe_verdict(post(os, a, cand_s, r_ref), *admissible) == ProbeVerdict::Accepted
                {
                    return true;
                }
            }
            false
        });
    }

    if saw_sensitivity {
        VacuityClass::SurvivedAllMutants
    } else {
        VacuityClass::UnboundReturnOutput
    }
}

/// Evaluates `post(old_s, args, s, r)` across the anchor outputs, the pre-state
/// revert `s = old_s`, and the first-order mutants of each non-subsingleton
/// output axis, stopping once both an accepted and a rejected output pair were
/// observed. Returns `(accepted, rejected)`.
fn observe_stateful_outputs_at<S, A, R, Post>(
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

/// Probes both `(new_s, ret)` output axes jointly when zero mutants were killed
/// across both axes of a stateful contract.
fn classify_stateful_all_survived<S, A, R, Pre, Post>(
    config: SpecCheckConfig,
    anchor: StatefulAnchor<S, A, R>,
    pre: &mut Pre,
    post: &mut Post,
) -> (VacuityClass, FailureDetail)
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.syntactic_hint {
        return (hint_class(hint), ProbeEvidence::default().detail());
    }

    let StatefulAnchor {
        old_s: anchor_old_s,
        args: anchor_args,
        new_s: anchor_new_s,
        ret: anchor_ret,
    } = anchor;

    let mut probe_rng = SplitMix64::new(config.seed ^ 0x51A7_E003_C3C3_3C3C);
    let mut evidence = ProbeEvidence::default();
    let mut rejected_witness: Option<(S, A, bool)> = None;
    let mut accepted_witness: Option<(S, A, bool)> = None;

    // The anchor execution is admissible by construction, so it is always safe
    // to probe and guarantees at least one probed input.
    let (accepted, rejected) = observe_stateful_outputs_at(
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
        let probe_input_count =
            probe_input_budget(<(S, A) as SampleInput>::BOUNDARY_COUNT, config.max_trials);
        for idx in 0..probe_input_count {
            let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
            let Some(admissible) = probe_admission(config.probe_domain, pre(&old_s, &args)) else {
                evidence.skipped_out_of_precondition += 1;
                continue;
            };

            let (accepted, rejected) = observe_stateful_outputs_at(
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
            let live = post(&anchor_old_s, &anchor_args, cand_s, &anchor_ret);
            if probe_verdict(live, true) == ProbeVerdict::Rejected {
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
            let live = post(&anchor_old_s, &anchor_args, &anchor_new_s, cand_r);
            if probe_verdict(live, true) == ProbeVerdict::Rejected {
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

/// Shared fallible core powering [`check_stateful_contract`] and
/// [`check_stateful_contract_fallible`].
fn check_stateful_contract_core<S, A, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> SpecCheckOutcome
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    Body: FnMut(&mut S, &A) -> Result<R, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    let mut stats = SpecCheckStats {
        subsingleton_return: R::IS_SUBSINGLETON,
        ..SpecCheckStats::default()
    };

    if config.max_trials == 0
        || config.min_precondition_hits == 0
        || config.min_precondition_hits > config.max_trials
    {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::DeadPrecondition,
            stats,
            detail: FailureDetail::Violation(ViolationKind::DegenerateConfig),
        });
    }

    let (mut rng, mut ret_mutant_rng, mut state_mutant_rng) = stateful_streams(config.seed);

    let mut return_mutants_tested = 0usize;
    let mut return_mutants_killed = 0usize;
    let mut state_mutants_tested = 0usize;
    let mut state_mutants_killed = 0usize;
    let mut anchor: Option<StatefulAnchor<S, A, R>> = None;

    for trial_idx in 0..config.max_trials {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(trial_idx, &mut rng);
        stats.trials_run += 1;

        let pre_holds = match pre(&old_s, &args) {
            Ok(holds) => holds,
            Err(()) => {
                return execution_trapped(stats, trial_idx, TrapKind::PreconditionPanicked);
            }
        };

        if !pre_holds {
            continue;
        }

        stats.precondition_hits += 1;

        // A trapping body may leave `new_s` partially mutated; the trap is
        // reported immediately and that state is never used as an output.
        let mut new_s = old_s.clone();
        let ret_ok = match body(&mut new_s, &args) {
            Ok(ret) => ret,
            Err(()) => return execution_trapped(stats, trial_idx, TrapKind::BodyPanicked),
        };

        let post_ok = match post(&old_s, &args, &new_s, &ret_ok) {
            Ok(holds) => holds,
            Err(()) => {
                return execution_trapped(stats, trial_idx, TrapKind::PostconditionPanicked);
            }
        };

        if !post_ok {
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class: VacuityClass::SpecViolation,
                stats,
                detail: FailureDetail::Violation(ViolationKind::PostconditionFalse { trial_idx }),
            });
        }

        let kills_before = stats.mutants_killed;

        // Return-value mutant perturbation axis.
        if !R::IS_SUBSINGLETON && config.max_mutants_per_hit > 0 {
            let mut tested_this_hit = 0usize;
            let mut seen_ret: [Option<R>; STAGE_D3_DEDUP_CAP] = array::from_fn(|_| None);
            let mut seen_ret_len = 0usize;
            let ret_kills_before = return_mutants_killed;
            ret_ok.visit_mutants(&mut ret_mutant_rng, |ret_bad| {
                let spent = stage_d3_budget_spent(
                    tested_this_hit,
                    return_mutants_killed > ret_kills_before,
                    config.max_mutants_per_hit,
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
                if record_mutant(&mut stats, post(&old_s, &args, &new_s, &ret_bad)) {
                    return_mutants_killed += 1;
                }
                if seen_ret_len < STAGE_D3_DEDUP_CAP {
                    seen_ret[seen_ret_len] = Some(ret_bad);
                    seen_ret_len += 1;
                }
            });
        }

        // State-mutation perturbation axis (always includes pre-state revert
        // whenever `new_s != old_s`).
        if !S::IS_SUBSINGLETON && config.max_mutants_per_hit > 0 {
            let mut tested_this_hit = 0usize;
            let state_kills_before = state_mutants_killed;
            let tested_pre_revert = new_s != old_s;
            if tested_pre_revert {
                tested_this_hit += 1;
                state_mutants_tested += 1;
                if record_mutant(&mut stats, post(&old_s, &args, &old_s, &ret_ok)) {
                    state_mutants_killed += 1;
                }
            }

            let mut seen_s: [Option<S>; STAGE_D3_DEDUP_CAP] = array::from_fn(|_| None);
            let mut seen_s_len = 0usize;
            new_s.visit_mutants(&mut state_mutant_rng, |bad_s| {
                let spent = stage_d3_budget_spent(
                    tested_this_hit,
                    state_mutants_killed > state_kills_before,
                    config.max_mutants_per_hit,
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
                if record_mutant(&mut stats, post(&old_s, &args, &bad_s, &ret_ok)) {
                    state_mutants_killed += 1;
                }
                if seen_s_len < STAGE_D3_DEDUP_CAP {
                    seen_s[seen_s_len] = Some(bad_s);
                    seen_s_len += 1;
                }
            });
        }

        if stats.mutants_killed > kills_before {
            stats.hits_with_kill += 1;
        }

        if anchor.is_none() {
            anchor = Some(StatefulAnchor {
                old_s,
                args,
                new_s,
                ret: ret_ok,
            });
        }
    }

    if stats.precondition_hits < config.min_precondition_hits {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::DeadPrecondition,
            stats,
            detail: FailureDetail::InsufficientPreconditionHits {
                required: config.min_precondition_hits,
                observed: stats.precondition_hits,
            },
        });
    }

    if S::IS_SUBSINGLETON && R::IS_SUBSINGLETON {
        if config.syntactic_hint == Some(SyntacticBindingHint::SyntacticallyTautological) {
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class: VacuityClass::TrivialPostcondition,
                stats,
                detail: ProbeEvidence::default().detail(),
            });
        }
        return SpecCheckOutcome::Strong(stats);
    }

    if config.max_mutants_per_hit == 0 {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::SurvivedAllMutants,
            stats,
            detail: FailureDetail::Violation(ViolationKind::DegenerateConfig),
        });
    }

    if stats.mutants_tested == 0 {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::SurvivedAllMutants,
            stats,
            detail: FailureDetail::NoDistinctMutantsTested,
        });
    }

    let axis_detail = FailureDetail::StatefulAxisUnconstrained {
        return_mutants_tested,
        return_mutants_killed,
        state_mutants_tested,
        state_mutants_killed,
    };

    if stats.mutants_killed == 0 {
        let (class, detail) = match anchor {
            Some(anchor) => classify_stateful_all_survived(config, anchor, &mut pre, &mut post),
            None => (
                VacuityClass::SurvivedAllMutants,
                FailureDetail::NoDistinctMutantsTested,
            ),
        };
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class,
            stats,
            detail,
        });
    }

    if config.require_both_state_and_return_kills {
        if !R::IS_SUBSINGLETON && return_mutants_killed == 0 {
            let class = match anchor {
                Some(anchor) if return_mutants_tested > 0 => {
                    probe_stateful_return_axis(config, anchor, &mut pre, &mut post)
                }
                _ => VacuityClass::SurvivedAllMutants,
            };
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class,
                stats,
                detail: axis_detail,
            });
        }

        if !S::IS_SUBSINGLETON && state_mutants_killed == 0 {
            let class = match anchor {
                Some(anchor) if state_mutants_tested > 0 => {
                    probe_stateful_state_axis(config, anchor, &mut pre, &mut post)
                }
                _ => VacuityClass::SurvivedAllMutants,
            };
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class,
                stats,
                detail: axis_detail,
            });
        }
    }

    SpecCheckOutcome::Strong(stats)
}

/// Checks a stateful `&mut S` contract accepting `(old_state, args)` and
/// validating `(old_state, args, new_state, ret)`.
///
/// Tests BOTH:
/// - Return-value perturbations `post(&old_s, &args, &new_s, &bad_ret)` when
///   `!R::IS_SUBSINGLETON`, AND
/// - State-mutation perturbations `post(&old_s, &args, &bad_s, &ok_ret)` when
///   `!S::IS_SUBSINGLETON`, ALWAYS testing pre-state revert `bad_s = old_s`
///   whenever `new_s != old_s` in addition to `S::visit_mutants`.
///
/// When `config.require_both_state_and_return_kills` is `true` (default), every
/// non-subsingleton output axis (`S` and `R`) must independently kill at least
/// one mutant so a stateful spec cannot silently ignore either `new_s` or `ret`.
///
/// `post` is evaluated only on `(old_state, args)` pairs satisfying `pre` (see
/// the module-level *Domain safety* section). Because a panic cannot be
/// intercepted in `core`-only code, a `body` or `post` that can panic must be
/// checked through [`check_stateful_contract_fallible`].
pub fn check_stateful_contract<S, A, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> SpecCheckOutcome
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> bool,
    Body: FnMut(&mut S, &A) -> R,
    Post: FnMut(&S, &A, &S, &R) -> bool,
{
    check_stateful_contract_core(
        config,
        |old_s, args| Ok(pre(old_s, args)),
        |state, args| Ok(body(state, args)),
        |old_s, args, new_s, ret| Ok(post(old_s, args, new_s, ret)),
    )
}

/// Checks a stateful `&mut S` contract whose `pre`, `body`, and `post`
/// callbacks may trap (for example, when wrapped in `std::panic::catch_unwind`
/// in tests).
///
/// An `Err(())` in `pre`, `body`, or live `post` ALWAYS fails immediately with
/// [`VacuityClass::SpecViolation`] and the corresponding [`TrapKind`]. A `body`
/// that traps after partially mutating its state is reported as
/// [`TrapKind::BodyPanicked`]; the partially mutated state is discarded and is
/// never treated as an output. An `Err(())` from `post` on a perturbed output
/// or post-state of a precondition-admissible input counts as that mutant being
/// rejected (`mutants_killed` and `mutants_trapped`).
pub fn check_stateful_contract_fallible<S, A, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    pre: Pre,
    body: Body,
    post: Post,
) -> SpecCheckOutcome
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> Result<bool, ()>,
    Body: FnMut(&mut S, &A) -> Result<R, ()>,
    Post: FnMut(&S, &A, &S, &R) -> Result<bool, ()>,
{
    check_stateful_contract_core(config, pre, body, post)
}

/// Panics if [`check_stateful_contract`] does not return
/// [`SpecCheckOutcome::Strong`], returning the collected [`SpecCheckStats`] on
/// success.
pub fn assert_stateful_contract_strong<S, A, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    pre: Pre,
    body: Body,
    post: Post,
) -> SpecCheckStats
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Pre: FnMut(&S, &A) -> bool,
    Body: FnMut(&mut S, &A) -> R,
    Post: FnMut(&S, &A, &S, &R) -> bool,
{
    match check_stateful_contract(config, pre, body, post) {
        SpecCheckOutcome::Strong(stats) => stats,
        SpecCheckOutcome::Failed(failure) => {
            panic!(
                "stateful contract failed dynamic strength check ({}): {:?}",
                failure.class.canonical_name(),
                failure
            );
        }
    }
}

// ============================================================================
// Specification-Boundary Soundness Guards
// ============================================================================
//
// A kernel-checked proof certifies a claim only relative to its specification.
// The three guards below reject specifications whose *boundary* makes the
// certificate worthless even though every vacuity class above passes:
//
// 1. `EntryPointPrecondition` (`verus#3606`): a binary entry point (`main`,
//    `#![no_main]` `_start`, `#[entry]`) has no verified caller, so a
//    non-trivial `requires` is never discharged.
// 2. `FixedWidthGhostLength` (`Slate` soundness bug 121): a ghost collection
//    length typed at a machine width wraps at `2^64` and makes the standard
//    collection axioms inconsistent. Its scanner lives in
//    `cargo_anneal::property_registry`; this module only freezes its identity.
// 3. `ErrorBranchWildcard` (`awsm2`): a postcondition arm such as
//    `Err(_) => true` passes postcondition dichotomy through its `Ok` arm
//    while accepting every error escape.
//
// The identifiers, ranks, and vacuity classes are frozen across
// `Anneal.SpecBoundaryGuards` (Lean), this module, and
// `cargo_anneal::property_registry::SpecBoundaryGuardId`.

/// Frozen 3-class specification-boundary guard taxonomy, in rank order `0..3`.
///
/// Each guard reports under one class of the frozen 5-class [`VacuityClass`]
/// taxonomy ([`Self::to_vacuity_class`]), which is left unchanged.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SpecBoundaryGuardClass {
    /// Rank 0 (`verus#3606`): a binary entry point carries a non-trivial
    /// `requires` clause that no verified caller discharges.
    EntryPointPrecondition,
    /// Rank 1 (`Slate` soundness bug 121): a ghost collection length or
    /// cardinality is typed at a fixed machine width instead of `Nat` / `Int`.
    FixedWidthGhostLength,
    /// Rank 2 (`awsm2`): a postcondition accepts every error payload, `Ub`, or
    /// `Unsupported` outcome.
    ErrorBranchWildcard,
}

impl SpecBoundaryGuardClass {
    /// Total number of specification-boundary guards.
    pub const COUNT: usize = 3;

    /// All three guards in their frozen cross-language rank order
    /// (`SpecBoundaryGuardClass.all` in Lean).
    pub const ALL: [Self; 3] = [
        Self::EntryPointPrecondition,
        Self::FixedWidthGhostLength,
        Self::ErrorBranchWildcard,
    ];

    /// 0-based canonical rank (`0..3`).
    pub const fn rank(self) -> usize {
        match self {
            Self::EntryPointPrecondition => 0,
            Self::FixedWidthGhostLength => 1,
            Self::ErrorBranchWildcard => 2,
        }
    }

    /// Reconstructs a guard from its canonical rank; `None` for `rank >= 3`.
    pub const fn from_rank(rank: usize) -> Option<Self> {
        match rank {
            0 => Some(Self::EntryPointPrecondition),
            1 => Some(Self::FixedWidthGhostLength),
            2 => Some(Self::ErrorBranchWildcard),
            _ => None,
        }
    }

    /// Canonical `snake_case` guard identifier shared with
    /// `cargo_anneal::property_registry::SpecBoundaryGuardId::as_str`.
    pub const fn guard_id(self) -> &'static str {
        match self {
            Self::EntryPointPrecondition => "entry_point_requires",
            Self::FixedWidthGhostLength => "fixed_width_ghost_length",
            Self::ErrorBranchWildcard => "error_branch_wildcard",
        }
    }

    /// Parses a guard identifier, the inverse of [`Self::guard_id`]. Matching
    /// is exact and case-sensitive.
    pub fn from_guard_id(id: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|guard| guard.guard_id() == id)
    }

    /// Canonical cross-language diagnostic name.
    pub const fn canonical_name(self) -> &'static str {
        match self {
            Self::EntryPointPrecondition => "EntryPointPrecondition",
            Self::FixedWidthGhostLength => "FixedWidthGhostLength",
            Self::ErrorBranchWildcard => "ErrorBranchWildcard",
        }
    }

    /// Parses a canonical diagnostic name, the inverse of
    /// [`Self::canonical_name`]. Matching is exact and case-sensitive.
    pub fn from_canonical_name(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|guard| guard.canonical_name() == name)
    }

    /// The frozen [`VacuityClass`] a violation of this guard is reported under.
    pub const fn to_vacuity_class(self) -> VacuityClass {
        match self {
            Self::EntryPointPrecondition => VacuityClass::DeadPrecondition,
            Self::FixedWidthGhostLength => VacuityClass::SpecViolation,
            Self::ErrorBranchWildcard => VacuityClass::SurvivedAllMutants,
        }
    }
}

impl fmt::Display for SpecBoundaryGuardClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.canonical_name())
    }
}

macro_rules! spec_boundary_guard_marker {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $name;

        impl $name {
            /// The guard class this check type reports.
            pub const CLASS: SpecBoundaryGuardClass = SpecBoundaryGuardClass::$name;
            /// Canonical guard identifier of [`Self::CLASS`].
            pub const GUARD_ID: &'static str = Self::CLASS.guard_id();
            /// Canonical diagnostic name of [`Self::CLASS`].
            pub const CANONICAL_NAME: &'static str = Self::CLASS.canonical_name();
            /// Frozen vacuity class of [`Self::CLASS`].
            pub const VACUITY_CLASS: VacuityClass = Self::CLASS.to_vacuity_class();
        }
    };
}

spec_boundary_guard_marker!(
    /// Check type of the `verus#3606` entry-point `requires` guard
    /// ([`check_entry_point_requires`]).
    EntryPointPrecondition
);
spec_boundary_guard_marker!(
    /// Check type of the `Slate` bug 121 fixed-width ghost length guard
    /// (scanned by `cargo_anneal::property_registry`).
    FixedWidthGhostLength
);
spec_boundary_guard_marker!(
    /// Check type of the `awsm2` error-branch wildcard guard
    /// ([`detect_error_branch_wildcard`],
    /// [`check_result_contract_no_error_wildcard`]).
    ErrorBranchWildcard
);

// ----------------------------------------------------------------------------
// Comment- and literal-aware specification lexer
// ----------------------------------------------------------------------------

/// Source dialect of a specification snippet, which decides what a comment is.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum SpecSyntax {
    /// Rust: `//` line comments and nested `/* */` block comments.
    Rust,
    /// Lean 4: `--` line comments and nested `/- -/` block comments.
    Lean,
    /// Unknown dialect: both comment families are recognized.
    ///
    /// The comment markers of one language are operators in the other (`--`
    /// is two Rust negations, `//` may be user notation in Lean), so prefer
    /// [`Self::Rust`] or [`Self::Lean`] whenever the dialect is known.
    #[default]
    Any,
}

/// Malformed-source error reported by the strict specification scanners.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SpecScanError {
    /// A block comment, string literal, or character literal is not closed, so
    /// the remaining source cannot be attributed to code or to a literal.
    UnclosedLiteralOrComment,
}

impl fmt::Display for SpecScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnclosedLiteralOrComment => {
                f.write_str("unclosed block comment, string literal, or character literal")
            }
        }
    }
}

/// One lexical token of a specification snippet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SpecTok<'a> {
    /// Identifier, keyword, or numeric literal.
    Word(&'a str),
    /// String, raw-string, byte-string, or character literal. Its contents are
    /// never inspected.
    Literal,
    /// The match-arm arrow `=>`.
    FatArrow,
    /// The path separator `::`.
    PathSep,
    /// A rest or range token: `..`, `..=`, or `...`.
    DotDot,
    /// Any other operator or punctuation (`(`, `|`, `==`, `==>`, `&&`, `∧`).
    Sym(&'a str),
}

/// Zero-allocation lexer over Rust and Lean specification source that skips
/// comments and never looks inside literals.
#[derive(Clone, Copy, Debug)]
struct SpecLexer<'a> {
    src: &'a str,
    pos: usize,
    syntax: SpecSyntax,
}

/// Longest character-literal escape body searched for a closing quote
/// (`'\u{10FFFF}'` needs 9 bytes after the escaped character).
const MAX_CHAR_ESCAPE_BYTES: usize = 12;

impl<'a> SpecLexer<'a> {
    const fn new(src: &'a str, syntax: SpecSyntax) -> Self {
        Self {
            src,
            pos: 0,
            syntax,
        }
    }

    const fn rust_comments(&self) -> bool {
        !matches!(self.syntax, SpecSyntax::Lean)
    }

    const fn lean_comments(&self) -> bool {
        !matches!(self.syntax, SpecSyntax::Rust)
    }

    fn byte_at(&self, idx: usize) -> Option<u8> {
        self.src.as_bytes().get(idx).copied()
    }

    fn skip_line_comment(&mut self) {
        let bytes = self.src.as_bytes();
        while self.pos < bytes.len() && bytes[self.pos] != b'\n' {
            self.pos += 1;
        }
    }

    /// Skips a nested block comment opened by `/` + `marker` and closed by
    /// `marker` + `/`.
    fn skip_block_comment(&mut self, marker: u8) -> Result<(), SpecScanError> {
        let bytes = self.src.as_bytes();
        self.pos += 2;
        let mut depth = 1usize;
        while self.pos < bytes.len() {
            let here = bytes[self.pos];
            let next = bytes.get(self.pos + 1).copied();
            if here == b'/' && next == Some(marker) {
                depth += 1;
                self.pos += 2;
            } else if here == marker && next == Some(b'/') {
                depth -= 1;
                self.pos += 2;
                if depth == 0 {
                    return Ok(());
                }
            } else {
                self.pos += 1;
            }
        }
        Err(SpecScanError::UnclosedLiteralOrComment)
    }

    /// Skips a `"…"` string literal starting at the opening quote.
    fn skip_string(&mut self) -> Result<(), SpecScanError> {
        let bytes = self.src.as_bytes();
        self.pos += 1;
        while self.pos < bytes.len() {
            match bytes[self.pos] {
                b'\\' => self.pos += 2,
                b'"' => {
                    self.pos += 1;
                    return Ok(());
                }
                _ => self.pos += 1,
            }
        }
        // A trailing backslash may have stepped past the end.
        self.pos = bytes.len();
        Err(SpecScanError::UnclosedLiteralOrComment)
    }

    /// Skips a raw string `#…#"…"#…#` whose hashes start at `self.pos`.
    /// Returns `Ok(false)` without consuming anything when no raw string
    /// starts here.
    fn skip_raw_string(&mut self) -> Result<bool, SpecScanError> {
        let bytes = self.src.as_bytes();
        let mut idx = self.pos;
        let mut hashes = 0usize;
        while bytes.get(idx) == Some(&b'#') {
            hashes += 1;
            idx += 1;
        }
        if bytes.get(idx) != Some(&b'"') {
            return Ok(false);
        }
        idx += 1;
        while idx < bytes.len() {
            if bytes[idx] == b'"' {
                let mut closing = 0usize;
                while closing < hashes && bytes.get(idx + 1 + closing) == Some(&b'#') {
                    closing += 1;
                }
                if closing == hashes {
                    self.pos = idx + 1 + hashes;
                    return Ok(true);
                }
            }
            idx += 1;
        }
        self.pos = bytes.len();
        Err(SpecScanError::UnclosedLiteralOrComment)
    }

    /// Lexes the token starting at a `'`: a character literal, or a lone quote
    /// (a Rust lifetime marker).
    fn lex_quote(&mut self) -> Result<SpecTok<'a>, SpecScanError> {
        let start = self.pos;
        let rest = &self.src[start + 1..];
        if let Some(escape_body) = rest.strip_prefix('\\') {
            // Escaped character literal: skip the escaped character, then
            // find the closing quote within a short single-line window.
            let Some(escaped) = escape_body.chars().next() else {
                self.pos = self.src.len();
                return Err(SpecScanError::UnclosedLiteralOrComment);
            };
            if escaped == '\n' || escaped == '\r' {
                self.pos = self.src.len();
                return Err(SpecScanError::UnclosedLiteralOrComment);
            }
            let body_start = start + 2 + escaped.len_utf8();
            let window_end = (body_start + MAX_CHAR_ESCAPE_BYTES).min(self.src.len());
            let mut idx = body_start;
            while idx < window_end {
                match self.byte_at(idx) {
                    Some(b'\'') => {
                        self.pos = idx + 1;
                        return Ok(SpecTok::Literal);
                    }
                    Some(b'\n' | b'\r') => break,
                    _ => idx += 1,
                }
            }
            self.pos = self.src.len();
            return Err(SpecScanError::UnclosedLiteralOrComment);
        }
        if let Some(ch) = rest.chars().next() {
            let after = start + 1 + ch.len_utf8();
            if ch != '\'' && ch != '\n' && ch != '\r' && self.byte_at(after) == Some(b'\'') {
                self.pos = after + 1;
                return Ok(SpecTok::Literal);
            }
        }
        self.pos = start + 1;
        Ok(SpecTok::Sym(&self.src[start..start + 1]))
    }

    /// Returns the next token, `Ok(None)` at end of input, or an error when a
    /// comment or literal is left unclosed.
    fn next_tok(&mut self) -> Result<Option<SpecTok<'a>>, SpecScanError> {
        let bytes = self.src.as_bytes();
        loop {
            while self.pos < bytes.len() && bytes[self.pos].is_ascii_whitespace() {
                self.pos += 1;
            }
            // Lean identifier quotes (`«pre»` is the identifier `pre`).
            if self.lean_comments()
                && (self.src[self.pos..].starts_with('«') || self.src[self.pos..].starts_with('»'))
            {
                self.pos += '«'.len_utf8();
                continue;
            }
            let Some(here) = self.byte_at(self.pos) else {
                return Ok(None);
            };
            let next = self.byte_at(self.pos + 1);
            let rust_line_comment = self.rust_comments() && here == b'/' && next == Some(b'/');
            let lean_line_comment = self.lean_comments() && here == b'-' && next == Some(b'-');
            if rust_line_comment || lean_line_comment {
                self.skip_line_comment();
            } else if self.rust_comments() && here == b'/' && next == Some(b'*') {
                self.skip_block_comment(b'*')?;
            } else if self.lean_comments() && here == b'/' && next == Some(b'-') {
                self.skip_block_comment(b'-')?;
            } else {
                break;
            }
        }

        let start = self.pos;
        let here = bytes[start];

        if here == b'"' {
            self.skip_string()?;
            return Ok(Some(SpecTok::Literal));
        }
        if here == b'\'' {
            return self.lex_quote().map(Some);
        }

        let first = self.src[start..]
            .chars()
            .next()
            .expect("`start` is a character boundary inside the source");
        if is_spec_word_char(first) {
            let mut end = start;
            for (offset, ch) in self.src[start..].char_indices() {
                if !is_spec_word_char(ch) {
                    break;
                }
                end = start + offset + ch.len_utf8();
            }
            let word = &self.src[start..end];
            self.pos = end;
            // Raw strings exist in both languages (`r"…"`, `r#"…"#`): a
            // backslash inside one is not an escape.
            if word == "r" && self.skip_raw_string()? {
                return Ok(Some(SpecTok::Literal));
            }
            // Rust byte/C-string literal prefixes (`br"…"`, `cr#"…"#`,
            // `b"…"`, `c"…"`, `b'…'`). Never apply these in Lean mode, where
            // `b'` is a primed identifier.
            if !matches!(self.syntax, SpecSyntax::Lean) {
                if matches!(word, "br" | "cr") && self.skip_raw_string()? {
                    return Ok(Some(SpecTok::Literal));
                }
                if matches!(word, "b" | "c") && self.byte_at(end) == Some(b'"') {
                    self.skip_string()?;
                    return Ok(Some(SpecTok::Literal));
                }
                if word == "b" && self.byte_at(end) == Some(b'\'') {
                    let mut look = *self;
                    match look.lex_quote()? {
                        SpecTok::Literal => {
                            *self = look;
                            return Ok(Some(SpecTok::Literal));
                        }
                        _ if matches!(self.syntax, SpecSyntax::Rust) => {
                            return Err(SpecScanError::UnclosedLiteralOrComment);
                        }
                        // In `SpecSyntax::Any`, fall through so Lean's primed
                        // identifier `b'` lexes cleanly as `Word("b'")`.
                        _ => {}
                    }
                }
            }
            // Lean identifiers may end in primes (`x'`, `b'`, `h''`). Rust
            // never places a quote directly after an identifier other than
            // `b'…'`.
            if !matches!(self.syntax, SpecSyntax::Rust) {
                while self.byte_at(self.pos) == Some(b'\'') {
                    self.pos += 1;
                }
            }
            return Ok(Some(SpecTok::Word(&self.src[start..self.pos])));
        }

        let rest = &self.src[start..];
        let (tok, len) = if rest.starts_with("==>") {
            (SpecTok::Sym(&rest[..3]), 3)
        } else if rest.starts_with("=>") {
            (SpecTok::FatArrow, 2)
        } else if rest.starts_with("...") || rest.starts_with("..=") {
            (SpecTok::DotDot, 3)
        } else if rest.starts_with("..") {
            (SpecTok::DotDot, 2)
        } else if rest.starts_with("::") {
            (SpecTok::PathSep, 2)
        } else if rest.starts_with("<->") {
            (SpecTok::Sym(&rest[..3]), 3)
        } else if [
            "==", "!=", "<=", ">=", "&&", "||", "->", "<-", ":=", "/\\", "\\/",
        ]
        .iter()
        .any(|op| rest.starts_with(op))
        {
            (SpecTok::Sym(&rest[..2]), 2)
        } else {
            let len = first.len_utf8();
            (SpecTok::Sym(&rest[..len]), len)
        };
        self.pos = start + len;
        Ok(Some(tok))
    }
}

/// Characters that make up identifiers, keywords, and numeric literals.
fn is_spec_word_char(ch: char) -> bool {
    ch == '_' || ch.is_alphanumeric()
}

// ----------------------------------------------------------------------------
// Guard 1: entry-point `requires` ban (`verus#3606`)
// ----------------------------------------------------------------------------

/// How an item becomes a binary entry point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EntryPointKind {
    /// Rust `fn main` of a binary crate, called by the `std` runtime.
    Main,
    /// `#![no_main]` entry symbol: `_start`, `__start`, or an exported C
    /// `main`.
    NoMainStart,
    /// Item marked by an entry attribute (`#[entry]`, `#[main]`, `#[start]`).
    EntryAttribute,
}

impl EntryPointKind {
    /// All entry-point kinds in declaration order.
    pub const ALL: [Self; 3] = [Self::Main, Self::NoMainStart, Self::EntryAttribute];

    /// Canonical wire identifier (`EntryPointKind.asStr` in Lean).
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Main => "main",
            Self::NoMainStart => "no_main_start",
            Self::EntryAttribute => "entry_attribute",
        }
    }
}

impl fmt::Display for EntryPointKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Facts about an item that decide whether it is a binary entry point
/// (`EntryPointDescriptor` in Lean).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EntryPointDescriptor<'a> {
    /// Crate-qualified definition path, for example `"my_crate::main"`.
    pub def_path: &'a str,
    /// The crate is compiled with `#![no_main]`.
    pub crate_no_main: bool,
    /// The item carries an entry attribute (`#[entry]`, `#[main]`, `#[start]`).
    pub has_entry_attr: bool,
    /// Exported link symbol when the item is `#[no_mangle]` or
    /// `#[export_name = "…"]`.
    pub link_symbol: Option<&'a str>,
    /// The item is an associated function or method (`Type::main`).
    pub is_assoc_fn: bool,
}

impl<'a> EntryPointDescriptor<'a> {
    /// Describes a free function at `def_path` in a default (`std` runtime)
    /// crate with no attributes.
    pub const fn new(def_path: &'a str) -> Self {
        Self {
            def_path,
            crate_no_main: false,
            has_entry_attr: false,
            link_symbol: None,
            is_assoc_fn: false,
        }
    }

    /// Sets whether the crate is compiled with `#![no_main]`.
    pub const fn with_crate_no_main(mut self, crate_no_main: bool) -> Self {
        self.crate_no_main = crate_no_main;
        self
    }

    /// Sets whether the item carries an entry attribute.
    pub const fn with_entry_attr(mut self, has_entry_attr: bool) -> Self {
        self.has_entry_attr = has_entry_attr;
        self
    }

    /// Sets the exported link symbol.
    pub const fn with_link_symbol(mut self, link_symbol: Option<&'a str>) -> Self {
        self.link_symbol = link_symbol;
        self
    }

    /// Sets whether the item is an associated function or method.
    pub const fn with_assoc_fn(mut self, is_assoc_fn: bool) -> Self {
        self.is_assoc_fn = is_assoc_fn;
        self
    }

    /// Derives [`Self::has_entry_attr`] and [`Self::link_symbol`] from the
    /// source text of the item's outer attributes, with or without the
    /// surrounding `#[…]`.
    ///
    /// `#[entry]`, `#[main]`, `#[start]` and their path-qualified forms
    /// (`#[cortex_m_rt::entry]`, `#[tokio::main]`) are entry attributes.
    /// `#[no_mangle]` exports the item under its own name, and
    /// `#[export_name = "sym"]` under `sym` (escape sequences are decoded, so
    /// `"\x5fstart"` is `_start`); an `unsafe(…)` wrapper is accepted around
    /// either.
    ///
    /// `#[cfg_attr(predicate, attr, …)]` contributes every conditional
    /// attribute: the predicate may hold in the configuration that ships, so
    /// `#[cfg_attr(not(test), no_mangle)]` exports the item. When several
    /// attributes name different link symbols, an entry symbol (`main`,
    /// `_start`, `__start`) takes precedence.
    pub fn with_attributes(mut self, attributes: &[&'a str]) -> Self {
        for attribute in attributes {
            for body in attribute_bodies(attribute) {
                self.apply_attribute(body, MAX_CFG_ATTR_DEPTH);
            }
        }
        self
    }

    /// Derives [`Self::crate_no_main`] from the source text of the crate-level
    /// attributes: `#![no_main]`, also behind `cfg_attr`
    /// (`#![cfg_attr(not(test), no_main)]`).
    pub fn with_crate_attributes(mut self, attributes: &[&str]) -> Self {
        if attributes.iter().any(|attr| is_no_main_attribute(attr)) {
            self.crate_no_main = true;
        }
        self
    }

    /// Records the link symbol `symbol`, never replacing an entry symbol by a
    /// non-entry one.
    fn export_as(&mut self, symbol: &'a str) {
        if !self.link_symbol.is_some_and(is_entry_leaf_symbol) {
            self.link_symbol = Some(symbol);
        }
    }

    /// Applies one attribute body (without `#[…]`); `fuel` bounds the nesting
    /// of `cfg_attr`.
    fn apply_attribute(&mut self, body: &'a str, fuel: usize) {
        let body = body.trim();
        if let Some(args) = cfg_attr_arguments(body) {
            // Skip the predicate, then apply every conditional attribute.
            let (_, mut rest) = split_top_level_comma(args);
            if fuel == 0 {
                // Nested too deeply to follow: assume the worst.
                self.has_entry_attr |= rest.is_some();
                return;
            }
            while let Some(attrs) = rest {
                let (attr, tail) = split_top_level_comma(attrs);
                self.apply_attribute(attr, fuel - 1);
                rest = tail;
            }
            return;
        }
        if is_entry_attribute(body) {
            self.has_entry_attr = true;
        }
        let inner = strip_unsafe_wrapper(body);
        if is_single_word(inner, "no_mangle") {
            let leaf = path_segment_count_and_leaf(self.def_path).1;
            if self.link_symbol.is_none() || is_entry_leaf_symbol(leaf) {
                self.link_symbol = Some(leaf);
            }
        } else if let Some((symbol, is_raw)) = export_name_literal(inner) {
            if is_raw || !symbol.contains('\\') {
                self.export_as(symbol);
            } else if let Some(entry) = escaped_entry_symbol(symbol) {
                self.export_as(entry);
            }
        }
    }
}

/// Maximum nesting of `cfg_attr(…, cfg_attr(…, …))` followed by
/// [`EntryPointDescriptor::with_attributes`]; deeper nests fail closed.
const MAX_CFG_ATTR_DEPTH: usize = 8;

/// Returns `true` when a crate-level attribute (with or without `#![…]`)
/// makes the crate `#![no_main]`, directly or as a conditional attribute of
/// `cfg_attr` (the predicate may hold in the configuration that ships).
pub fn is_no_main_attribute(attribute: &str) -> bool {
    fn declares_no_main(body: &str, fuel: usize) -> bool {
        let body = body.trim();
        let Some(args) = cfg_attr_arguments(body) else {
            return is_single_word(body, "no_main");
        };
        let (_, mut rest) = split_top_level_comma(args);
        if fuel == 0 {
            // Nested too deeply to follow: assume the worst.
            return rest.is_some();
        }
        while let Some(attrs) = rest {
            let (attr, tail) = split_top_level_comma(attrs);
            if declares_no_main(attr, fuel - 1) {
                return true;
            }
            rest = tail;
        }
        false
    }
    attribute_bodies(attribute).any(|body| declares_no_main(body, MAX_CFG_ATTR_DEPTH))
}

/// Skips leading Rust whitespace and comments (`//…` and nested `/*…*/`).
/// Returns `None` if an unclosed block comment is encountered.
fn strip_leading_rust_ws_and_comments(s: &str) -> Option<&str> {
    let bytes = s.as_bytes();
    let mut pos = 0usize;
    while pos < bytes.len() {
        let rest = &s[pos..];
        let first = rest.chars().next()?;
        if first.is_whitespace() {
            pos += first.len_utf8();
            continue;
        }
        if rest.starts_with("//") {
            pos += 2;
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if rest.starts_with("/*") {
            pos += 2;
            let mut depth = 1u32;
            while pos < bytes.len() && depth > 0 {
                if bytes[pos..].starts_with(b"/*") {
                    depth += 1;
                    pos += 2;
                } else if bytes[pos..].starts_with(b"*/") {
                    depth -= 1;
                    pos += 2;
                } else {
                    pos += 1;
                }
            }
            if depth > 0 {
                return None;
            }
            continue;
        }
        break;
    }
    Some(&s[pos..])
}

/// Returns `true` when `s` contains only Rust whitespace and well-formed
/// comments.
fn has_only_rust_ws_and_comments(s: &str) -> bool {
    strip_leading_rust_ws_and_comments(s).is_some_and(str::is_empty)
}

/// Returns `true` when `body` consists solely of the identifier `expected`
/// (ignoring Rust whitespace and comments).
fn is_single_word(body: &str, expected: &str) -> bool {
    let mut lexer = SpecLexer::new(body, SpecSyntax::Rust);
    matches!(lexer.next_tok(), Ok(Some(SpecTok::Word(w))) if w == expected)
        && matches!(lexer.next_tok(), Ok(None))
}

/// If `body` (ignoring Rust whitespace and comments) has the exact form
/// `<kw>(<inner>)`, returns `<inner>`.
fn unwrap_keyword_parens<'a>(body: &'a str, kw: &str) -> Option<&'a str> {
    let mut lexer = SpecLexer::new(body, SpecSyntax::Rust);
    if !matches!(lexer.next_tok(), Ok(Some(SpecTok::Word(w))) if w == kw) {
        return None;
    }
    if !matches!(lexer.next_tok(), Ok(Some(SpecTok::Sym("(")))) {
        return None;
    }
    let inner_start = lexer.pos;
    let mut depth = 1u32;
    let inner_end = loop {
        match lexer.next_tok() {
            Ok(Some(SpecTok::Sym("("))) => depth += 1,
            Ok(Some(SpecTok::Sym(")"))) => {
                depth -= 1;
                if depth == 0 {
                    break lexer.pos - 1;
                }
            }
            Ok(Some(_)) => {}
            Ok(None) | Err(_) => return None,
        }
    };
    matches!(lexer.next_tok(), Ok(None)).then_some(&body[inner_start..inner_end])
}

/// Returns the argument list of a `cfg_attr(…)` attribute body (ignoring Rust
/// whitespace and comments around `cfg_attr` and its parentheses).
fn cfg_attr_arguments(body: &str) -> Option<&str> {
    unwrap_keyword_parens(body, "cfg_attr")
}

/// Splits `args` at its first top-level comma (outside brackets and
/// literals): returns the text before it and, when there is one, the text
/// after it.
fn split_top_level_comma(args: &str) -> (&str, Option<&str>) {
    let mut lexer = SpecLexer::new(args, SpecSyntax::Rust);
    let mut depth = 0u32;
    loop {
        match lexer.next_tok() {
            Ok(Some(SpecTok::Sym("(" | "[" | "{"))) => depth += 1,
            Ok(Some(SpecTok::Sym(")" | "]" | "}"))) => depth = depth.saturating_sub(1),
            Ok(Some(SpecTok::Sym(","))) if depth == 0 => {
                // `lexer.pos` is right after the one-byte comma.
                return (&args[..lexer.pos - 1], Some(&args[lexer.pos..]));
            }
            Ok(Some(_)) => {}
            Ok(None) | Err(_) => return (args, None),
        }
    }
}

/// Returns `true` when the body of a non-raw Rust string literal decodes to
/// exactly `target` (`"\x5fstart"` and `"\u{5f}start"` decode to `_start`).
/// Malformed escapes decode to nothing.
fn escaped_literal_decodes_to(raw: &str, target: &str) -> bool {
    let mut chars = raw.chars();
    let mut expected = target.chars();
    while let Some(ch) = chars.next() {
        let decoded = if ch == '\\' {
            match chars.next() {
                Some('n') => '\n',
                Some('r') => '\r',
                Some('t') => '\t',
                Some('0') => '\0',
                Some(quoted @ ('\\' | '\'' | '"')) => quoted,
                Some('x') => {
                    let hi = chars.next().and_then(|c| c.to_digit(16));
                    let lo = chars.next().and_then(|c| c.to_digit(16));
                    match (hi, lo) {
                        (Some(hi), Some(lo)) if hi < 8 => match char::from_u32(hi * 16 + lo) {
                            Some(c) => c,
                            None => return false,
                        },
                        _ => return false,
                    }
                }
                Some('u') => {
                    if chars.next() != Some('{') {
                        return false;
                    }
                    let mut value = 0u32;
                    let mut digits = 0u32;
                    loop {
                        match chars.next() {
                            Some('}') => break,
                            Some('_') if digits > 0 => {}
                            Some(c) => match c.to_digit(16) {
                                Some(digit) if digits < 6 => {
                                    value = value * 16 + digit;
                                    digits += 1;
                                }
                                _ => return false,
                            },
                            None => return false,
                        }
                    }
                    match char::from_u32(value) {
                        Some(c) if digits > 0 => c,
                        _ => return false,
                    }
                }
                Some('\n' | '\r') => {
                    // Line continuation: the newline and the whitespace that
                    // follows it are dropped.
                    loop {
                        let mut look = chars.clone();
                        match look.next() {
                            Some(' ' | '\t' | '\n' | '\r') => chars = look,
                            _ => break,
                        }
                    }
                    continue;
                }
                _ => return false,
            }
        } else {
            ch
        };
        if expected.next() != Some(decoded) {
            return false;
        }
    }
    expected.next().is_none()
}

/// The entry link symbol an escaped string-literal body decodes to, if any.
fn escaped_entry_symbol(raw: &str) -> Option<&'static str> {
    ["main", "_start", "__start"]
        .into_iter()
        .find(|target| escaped_literal_decodes_to(raw, target))
}

/// Iterator over the bodies (the text inside `#[…]` / `#![…]`) of the
/// attributes in a source snippet; see [`attribute_bodies`].
struct AttributeBodies<'a> {
    rest: &'a str,
}

impl<'a> Iterator for AttributeBodies<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        let rest = strip_leading_rust_ws_and_comments(self.rest).unwrap_or(self.rest);
        if rest.is_empty() {
            self.rest = rest;
            return None;
        }
        let mut lexer = SpecLexer::new(rest, SpecSyntax::Rust);
        let opened = matches!(lexer.next_tok(), Ok(Some(SpecTok::Sym("#"))))
            && match lexer.next_tok() {
                Ok(Some(SpecTok::Sym("!"))) => {
                    matches!(lexer.next_tok(), Ok(Some(SpecTok::Sym("["))))
                }
                Ok(Some(SpecTok::Sym("["))) => true,
                _ => false,
            };
        if !opened {
            // A bare attribute body (`no_mangle`).
            self.rest = "";
            return Some(rest);
        }
        let body_start = lexer.pos;
        let mut depth = 1u32;
        loop {
            match lexer.next_tok() {
                Ok(Some(SpecTok::Sym("[" | "(" | "{"))) => depth += 1,
                Ok(Some(SpecTok::Sym("]" | ")" | "}"))) => {
                    depth -= 1;
                    if depth == 0 {
                        // `lexer.pos` is right after the one-byte closer.
                        let body = &rest[body_start..lexer.pos - 1];
                        self.rest = &rest[lexer.pos..];
                        return Some(body);
                    }
                }
                Ok(Some(_)) => {}
                Ok(None) | Err(_) => {
                    // Unclosed: the remainder is the body.
                    self.rest = "";
                    return Some(&rest[body_start..]);
                }
            }
        }
    }
}

/// The attribute bodies of `attribute`, the source text of one or more
/// attributes with or without the surrounding `#[…]` / `#![…]`.
///
/// Attributes are found the way the Rust lexer finds them: whitespace and
/// comments (doc comments included) may surround them and separate `#`, `!`,
/// and `[` (`# [no_mangle]`, `#[no_mangle] // exported`), and a snippet may
/// hold several (`#[inline] #[no_mangle]`).
fn attribute_bodies(attribute: &str) -> AttributeBodies<'_> {
    AttributeBodies { rest: attribute }
}

/// Strips an `unsafe(…)` attribute wrapper (`#[unsafe(no_mangle)]`), ignoring
/// Rust whitespace and comments around `unsafe` and its parentheses.
fn strip_unsafe_wrapper(body: &str) -> &str {
    unwrap_keyword_parens(body, "unsafe").unwrap_or(body)
}

/// Extracts the literal of `export_name = "sym"`, `export_name = r"sym"`, or
/// `export_name = r#"sym"#`, ignoring Rust comments around the tokens and
/// rejecting trailing non-comment tokens after it. Returns the text between
/// the quotes and whether the literal is raw (a non-raw literal may contain
/// escape sequences).
fn export_name_literal(body: &str) -> Option<(&str, bool)> {
    let mut lexer = SpecLexer::new(body, SpecSyntax::Rust);
    if !matches!(lexer.next_tok(), Ok(Some(SpecTok::Word("export_name")))) {
        return None;
    }
    if !matches!(lexer.next_tok(), Ok(Some(SpecTok::Sym("=")))) {
        return None;
    }
    let rest = strip_leading_rust_ws_and_comments(&body[lexer.pos..])?;
    if let Some(after_r) = rest.strip_prefix('r') {
        let bytes = after_r.as_bytes();
        let mut hashes = 0usize;
        while bytes.get(hashes) == Some(&b'#') {
            hashes += 1;
        }
        if bytes.get(hashes) != Some(&b'"') {
            return None;
        }
        let content_start = hashes + 1;
        let mut idx = content_start;
        while idx < bytes.len() {
            if bytes[idx] == b'"' {
                let mut closing = 0usize;
                while closing < hashes && bytes.get(idx + 1 + closing) == Some(&b'#') {
                    closing += 1;
                }
                if closing == hashes {
                    let after = &after_r[idx + 1 + hashes..];
                    return has_only_rust_ws_and_comments(after)
                        .then_some((&after_r[content_start..idx], true));
                }
            }
            idx += 1;
        }
        return None;
    }
    let rest = rest.strip_prefix('"')?;
    // Find the closing quote, stepping over escaped characters.
    let bytes = rest.as_bytes();
    let mut end = 0usize;
    loop {
        match bytes.get(end) {
            Some(b'"') => break,
            Some(b'\\') => end += 2,
            Some(_) => end += 1,
            None => return None,
        }
    }
    let after = &rest[end + 1..];
    if !has_only_rust_ws_and_comments(after) {
        return None;
    }
    Some((&rest[..end], false))
}

/// Returns `true` when the attribute (with or without `#[…]`) names an entry
/// attribute: its path ends in the segment `entry`, `main`, or `start`, either
/// directly or as a conditional attribute of `cfg_attr`.
///
/// Handles whitespace and comments around `::` (`#[cortex_m_rt :: entry]`,
/// `#[::tokio::main]`, `#[cfg_attr(not(test), entry)]`) and matches on the
/// whole final segment, so `maintain`, `entry_point`, and `restart` are not
/// entry attributes.
pub fn is_entry_attribute(attribute: &str) -> bool {
    fn is_entry_body(body: &str, fuel: usize) -> bool {
        let body = body.trim();
        if let Some(args) = cfg_attr_arguments(body) {
            let (_, mut rest) = split_top_level_comma(args);
            if fuel == 0 {
                return rest.is_some();
            }
            while let Some(attrs) = rest {
                let (attr, tail) = split_top_level_comma(attrs);
                if is_entry_body(attr, fuel - 1) {
                    return true;
                }
                rest = tail;
            }
            return false;
        }
        let mut lexer = SpecLexer::new(body, SpecSyntax::Rust);
        let mut last_segment: Option<&str> = None;
        let mut expect_segment = true;
        while let Ok(Some(tok)) = lexer.next_tok() {
            match tok {
                SpecTok::PathSep => {
                    expect_segment = true;
                }
                SpecTok::Word(word) if expect_segment => {
                    last_segment = Some(word);
                    expect_segment = false;
                }
                SpecTok::Sym("(") if !expect_segment => break,
                SpecTok::Sym("=") => return false,
                _ => return false,
            }
        }
        if expect_segment {
            return false;
        }
        matches!(last_segment, Some("entry" | "main" | "start"))
    }
    attribute_bodies(attribute).any(|body| is_entry_body(body, MAX_CFG_ATTR_DEPTH))
}

/// Number of `::`-separated segments of `path`, and its last segment.
///
/// Splits at the leftmost non-overlapping `::` occurrences, exactly as
/// `pathSegments` does in Lean; the empty path has the single segment `""`.
fn path_segment_count_and_leaf(path: &str) -> (usize, &str) {
    let mut count = 0usize;
    let mut leaf = path;
    for segment in path.split("::") {
        count += 1;
        leaf = segment;
    }
    (count, leaf)
}

/// Whether `seg` is a valid crate-root segment name (`isValidCrateSegment` in
/// Lean): non-empty, starting with an ASCII letter or `_`, containing only
/// ASCII alphanumerics, `_`, or `-`. Rejects rustc impl/trait segments such as
/// `<MyType as Trait>`, `<impl Foo>`, and `{{impl}}`.
fn is_valid_crate_segment(seg: &str) -> bool {
    let mut chars = seg.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '-')
}

/// Strips a single leading root `::` and returns `(optional_crate_segment, leaf)`
/// when the normalized path has 1 or 2 segments (`normalizeEntryPathSegments` in
/// Lean).
fn split_entry_path(def_path: &str) -> Option<(Option<&str>, &str)> {
    let stripped = def_path.strip_prefix("::").unwrap_or(def_path);
    let mut iter = stripped.split("::");
    let first = iter.next()?;
    match iter.next() {
        None => Some((None, first)),
        Some(second) => {
            if iter.next().is_some() {
                None
            } else {
                Some((Some(first), second))
            }
        }
    }
}

/// Link-level names under which a loader or C runtime transfers control to a
/// binary: `main`, `_start`, and `__start` (`isEntryLeafSymbol` in Lean).
pub fn is_entry_leaf_symbol(leaf: &str) -> bool {
    matches!(leaf, "main" | "_start" | "__start")
}

/// Name-only entry-point test (`isBinaryEntrySymbol` in Lean): `main`,
/// `::main`, `<crate>::main`, `::<crate>::main`, `_start`, `<crate>::_start`,
/// `__start`, and `<crate>::__start`.
///
/// Matching is on whole path segments with a validated crate segment, so
/// `domain`, `maintain`, `main_loop`, `<crate>::Type::main`,
/// `<MyType as Trait>::main`, `{{impl}}::main`, and `:::main` are rejected.
/// This over-approximates [`classify_entry_point`] for callers that have no
/// attribute information.
pub fn is_binary_entry_symbol(def_path: &str) -> bool {
    match split_entry_path(def_path) {
        Some((None, leaf)) => is_entry_leaf_symbol(leaf),
        Some((Some(crate_seg), leaf)) => {
            is_valid_crate_segment(crate_seg) && is_entry_leaf_symbol(leaf)
        }
        None => false,
    }
}

/// Classifies a crate-root item by its leaf name (`classifyEntryLeaf` in
/// Lean): `main` is always an entry point, and `_start` / `__start` are entry
/// points under `#![no_main]`.
fn classify_entry_leaf(leaf: &str, crate_no_main: bool) -> Option<EntryPointKind> {
    if leaf == "main" {
        Some(if crate_no_main {
            EntryPointKind::NoMainStart
        } else {
            EntryPointKind::Main
        })
    } else if crate_no_main && (leaf == "_start" || leaf == "__start") {
        Some(EntryPointKind::NoMainStart)
    } else {
        None
    }
}

/// Classifies an item by its definition path alone (`classifyEntryPath` in
/// Lean): only crate-root items (`leaf`, `::leaf`, `<crate>::leaf`,
/// `::<crate>::leaf` with a valid crate segment) can be entry points.
pub fn classify_entry_path(def_path: &str, crate_no_main: bool) -> Option<EntryPointKind> {
    match split_entry_path(def_path) {
        Some((None, leaf)) => classify_entry_leaf(leaf, crate_no_main),
        Some((Some(crate_seg), leaf)) if is_valid_crate_segment(crate_seg) => {
            classify_entry_leaf(leaf, crate_no_main)
        }
        _ => None,
    }
}

/// Classifies an item as a binary entry point (`classifyEntryPoint` in Lean):
///
/// 1. an associated function is an entry point only when it is exported
///    under the link symbol `main`, `_start`, or `__start` (the linker does
///    not see Rust namespaces); its path and attributes never make it one;
/// 2. an entry attribute makes the item an [`EntryPointKind::EntryAttribute`]
///    entry point;
/// 3. an exported link symbol `main`, `_start`, or `__start` is an
///    [`EntryPointKind::NoMainStart`] entry point;
/// 4. otherwise the crate-root items `main` (always) and `_start` / `__start`
///    (under `#![no_main]`) are entry points.
pub fn classify_entry_point(desc: &EntryPointDescriptor<'_>) -> Option<EntryPointKind> {
    let exported_entry_symbol = desc.link_symbol.is_some_and(is_entry_leaf_symbol);
    if desc.is_assoc_fn {
        return exported_entry_symbol.then_some(EntryPointKind::NoMainStart);
    }
    if desc.has_entry_attr {
        return Some(EntryPointKind::EntryAttribute);
    }
    if exported_entry_symbol {
        return Some(EntryPointKind::NoMainStart);
    }
    classify_entry_path(desc.def_path, desc.crate_no_main)
}

/// Maximum bracket nesting accepted by the trivial-`requires` scanner; deeper
/// nesting fails closed.
const MAX_TRIVIAL_REQUIRES_DEPTH: usize = 32;

/// Strict form of [`is_syntactically_trivial_requires_in`]: reports malformed
/// source instead of folding it into `false`.
pub fn scan_trivial_requires(src: &str, syntax: SpecSyntax) -> Result<bool, SpecScanError> {
    let mut lexer = SpecLexer::new(src, syntax);
    let mut stack = [0u8; MAX_TRIVIAL_REQUIRES_DEPTH];
    let mut depth = 0usize;
    // True while the grammar expects a value: at the start, after an opening
    // bracket, and after a comma.
    let mut expect_value = true;
    let mut seen_any = false;
    while let Some(tok) = lexer.next_tok()? {
        seen_any = true;
        match tok {
            SpecTok::Word(word)
                if matches!(
                    (syntax, word),
                    (SpecSyntax::Rust, "true")
                        | (SpecSyntax::Lean, "True")
                        | (SpecSyntax::Any, "true" | "True")
                ) =>
            {
                if !expect_value {
                    return Ok(false);
                }
                expect_value = false;
            }
            SpecTok::Sym(open @ ("(" | "[")) => {
                if !expect_value || depth == MAX_TRIVIAL_REQUIRES_DEPTH {
                    return Ok(false);
                }
                stack[depth] = open.as_bytes()[0];
                depth += 1;
            }
            SpecTok::Sym(")") => {
                // A parenthesized value: `()` is the unit value, not `true`.
                if depth == 0 || stack[depth - 1] != b'(' || expect_value {
                    return Ok(false);
                }
                depth -= 1;
            }
            SpecTok::Sym("]") => {
                // A list may be empty and may end in a trailing comma.
                if depth == 0 || stack[depth - 1] != b'[' {
                    return Ok(false);
                }
                depth -= 1;
                expect_value = false;
            }
            SpecTok::Sym(",") => {
                if depth == 0 || stack[depth - 1] != b'[' || expect_value {
                    return Ok(false);
                }
                expect_value = true;
            }
            _ => return Ok(false),
        }
    }
    Ok(depth == 0 && (!seen_any || !expect_value))
}

/// Returns `true` iff the `requires` source `src` in dialect `syntax` is
/// syntactically trivial: empty, `true` (Lean `True`), a parenthesized trivial
/// clause, or a list `[…]` of trivial clauses.
///
/// Comments are ignored. Any other token, including a string literal or an
/// operator, makes the clause non-trivial, and malformed source (an unclosed
/// comment or literal, unbalanced brackets) fails closed with `false`.
pub fn is_syntactically_trivial_requires_in(src: &str, syntax: SpecSyntax) -> bool {
    matches!(scan_trivial_requires(src, syntax), Ok(true))
}

/// [`is_syntactically_trivial_requires_in`] for source of unknown dialect
/// ([`SpecSyntax::Any`]): Rust and Lean comments are both ignored.
pub fn is_syntactically_trivial_requires(src: &str) -> bool {
    is_syntactically_trivial_requires_in(src, SpecSyntax::Any)
}

/// An authored `requires` clause together with its source dialect.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RequiresClause<'a> {
    /// Source text of the clause, without the `requires:` keyword.
    pub source: &'a str,
    /// Dialect the clause is written in.
    pub syntax: SpecSyntax,
}

impl<'a> RequiresClause<'a> {
    /// A Rust `requires` clause (`#[spec(requires: …)]`).
    pub const fn rust(source: &'a str) -> Self {
        Self {
            source,
            syntax: SpecSyntax::Rust,
        }
    }

    /// A Lean precondition body (`def pre … : Prop := …`).
    pub const fn lean(source: &'a str) -> Self {
        Self {
            source,
            syntax: SpecSyntax::Lean,
        }
    }

    /// A clause of unknown dialect.
    pub const fn any(source: &'a str) -> Self {
        Self {
            source,
            syntax: SpecSyntax::Any,
        }
    }

    /// See [`is_syntactically_trivial_requires_in`].
    pub fn is_syntactically_trivial(&self) -> bool {
        is_syntactically_trivial_requires_in(self.source, self.syntax)
    }
}

/// Why the entry-point `requires` guard rejected an entry point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EntryPointGuardViolationKind {
    /// The entry point carries an authored `requires` clause that is not
    /// syntactically trivial (or whose source is malformed).
    ExplicitNonTrivialRequires,
    /// The precondition rejected the ABI-admissible input sampled at
    /// `trial_idx`.
    PreconditionRejectedInput { trial_idx: usize },
    /// The precondition trapped on the input sampled at `trial_idx`.
    PreconditionTrapped { trial_idx: usize },
    /// `max_trials == 0`: no input was sampled (fail-closed).
    DegenerateConfig,
}

/// Structured report of an entry-point `requires` guard violation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EntryPointGuardViolation {
    /// Always [`SpecBoundaryGuardClass::EntryPointPrecondition`].
    pub guard: SpecBoundaryGuardClass,
    /// How the item was classified as an entry point.
    pub entry_kind: EntryPointKind,
    /// What the guard found.
    pub kind: EntryPointGuardViolationKind,
    /// Number of inputs sampled before the violation.
    pub trials_run: usize,
    /// Number of sampled inputs the precondition admitted.
    pub precondition_hits: usize,
}

impl EntryPointGuardViolation {
    /// Frozen vacuity class of the violation
    /// ([`VacuityClass::DeadPrecondition`]).
    pub const fn vacuity_class(&self) -> VacuityClass {
        self.guard.to_vacuity_class()
    }

    /// Index of the sampled input the precondition rejected or trapped on.
    /// Pass it to [`replay_trial_input`] with the same [`SpecCheckConfig`] to
    /// reconstruct the excluded ABI-admissible input.
    pub const fn counterexample_trial(&self) -> Option<usize> {
        match self.kind {
            EntryPointGuardViolationKind::PreconditionRejectedInput { trial_idx }
            | EntryPointGuardViolationKind::PreconditionTrapped { trial_idx } => Some(trial_idx),
            EntryPointGuardViolationKind::ExplicitNonTrivialRequires
            | EntryPointGuardViolationKind::DegenerateConfig => None,
        }
    }
}

/// Outcome of the entry-point `requires` guard.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EntryPointGuardOutcome {
    /// The item is not a binary entry point; the guard does not apply and the
    /// precondition was not evaluated.
    NotEntryPoint,
    /// The item is an entry point whose precondition held, without trapping,
    /// on every sampled ABI-admissible input.
    Guarded {
        /// How the item was classified as an entry point.
        entry_kind: EntryPointKind,
        /// Number of inputs sampled.
        trials_run: usize,
    },
    /// The item is an entry point that violates the guard.
    Violation(EntryPointGuardViolation),
}

impl EntryPointGuardOutcome {
    /// Returns `true` iff the guard found no violation.
    pub const fn passes(&self) -> bool {
        !matches!(self, Self::Violation(_))
    }

    /// Returns the violation, if any.
    pub const fn violation(&self) -> Option<&EntryPointGuardViolation> {
        match self {
            Self::Violation(violation) => Some(violation),
            Self::NotEntryPoint | Self::Guarded { .. } => None,
        }
    }

    /// Returns the guard class of the violation, if any.
    pub const fn guard_class(&self) -> Option<SpecBoundaryGuardClass> {
        match self {
            Self::Violation(violation) => Some(violation.guard),
            Self::NotEntryPoint | Self::Guarded { .. } => None,
        }
    }

    /// Converts the outcome into a `Result` carrying the entry-point kind
    /// (`None` when the item is not an entry point).
    pub const fn into_result(self) -> Result<Option<EntryPointKind>, EntryPointGuardViolation> {
        match self {
            Self::NotEntryPoint => Ok(None),
            Self::Guarded { entry_kind, .. } => Ok(Some(entry_kind)),
            Self::Violation(violation) => Err(violation),
        }
    }
}

/// Checks the entry-point `requires` guard with a precondition that may trap.
///
/// The input type `I` models the loader ABI: every value [`SampleInput`]
/// produces is an initial state the operating system, C runtime, or reset
/// vector may start the entry point in. The guard:
///
/// 1. returns [`EntryPointGuardOutcome::NotEntryPoint`] unless
///    [`classify_entry_point`] accepts `desc`;
/// 2. rejects an authored `requires` clause that is not syntactically trivial;
/// 3. fails closed on `config.max_trials == 0`;
/// 4. samples trials `0..config.max_trials` from the same stream as
///    [`check_contract`] and requires `pre` to return `Ok(true)` on every one
///    of them. A single rejected input or trap is a violation.
///
/// Only `config.seed` and `config.max_trials` are consulted.
pub fn check_entry_point_requires_fallible<I, Pre>(
    config: SpecCheckConfig,
    desc: &EntryPointDescriptor<'_>,
    requires: Option<RequiresClause<'_>>,
    mut pre: Pre,
) -> EntryPointGuardOutcome
where
    I: SampleInput,
    Pre: FnMut(&I) -> Result<bool, ()>,
{
    let Some(entry_kind) = classify_entry_point(desc) else {
        return EntryPointGuardOutcome::NotEntryPoint;
    };
    let violation = |kind, trials_run, precondition_hits| {
        EntryPointGuardOutcome::Violation(EntryPointGuardViolation {
            guard: SpecBoundaryGuardClass::EntryPointPrecondition,
            entry_kind,
            kind,
            trials_run,
            precondition_hits,
        })
    };

    if let Some(clause) = requires
        && !clause.is_syntactically_trivial()
    {
        return violation(
            EntryPointGuardViolationKind::ExplicitNonTrivialRequires,
            0,
            0,
        );
    }
    if config.max_trials == 0 {
        return violation(EntryPointGuardViolationKind::DegenerateConfig, 0, 0);
    }

    let (mut rng, _) = stateless_streams(config.seed);
    let mut precondition_hits = 0usize;
    for trial_idx in 0..config.max_trials {
        let input = I::sample_at(trial_idx, &mut rng);
        match pre(&input) {
            Ok(true) => precondition_hits += 1,
            Ok(false) => {
                return violation(
                    EntryPointGuardViolationKind::PreconditionRejectedInput { trial_idx },
                    trial_idx + 1,
                    precondition_hits,
                );
            }
            Err(()) => {
                return violation(
                    EntryPointGuardViolationKind::PreconditionTrapped { trial_idx },
                    trial_idx + 1,
                    precondition_hits,
                );
            }
        }
    }
    EntryPointGuardOutcome::Guarded {
        entry_kind,
        trials_run: config.max_trials,
    }
}

/// Checks the entry-point `requires` guard with an infallible precondition.
/// See [`check_entry_point_requires_fallible`].
pub fn check_entry_point_requires<I, Pre>(
    config: SpecCheckConfig,
    desc: &EntryPointDescriptor<'_>,
    requires: Option<RequiresClause<'_>>,
    mut pre: Pre,
) -> EntryPointGuardOutcome
where
    I: SampleInput,
    Pre: FnMut(&I) -> bool,
{
    check_entry_point_requires_fallible(config, desc, requires, |input: &I| Ok(pre(input)))
}

// ----------------------------------------------------------------------------
// Guard 3: error-branch `true` wildcard (`awsm2`)
// ----------------------------------------------------------------------------

/// Four-branch semantic outcome of a fallible computation
/// (`FallibleOutcome` in Lean).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SemanticOutcome<T, E> {
    /// Successful completion with a value.
    Ok(T),
    /// Domain error with a payload.
    Err(E),
    /// Undefined behavior.
    Ub,
    /// Unsupported, fail-closed construct.
    Unsupported,
}

impl<T, E> SemanticOutcome<T, E> {
    /// Embeds a `Result`.
    pub fn from_result(result: Result<T, E>) -> Self {
        match result {
            Ok(value) => Self::Ok(value),
            Err(error) => Self::Err(error),
        }
    }

    /// Projects back to a `Result`; `None` for [`Self::Ub`] and
    /// [`Self::Unsupported`].
    pub fn into_result(self) -> Option<Result<T, E>> {
        match self {
            Self::Ok(value) => Some(Ok(value)),
            Self::Err(error) => Some(Err(error)),
            Self::Ub | Self::Unsupported => None,
        }
    }

    /// Which of the four branches this outcome is.
    pub const fn branch(&self) -> OutcomeBranch {
        match self {
            Self::Ok(_) => OutcomeBranch::Ok,
            Self::Err(_) => OutcomeBranch::Err,
            Self::Ub => OutcomeBranch::Ub,
            Self::Unsupported => OutcomeBranch::Unsupported,
        }
    }

    /// Returns `true` for the operational faults [`Self::Ub`] and
    /// [`Self::Unsupported`].
    pub const fn is_fault(&self) -> bool {
        matches!(self, Self::Ub | Self::Unsupported)
    }
}

impl<T, E> From<Result<T, E>> for SemanticOutcome<T, E> {
    fn from(result: Result<T, E>) -> Self {
        Self::from_result(result)
    }
}

impl<T: SampleInput, E: SampleInput> SampleInput for SemanticOutcome<T, E> {
    const BOUNDARY_COUNT: usize = <Result<T, E> as SampleInput>::BOUNDARY_COUNT.saturating_add(2);

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        let result_count = <Result<T, E> as SampleInput>::BOUNDARY_COUNT;
        if trial_idx < result_count {
            Self::from_result(<Result<T, E>>::sample_at(trial_idx, rng))
        } else if trial_idx == result_count {
            Self::Ub
        } else if trial_idx == result_count.saturating_add(1) {
            Self::Unsupported
        } else {
            match rng.next_u64() & 7 {
                0 => Self::Ub,
                1 => Self::Unsupported,
                _ => Self::from_result(<Result<T, E>>::sample_at(trial_idx.max(result_count), rng)),
            }
        }
    }
}

impl<T: SampleInput + ReturnMutants, E: SampleInput + ReturnMutants> ReturnMutants
    for SemanticOutcome<T, E>
{
    // `Ub` and `Unsupported` are always two distinct inhabitants.
    const IS_SUBSINGLETON: bool = false;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        let mut flip_rng = rng.fork();
        match self {
            Self::Ok(value) => {
                let mut emitted_flips = false;
                if !T::IS_SUBSINGLETON {
                    value.visit_mutants(rng, |mutant| {
                        emit(Self::Ok(mutant));
                        if !emitted_flips {
                            emitted_flips = true;
                            // Emit the fault and error flips right after the
                            // first payload mutant so small budgets test
                            // every branch.
                            emit(Self::Ub);
                            emit(Self::Unsupported);
                            emit_variant_flip_samples(&mut flip_rng, Self::Err, &mut emit);
                        }
                    });
                }
                if !emitted_flips {
                    emit(Self::Ub);
                    emit(Self::Unsupported);
                    emit_variant_flip_samples(&mut flip_rng, Self::Err, &mut emit);
                }
            }
            Self::Err(error) => {
                let mut emitted_flips = false;
                if !E::IS_SUBSINGLETON {
                    error.visit_mutants(rng, |mutant| {
                        emit(Self::Err(mutant));
                        if !emitted_flips {
                            emitted_flips = true;
                            emit(Self::Ub);
                            emit(Self::Unsupported);
                            emit_variant_flip_samples(&mut flip_rng, Self::Ok, &mut emit);
                        }
                    });
                }
                if !emitted_flips {
                    emit(Self::Ub);
                    emit(Self::Unsupported);
                    emit_variant_flip_samples(&mut flip_rng, Self::Ok, &mut emit);
                }
            }
            Self::Ub => {
                emit(Self::Unsupported);
                emit_variant_flip_samples(&mut flip_rng, Self::Ok, &mut emit);
                emit_variant_flip_samples(&mut flip_rng, Self::Err, &mut emit);
            }
            Self::Unsupported => {
                emit(Self::Ub);
                emit_variant_flip_samples(&mut flip_rng, Self::Ok, &mut emit);
                emit_variant_flip_samples(&mut flip_rng, Self::Err, &mut emit);
            }
        }
    }
}

/// Branch of a fallible outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutcomeBranch {
    /// Successful completion.
    Ok,
    /// Domain error.
    Err,
    /// Undefined behavior.
    Ub,
    /// Unsupported construct.
    Unsupported,
}

/// Outcome types whose error and fault branches the error-branch wildcard
/// probes can construct and inspect: `Result<T, E>` and
/// [`SemanticOutcome<T, E>`].
pub trait ErrorBranchOutcome: Sized {
    /// Error payload type.
    type Error;

    /// Which branch this outcome is.
    fn branch(&self) -> OutcomeBranch;

    /// The error payload of an error outcome.
    fn error_payload(&self) -> Option<&Self::Error>;

    /// Builds the error outcome carrying `error`.
    fn from_error(error: Self::Error) -> Self;

    /// The undefined-behavior outcome, when the type has one.
    fn ub() -> Option<Self>;

    /// The unsupported-construct outcome, when the type has one.
    fn unsupported() -> Option<Self>;
}

impl<T, E> ErrorBranchOutcome for Result<T, E> {
    type Error = E;

    fn branch(&self) -> OutcomeBranch {
        match self {
            Ok(_) => OutcomeBranch::Ok,
            Err(_) => OutcomeBranch::Err,
        }
    }

    fn error_payload(&self) -> Option<&E> {
        self.as_ref().err()
    }

    fn from_error(error: E) -> Self {
        Err(error)
    }

    fn ub() -> Option<Self> {
        None
    }

    fn unsupported() -> Option<Self> {
        None
    }
}

impl<T, E> ErrorBranchOutcome for SemanticOutcome<T, E> {
    type Error = E;

    fn branch(&self) -> OutcomeBranch {
        SemanticOutcome::branch(self)
    }

    fn error_payload(&self) -> Option<&E> {
        match self {
            Self::Err(error) => Some(error),
            Self::Ok(_) | Self::Ub | Self::Unsupported => None,
        }
    }

    fn from_error(error: E) -> Self {
        Self::Err(error)
    }

    fn ub() -> Option<Self> {
        Some(Self::Ub)
    }

    fn unsupported() -> Option<Self> {
        Some(Self::Unsupported)
    }
}

/// Syntactic shape of an error-branch wildcard found in postcondition source.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ErrorWildcardPattern {
    /// A match arm accepting every error payload: `Err(_) => true`,
    /// `Err(..) => true`, `Err(e) => true`, `| Err _ => True`,
    /// `| .err _ => True`, `| .error _ => True`.
    ErrArmTrue,
    /// A match arm accepting undefined behavior: `| .ub => True`,
    /// `| .fail .ub => True`, `| .fail _ => True`, `Ub => true`.
    UbArmTrue,
    /// A match arm accepting an unsupported construct:
    /// `| .unsupported => True`, `Unsupported => true`.
    UnsupportedArmTrue,
    /// A `matches!` whose pattern accepts every error payload:
    /// `matches!(out, Ok(_) | Err(_))`.
    MatchesAnyErr,
    /// A catch-all arm `_ => true` in a postcondition that also matches an
    /// `Ok` constructor, so the catch-all covers the error branches.
    CatchAllArmTrue,
    /// The source is malformed (an unclosed comment or literal): the scanner
    /// cannot tell code from text and fails closed.
    UnclosedLiteralOrComment,
}

impl ErrorWildcardPattern {
    /// Short wire identifier of the pattern.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ErrArmTrue => "err_arm_true",
            Self::UbArmTrue => "ub_arm_true",
            Self::UnsupportedArmTrue => "unsupported_arm_true",
            Self::MatchesAnyErr => "matches_any_err",
            Self::CatchAllArmTrue => "catch_all_arm_true",
            Self::UnclosedLiteralOrComment => "unclosed_literal_or_comment",
        }
    }

    /// The guard class every pattern reports under
    /// ([`SpecBoundaryGuardClass::ErrorBranchWildcard`]).
    pub const fn guard_class(self) -> SpecBoundaryGuardClass {
        SpecBoundaryGuardClass::ErrorBranchWildcard
    }
}

impl fmt::Display for ErrorWildcardPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Error-like constructor an arm alternative accepts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ErrorCtor {
    /// `Err`, `.err`, `.error`.
    Err,
    /// `Ub`, `.ub`.
    Ub,
    /// `Unsupported`, `.unsupported`.
    Unsupported,
    /// `.fail`: every failure kind, undefined behavior included.
    Fail,
}

impl ErrorCtor {
    /// Recognizes an error constructor. Capitalized names stand on their own
    /// (`Err`, `Result::Err`, `SemanticOutcome::Ub`); lowercase names are
    /// constructors only in dotted position (`.err`, `Except.error`), since a
    /// bare lowercase word is a variable.
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

    const fn pattern(self) -> ErrorWildcardPattern {
        match self {
            Self::Err => ErrorWildcardPattern::ErrArmTrue,
            Self::Ub | Self::Fail => ErrorWildcardPattern::UbArmTrue,
            Self::Unsupported => ErrorWildcardPattern::UnsupportedArmTrue,
        }
    }
}

/// Returns `true` when `word`, appearing as an error payload, binds or ignores
/// the payload instead of constraining it: `_`, `_e`, `e`, `ref`, `mut`.
/// Capitalized names (constructors, types), numeric literals, and the boolean
/// literals constrain it.
fn is_wildcard_payload_word(word: &str) -> bool {
    if matches!(word, "true" | "false") {
        return false;
    }
    match word.chars().next() {
        Some(first) => first == '_' || (!first.is_uppercase() && !first.is_numeric()),
        None => true,
    }
}

/// Returns `true` when `word`, standing alone as a pattern alternative, binds
/// every value: `_`, `_rest`, `e`, `other`. Capitalized names (constructors,
/// constants), numeric and boolean literals, and the lowercase Lean
/// constructors of `Option`, `List`, `Nat`, and `Unit` are specific patterns.
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

/// One pattern alternative of a match arm (the text between two `|`), or the
/// arm body that follows `=>`.
#[derive(Clone, Copy, Debug, Default)]
struct ArmAlternative {
    /// Brackets opened and not yet closed around the scan position.
    depth: u32,
    /// Bracket depth at which this match arm's pattern began (e.g. `1` inside
    /// `(match r with | …)`).
    arm_base_depth: u32,
    /// Number of outer grouping parentheses `(` opened around a catch-all
    /// pattern (`(_)`, `((e))`, `(_ : T)`).
    catch_all_parens: u32,
    /// Number of tokens.
    tokens: u32,
    /// The alternative is exactly a catch-all so far: `_`, a bare binding
    /// (`e`, `other`), or a binding behind `&` / `ref` / `mut` / `(...)` /
    /// Lean type ascription `(_ : T)`.
    catch_all: bool,
    /// Every token so far is a `&` / `ref` / `mut` / `(` catch-all modifier.
    only_modifiers: bool,
    /// Innermost error constructor seen.
    error_ctor: Option<ErrorCtor>,
    /// Bracket depth at which `error_ctor` was encountered.
    error_ctor_depth: Option<u32>,
    /// The error payload is constrained (a constructor, literal, or path).
    constrained: bool,
    /// Bracket depth of a Lean type ascription `(_ : Type)` inside an
    /// unconstrained error payload or catch-all; tokens at `depth >= d` are
    /// type syntax.
    type_ascription_depth: Option<u32>,
    /// The alternative began right after `=>`: it is an arm body, not a
    /// pattern.
    after_arrow: bool,
    /// Bracket depth at which the arm body began. A `|` at this depth ends
    /// the body and starts the next arm; a deeper `|` belongs to the body
    /// (`(a ||| b)`, a Rust closure `|x| …`).
    body_depth: u32,
    /// Scanning a Lean `fun … =>` / `λ … =>` lambda binder list rather than a
    /// match arm.
    in_lambda: bool,
    /// Bracket depth just inside the outermost struct-pattern brace around
    /// the scan position (`W { r: Err(_) }`, Lean `{ val := .err _ }`); a
    /// `:=` at or below it separates a field from its pattern.
    struct_pattern_depth: Option<u32>,
    /// An earlier `|` alternative of the current component of a
    /// parenthesized catch-all candidate was a catch-all (`(_ | 0)`).
    or_wild: bool,
    /// A `,` was seen directly inside the outer catch-all parentheses: the
    /// candidate is a tuple (`(_, _)`).
    tuple_started: bool,
    /// Every completed component of that tuple was a catch-all.
    tuple_wild: bool,
}

impl ArmAlternative {
    /// A fresh pattern alternative starting a new arm at bracket depth `depth`.
    fn pattern(depth: u32) -> Self {
        Self {
            depth,
            arm_base_depth: depth,
            ..Self::default()
        }
    }

    /// The next `|` / sibling alternative inside the same arm, preserving the
    /// arm's base depth, the enclosing struct pattern, and `catch_all_parens`
    /// outer catch-all parentheses.
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

    /// An arm body beginning at bracket depth `depth`.
    fn body(depth: u32) -> Self {
        Self {
            depth,
            arm_base_depth: depth,
            after_arrow: true,
            body_depth: depth,
            ..Self::default()
        }
    }

    /// Records a pattern token that is not an identifier.
    fn push_non_word(&mut self) {
        self.tokens += 1;
        self.catch_all = false;
        self.only_modifiers = false;
    }
}

/// Accumulated facts about the alternatives of the arm being scanned.
#[derive(Clone, Copy, Debug, Default)]
struct ArmState {
    /// First alternative that accepts an error constructor with an
    /// unconstrained payload.
    wildcard: Option<ErrorCtor>,
    /// Some alternative is a catch-all (`_` or a bare binding).
    catch_all: bool,
    /// A Rust `if` guard follows the pattern.
    guarded: bool,
    /// Number of guard tokens.
    guard_tokens: u32,
    /// The guard is the literal `true`.
    guard_trivial: bool,
}

impl ArmState {
    fn absorb(&mut self, alt: &ArmAlternative) {
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

    const fn guard_blocks(&self) -> bool {
        self.guarded && !(self.guard_tokens == 1 && self.guard_trivial)
    }
}

/// Kind of a scope tracked for [`ErrorWildcardPattern::CatchAllArmTrue`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OkScopeKind {
    /// A `{ … }` block; `saved_depth` is the bracket depth around it,
    /// restored when the block closes.
    Brace { saved_depth: u32 },
    /// The arms of a Lean `match … with` opened at bracket depth `depth`.
    /// A Lean match has no terminator: its arms extend to the bracket
    /// closing that depth, to the brace closing the enclosing block, or to
    /// the next declaration.
    LeanMatch { depth: u32 },
}

/// One entry of [`OkScopes`].
#[derive(Clone, Copy, Debug)]
struct OkScope {
    kind: OkScopeKind,
    /// The scope matched an `Ok` constructor.
    saw_ok: bool,
}

/// Maximum nested `{ … }` / Lean `match … with` scopes tracked for
/// `CatchAllArmTrue`.
const MAX_OK_SCOPE_DEPTH: usize = 32;

/// Fixed-capacity stack of the scopes enclosing the scan position. A
/// catch-all arm is an error wildcard only when its own scope also matches an
/// `Ok` constructor, so an inner `match n { 0 => false, _ => true }` never
/// inherits the `Ok` of the result match around it.
#[derive(Clone, Copy, Debug)]
struct OkScopes {
    /// `saw_ok` of the outermost (unbracketed) scope.
    root_saw_ok: bool,
    stack: [OkScope; MAX_OK_SCOPE_DEPTH],
    len: usize,
    /// Brace scopes opened beyond the capacity of `stack`.
    overflow: u32,
}

impl OkScopes {
    const fn new() -> Self {
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

    /// Records an `Ok` constructor in the innermost scope.
    fn mark_ok(&mut self) {
        if self.overflow > 0 {
            return;
        }
        match self.len {
            0 => self.root_saw_ok = true,
            len => self.stack[len - 1].saw_ok = true,
        }
    }

    /// Whether the innermost scope matched an `Ok` constructor. Scopes nested
    /// beyond the tracked capacity answer `true` (fail closed).
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

    /// Closes the innermost brace scope above `floor`, together with the Lean
    /// matches opened inside it, and returns the bracket depth to restore.
    /// Returns `None` when no brace scope is open above `floor`.
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

    /// Closes the innermost Lean matches opened at a bracket depth of at
    /// least `min_depth`.
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

    /// A new top-level declaration begins: every open Lean match ends, and
    /// the outermost scope forgets the `Ok` of the previous declaration.
    fn begin_declaration(&mut self) {
        self.close_lean_matches(0);
        if self.len == 0 && self.overflow == 0 {
            self.root_saw_ok = false;
        }
    }
}

/// Position of the scanner relative to a `matches!(scrutinee, pattern)` call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MatchesState {
    /// Not inside a `matches!` call.
    Outside,
    /// Inside the scrutinee expression, at bracket depth `depth`.
    Scrutinee { depth: u32 },
    /// Inside the pattern.
    Pattern,
}

/// Returns `true` when the operator following a trivially true arm body
/// combines it into a body that is no longer trivially true (`true && p`,
/// `True ∧ P`, `True → P`, `true == p`).
fn is_constraining_continuation(tok: SpecTok<'_>) -> bool {
    match tok {
        SpecTok::Sym(sym) => matches!(
            sym,
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
        SpecTok::PathSep | SpecTok::DotDot => true,
        SpecTok::Word(word) => matches!(word, "as" | "and"),
        SpecTok::Literal | SpecTok::FatArrow => false,
    }
}

/// Maximum number of `&&` / `∧` terms unfolded in a trivially-true arm body.
const MAX_TRIVIAL_CONJUNCTS: usize = 8;

/// Maximum nesting of parenthesized / braced expressions inspected inside a
/// trivially-true arm body.
const MAX_TRIVIAL_EXPR_DEPTH: u32 = 8;

/// Maximum tokens scanned while inspecting disjunctions inside an arm body.
const MAX_ARM_BODY_SCAN_TOKENS: usize = 128;

fn is_disjunction_tok(tok: SpecTok<'_>) -> bool {
    matches!(tok, SpecTok::Sym("||" | "∨" | "\\/") | SpecTok::Word("or"))
}

fn is_conjunction_tok(tok: SpecTok<'_>) -> bool {
    matches!(tok, SpecTok::Sym("&&" | "∧" | "/\\") | SpecTok::Word("and"))
}

fn is_looser_than_disjunction(tok: SpecTok<'_>) -> bool {
    matches!(tok, SpecTok::Sym("->" | "→" | "↔" | "<->" | "==>"))
}

/// Whether `tok` (followed by `next`) ends an arm body that no bracket
/// closes: the next arm, a statement or item boundary, or the next top-level
/// command of a Lean module (`#eval …`, `@[simp] theorem …`, `namespace …`).
/// Scanning past it would attribute unrelated code to the arm.
fn is_arm_body_terminator(tok: SpecTok<'_>, next: Option<SpecTok<'_>>) -> bool {
    match tok {
        SpecTok::FatArrow => true,
        SpecTok::Sym("," | "|" | ";" | ")" | "]" | "}" | "#") => true,
        SpecTok::Sym("@") => matches!(next, Some(SpecTok::Sym("["))),
        SpecTok::Word(word) => {
            is_lean_decl_reset_word(word)
                || matches!(
                    word,
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
/// a later disjunction belongs to that construct, not to the whole body, so
/// `if c then False else P ∨ True` is not a disjunction with `True`.
fn extends_to_the_right(tok: SpecTok<'_>) -> bool {
    matches!(
        tok,
        SpecTok::Word(
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
        ) | SpecTok::Sym("∀" | "∃" | "Σ" | "∑" | "∏")
    )
}

/// Consumes one trivially-true boolean/Prop atom (`true`, `True`, `trivial`,
/// `!false`, `¬False`, `Not False`, or a parenthesized/braced trivially-true
/// expression, optionally preceded by `return`/`by` and followed by `as bool`).
/// Returns `Ok(true)` iff such an atom was consumed; `look` is left right
/// after it.
fn consume_trivial_true_atom(look: &mut SpecLexer<'_>, depth: u32) -> Result<bool, SpecScanError> {
    if depth == 0 {
        return Ok(false);
    }
    let mut probe = *look;
    let mut tok = probe.next_tok()?;
    while matches!(tok, Some(SpecTok::Word("return" | "by"))) {
        tok = probe.next_tok()?;
    }
    let matched = match tok {
        Some(SpecTok::Sym("(")) => expr_is_trivially_true(&mut probe, Some(")"), depth - 1)?,
        Some(SpecTok::Sym("{")) => expr_is_trivially_true(&mut probe, Some("}"), depth - 1)?,
        Some(SpecTok::Word("true" | "True" | "trivial")) => true,
        Some(SpecTok::Sym("!")) => matches!(probe.next_tok()?, Some(SpecTok::Word("false"))),
        Some(SpecTok::Sym("¬") | SpecTok::Word("Not")) => {
            matches!(probe.next_tok()?, Some(SpecTok::Word("False")))
        }
        _ => false,
    };
    if !matched {
        return Ok(false);
    }
    // Consume an optional `as bool` cast.
    let mut cast_probe = probe;
    if matches!(cast_probe.next_tok()?, Some(SpecTok::Word("as")))
        && matches!(cast_probe.next_tok()?, Some(SpecTok::Word("bool")))
    {
        probe = cast_probe;
    }
    *look = probe;
    Ok(true)
}

/// Consumes a conjunction of trivially-true atoms (`true && true`,
/// `(True ∧ True)`, optionally followed by `as bool` or a parenthesized
/// `: Prop` / `: Bool` ascription) that is not continued by a constraining
/// operator.
fn consume_trivial_conjunction(
    look: &mut SpecLexer<'_>,
    allow_type_ascription: bool,
    depth: u32,
) -> Result<bool, SpecScanError> {
    let mut probe = *look;
    if !consume_trivial_true_atom(&mut probe, depth)? {
        return Ok(false);
    }
    for _ in 0..MAX_TRIVIAL_CONJUNCTS {
        let mut next_probe = probe;
        let next = next_probe.next_tok()?;
        match next {
            Some(tok) if is_conjunction_tok(tok) => {
                if !consume_trivial_true_atom(&mut next_probe, depth)? {
                    return Ok(false);
                }
                probe = next_probe;
            }
            Some(SpecTok::Word("as")) => {
                if matches!(next_probe.next_tok()?, Some(SpecTok::Word("bool"))) {
                    probe = next_probe;
                } else {
                    return Ok(false);
                }
            }
            Some(SpecTok::Sym(":")) if allow_type_ascription => {
                if matches!(
                    next_probe.next_tok()?,
                    Some(SpecTok::Word("Prop" | "Bool" | "bool"))
                ) {
                    probe = next_probe;
                } else {
                    return Ok(false);
                }
            }
            other => {
                if !other.is_some_and(is_constraining_continuation) {
                    *look = probe;
                    return Ok(true);
                }
                return Ok(false);
            }
        }
    }
    Ok(false)
}

/// Evaluates whether the expression starting at `look` (up to `stop_delim` at
/// inner depth 0, or up to the arm-body terminator when `stop_delim` is
/// `None`) is trivially true: a disjunction where at least one disjunct is a
/// conjunction of trivially-true atoms, with no looser operator (`→`, `↔`) or
/// trailing non-empty block statement invalidating it.
fn expr_is_trivially_true(
    look: &mut SpecLexer<'_>,
    stop_delim: Option<&str>,
    depth: u32,
) -> Result<bool, SpecScanError> {
    if depth == 0 {
        return Ok(false);
    }
    // Strip optional leading `return` / `by` before splitting disjunctions so
    // `{ return x == 1 || true; }` is handled identically to `x == 1 || true`.
    loop {
        let mut peek = *look;
        if matches!(peek.next_tok()?, Some(SpecTok::Word("return" | "by"))) {
            *look = peek;
        } else {
            break;
        }
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
            let mut conj_probe = *look;
            if !disjuncts_blocked
                && consume_trivial_conjunction(&mut conj_probe, stop_delim == Some(")"), depth)?
            {
                found_trivial = true;
                *look = conj_probe;
            }
        }
        let before = *look;
        let Some(tok) = look.next_tok()? else {
            return Ok(stop_delim.is_none() && found_trivial);
        };
        scanned += 1;
        if scanned > MAX_ARM_BODY_SCAN_TOKENS {
            return Ok(false);
        }
        if inner_depth == 0 {
            if prev_closed_brace_at_zero {
                prev_closed_brace_at_zero = false;
                if stop_delim.is_none()
                    && matches!(
                        tok,
                        SpecTok::Word(w) if !matches!(w, "else" | "or" | "and" | "as")
                    )
                {
                    *look = before;
                    return Ok(found_trivial);
                }
            }
            if let Some(delim) = stop_delim {
                if tok == SpecTok::Sym(delim) {
                    return Ok(found_trivial);
                }
                if delim == "}" && tok == SpecTok::Sym(";") {
                    return Ok(matches!(look.next_tok()?, Some(SpecTok::Sym("}"))) && found_trivial);
                }
                // A tuple or argument list (`(true, x)`) is not a
                // parenthesized proposition.
                if matches!(tok, SpecTok::Sym(")" | "]" | "}" | ",")) {
                    return Ok(false);
                }
            } else {
                let mut peek = *look;
                if is_arm_body_terminator(tok, peek.next_tok()?) {
                    *look = before;
                    return Ok(found_trivial);
                }
            }
            if is_looser_than_disjunction(tok) {
                return Ok(false);
            }
            if extends_to_the_right(tok) {
                disjuncts_blocked = true;
            }
            if is_disjunction_tok(tok) {
                at_disjunct_start = true;
                continue;
            }
            if stop_delim == Some(")") && tok == SpecTok::Sym(":") {
                let mut asc = *look;
                if matches!(
                    asc.next_tok()?,
                    Some(SpecTok::Word("Prop" | "Bool" | "bool"))
                ) && matches!(asc.next_tok()?, Some(SpecTok::Sym(")")))
                {
                    *look = asc;
                    return Ok(found_trivial);
                }
                return Ok(false);
            }
            if tok == SpecTok::Word("as") {
                let mut cast = *look;
                if matches!(cast.next_tok()?, Some(SpecTok::Word("bool"))) {
                    *look = cast;
                    continue;
                }
                found_trivial = false;
            }
        }
        match tok {
            SpecTok::Sym("(" | "[" | "{") => inner_depth += 1,
            SpecTok::Sym(")" | "]" | "}") => {
                if inner_depth == 0 {
                    return Ok(false);
                }
                inner_depth -= 1;
                if inner_depth == 0 && tok == SpecTok::Sym("}") {
                    prev_closed_brace_at_zero = true;
                }
            }
            _ => {}
        }
    }
}

/// Returns `true` when the arm body starting at `look` is trivially true:
/// `true`, `True`, `trivial`, `!false`, `¬False`, `Not False`, optionally
/// wrapped (`(true)`, `{ true }`, `{ return true; }`, `by trivial`,
/// `true as bool`), a conjunction of trivially-true atoms (`true && true`,
/// `(true && true)`, `(True ∧ True)`), or a disjunction containing one
/// (`true || p`, `p || true`, `(p || true)`, `P ∨ True`), and not combined
/// with a constraining operator.
fn arm_body_is_trivially_true(mut look: SpecLexer<'_>) -> Result<bool, SpecScanError> {
    expr_is_trivially_true(&mut look, None, MAX_TRIVIAL_EXPR_DEPTH)
}

/// Lean declaration keywords that begin a fresh top-level item and therefore
/// close any prior `match` or arm-pattern state.
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

/// Maximum tokens of a brace group inspected to recognize a struct pattern.
const MAX_STRUCT_PATTERN_TOKENS: usize = 256;

/// Whether the brace group whose `{` was just read closes within
/// [`MAX_STRUCT_PATTERN_TOKENS`] tokens without containing `=>` or `;`: such
/// a group has no arms or statements of its own (a struct pattern, a struct
/// literal, a one-expression block).
fn brace_is_pattern_like(mut look: SpecLexer<'_>) -> Result<bool, SpecScanError> {
    let mut depth = 1u32;
    for _ in 0..MAX_STRUCT_PATTERN_TOKENS {
        match look.next_tok()? {
            None | Some(SpecTok::FatArrow | SpecTok::Sym(";")) => return Ok(false),
            Some(SpecTok::Sym("{")) => depth += 1,
            Some(SpecTok::Sym("}")) => {
                depth -= 1;
                if depth == 0 {
                    return Ok(true);
                }
            }
            Some(_) => {}
        }
    }
    Ok(false)
}

/// Strict error-branch wildcard scanner over postcondition source in dialect
/// `syntax`. Returns the first wildcard in source order, `Ok(None)` when the
/// source has none, and an error when the source is malformed.
///
/// A match arm is a wildcard when one of its pattern alternatives names an
/// error constructor (`Err`, `.err`, `.error`, `.ub`, `.unsupported`,
/// `.fail`) whose payload is unconstrained (`_`, `..`, a bare binding, or a
/// Lean type ascription `(_ : E)`) and its body is trivially true (`true`,
/// `True`, `trivial`, `!false`, `¬False`, possibly parenthesized or in a
/// disjunction). `matches!(…, … | Err(_))` is a wildcard without a body, and
/// a catch-all arm (`_ => true`, `e => true`) is one when its own match also
/// has an `Ok` arm. Arms are found at any bracket depth
/// (`P ∧ (match r with | .ok v => … | .err _ => True)`), and each component
/// of a tuple pattern or Lean multi-discriminant arm is judged on its own
/// (`(Err(_), Ok(_)) => true`). An error constructor inside a struct pattern
/// counts (`Wrapper { inner: Err(_) } => true`, Lean `{ val := .err _ }`),
/// and a tuple of catch-alls is a catch-all (`(_, _) => true`).
///
/// An arm body ends at the next arm, at the bracket that closes the match,
/// or at the next top-level item or Lean command; nothing after it is read
/// as part of the body.
///
/// The scanner is syntactic: it reads `match` arms and `matches!`. An error
/// escape written without them (`out.map_or(true, …)`,
/// `out.is_err() || …`, `if let Ok(v) = out { … } else { true }`,
/// `∀ v, out = .ok v → …`) is caught by the dynamic probes of
/// [`check_result_contract_no_error_wildcard`] and
/// [`check_semantic_outcome_no_error_wildcard`], not here.
///
/// An arm that constrains the payload (`Err(E::Overflow) => …`,
/// `Err(Unsupported) => …`, `| .err .ub => …`), has a non-trivial `if` guard,
/// or has any other body (`| .ub => False`, `Err(_) => x == u32::MAX`) is not
/// reported. Comments and literals are never inspected.
pub fn scan_error_branch_wildcard(
    post_src: &str,
    syntax: SpecSyntax,
) -> Result<Option<ErrorWildcardPattern>, SpecScanError> {
    let lean_keywords = !matches!(syntax, SpecSyntax::Rust);
    let mut lexer = SpecLexer::new(post_src, syntax);
    let mut alt = ArmAlternative::default();
    let mut arm = ArmState::default();
    let mut matches_state = MatchesState::Outside;
    let mut matches_saw_ok = false;
    let mut matches_scope_floor = 0usize;
    let mut after_dot = false;
    let mut in_match_scrutinee = false;
    let mut scopes = OkScopes::new();

    while let Some(tok) = lexer.next_tok()? {
        let was_after_dot = after_dot;
        after_dot = matches!(tok, SpecTok::Sym("."));

        // Skip the scrutinee of `matches!(scrutinee, pattern)`.
        if let MatchesState::Scrutinee { depth } = matches_state {
            match tok {
                SpecTok::Sym("(" | "[" | "{") => {
                    matches_state = MatchesState::Scrutinee { depth: depth + 1 };
                }
                SpecTok::Sym(")" | "]" | "}") => {
                    matches_state = if depth <= 1 {
                        MatchesState::Outside
                    } else {
                        MatchesState::Scrutinee { depth: depth - 1 }
                    };
                }
                SpecTok::Sym(",") if depth == 1 => {
                    matches_state = MatchesState::Pattern;
                    matches_saw_ok = false;
                    matches_scope_floor = scopes.len;
                    in_match_scrutinee = false;
                    alt = ArmAlternative::default();
                    arm = ArmState::default();
                }
                _ => {}
            }
            continue;
        }

        match tok {
            SpecTok::FatArrow => {
                in_match_scrutinee = false;
                if !alt.in_lambda {
                    arm.absorb(&alt);
                    if !arm.guard_blocks() && arm_body_is_trivially_true(lexer)? {
                        if let Some(ctor) = arm.wildcard {
                            return Ok(Some(ctor.pattern()));
                        }
                        if arm.catch_all && scopes.saw_ok() {
                            return Ok(Some(ErrorWildcardPattern::CatchAllArmTrue));
                        }
                    }
                }
                arm = ArmState::default();
                alt = ArmAlternative::body(alt.depth);
            }
            SpecTok::Sym("|")
                if !arm.guarded && (!alt.after_arrow || alt.depth == alt.body_depth) =>
            {
                if alt.after_arrow {
                    // The previous arm's body ends here: it is not a pattern.
                    arm = ArmState::default();
                    alt = ArmAlternative::pattern(alt.depth);
                } else {
                    if alt.at_catch_all_paren_level() {
                        // Record the error wildcard now; the catch-all
                        // verdict waits for the closing parenthesis.
                        arm.absorb(&ArmAlternative {
                            catch_all: false,
                            ..alt
                        });
                    } else {
                        arm.absorb(&alt);
                    }
                    match alt.error_ctor_depth {
                        Some(ctor_depth) if alt.depth > ctor_depth => {
                            // Or-pattern inside an error payload. Directly
                            // under the constructor (`Err(E::A | _)`) the
                            // next alternative starts unconstrained; deeper
                            // (`Err(Wrap(E::A | _))`) the enclosing
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
                        // Top-level or nested or-pattern
                        // (`Some(Err(_) | Ok(0))`).
                        _ => alt = alt.next_alt(alt.catch_all_parens),
                    }
                }
            }
            SpecTok::Sym(",")
                if !arm.guarded
                    && !alt.after_arrow
                    && !alt.in_lambda
                    && alt.error_ctor_depth.is_some_and(|d| alt.depth <= d) =>
            {
                // A sibling of the error constructor, not part of its
                // payload: the next tuple component (`(Err(_), Ok(_))`) or
                // Lean discriminant (`| .err _, .ok v`). Its constructors
                // must not constrain the payload already scanned.
                arm.absorb(&ArmAlternative {
                    catch_all: false,
                    ..alt
                });
                alt = alt.next_alt(0);
            }
            SpecTok::Sym("," | ";") if alt.depth == 0 => {
                in_match_scrutinee = false;
                if matches_state == MatchesState::Pattern {
                    // Allow a Rust trailing comma in `matches!(out, pat,)`.
                    let mut look = lexer;
                    if tok == SpecTok::Sym(",")
                        && matches!(look.next_tok()?, Some(SpecTok::Sym(")" | "]" | "}")))
                    {
                        continue;
                    }
                    matches_state = MatchesState::Outside;
                }
                arm = ArmState::default();
                alt = ArmAlternative::default();
            }
            SpecTok::Sym("(") => {
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
            SpecTok::Sym("[") => {
                alt.depth += 1;
                if alt.type_ascription_depth.is_some() {
                    alt.tokens += 1;
                } else {
                    alt.push_non_word();
                }
            }
            SpecTok::Sym("{") => {
                // In pattern position a brace group without `=>` or `;` is a
                // struct pattern (`W { r: Err(_) }`, Lean `{ val := .err _ }`)
                // or a small expression: either way it holds no arms of its
                // own, so it is tracked by depth and its error constructors
                // stay with the arm around it.
                let is_struct_pattern_brace = !alt.after_arrow
                    && !arm.guarded
                    && !in_match_scrutinee
                    && (matches_state == MatchesState::Pattern || brace_is_pattern_like(lexer)?);
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
                    arm = ArmState::default();
                    alt = ArmAlternative::default();
                }
            }
            SpecTok::Sym(")" | "]" | "}") => {
                if alt.depth > 0 {
                    alt.depth -= 1;
                    let was_ascription = alt.type_ascription_depth.is_some();
                    if alt.type_ascription_depth.is_some_and(|d| alt.depth < d) {
                        alt.type_ascription_depth = None;
                    }
                    if alt.struct_pattern_depth.is_some_and(|d| alt.depth < d) {
                        alt.struct_pattern_depth = None;
                    }
                    let closed_outer_catch_all_paren = tok == SpecTok::Sym(")")
                        && alt.catch_all_parens > 0
                        && alt.depth < alt.arm_base_depth + alt.catch_all_parens;
                    if closed_outer_catch_all_paren {
                        alt.catch_all_parens -= 1;
                        // The group is a catch-all when its last component
                        // is (`(e)`, `(0 | _)`) and, for a tuple, every
                        // earlier component was too (`(_, _)`, `(_, _,)`).
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
                        // The bracket around the arm list closed: what
                        // follows continues the enclosing body.
                        alt.body_depth = alt.depth;
                    }
                    scopes.close_lean_matches(alt.depth + 1);
                } else if tok == SpecTok::Sym("}")
                    && let Some(saved_depth) =
                        scopes.pop_brace(if matches_state == MatchesState::Pattern {
                            matches_scope_floor
                        } else {
                            0
                        })
                {
                    // The block closed: a new arm pattern may follow
                    // (`Ok(v) => { … } Err(_) => true`).
                    in_match_scrutinee = false;
                    arm = ArmState::default();
                    alt = ArmAlternative::pattern(saved_depth);
                } else {
                    // The closer of a bracket opened before the scanned
                    // text, or of `matches!(…)`.
                    if matches_state == MatchesState::Pattern {
                        arm.absorb(&alt);
                        if !arm.guard_blocks()
                            && (arm.wildcard.is_some() || (arm.catch_all && matches_saw_ok))
                        {
                            return Ok(Some(ErrorWildcardPattern::MatchesAnyErr));
                        }
                        matches_state = MatchesState::Outside;
                    }
                    in_match_scrutinee = false;
                    scopes.close_lean_matches(0);
                    arm = ArmState::default();
                    alt = ArmAlternative::default();
                }
            }
            SpecTok::Sym(":=")
                if alt.struct_pattern_depth.is_some() && !alt.after_arrow && !alt.in_lambda =>
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
            SpecTok::Sym(":=") => {
                in_match_scrutinee = false;
                arm = ArmState::default();
                alt = ArmAlternative::body(alt.depth);
            }
            SpecTok::Word(word) => {
                if word == "Ok" || (was_after_dot && word == "ok") {
                    if matches_state == MatchesState::Pattern {
                        matches_saw_ok = true;
                    } else {
                        scopes.mark_ok();
                    }
                }
                if word == "matches" && matches_state == MatchesState::Outside {
                    let mut look = lexer;
                    if matches!(look.next_tok()?, Some(SpecTok::Sym("!")))
                        && matches!(look.next_tok()?, Some(SpecTok::Sym("(" | "[" | "{")))
                    {
                        lexer = look;
                        after_dot = false;
                        matches_state = MatchesState::Scrutinee { depth: 1 };
                        continue;
                    }
                }
                if !arm.guarded && alt.depth == 0 && is_lean_decl_reset_word(word) {
                    in_match_scrutinee = false;
                    scopes.begin_declaration();
                    arm = ArmState::default();
                    alt = ArmAlternative::default();
                    continue;
                }
                if !arm.guarded
                    && lean_keywords
                    && matches!(word, "fun" | "λ")
                    && alt.error_ctor.is_none()
                    && (alt.after_arrow || alt.tokens == 0)
                {
                    arm = ArmState::default();
                    alt = ArmAlternative {
                        in_lambda: true,
                        ..ArmAlternative::pattern(alt.depth)
                    };
                    continue;
                }
                if !arm.guarded && matches!(word, "match" | "with") {
                    in_match_scrutinee = word == "match";
                    if word == "with" && lean_keywords {
                        scopes.push(OkScopeKind::LeanMatch { depth: alt.depth });
                    }
                    arm = ArmState::default();
                    alt = ArmAlternative::pattern(alt.depth);
                    continue;
                }
                if arm.guarded {
                    arm.guard_tokens += 1;
                    arm.guard_trivial = word == "true";
                } else if word == "if" && alt.depth == 0 && !alt.after_arrow && !alt.in_lambda {
                    arm.absorb(&alt);
                    alt = ArmAlternative::default();
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
                    if let Some(ctor) = ErrorCtor::of(word, was_after_dot) {
                        match alt.error_ctor {
                            None => {
                                alt.error_ctor = Some(ctor);
                                alt.error_ctor_depth = Some(alt.depth);
                            }
                            Some(ErrorCtor::Fail)
                                if matches!(ctor, ErrorCtor::Ub | ErrorCtor::Unsupported) =>
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
            SpecTok::Literal | SpecTok::PathSep => {
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
            SpecTok::DotDot | SpecTok::Sym(_) => {
                if arm.guarded {
                    arm.guard_tokens += 1;
                    arm.guard_trivial = false;
                } else if !alt.after_arrow && !alt.in_lambda {
                    if alt.type_ascription_depth.is_some() {
                        alt.tokens += 1;
                    } else if matches!(tok, SpecTok::Sym("&" | "&&")) {
                        let keep_mod = alt.tokens == 0 || alt.only_modifiers;
                        alt.tokens += 1;
                        alt.catch_all = false;
                        alt.only_modifiers = keep_mod;
                    } else if tok == SpecTok::Sym(",") && alt.at_catch_all_paren_level() {
                        // A tuple component ended (`(_, _)`).
                        let component_wild = alt.catch_all || alt.or_wild;
                        alt.tuple_wild = component_wild && (alt.tuple_wild || !alt.tuple_started);
                        alt.tuple_started = true;
                        alt.or_wild = false;
                        alt.tokens += 1;
                        alt.catch_all = false;
                        alt.only_modifiers = alt.tuple_wild;
                    } else if tok == SpecTok::Sym("@") && alt.catch_all {
                        alt.tokens += 1;
                        alt.catch_all = false;
                        alt.only_modifiers = true;
                    } else if tok == SpecTok::Sym(":")
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
    Ok(None)
}

/// Scans postcondition source of unknown dialect for an error-branch
/// wildcard. Malformed source fails closed with
/// [`ErrorWildcardPattern::UnclosedLiteralOrComment`]. See
/// [`scan_error_branch_wildcard`] for the strict, dialect-aware form.
pub fn detect_error_branch_wildcard(post_src: &str) -> Option<ErrorWildcardPattern> {
    match scan_error_branch_wildcard(post_src, SpecSyntax::Any) {
        Ok(pattern) => pattern,
        Err(SpecScanError::UnclosedLiteralOrComment) => {
            Some(ErrorWildcardPattern::UnclosedLiteralOrComment)
        }
    }
}

/// Statistics of a passing error-branch wildcard check.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ErrorWildcardStats {
    /// Statistics of the base contract check.
    pub base: SpecCheckStats,
    /// Precondition hits on which the function returned `Ok`.
    pub ok_hits: usize,
    /// Precondition hits on which the function returned `Err`.
    pub err_hits: usize,
    /// `Err(e)` candidates offered on `Ok` hits, all rejected.
    pub error_escape_probes: usize,
    /// Distinct `Err(e_bad)` payload mutants offered on `Err` hits.
    pub err_payload_mutants_tested: usize,
    /// Payload mutants the postcondition rejected.
    pub err_payload_mutants_killed: usize,
    /// `Ub` / `Unsupported` candidates offered, all rejected.
    pub fault_probes: usize,
}

/// What the error-branch wildcard probes found.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ErrorWildcardViolationKind {
    /// On the `Ok` hit at `trial_idx` the postcondition accepted an `Err`
    /// outcome: an implementation may fail where the function succeeds.
    ErrorEscapeAccepted { trial_idx: usize },
    /// On the `Err` hit at `trial_idx` the postcondition accepted every
    /// distinct error payload offered.
    ErrorPayloadUnconstrained { trial_idx: usize },
    /// On the hit at `trial_idx` the postcondition accepted `Ub`.
    UbAccepted { trial_idx: usize },
    /// On the hit at `trial_idx` the postcondition accepted `Unsupported`.
    UnsupportedAccepted { trial_idx: usize },
}

/// Structured report of an error-branch wildcard violation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ErrorWildcardViolation {
    /// Always [`SpecBoundaryGuardClass::ErrorBranchWildcard`].
    pub guard: SpecBoundaryGuardClass,
    /// What the probes found.
    pub kind: ErrorWildcardViolationKind,
    /// Statistics accumulated up to the violation.
    pub stats: ErrorWildcardStats,
}

impl ErrorWildcardViolation {
    /// Frozen vacuity class of the violation
    /// ([`VacuityClass::SurvivedAllMutants`]).
    pub const fn vacuity_class(&self) -> VacuityClass {
        self.guard.to_vacuity_class()
    }

    /// Index of the trial whose input exhibits the wildcard. Pass it to
    /// [`replay_trial_input`] with the same [`SpecCheckConfig`].
    pub const fn counterexample_trial(&self) -> usize {
        match self.kind {
            ErrorWildcardViolationKind::ErrorEscapeAccepted { trial_idx }
            | ErrorWildcardViolationKind::ErrorPayloadUnconstrained { trial_idx }
            | ErrorWildcardViolationKind::UbAccepted { trial_idx }
            | ErrorWildcardViolationKind::UnsupportedAccepted { trial_idx } => trial_idx,
        }
    }
}

/// Outcome of an error-branch wildcard check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorWildcardCheckOutcome {
    /// The base contract check passed and every error and fault probe was
    /// rejected.
    Strong(ErrorWildcardStats),
    /// The base contract check ([`check_contract`]) failed with its own
    /// [`VacuityClass`].
    BaseFailed(SpecCheckFailure),
    /// The base check passed but the postcondition is an error-branch
    /// wildcard.
    Wildcard(ErrorWildcardViolation),
}

impl ErrorWildcardCheckOutcome {
    /// Returns `true` iff the contract passed the base check and every probe.
    pub const fn is_strong(&self) -> bool {
        matches!(self, Self::Strong(_))
    }

    /// Returns the failing [`VacuityClass`], or `None` when [`Self::Strong`].
    pub const fn vacuity_class(&self) -> Option<VacuityClass> {
        match self {
            Self::Strong(_) => None,
            Self::BaseFailed(failure) => Some(failure.class),
            Self::Wildcard(violation) => Some(violation.vacuity_class()),
        }
    }

    /// Returns the guard class when the outcome is a wildcard violation.
    pub const fn guard_class(&self) -> Option<SpecBoundaryGuardClass> {
        match self {
            Self::Wildcard(violation) => Some(violation.guard),
            Self::Strong(_) | Self::BaseFailed(_) => None,
        }
    }

    /// Returns the wildcard violation, if any.
    pub const fn violation(&self) -> Option<&ErrorWildcardViolation> {
        match self {
            Self::Wildcard(violation) => Some(violation),
            Self::Strong(_) | Self::BaseFailed(_) => None,
        }
    }
}

/// Maximum number of boundary error payloads offered per `Ok` hit by the
/// error-escape probe.
pub const MAX_ERROR_ESCAPE_BOUNDARY_PROBES: usize = 16;

/// Number of seeded error payloads offered per `Ok` hit after the boundary
/// payloads.
const ERROR_ESCAPE_SEEDED_PROBES: usize = 2;

/// Shared core of the error-branch wildcard checks.
///
/// Runs the base contract check, then replays the same input stream and, on
/// every precondition hit:
///
/// - **`Ok` hit** — offers `Err(e)` for the boundary payloads of the error
///   type and two seeded payloads. Accepting any of them is an error escape.
/// - **`Err(e_ok)` hit** — when the error type is not a subsingleton, offers
///   its distinct payload mutants `Err(e_bad)`. Accepting all of them (or
///   having none to offer) leaves the payload unconstrained.
/// - **every hit** — offers `Ub` and `Unsupported` when the outcome type has
///   them. Accepting either is a violation, as is a live `Ub` / `Unsupported`
///   outcome the base check let through.
///
/// A postcondition that traps on a probe rejects it.
fn check_no_error_wildcard_core<I, R, Pre, Body, Post>(
    config: SpecCheckConfig,
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> ErrorWildcardCheckOutcome
where
    I: SampleInput,
    R: ErrorBranchOutcome + ReturnMutants + PartialEq,
    R::Error: SampleInput + ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    Body: FnMut(&I) -> Result<R, ()>,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    let base = match check_contract_core(config, None, &mut pre, &mut body, &mut post) {
        SpecCheckOutcome::Strong(stats) => stats,
        SpecCheckOutcome::Failed(failure) => {
            return ErrorWildcardCheckOutcome::BaseFailed(failure);
        }
    };
    let mut stats = ErrorWildcardStats {
        base,
        ..ErrorWildcardStats::default()
    };
    let wildcard = |kind, stats| {
        ErrorWildcardCheckOutcome::Wildcard(ErrorWildcardViolation {
            guard: SpecBoundaryGuardClass::ErrorBranchWildcard,
            kind,
            stats,
        })
    };
    let trapped = |trial_idx, trap| match execution_trapped(base, trial_idx, trap) {
        SpecCheckOutcome::Failed(failure) => ErrorWildcardCheckOutcome::BaseFailed(failure),
        SpecCheckOutcome::Strong(_) => unreachable!("`execution_trapped` always fails"),
    };

    let (mut rng, mut mutant_rng) = stateless_streams(config.seed);
    let mut probe_rng = mutant_rng.fork();
    let boundary_probes = min_usize(
        <R::Error as SampleInput>::BOUNDARY_COUNT,
        MAX_ERROR_ESCAPE_BOUNDARY_PROBES,
    );

    for trial_idx in 0..config.max_trials {
        let input = I::sample_at(trial_idx, &mut rng);
        match pre(&input) {
            Ok(true) => {}
            Ok(false) => continue,
            Err(()) => return trapped(trial_idx, TrapKind::PreconditionPanicked),
        }
        let ret = match body(&input) {
            Ok(ret) => ret,
            Err(()) => return trapped(trial_idx, TrapKind::BodyPanicked),
        };

        match ret.branch() {
            // The base check verified that `post` accepts the live outcome.
            OutcomeBranch::Ub => {
                return wildcard(ErrorWildcardViolationKind::UbAccepted { trial_idx }, stats);
            }
            OutcomeBranch::Unsupported => {
                return wildcard(
                    ErrorWildcardViolationKind::UnsupportedAccepted { trial_idx },
                    stats,
                );
            }
            OutcomeBranch::Ok => {
                stats.ok_hits += 1;
                for probe in 0..boundary_probes + ERROR_ESCAPE_SEEDED_PROBES {
                    let sample_idx = if probe < boundary_probes {
                        probe
                    } else {
                        <R::Error as SampleInput>::BOUNDARY_COUNT
                            .saturating_add(probe - boundary_probes)
                    };
                    let candidate = R::from_error(<R::Error as SampleInput>::sample_at(
                        sample_idx,
                        &mut probe_rng,
                    ));
                    stats.error_escape_probes += 1;
                    if matches!(post(&input, &candidate), Ok(true)) {
                        return wildcard(
                            ErrorWildcardViolationKind::ErrorEscapeAccepted { trial_idx },
                            stats,
                        );
                    }
                }
            }
            OutcomeBranch::Err => {
                stats.err_hits += 1;
                if !<R::Error as ReturnMutants>::IS_SUBSINGLETON
                    && let Some(error_ok) = ret.error_payload()
                {
                    let mut tested = 0usize;
                    let mut killed = 0usize;
                    error_ok.visit_mutants(&mut mutant_rng, |error_bad| {
                        if killed > 0 || &error_bad == error_ok {
                            return;
                        }
                        tested += 1;
                        if !matches!(post(&input, &R::from_error(error_bad)), Ok(true)) {
                            killed += 1;
                        }
                    });
                    stats.err_payload_mutants_tested += tested;
                    stats.err_payload_mutants_killed += killed;
                    if killed == 0 {
                        return wildcard(
                            ErrorWildcardViolationKind::ErrorPayloadUnconstrained { trial_idx },
                            stats,
                        );
                    }
                }
            }
        }

        if let Some(ub) = R::ub() {
            stats.fault_probes += 1;
            if matches!(post(&input, &ub), Ok(true)) {
                return wildcard(ErrorWildcardViolationKind::UbAccepted { trial_idx }, stats);
            }
        }
        if let Some(unsupported) = R::unsupported() {
            stats.fault_probes += 1;
            if matches!(post(&input, &unsupported), Ok(true)) {
                return wildcard(
                    ErrorWildcardViolationKind::UnsupportedAccepted { trial_idx },
                    stats,
                );
            }
        }
    }

    ErrorWildcardCheckOutcome::Strong(stats)
}

/// Checks a `Result`-returning contract `(pre, body, post)` against the
/// error-branch wildcard guard.
///
/// On top of [`check_contract`], the check offers `Err(e)` on every input
/// where `body` returned `Ok` and distinct `Err(e_bad)` payloads on every
/// input where it returned `Err`. The postcondition
/// `Ok(v) => v == x + 1, Err(_) => true` passes [`check_contract`] (its `Ok`
/// mutants are killed) and is rejected here with
/// [`ErrorWildcardViolationKind::ErrorEscapeAccepted`].
///
/// As with [`check_contract`], a `post` that can panic on a wrong output must
/// be checked through [`check_result_contract_no_error_wildcard_fallible`].
pub fn check_result_contract_no_error_wildcard<I, T, E, Pre, Body, Post>(
    config: SpecCheckConfig,
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> ErrorWildcardCheckOutcome
where
    I: SampleInput,
    T: SampleInput + ReturnMutants + PartialEq,
    E: SampleInput + ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    Body: FnMut(&I) -> Result<T, E>,
    Post: FnMut(&I, &Result<T, E>) -> bool,
{
    check_no_error_wildcard_core(
        config,
        |input: &I| Ok(pre(input)),
        |input: &I| Ok(body(input)),
        |input: &I, ret: &Result<T, E>| Ok(post(input, ret)),
    )
}

/// Fallible form of [`check_result_contract_no_error_wildcard`]: `pre`,
/// `body`, and `post` may trap by returning `Err(())`, exactly as in
/// [`check_contract_fallible`]. A `post` that traps on a probe rejects it.
pub fn check_result_contract_no_error_wildcard_fallible<I, T, E, Pre, Body, Post>(
    config: SpecCheckConfig,
    pre: Pre,
    body: Body,
    post: Post,
) -> ErrorWildcardCheckOutcome
where
    I: SampleInput,
    T: SampleInput + ReturnMutants + PartialEq,
    E: SampleInput + ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    Body: FnMut(&I) -> Result<Result<T, E>, ()>,
    Post: FnMut(&I, &Result<T, E>) -> Result<bool, ()>,
{
    check_no_error_wildcard_core(config, pre, body, post)
}

/// Checks a [`SemanticOutcome`]-returning contract against the error-branch
/// wildcard guard.
///
/// In addition to the error probes of
/// [`check_result_contract_no_error_wildcard`], the postcondition must reject
/// [`SemanticOutcome::Ub`] and [`SemanticOutcome::Unsupported`] on every
/// precondition-admissible input.
pub fn check_semantic_outcome_no_error_wildcard<I, T, E, Pre, Body, Post>(
    config: SpecCheckConfig,
    mut pre: Pre,
    mut body: Body,
    mut post: Post,
) -> ErrorWildcardCheckOutcome
where
    I: SampleInput,
    T: SampleInput + ReturnMutants + PartialEq,
    E: SampleInput + ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> bool,
    Body: FnMut(&I) -> SemanticOutcome<T, E>,
    Post: FnMut(&I, &SemanticOutcome<T, E>) -> bool,
{
    check_no_error_wildcard_core(
        config,
        |input: &I| Ok(pre(input)),
        |input: &I| Ok(body(input)),
        |input: &I, ret: &SemanticOutcome<T, E>| Ok(post(input, ret)),
    )
}

/// Fallible form of [`check_semantic_outcome_no_error_wildcard`].
pub fn check_semantic_outcome_no_error_wildcard_fallible<I, T, E, Pre, Body, Post>(
    config: SpecCheckConfig,
    pre: Pre,
    body: Body,
    post: Post,
) -> ErrorWildcardCheckOutcome
where
    I: SampleInput,
    T: SampleInput + ReturnMutants + PartialEq,
    E: SampleInput + ReturnMutants + PartialEq,
    Pre: FnMut(&I) -> Result<bool, ()>,
    Body: FnMut(&I) -> Result<SemanticOutcome<T, E>, ()>,
    Post: FnMut(&I, &SemanticOutcome<T, E>) -> Result<bool, ()>,
{
    check_no_error_wildcard_core(config, pre, body, post)
}

/// Implements [`SampleInput`](crate::spec_check::SampleInput) and
/// [`ReturnMutants`](crate::spec_check::ReturnMutants) for a struct by
/// delegating to the implementations of its field types.
///
/// Supports unit structs, empty braced structs, named structs with one to four
/// fields, and tuple structs with one to four fields. Multi-field structs
/// sample and mutate identically to the tuple of their field types (boundary
/// cross-products first, then seeded draws; round-robin interleaved per-field
/// and joint perturbations):
///
/// ```text
/// struct Marker;
/// anneal_spec::impl_spec_check_struct!(Marker);
///
/// struct Span { lo: u16, hi: u16 }
/// anneal_spec::impl_spec_check_struct!(Span { lo: u16, hi: u16 });
///
/// struct Meters(u32);
/// anneal_spec::impl_spec_check_struct!(Meters(u32));
///
/// struct Pair(u16, u16);
/// anneal_spec::impl_spec_check_struct!(Pair(u16, u16));
/// ```
///
/// Single-field structs require only `SampleInput` and `ReturnMutants` on their
/// inner field; multi-field structs additionally require `Clone` on each field.
///
/// The generated sampler and mutant generator ignore any invariant the struct
/// carries, which is what the checker needs. On the input side, state the
/// invariant (or call the `#[invariant]` companion method) in the precondition:
/// samples that violate it are rejected like any other inadmissible input. On
/// the output side, a mutant that violates the invariant is a legitimate wrong
/// answer that a postcondition restating the invariant must reject.
#[macro_export]
macro_rules! impl_spec_check_struct {
    ($name:ident) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize = 1;

            fn sample_at(
                _trial_idx: usize,
                _rng: &mut $crate::spec_check::SplitMix64,
            ) -> Self {
                Self
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool = true;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                _rng: &mut $crate::spec_check::SplitMix64,
                _emit: F,
            ) {
            }
        }
    };
    ($name:ident {}) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize = 1;

            fn sample_at(
                _trial_idx: usize,
                _rng: &mut $crate::spec_check::SplitMix64,
            ) -> Self {
                Self {}
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool = true;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                _rng: &mut $crate::spec_check::SplitMix64,
                _emit: F,
            ) {
            }
        }
    };
    ($name:ident { $field:ident : $fty:ty $(,)? }) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize =
                <$fty as $crate::spec_check::SampleInput>::BOUNDARY_COUNT;

            fn sample_at(trial_idx: usize, rng: &mut $crate::spec_check::SplitMix64) -> Self {
                Self {
                    $field: <$fty as $crate::spec_check::SampleInput>::sample_at(trial_idx, rng),
                }
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool =
                <$fty as $crate::spec_check::ReturnMutants>::IS_SUBSINGLETON;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                rng: &mut $crate::spec_check::SplitMix64,
                mut emit: F,
            ) {
                $crate::spec_check::ReturnMutants::visit_mutants(&self.$field, rng, |$field| {
                    emit(Self { $field })
                });
            }
        }
    };
    ($name:ident { $first:ident : $first_ty:ty, $($field:ident : $fty:ty),+ $(,)? }) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize =
                <($first_ty, $($fty,)+) as $crate::spec_check::SampleInput>::BOUNDARY_COUNT;

            fn sample_at(trial_idx: usize, rng: &mut $crate::spec_check::SplitMix64) -> Self {
                let ($first, $($field,)+) =
                    <($first_ty, $($fty,)+) as $crate::spec_check::SampleInput>::sample_at(
                        trial_idx, rng,
                    );
                Self { $first, $($field),+ }
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool =
                <($first_ty, $($fty,)+) as $crate::spec_check::ReturnMutants>::IS_SUBSINGLETON;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                rng: &mut $crate::spec_check::SplitMix64,
                mut emit: F,
            ) {
                let fields = (
                    ::core::clone::Clone::clone(&self.$first),
                    $(::core::clone::Clone::clone(&self.$field),)+
                );
                $crate::spec_check::ReturnMutants::visit_mutants(
                    &fields,
                    rng,
                    |($first, $($field,)+)| emit(Self { $first, $($field),+ }),
                );
            }
        }
    };
    ($name:ident ( $fty:ty $(,)? )) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize =
                <$fty as $crate::spec_check::SampleInput>::BOUNDARY_COUNT;

            fn sample_at(trial_idx: usize, rng: &mut $crate::spec_check::SplitMix64) -> Self {
                Self(<$fty as $crate::spec_check::SampleInput>::sample_at(
                    trial_idx, rng,
                ))
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool =
                <$fty as $crate::spec_check::ReturnMutants>::IS_SUBSINGLETON;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                rng: &mut $crate::spec_check::SplitMix64,
                mut emit: F,
            ) {
                $crate::spec_check::ReturnMutants::visit_mutants(&self.0, rng, |inner| {
                    emit(Self(inner))
                });
            }
        }
    };
    ($name:ident ( $t0:ty, $t1:ty $(,)? )) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize =
                <($t0, $t1) as $crate::spec_check::SampleInput>::BOUNDARY_COUNT;

            fn sample_at(trial_idx: usize, rng: &mut $crate::spec_check::SplitMix64) -> Self {
                let (v0, v1) =
                    <($t0, $t1) as $crate::spec_check::SampleInput>::sample_at(trial_idx, rng);
                Self(v0, v1)
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool =
                <($t0, $t1) as $crate::spec_check::ReturnMutants>::IS_SUBSINGLETON;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                rng: &mut $crate::spec_check::SplitMix64,
                mut emit: F,
            ) {
                let fields = (
                    ::core::clone::Clone::clone(&self.0),
                    ::core::clone::Clone::clone(&self.1),
                );
                $crate::spec_check::ReturnMutants::visit_mutants(&fields, rng, |(v0, v1)| {
                    emit(Self(v0, v1))
                });
            }
        }
    };
    ($name:ident ( $t0:ty, $t1:ty, $t2:ty $(,)? )) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize =
                <($t0, $t1, $t2) as $crate::spec_check::SampleInput>::BOUNDARY_COUNT;

            fn sample_at(trial_idx: usize, rng: &mut $crate::spec_check::SplitMix64) -> Self {
                let (v0, v1, v2) =
                    <($t0, $t1, $t2) as $crate::spec_check::SampleInput>::sample_at(
                        trial_idx, rng,
                    );
                Self(v0, v1, v2)
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool =
                <($t0, $t1, $t2) as $crate::spec_check::ReturnMutants>::IS_SUBSINGLETON;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                rng: &mut $crate::spec_check::SplitMix64,
                mut emit: F,
            ) {
                let fields = (
                    ::core::clone::Clone::clone(&self.0),
                    ::core::clone::Clone::clone(&self.1),
                    ::core::clone::Clone::clone(&self.2),
                );
                $crate::spec_check::ReturnMutants::visit_mutants(&fields, rng, |(v0, v1, v2)| {
                    emit(Self(v0, v1, v2))
                });
            }
        }
    };
    ($name:ident ( $t0:ty, $t1:ty, $t2:ty, $t3:ty $(,)? )) => {
        impl $crate::spec_check::SampleInput for $name {
            const BOUNDARY_COUNT: usize =
                <($t0, $t1, $t2, $t3) as $crate::spec_check::SampleInput>::BOUNDARY_COUNT;

            fn sample_at(trial_idx: usize, rng: &mut $crate::spec_check::SplitMix64) -> Self {
                let (v0, v1, v2, v3) =
                    <($t0, $t1, $t2, $t3) as $crate::spec_check::SampleInput>::sample_at(
                        trial_idx, rng,
                    );
                Self(v0, v1, v2, v3)
            }
        }

        impl $crate::spec_check::ReturnMutants for $name {
            const IS_SUBSINGLETON: bool =
                <($t0, $t1, $t2, $t3) as $crate::spec_check::ReturnMutants>::IS_SUBSINGLETON;

            fn visit_mutants<F: FnMut(Self)>(
                &self,
                rng: &mut $crate::spec_check::SplitMix64,
                mut emit: F,
            ) {
                let fields = (
                    ::core::clone::Clone::clone(&self.0),
                    ::core::clone::Clone::clone(&self.1),
                    ::core::clone::Clone::clone(&self.2),
                    ::core::clone::Clone::clone(&self.3),
                );
                $crate::spec_check::ReturnMutants::visit_mutants(
                    &fields,
                    rng,
                    |(v0, v1, v2, v3)| emit(Self(v0, v1, v2, v3)),
                );
            }
        }
    };
}

#[cfg(test)]
mod spec_boundary_guard_tests {
    use super::*;
    use std::vec::Vec;

    fn desc(def_path: &'static str) -> EntryPointDescriptor<'static> {
        EntryPointDescriptor::new(def_path)
    }

    fn config() -> SpecCheckConfig {
        SpecCheckConfig::default()
    }

    // ---- Frozen taxonomy contract ------------------------------------------

    #[test]
    fn guard_taxonomy_matches_frozen_cross_language_contract() {
        let table: [(usize, &str, &str, VacuityClass, &str); 3] = [
            (
                0,
                "entry_point_requires",
                "EntryPointPrecondition",
                VacuityClass::DeadPrecondition,
                "DeadPrecondition",
            ),
            (
                1,
                "fixed_width_ghost_length",
                "FixedWidthGhostLength",
                VacuityClass::SpecViolation,
                "SpecViolation",
            ),
            (
                2,
                "error_branch_wildcard",
                "ErrorBranchWildcard",
                VacuityClass::SurvivedAllMutants,
                "SurvivedAllMutants",
            ),
        ];
        assert_eq!(SpecBoundaryGuardClass::COUNT, 3);
        assert_eq!(
            SpecBoundaryGuardClass::ALL.len(),
            SpecBoundaryGuardClass::COUNT
        );
        for (guard, (rank, id, name, class, class_name)) in
            SpecBoundaryGuardClass::ALL.into_iter().zip(table)
        {
            assert_eq!(guard.rank(), rank);
            assert_eq!(SpecBoundaryGuardClass::from_rank(rank), Some(guard));
            assert_eq!(guard.guard_id(), id);
            assert_eq!(SpecBoundaryGuardClass::from_guard_id(id), Some(guard));
            assert_eq!(guard.canonical_name(), name);
            assert_eq!(
                SpecBoundaryGuardClass::from_canonical_name(name),
                Some(guard)
            );
            assert_eq!(guard.to_vacuity_class(), class);
            assert_eq!(guard.to_vacuity_class().canonical_name(), class_name);
            assert_eq!(std::format!("{guard}"), name);
        }
        assert_eq!(SpecBoundaryGuardClass::from_rank(3), None);
        assert_eq!(SpecBoundaryGuardClass::from_rank(usize::MAX), None);
    }

    #[test]
    fn guard_parsing_is_exact_and_namespaces_do_not_mix() {
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
            assert_eq!(
                SpecBoundaryGuardClass::from_guard_id(near_miss),
                None,
                "{near_miss:?}"
            );
        }
        for near_miss in [
            "",
            "entry_point_requires",
            "entryPointPrecondition",
            "EntryPointRequires",
            "DeadPrecondition",
            "FixedWidthGhostLength ",
            "ErrorBranchWildCard",
        ] {
            assert_eq!(
                SpecBoundaryGuardClass::from_canonical_name(near_miss),
                None,
                "{near_miss:?}"
            );
        }
        // No guard name collides with a vacuity class name.
        for guard in SpecBoundaryGuardClass::ALL {
            assert_eq!(
                VacuityClass::from_canonical_name(guard.canonical_name()),
                None
            );
            assert_eq!(VacuityClass::from_canonical_name(guard.guard_id()), None);
        }
    }

    #[test]
    fn vacuity_taxonomy_stays_frozen_at_five_classes() {
        assert_eq!(
            VacuityClass::ALL.map(VacuityClass::canonical_name),
            [
                "DeadPrecondition",
                "SpecViolation",
                "TrivialPostcondition",
                "UnboundReturnOutput",
                "SurvivedAllMutants",
            ]
        );
        // The three guards report under three distinct existing classes.
        let classes = SpecBoundaryGuardClass::ALL.map(SpecBoundaryGuardClass::to_vacuity_class);
        assert_ne!(classes[0], classes[1]);
        assert_ne!(classes[1], classes[2]);
        assert_ne!(classes[0], classes[2]);
        for class in classes {
            assert!(VacuityClass::ALL.contains(&class));
        }
    }

    #[test]
    fn guard_marker_types_agree_with_the_enum() {
        assert_eq!(
            EntryPointPrecondition::CLASS,
            SpecBoundaryGuardClass::EntryPointPrecondition
        );
        assert_eq!(EntryPointPrecondition::GUARD_ID, "entry_point_requires");
        assert_eq!(
            EntryPointPrecondition::CANONICAL_NAME,
            "EntryPointPrecondition"
        );
        assert_eq!(
            EntryPointPrecondition::VACUITY_CLASS,
            VacuityClass::DeadPrecondition
        );
        assert_eq!(
            FixedWidthGhostLength::CLASS,
            SpecBoundaryGuardClass::FixedWidthGhostLength
        );
        assert_eq!(FixedWidthGhostLength::GUARD_ID, "fixed_width_ghost_length");
        assert_eq!(
            FixedWidthGhostLength::VACUITY_CLASS,
            VacuityClass::SpecViolation
        );
        assert_eq!(
            ErrorBranchWildcard::CLASS,
            SpecBoundaryGuardClass::ErrorBranchWildcard
        );
        assert_eq!(ErrorBranchWildcard::GUARD_ID, "error_branch_wildcard");
        assert_eq!(
            ErrorBranchWildcard::VACUITY_CLASS,
            VacuityClass::SurvivedAllMutants
        );
    }

    // ---- Guard 1: entry-point classification -------------------------------

    #[test]
    fn entry_point_kind_wire_ids_match_lean() {
        assert_eq!(
            EntryPointKind::ALL.map(EntryPointKind::as_str),
            ["main", "no_main_start", "entry_attribute"]
        );
    }

    #[test]
    fn name_only_entry_symbol_test_matches_lean_vectors() {
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
            assert!(is_binary_entry_symbol(accepted), "{accepted:?}");
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
            assert!(!is_binary_entry_symbol(rejected), "{rejected:?}");
        }
    }

    #[test]
    fn path_segmentation_matches_lean_vectors() {
        assert_eq!(path_segment_count_and_leaf("main"), (1, "main"));
        assert_eq!(path_segment_count_and_leaf("my_crate::main"), (2, "main"));
        assert_eq!(path_segment_count_and_leaf("a::b::c"), (3, "c"));
        assert_eq!(path_segment_count_and_leaf(""), (1, ""));
        assert_eq!(path_segment_count_and_leaf("::main"), (2, "main"));
        assert_eq!(path_segment_count_and_leaf("a:b"), (1, "a:b"));
        assert_eq!(path_segment_count_and_leaf("a:::b"), (2, ":b"));
    }

    /// The same table is asserted by `entryClassificationVectors` in
    /// `tests/mir/SpecBoundaryGuardsTests.lean`.
    #[test]
    fn entry_point_classification_matches_lean_vectors() {
        use EntryPointKind::{EntryAttribute, Main, NoMainStart};
        let vectors: [(EntryPointDescriptor<'static>, Option<EntryPointKind>); 38] = [
            (desc("main"), Some(Main)),
            (desc("::main"), Some(Main)),
            (desc("my_crate::main"), Some(Main)),
            (desc("::my_crate::main"), Some(Main)),
            (
                desc("my_crate::main").with_crate_no_main(true),
                Some(NoMainStart),
            ),
            (desc("_start").with_crate_no_main(true), Some(NoMainStart)),
            (desc("::_start").with_crate_no_main(true), Some(NoMainStart)),
            (
                desc("my_crate::_start").with_crate_no_main(true),
                Some(NoMainStart),
            ),
            (
                desc("::my_crate::_start").with_crate_no_main(true),
                Some(NoMainStart),
            ),
            (
                desc("my_crate::__start").with_crate_no_main(true),
                Some(NoMainStart),
            ),
            (desc("my_crate::_start"), None),
            (desc("my_crate::__start"), None),
            (
                desc("my_crate::boot").with_link_symbol(Some("_start")),
                Some(NoMainStart),
            ),
            (
                desc("my_crate::arch::boot").with_link_symbol(Some("__start")),
                Some(NoMainStart),
            ),
            (
                desc("my_crate::arch::c_main").with_link_symbol(Some("main")),
                Some(NoMainStart),
            ),
            (
                desc("my_crate::helper").with_link_symbol(Some("helper")),
                None,
            ),
            (
                desc("my_crate::helper").with_link_symbol(Some("main_loop")),
                None,
            ),
            (
                desc("my_crate::reset").with_entry_attr(true),
                Some(EntryAttribute),
            ),
            (
                desc("my_crate::main").with_entry_attr(true),
                Some(EntryAttribute),
            ),
            (desc("my_crate::Type::main").with_assoc_fn(true), None),
            (desc("Type::main").with_assoc_fn(true), None),
            (
                desc("my_crate::Type::run")
                    .with_assoc_fn(true)
                    .with_entry_attr(true),
                None,
            ),
            (
                desc("my_crate::Boot::_start")
                    .with_assoc_fn(true)
                    .with_link_symbol(Some("_start")),
                Some(NoMainStart),
            ),
            (
                desc("my_crate::Server::main")
                    .with_assoc_fn(true)
                    .with_entry_attr(true)
                    .with_link_symbol(Some("main")),
                Some(NoMainStart),
            ),
            (
                desc("my_crate::Boot::run")
                    .with_assoc_fn(true)
                    .with_link_symbol(Some("run")),
                None,
            ),
            (
                desc("my_crate::Boot::main")
                    .with_assoc_fn(true)
                    .with_link_symbol(Some("boot_main")),
                None,
            ),
            (desc("my_crate::Type::main"), None),
            (desc("<MyType as Trait>::main"), None),
            (desc("<impl Foo>::main"), None),
            (desc("{{impl}}::main"), None),
            (desc(":::main"), None),
            (desc("::::main"), None),
            (desc("123::main"), None),
            (desc("my_crate::module::main"), None),
            (desc("my_crate::domain"), None),
            (desc("my_crate::maintain"), None),
            (desc("my_crate::main_loop"), None),
            (desc("my_crate::main_loop").with_crate_no_main(true), None),
        ];
        for (descriptor, expected) in vectors {
            assert_eq!(
                classify_entry_point(&descriptor),
                expected,
                "{descriptor:?}"
            );
            // Path-based classification never accepts a path the name-only
            // test rejects.
            if classify_entry_path(descriptor.def_path, descriptor.crate_no_main).is_some() {
                assert!(
                    is_binary_entry_symbol(descriptor.def_path),
                    "{descriptor:?}"
                );
            }
        }
    }

    #[test]
    fn entry_attributes_are_recognized_by_whole_segment() {
        for entry in [
            "entry",
            "#[entry]",
            "cortex_m_rt::entry",
            "#[cortex_m_rt :: entry]",
            "#[::tokio::main]",
            "#[riscv_rt::entry]",
            "main",
            "#[tokio::main]",
            "tokio::main(flavor = \"current_thread\")",
            "#[ start ]",
            "start",
        ] {
            assert!(is_entry_attribute(entry), "{entry:?}");
        }
        for other in [
            "",
            "maintain",
            "entry_point",
            "restart",
            "test",
            "inline",
            "no_mangle",
            "export_name = \"main\"",
            "doc = \"the main entry\"",
            "main_loop",
            "cfg(main)",
            "main = \"x\"",
        ] {
            assert!(!is_entry_attribute(other), "{other:?}");
        }
    }

    #[test]
    fn descriptor_attributes_derive_entry_attr_and_link_symbol() {
        use EntryPointKind::{EntryAttribute, Main, NoMainStart};
        let reset = desc("fw::reset").with_attributes(&["#[cortex_m_rt::entry]"]);
        assert!(reset.has_entry_attr);
        assert_eq!(classify_entry_point(&reset), Some(EntryAttribute));

        let spaced_entry = desc("fw::reset").with_attributes(&["#[cortex_m_rt :: entry]"]);
        assert_eq!(classify_entry_point(&spaced_entry), Some(EntryAttribute));

        let nested_start = desc("fw::arch::_start").with_attributes(&["#[no_mangle]"]);
        assert_eq!(nested_start.link_symbol, Some("_start"));
        assert_eq!(classify_entry_point(&nested_start), Some(NoMainStart));
        // Without the attribute the nested `_start` is an ordinary function.
        assert_eq!(classify_entry_point(&desc("fw::arch::_start")), None);

        let unsafe_no_mangle = desc("fw::arch::__start").with_attributes(&["#[unsafe(no_mangle)]"]);
        assert_eq!(unsafe_no_mangle.link_symbol, Some("__start"));
        assert_eq!(classify_entry_point(&unsafe_no_mangle), Some(NoMainStart));

        let exported = desc("fw::boot").with_attributes(&["#[export_name = \"_start\"]"]);
        assert_eq!(exported.link_symbol, Some("_start"));
        assert_eq!(classify_entry_point(&exported), Some(NoMainStart));

        let raw_exported = desc("fw::boot").with_attributes(&["#[export_name = r#\"_start\"#]"]);
        assert_eq!(raw_exported.link_symbol, Some("_start"));
        assert_eq!(classify_entry_point(&raw_exported), Some(NoMainStart));

        let malformed_exported =
            desc("fw::boot").with_attributes(&["#[export_name = \"_start\" + \"x\"]"]);
        assert_eq!(malformed_exported.link_symbol, None);
        assert_eq!(classify_entry_point(&malformed_exported), None);

        let unsafe_exported =
            desc("fw::boot").with_attributes(&["#[unsafe(export_name = \"main\")]"]);
        assert_eq!(unsafe_exported.link_symbol, Some("main"));
        assert_eq!(classify_entry_point(&unsafe_exported), Some(NoMainStart));

        let helper = desc("fw::helper").with_attributes(&["#[no_mangle]", "#[inline]"]);
        assert_eq!(helper.link_symbol, Some("helper"));
        assert_eq!(classify_entry_point(&helper), None);

        let renamed = desc("fw::helper").with_attributes(&["#[export_name = \"main_loop\"]"]);
        assert_eq!(classify_entry_point(&renamed), None);

        let tokio_main = desc("app::main").with_attributes(&["#[tokio::main]"]);
        assert_eq!(classify_entry_point(&tokio_main), Some(EntryAttribute));
        assert_eq!(classify_entry_point(&desc("app::main")), Some(Main));

        // A method is not an entry point by its path or an entry attribute…
        let method = desc("app::Server::main")
            .with_assoc_fn(true)
            .with_attributes(&["#[entry]", "#[inline]"]);
        assert_eq!(classify_entry_point(&method), None);
        let exported_method = desc("app::Server::run")
            .with_assoc_fn(true)
            .with_attributes(&["#[no_mangle]"]);
        assert_eq!(classify_entry_point(&exported_method), None);
        // …but the linker does not see Rust namespaces: exported as `main`
        // or `_start` it is the entry symbol of the binary.
        let no_mangle_method = desc("app::Server::main")
            .with_assoc_fn(true)
            .with_attributes(&["#[no_mangle]"]);
        assert_eq!(no_mangle_method.link_symbol, Some("main"));
        assert_eq!(classify_entry_point(&no_mangle_method), Some(NoMainStart));
        let exported_start = desc("fw::Boot::reset")
            .with_assoc_fn(true)
            .with_attributes(&["#[unsafe(export_name = \"_start\")]"]);
        assert_eq!(classify_entry_point(&exported_start), Some(NoMainStart));
    }

    #[test]
    fn conditional_attributes_count_as_present() {
        use EntryPointKind::{EntryAttribute, NoMainStart};
        for attrs in [
            &["#[cfg_attr(not(test), no_mangle)]"][..],
            &["#[cfg_attr(not(test), unsafe(no_mangle))]"],
            &["#[cfg_attr(target_os = \"none\", inline, no_mangle)]"],
            &["#[cfg_attr(all(a, any(b, c)), cfg_attr(d, no_mangle))]"],
            &["#[ cfg_attr ( feature = \"rt,x\" , no_mangle , ) ]"],
            &["#[inline]", "#[cfg_attr(not(test), no_mangle)]"],
        ] {
            let start = desc("fw::arch::_start").with_attributes(attrs);
            assert_eq!(start.link_symbol, Some("_start"), "{attrs:?}");
            assert_eq!(classify_entry_point(&start), Some(NoMainStart), "{attrs:?}");
        }
        for attrs in [
            &["#[cfg_attr(not(test), export_name = \"_start\")]"][..],
            &[
                "#[cfg_attr(a, export_name = \"boot\")]",
                "#[cfg_attr(not(a), export_name = \"__start\")]",
            ],
            &[
                "#[cfg_attr(not(a), export_name = \"main\")]",
                "#[cfg_attr(a, export_name = \"boot\")]",
            ],
            &["#[export_name = \"main\"]", "#[no_mangle]"],
        ] {
            let boot = desc("fw::arch::boot").with_attributes(attrs);
            assert_eq!(classify_entry_point(&boot), Some(NoMainStart), "{attrs:?}");
        }
        for attrs in [
            &["#[cfg_attr(not(test), entry)]"][..],
            &["#[cfg_attr(not(test), cortex_m_rt::entry)]"],
            &["#[cfg_attr(feature = \"rt\", tokio::main(flavor = \"current_thread\"))]"],
        ] {
            let reset = desc("fw::reset").with_attributes(attrs);
            assert!(reset.has_entry_attr, "{attrs:?}");
            assert_eq!(
                classify_entry_point(&reset),
                Some(EntryAttribute),
                "{attrs:?}"
            );
        }
        // The predicate itself is never an attribute, and a `cfg_attr`
        // without attributes adds nothing.
        for attrs in [
            &["#[cfg_attr(entry, inline)]"][..],
            &["#[cfg_attr(no_mangle, inline)]"],
            &["#[cfg_attr(main)]"],
            &["#[cfg_attr(feature = \"entry, no_mangle\", inline)]"],
            &["#[cfg(not(test))]"],
            &["#[cfg_attrs(a, entry)]"],
        ] {
            let helper = desc("fw::arch::_start").with_attributes(attrs);
            assert!(!helper.has_entry_attr, "{attrs:?}");
            assert_eq!(helper.link_symbol, None, "{attrs:?}");
            assert_eq!(classify_entry_point(&helper), None, "{attrs:?}");
        }
        // Nesting beyond the followed depth fails closed.
        let mut nested = std::string::String::from("no_mangle");
        for _ in 0..=MAX_CFG_ATTR_DEPTH {
            nested = std::format!("cfg_attr(a, {nested})");
        }
        let deep = desc("fw::helper").with_attributes(&[nested.as_str()]);
        assert_eq!(classify_entry_point(&deep), Some(EntryAttribute));
    }

    #[test]
    fn attributes_are_found_like_the_rust_lexer_finds_them() {
        use EntryPointKind::{EntryAttribute, NoMainStart};
        for attrs in [
            &["# [no_mangle]"][..],
            &["#\n[no_mangle]"],
            &["#[no_mangle] // exported for the loader"],
            &["/* boot */ #[no_mangle]"],
            &["/// The reset vector.\n#[no_mangle]"],
            &["#[inline] #[no_mangle]"],
            &["#[no_mangle]\n#[inline]"],
            &["#[unsafe(no_mangle)] /* c */"],
            &["#[cfg_attr(not(test), no_mangle)] // c"],
            &["# [ cfg_attr ( not ( test ) , no_mangle ) ]"],
        ] {
            let start = desc("fw::arch::_start").with_attributes(attrs);
            assert_eq!(start.link_symbol, Some("_start"), "{attrs:?}");
            assert_eq!(classify_entry_point(&start), Some(NoMainStart), "{attrs:?}");
        }
        for attrs in [
            &["# [ export_name = \"_start\" ]"][..],
            &["#[inline]\n#[export_name = \"__start\"] // c"],
            &["/** doc */ #[unsafe(export_name = \"main\")]"],
        ] {
            let boot = desc("fw::boot").with_attributes(attrs);
            assert_eq!(classify_entry_point(&boot), Some(NoMainStart), "{attrs:?}");
        }
        for attr in [
            "# [entry]",
            "#[entry] // c",
            "/* c */ #[cortex_m_rt::entry]",
            "#[inline]\n#[entry]",
            "#[tokio::main(flavor = \"current_thread\")] // c",
        ] {
            assert!(is_entry_attribute(attr), "{attr}");
            let reset = desc("fw::reset").with_attributes(&[attr]);
            assert_eq!(classify_entry_point(&reset), Some(EntryAttribute), "{attr}");
        }
        for attr in [
            "# ! [no_main]",
            "#!\n[no_main]",
            "#![no_main] // c",
            "/* c */ #![no_main]",
            "#![no_std]\n#![no_main]",
        ] {
            assert!(is_no_main_attribute(attr), "{attr}");
        }
        // Text inside comments and literals is never an attribute.
        for attrs in [
            &["// #[no_mangle]"][..],
            &["/* #[no_mangle] */ #[inline]"],
            &["#[doc = \"#[no_mangle]\"]"],
            &["#[inline] // #[entry]"],
            &["#[doc = \"entry\"]"],
            &[""],
        ] {
            let helper = desc("fw::arch::_start").with_attributes(attrs);
            assert_eq!(helper.link_symbol, None, "{attrs:?}");
            assert!(!helper.has_entry_attr, "{attrs:?}");
            assert_eq!(classify_entry_point(&helper), None, "{attrs:?}");
        }
        assert!(!is_no_main_attribute("// #![no_main]"));
        assert!(!is_no_main_attribute("#![doc = \"#![no_main]\"]"));
        assert!(!is_entry_attribute("/* #[entry] */"));
        // The iterator itself.
        let bodies: Vec<&str> =
            attribute_bodies("/// d\n#[a(b, [c])] # ! [d = \"]\"] // e\n#[f]").collect();
        assert_eq!(bodies, ["a(b, [c])", "d = \"]\"", "f"]);
        assert_eq!(
            attribute_bodies("no_mangle").collect::<Vec<_>>(),
            ["no_mangle"]
        );
        assert_eq!(attribute_bodies("  ").count(), 0);
        assert_eq!(
            attribute_bodies("#[unclosed").collect::<Vec<_>>(),
            ["unclosed"]
        );
    }

    #[test]
    fn crate_attributes_derive_no_main() {
        use EntryPointKind::NoMainStart;
        for attr in [
            "#![no_main]",
            "no_main",
            "#![cfg_attr(not(test), no_main)]",
            "#![cfg_attr(target_os = \"none\", no_std, no_main)]",
            "#![cfg_attr(a, cfg_attr(b, no_main))]",
        ] {
            assert!(is_no_main_attribute(attr), "{attr}");
            let start = desc("fw::_start").with_crate_attributes(&["#![no_std]", attr]);
            assert!(start.crate_no_main, "{attr}");
            assert_eq!(classify_entry_point(&start), Some(NoMainStart), "{attr}");
        }
        for attr in [
            "#![no_std]",
            "#![cfg_attr(no_main, no_std)]",
            "#![cfg_attr(feature = \"x, no_main\", no_std)]",
            "#![no_main_please]",
            "#![doc = \"no_main\"]",
            "",
        ] {
            assert!(!is_no_main_attribute(attr), "{attr}");
            let start = desc("fw::_start").with_crate_attributes(&[attr]);
            assert!(!start.crate_no_main, "{attr}");
            assert_eq!(classify_entry_point(&start), None, "{attr}");
        }
        // Attributes only ever add the fact.
        let kept = desc("fw::_start")
            .with_crate_no_main(true)
            .with_crate_attributes(&["#![no_std]"]);
        assert!(kept.crate_no_main);
    }

    #[test]
    fn attributes_tolerate_rust_comments_and_cfg_attr_entry_symmetry() {
        use EntryPointKind::{EntryAttribute, NoMainStart};
        // `is_entry_attribute` unwraps `cfg_attr` symmetrically with
        // `is_no_main_attribute` and ignores comments inside attributes.
        for attr in [
            "#[cfg_attr(not(test), entry)]",
            "#[cfg_attr(not(test), cortex_m_rt::entry)]",
            "#[/* boot */ cfg_attr(/* pred */ not(test), /* attr */ entry /* end */)]",
            "#[cfg_attr(a, cfg_attr(b, tokio::main(flavor = \"current_thread\")))]",
        ] {
            assert!(is_entry_attribute(attr), "{attr}");
        }
        for attr in [
            "#[cfg_attr(entry, inline)]",
            "#[cfg_attr(not(test), inline)]",
            "#[cfg_attr(not(test), /* c */ maintain)]",
        ] {
            assert!(!is_entry_attribute(attr), "{attr}");
        }
        // Comments inside `no_main`, `no_mangle`, `unsafe(...)`, `export_name`,
        // and `cfg_attr` must not hide entry points.
        for attr in [
            "#![/* boot */ no_main /* end */]",
            "#![/* c */ cfg_attr(not(test), /* c */ no_main /* c */)]",
        ] {
            assert!(is_no_main_attribute(attr), "{attr}");
        }
        for attrs in [
            &["#[/* boot */ no_mangle /* end */]"][..],
            &["#[/* c */ unsafe(/* c */ no_mangle /* c */) /* c */]"],
            &["#[cfg_attr(not(test), /* c */ no_mangle /* c */)]"],
            &["#[/* c */ cfg_attr(not(test), /* c */ unsafe(/* c */ no_mangle))]"],
        ] {
            let start = desc("fw::arch::_start").with_attributes(attrs);
            assert_eq!(classify_entry_point(&start), Some(NoMainStart), "{attrs:?}");
        }
        for attrs in [
            &["#[/* c */ export_name /* c */ = /* c */ \"_start\" /* c */]"][..],
            &["#[unsafe(/* c */ export_name = /* c */ r#\"_start\"# /* c */)]"],
            &["#[cfg_attr(not(test), /* c */ export_name /* c */ = /* c */ \"\\x5fstart\")]"],
        ] {
            let boot = desc("fw::arch::boot").with_attributes(attrs);
            assert_eq!(classify_entry_point(&boot), Some(NoMainStart), "{attrs:?}");
        }
        let reset = desc("fw::reset").with_attributes(&[
            "#[/* c */ cfg_attr(not(test), /* c */ cortex_m_rt :: /* c */ entry)]",
        ]);
        assert_eq!(classify_entry_point(&reset), Some(EntryAttribute));
        // Trailing non-comment tokens after `unsafe(...)` or `export_name` stay rejected.
        assert_eq!(
            classify_entry_point(
                &desc("fw::arch::_start").with_attributes(&["#[unsafe(no_mangle) bogus]"])
            ),
            None
        );
        assert_eq!(
            classify_entry_point(
                &desc("fw::boot").with_attributes(&["#[export_name = \"_start\" bogus]"])
            ),
            None
        );
    }

    #[test]
    fn escaped_export_names_are_decoded() {
        use EntryPointKind::NoMainStart;
        for (attr, symbol) in [
            ("#[export_name = \"\\x5fstart\"]", "_start"),
            ("#[export_name = \"\\u{5f}start\"]", "_start"),
            ("#[export_name = \"\\u{00_5F}\\x5Fstart\"]", "__start"),
            ("#[export_name = \"m\\x61in\"]", "main"),
            ("#[export_name = \"ma\\\n      in\"]", "main"),
            ("#[unsafe(export_name = \"\\u{6d}ain\")]", "main"),
            (
                "#[cfg_attr(not(test), export_name = \"_st\\x61rt\")]",
                "_start",
            ),
        ] {
            let boot = desc("fw::boot").with_attributes(&[attr]);
            assert_eq!(boot.link_symbol, Some(symbol), "{attr}");
            assert_eq!(classify_entry_point(&boot), Some(NoMainStart), "{attr}");
        }
        for attr in [
            // Escapes that decode to another name, or to nothing.
            "#[export_name = \"\\x5fstar\\x74ed\"]",
            "#[export_name = \"\\x5f\\x5f\\x5fstart\"]",
            "#[export_name = \"\\nmain\"]",
            "#[export_name = \"main\\0\"]",
            "#[export_name = \"\\xffstart\"]",
            "#[export_name = \"\\u{}main\"]",
            "#[export_name = \"\\u{110000}main\"]",
            "#[export_name = \"\\qmain\"]",
            // A raw literal has no escapes: this exports the 8 characters.
            "#[export_name = r\"\\x5fstart\"]",
            "#[export_name = \"_start\\\"\" extra]",
        ] {
            let helper = desc("fw::helper").with_attributes(&[attr]);
            assert_eq!(classify_entry_point(&helper), None, "{attr}");
        }
        assert!(escaped_literal_decodes_to("\\x5fstart", "_start"));
        assert!(escaped_literal_decodes_to("_start", "_start"));
        assert!(!escaped_literal_decodes_to("_start", "__start"));
        assert!(!escaped_literal_decodes_to("__start", "_start"));
        assert!(!escaped_literal_decodes_to("", "main"));
        assert_eq!(escaped_entry_symbol("\\x6dain"), Some("main"));
        assert_eq!(escaped_entry_symbol("\\x6dain_loop"), None);
    }

    // ---- Guard 1: trivial `requires` lexer ---------------------------------

    #[test]
    fn trivial_requires_accepts_only_tautological_clauses() {
        for trivial in [
            "",
            "   \n\t ",
            "true",
            "True",
            "(true)",
            "((true))",
            "[true]",
            "[true, true]",
            "[true, (true),]",
            "[ True , True ]",
            "[]",
            "// nothing to require\ntrue",
            "true // trailing comment",
            "/* a /* nested */ block */ true",
            "true /* x > 0 */",
            "-- Lean line comment\nTrue",
            "/- Lean /- nested -/ block -/ True",
            "// only a comment",
        ] {
            assert!(is_syntactically_trivial_requires(trivial), "{trivial:?}");
        }
        for non_trivial in [
            "x > 0",
            "argc == 1",
            "false",
            "False",
            "TRUE",
            "!true",
            "true && x",
            "true || false",
            "true, true",
            "true true",
            "()",
            "(true",
            "true)",
            "[true",
            "true]",
            "[true,,]",
            "[,]",
            "(true,)",
            "[true, argc > 0]",
            "\"true\"",
            "r#\"true\"#",
            "'t'",
            "true.then(|| ())",
            "truex",
            "x",
        ] {
            assert!(
                !is_syntactically_trivial_requires(non_trivial),
                "{non_trivial:?}"
            );
        }
    }

    #[test]
    fn trivial_requires_fails_closed_on_malformed_source() {
        for malformed in [
            "/* unclosed true",
            "true /* unclosed",
            "/- unclosed true",
            "/* outer /* inner */ true",
            "\"unclosed",
            "true \"unclosed",
            "r#\"unclosed\"",
            "'\\",
        ] {
            assert!(
                !is_syntactically_trivial_requires(malformed),
                "{malformed:?}"
            );
            assert_eq!(
                scan_trivial_requires(malformed, SpecSyntax::Any),
                Err(SpecScanError::UnclosedLiteralOrComment),
                "{malformed:?}"
            );
        }
        // Nesting beyond the fixed stack fails closed instead of overflowing.
        let mut deep = std::string::String::new();
        for _ in 0..MAX_TRIVIAL_REQUIRES_DEPTH {
            deep.push('(');
        }
        deep.push_str("true");
        for _ in 0..MAX_TRIVIAL_REQUIRES_DEPTH {
            deep.push(')');
        }
        assert!(is_syntactically_trivial_requires(&deep));
        let deeper = std::format!("({deep})");
        assert!(!is_syntactically_trivial_requires(&deeper));
    }

    #[test]
    fn trivial_requires_respects_the_source_dialect() {
        // `--` is a Lean comment but Rust code; `//` is the reverse.
        let lean_commented = "True -- x > 0";
        assert!(is_syntactically_trivial_requires_in(
            lean_commented,
            SpecSyntax::Lean
        ));
        assert!(!is_syntactically_trivial_requires_in(
            lean_commented,
            SpecSyntax::Rust
        ));
        let rust_commented = "true // x > 0";
        assert!(is_syntactically_trivial_requires_in(
            rust_commented,
            SpecSyntax::Rust
        ));
        assert!(!is_syntactically_trivial_requires_in(
            rust_commented,
            SpecSyntax::Lean
        ));
        // Block comments of the other dialect are code as well.
        assert!(!is_syntactically_trivial_requires_in(
            "true /- x -/",
            SpecSyntax::Rust
        ));
        assert!(!is_syntactically_trivial_requires_in(
            "True /* x */",
            SpecSyntax::Lean
        ));
        assert!(RequiresClause::rust("[true, true]").is_syntactically_trivial());
        assert!(RequiresClause::lean("True").is_syntactically_trivial());
        assert!(!RequiresClause::any("argc > 0").is_syntactically_trivial());
        // `True` is an arbitrary identifier in Rust, not the boolean literal
        // `true`, and `true` is `Bool.true` rather than `Prop` `True` in Lean.
        assert!(!RequiresClause::rust("True").is_syntactically_trivial());
        assert!(!RequiresClause::lean("true").is_syntactically_trivial());
        // Lean primed identifier `b'` must not fail as an unclosed byte literal.
        assert_eq!(scan_trivial_requires("b' = 1", SpecSyntax::Lean), Ok(false));
        assert_eq!(scan_trivial_requires("b' = 1", SpecSyntax::Any), Ok(false));
        assert_eq!(
            scan_trivial_requires("b' = 1", SpecSyntax::Rust),
            Err(SpecScanError::UnclosedLiteralOrComment)
        );
        assert_eq!(
            scan_trivial_requires("cr#\"quote \" true\"#", SpecSyntax::Rust),
            Ok(false)
        );
    }

    // ---- Guard 1: dynamic entry-point `requires` check ---------------------

    #[test]
    fn non_entry_points_are_exempt_and_never_evaluated() {
        let outcome = check_entry_point_requires(
            config().with_max_trials(0),
            &desc("my_crate::helper"),
            Some(RequiresClause::rust("x > 0")),
            |_: &u8| -> bool { panic!("precondition of a non-entry point must not run") },
        );
        assert_eq!(outcome, EntryPointGuardOutcome::NotEntryPoint);
        assert!(outcome.passes());
        assert_eq!(outcome.violation(), None);
        assert_eq!(outcome.guard_class(), None);
        assert_eq!(outcome.into_result(), Ok(None));
        // A method named `main` is exempt as well.
        let method = desc("my_crate::Type::main").with_assoc_fn(true);
        assert_eq!(
            check_entry_point_requires(config(), &method, None, |x: &u8| *x == 1),
            EntryPointGuardOutcome::NotEntryPoint
        );
    }

    #[test]
    fn entry_point_without_requires_passes() {
        let outcome = check_entry_point_requires(config(), &desc("app::main"), None, |_: &()| true);
        assert_eq!(
            outcome,
            EntryPointGuardOutcome::Guarded {
                entry_kind: EntryPointKind::Main,
                trials_run: 256,
            }
        );
        assert_eq!(outcome.into_result(), Ok(Some(EntryPointKind::Main)));

        // A trivial clause and an ABI-total precondition pass on `_start`.
        let start = desc("fw::_start").with_crate_no_main(true);
        let outcome = check_entry_point_requires(
            config().with_max_trials(64),
            &start,
            Some(RequiresClause::rust("[true, true] // nothing to require")),
            |_: &(u32, usize)| true,
        );
        assert_eq!(
            outcome,
            EntryPointGuardOutcome::Guarded {
                entry_kind: EntryPointKind::NoMainStart,
                trials_run: 64,
            }
        );
    }

    #[test]
    fn explicit_non_trivial_requires_on_entry_point_is_rejected() {
        for (descriptor, kind) in [
            (desc("app::main"), EntryPointKind::Main),
            (
                desc("fw::_start").with_crate_no_main(true),
                EntryPointKind::NoMainStart,
            ),
            (
                desc("fw::reset").with_entry_attr(true),
                EntryPointKind::EntryAttribute,
            ),
        ] {
            // The dynamic precondition is total: only the authored clause is
            // at fault.
            let outcome = check_entry_point_requires(
                config(),
                &descriptor,
                Some(RequiresClause::rust("argc == 1")),
                |_: &u8| true,
            );
            let violation = outcome.violation().copied().expect("violation");
            assert_eq!(
                violation,
                EntryPointGuardViolation {
                    guard: SpecBoundaryGuardClass::EntryPointPrecondition,
                    entry_kind: kind,
                    kind: EntryPointGuardViolationKind::ExplicitNonTrivialRequires,
                    trials_run: 0,
                    precondition_hits: 0,
                }
            );
            assert_eq!(violation.vacuity_class(), VacuityClass::DeadPrecondition);
            assert_eq!(violation.counterexample_trial(), None);
            assert!(!outcome.passes());
            assert_eq!(
                outcome.guard_class(),
                Some(SpecBoundaryGuardClass::EntryPointPrecondition)
            );
            assert_eq!(outcome.into_result(), Err(violation));
        }
        // Malformed clause source fails closed.
        let outcome = check_entry_point_requires(
            config(),
            &desc("app::main"),
            Some(RequiresClause::rust("true /* unclosed")),
            |_: &u8| true,
        );
        assert_eq!(
            outcome.violation().map(|violation| violation.kind),
            Some(EntryPointGuardViolationKind::ExplicitNonTrivialRequires)
        );
    }

    /// `verus#3606`: `fn main(argc: u8) -> u8 { 1 / argc }` with
    /// `requires argc == 1` passes every ordinary gate (the precondition is
    /// satisfiable, the contract is strong), and only the entry-point guard
    /// reports that the loader may start it with `argc == 0`.
    #[test]
    fn satisfiable_non_universal_requires_passes_contract_check_but_not_the_guard() {
        let pre = |argc: &u8| *argc == 1;
        let strong = check_contract(
            config(),
            pre,
            |argc: &u8| 1 / *argc,
            |_: &u8, ret: &u8| *ret == 1,
        );
        assert!(strong.is_strong(), "{strong:?}");
        assert!(strong.stats().precondition_hits >= 1);

        let outcome = check_entry_point_requires(
            config(),
            &desc("entry_demo::main"),
            Some(RequiresClause::rust("true")),
            pre,
        );
        let violation = outcome.violation().copied().expect("violation");
        assert_eq!(
            violation.kind,
            EntryPointGuardViolationKind::PreconditionRejectedInput { trial_idx: 0 }
        );
        assert_eq!(violation.entry_kind, EntryPointKind::Main);
        assert_eq!(violation.trials_run, 1);
        assert_eq!(violation.precondition_hits, 0);
        assert_eq!(violation.vacuity_class(), VacuityClass::DeadPrecondition);
        // The counterexample replays to the excluded ABI input `argc == 0`.
        let trial = violation.counterexample_trial().expect("trial");
        assert_eq!(replay_trial_input::<u8>(config(), trial), Some(0));
    }

    #[test]
    fn precondition_excluding_one_abi_input_is_found_and_replayed() {
        let outcome = check_entry_point_requires(
            config(),
            &desc("fw::__start").with_crate_no_main(true),
            None,
            |argc: &u32| *argc != u32::MAX,
        );
        let violation = outcome.violation().copied().expect("violation");
        let EntryPointGuardViolationKind::PreconditionRejectedInput { trial_idx } = violation.kind
        else {
            panic!("unexpected violation {violation:?}");
        };
        assert_eq!(
            replay_trial_input::<u32>(config(), trial_idx),
            Some(u32::MAX)
        );
        assert_eq!(violation.trials_run, trial_idx + 1);
        assert_eq!(violation.precondition_hits, trial_idx);
        assert_eq!(violation.entry_kind, EntryPointKind::NoMainStart);
    }

    #[test]
    fn trapping_precondition_and_zero_budget_fail_closed() {
        let outcome =
            check_entry_point_requires_fallible(config(), &desc("app::main"), None, |argc: &u8| {
                if *argc == 2 { Err(()) } else { Ok(true) }
            });
        let violation = outcome.violation().copied().expect("violation");
        let EntryPointGuardViolationKind::PreconditionTrapped { trial_idx } = violation.kind else {
            panic!("unexpected violation {violation:?}");
        };
        assert_eq!(replay_trial_input::<u8>(config(), trial_idx), Some(2));
        assert_eq!(violation.counterexample_trial(), Some(trial_idx));
        assert_eq!(violation.precondition_hits, trial_idx);

        // `max_trials == 0` proves nothing about the ABI: fail closed.
        let outcome = check_entry_point_requires(
            config().with_max_trials(0),
            &desc("app::main"),
            None,
            |_: &u8| true,
        );
        assert_eq!(
            outcome.violation().copied(),
            Some(EntryPointGuardViolation {
                guard: SpecBoundaryGuardClass::EntryPointPrecondition,
                entry_kind: EntryPointKind::Main,
                kind: EntryPointGuardViolationKind::DegenerateConfig,
                trials_run: 0,
                precondition_hits: 0,
            })
        );
        // A single trial is enough to observe a rejection at the first
        // boundary input.
        let outcome = check_entry_point_requires(
            config().with_max_trials(1),
            &desc("app::main"),
            None,
            |argc: &u8| *argc != 0,
        );
        assert_eq!(
            outcome.violation().map(|violation| violation.kind),
            Some(EntryPointGuardViolationKind::PreconditionRejectedInput { trial_idx: 0 })
        );
    }

    #[test]
    fn entry_point_guard_is_deterministic_in_the_seed() {
        let run = |seed: u64| {
            check_entry_point_requires(
                config().with_seed(seed).with_max_trials(512),
                &desc("app::main"),
                None,
                |argc: &u64| *argc % 1_000_003 != 17,
            )
        };
        assert_eq!(run(7), run(7));
        assert_eq!(run(0), run(0));
    }

    // ---- Guard 3: `SemanticOutcome` ----------------------------------------

    #[test]
    fn semantic_outcome_conversions_and_branches() {
        type Outcome = SemanticOutcome<u8, bool>;
        assert_eq!(Outcome::from_result(Ok(3)), SemanticOutcome::Ok(3));
        assert_eq!(Outcome::from(Err(true)), SemanticOutcome::Err(true));
        assert_eq!(Outcome::Ok(3).into_result(), Some(Ok(3)));
        assert_eq!(Outcome::Err(false).into_result(), Some(Err(false)));
        assert_eq!(Outcome::Ub.into_result(), None);
        assert_eq!(Outcome::Unsupported.into_result(), None);
        assert_eq!(Outcome::Ok(3).branch(), OutcomeBranch::Ok);
        assert_eq!(Outcome::Err(true).branch(), OutcomeBranch::Err);
        assert_eq!(Outcome::Ub.branch(), OutcomeBranch::Ub);
        assert_eq!(Outcome::Unsupported.branch(), OutcomeBranch::Unsupported);
        assert!(Outcome::Ub.is_fault() && Outcome::Unsupported.is_fault());
        assert!(!Outcome::Ok(0).is_fault() && !Outcome::Err(true).is_fault());

        assert_eq!(<Outcome as ErrorBranchOutcome>::ub(), Some(Outcome::Ub));
        assert_eq!(
            <Outcome as ErrorBranchOutcome>::unsupported(),
            Some(Outcome::Unsupported)
        );
        assert_eq!(
            <Outcome as ErrorBranchOutcome>::from_error(true),
            Outcome::Err(true)
        );
        assert_eq!(Outcome::Err(true).error_payload(), Some(&true));
        assert_eq!(Outcome::Ok(1).error_payload(), None);
        assert_eq!(<Result<u8, bool> as ErrorBranchOutcome>::ub(), None);
        assert_eq!(
            <Result<u8, bool> as ErrorBranchOutcome>::unsupported(),
            None
        );
        assert_eq!(Err::<u8, bool>(true).error_payload(), Some(&true));
        assert_eq!(Ok::<u8, bool>(1).branch(), OutcomeBranch::Ok);
    }

    #[test]
    fn semantic_outcome_sampling_covers_all_four_branches_at_the_boundary() {
        type Outcome = SemanticOutcome<u8, bool>;
        let count = <Outcome as SampleInput>::BOUNDARY_COUNT;
        assert_eq!(count, <Result<u8, bool> as SampleInput>::BOUNDARY_COUNT + 2);
        let mut rng = SplitMix64::default();
        let mut seen = [false; 4];
        for trial_idx in 0..count {
            let sample = Outcome::sample_at(trial_idx, &mut rng);
            seen[match sample.branch() {
                OutcomeBranch::Ok => 0,
                OutcomeBranch::Err => 1,
                OutcomeBranch::Ub => 2,
                OutcomeBranch::Unsupported => 3,
            }] = true;
        }
        assert_eq!(seen, [true; 4]);
        assert_eq!(Outcome::sample_at(count - 2, &mut rng), Outcome::Ub);
        assert_eq!(
            Outcome::sample_at(count - 1, &mut rng),
            Outcome::Unsupported
        );
        // Seeded draws are deterministic.
        let draw = |seed: u64| {
            let mut rng = SplitMix64::new(seed);
            (count..count + 64)
                .map(|idx| Outcome::sample_at(idx, &mut rng))
                .collect::<Vec<_>>()
        };
        assert_eq!(draw(1), draw(1));
    }

    #[test]
    fn semantic_outcome_mutants_flip_into_every_other_branch() {
        type Outcome = SemanticOutcome<u8, bool>;
        let collect = |start: Outcome| {
            let mut rng = SplitMix64::default();
            let mut mutants = Vec::new();
            start.visit_mutants(&mut rng, |mutant| mutants.push(mutant));
            mutants
        };
        let is_subsingleton = <Outcome as ReturnMutants>::IS_SUBSINGLETON;
        assert!(!is_subsingleton);

        let from_ok = collect(Outcome::Ok(5));
        assert!(from_ok.contains(&Outcome::Ok(6)));
        assert!(from_ok.contains(&Outcome::Ub));
        assert!(from_ok.contains(&Outcome::Unsupported));
        assert!(from_ok.iter().any(|m| matches!(m, Outcome::Err(_))));
        assert!(!from_ok.contains(&Outcome::Ok(5)));
        // The fault flips arrive within the first three mutants.
        assert!(from_ok[..3].contains(&Outcome::Ub));

        let from_err = collect(Outcome::Err(true));
        assert!(from_err.contains(&Outcome::Err(false)));
        assert!(from_err.contains(&Outcome::Ub));
        assert!(from_err.contains(&Outcome::Unsupported));
        assert!(from_err.iter().any(|m| matches!(m, Outcome::Ok(_))));

        let from_ub = collect(Outcome::Ub);
        assert_eq!(from_ub[0], Outcome::Unsupported);
        assert!(!from_ub.contains(&Outcome::Ub));
        assert!(from_ub.iter().any(|m| matches!(m, Outcome::Ok(_))));
        assert!(from_ub.iter().any(|m| matches!(m, Outcome::Err(_))));

        let from_unsupported = collect(Outcome::Unsupported);
        assert_eq!(from_unsupported[0], Outcome::Ub);
        assert!(!from_unsupported.contains(&Outcome::Unsupported));

        // Subsingleton payloads still flip across branches.
        let unit: SemanticOutcome<(), ()> = SemanticOutcome::Ok(());
        let mut rng = SplitMix64::default();
        let mut mutants = Vec::new();
        unit.visit_mutants(&mut rng, |mutant| mutants.push(mutant));
        assert!(mutants.contains(&SemanticOutcome::Ub));
        assert!(mutants.contains(&SemanticOutcome::Unsupported));
        assert!(mutants.contains(&SemanticOutcome::Err(())));
    }

    // ---- Guard 3: static error-branch wildcard scanner ---------------------

    #[test]
    fn wildcard_scanner_flags_every_listed_error_arm_shape() {
        use ErrorWildcardPattern::{
            CatchAllArmTrue, ErrArmTrue, MatchesAnyErr, UbArmTrue, UnsupportedArmTrue,
        };
        let cases: &[(&str, ErrorWildcardPattern)] = &[
            // Rust.
            ("Err(_) => true", ErrArmTrue),
            ("Err(..) => true", ErrArmTrue),
            ("Err(_e) => true", ErrArmTrue),
            ("Err(e) => true", ErrArmTrue),
            ("Err(fun) => true", ErrArmTrue),
            ("Err(ref e) => true", ErrArmTrue),
            ("Result::Err(_) => true", ErrArmTrue),
            ("core::result::Result::Err(_) => true", ErrArmTrue),
            ("Err(_) => (true)", ErrArmTrue),
            ("Err(_) => ((true))", ErrArmTrue),
            ("Err(_) => { true }", ErrArmTrue),
            ("Err(_) => { return true; }", ErrArmTrue),
            ("Err(_) => true,", ErrArmTrue),
            ("Err(_) if true => true", ErrArmTrue),
            ("Err(_) => true || x == 3", ErrArmTrue),
            ("Ok(0) | Err(_) => true", ErrArmTrue),
            ("Some(Ok(_) | Err(_)) => true", ErrArmTrue),
            ("Some(Err(_) | Ok(0)) => true", ErrArmTrue),
            ("(Err(_) | Ok(0)) => true", ErrArmTrue),
            ("Err(E::A | _) => true", ErrArmTrue),
            ("Err(_ | E::A) => true", ErrArmTrue),
            ("Err(()) => true", ErrArmTrue),
            ("Err(_) => !false", ErrArmTrue),
            ("Err(_) => true && true", ErrArmTrue),
            ("Err(_) => (true || x == 3)", ErrArmTrue),
            ("Err(_) => true as bool", ErrArmTrue),
            ("Err(_) => (true as bool)", ErrArmTrue),
            ("(Err(_), _) => true", ErrArmTrue),
            (
                "match out { Ok(v) => *v == x + 1, Err(_) => true }",
                ErrArmTrue,
            ),
            (
                "|out: &Result<u32, E>| match out {\n    Ok(v) => *v == x + 1,\n    Err(_) => true,\n}",
                ErrArmTrue,
            ),
            (
                "#[spec(ensures: |out| match out { Ok(v) => v == x + 1, Err(_) => true })]",
                ErrArmTrue,
            ),
            ("SemanticOutcome::Ub => true", UbArmTrue),
            ("Ub => true", UbArmTrue),
            ("SemanticOutcome::Unsupported => true", UnsupportedArmTrue),
            ("matches!(out, Ok(_) | Err(_))", MatchesAnyErr),
            ("matches!(out, Ok(_) | Err(_),)", MatchesAnyErr),
            ("matches!(out, Err(_) if true)", MatchesAnyErr),
            ("matches!(out, Ok(v) | _)", MatchesAnyErr),
            ("matches!(out, (Err(_) | Ok(0)))", MatchesAnyErr),
            ("matches!(out, Err(_))", MatchesAnyErr),
            ("matches!(f(x), Ok(v) | Err(..))", MatchesAnyErr),
            ("match out { Ok(v) => *v == 1, _ => true }", CatchAllArmTrue),
            // Lean.
            ("| Err _ => True", ErrArmTrue),
            ("| .err _ => True", ErrArmTrue),
            ("| .error _ => True", ErrArmTrue),
            ("| .err e => True", ErrArmTrue),
            ("| .err () => True", ErrArmTrue),
            ("| .err (_ : String) => True", ErrArmTrue),
            ("| .err (e : Result Nat String) => True", ErrArmTrue),
            ("| Except.error _ => True", ErrArmTrue),
            ("| .err _ => (True)", ErrArmTrue),
            ("| .err _ => trivial", ErrArmTrue),
            ("| .err _ => by trivial", ErrArmTrue),
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
            ("| .fail .unsupported => True", UnsupportedArmTrue),
            ("| .fail _ => True", UbArmTrue),
            ("| .ub | .unsupported => True", UbArmTrue),
            ("| .unsupported | .ub => True", UnsupportedArmTrue),
            (
                "match out with\n  | .ok v => v = specFn x\n  | .err _ => True\n  | .ub => False",
                ErrArmTrue,
            ),
            (
                "fun x out => match out with | .ok v => v = x + 1 | .ub => True",
                UbArmTrue,
            ),
            (
                "def post (x : Nat) : Except String Nat → Prop\n  | .ok v => v = x + 1\n  | .error _ => True\n\ntheorem next : True := trivial",
                ErrArmTrue,
            ),
            ("| .ok v => v = 1 | _ => True", CatchAllArmTrue),
        ];
        for (src, expected) in cases {
            assert_eq!(
                detect_error_branch_wildcard(src),
                Some(*expected),
                "{src:?}"
            );
            assert_eq!(
                expected.guard_class(),
                SpecBoundaryGuardClass::ErrorBranchWildcard
            );
        }
    }

    #[test]
    fn wildcard_scanner_does_not_flag_constrained_arms_comments_or_literals() {
        for src in [
            // Constrained error arms.
            "match out { Ok(v) => *v == x + 1, Err(E::Overflow) => x == u32::MAX }",
            "Err(E::Overflow) => true",
            "Err(Unsupported) => true",
            "Err(E::A | E::B) => true",
            "Err(Error::Overflow) => true",
            "Err(0) => true",
            "Err(\"overflow\") => true",
            "Err(MyErr { .. }) => true",
            "Err(_) => x == u32::MAX",
            "Err(()) => *x == u32::MAX",
            "Err(e) => *e == E::Overflow",
            "Err(_) => false",
            "Err(_) if x == u32::MAX => true",
            "Err(_) => true && x == 3",
            "Err(_) => (true && x == 3)",
            "Err(_) => (true || x == 3) && y == 4",
            "Err(_) => true as u8 == 1",
            "Err(_) => true as bool && x == 1",
            "Err(_) => true == done",
            "| .ub => False",
            "| .unsupported => False",
            "| .err _ => False",
            "| .err e => e = .overflow",
            "| .err .overflow => True",
            "| .err .ub => True",
            "| .err .unsupported => True",
            "| .fail .outOfFuel => True",
            "| .err _ => True ∧ x = 3",
            "| .err _ => True → False",
            "| .ub => True = False",
            "| .ok v => v = 1",
            "| .ok _ => True",
            "Ok(_) => true",
            // Scoped catch-all arms: nested inner match and subsequent items
            // must not inherit `Ok` from an outer or earlier `Result` match.
            "match out { Ok(v) => match *v { 0 => false, _ => true }, Err(E::A) => true }",
            "match out { Ok(v) => *v == 1, Err(E::A) => true }\nfn other(x: u32) { match x { 0 => false, _ => true } }",
            "def post1 : Except String Nat → Prop\n  | .ok v => v = 1\n  | .error e => e = \"a\"\ndef helper : Nat → Prop\n  | 0 => False\n  | _ => True",
            "def post : Except String Nat → Prop\n  | .ok v => (match v with | 0 => False | _ => True)\n  | .error e => e = \"a\"",
            // Lambdas and prior definitions must not leak an error ctor into `fun _ => True`.
            "def helper (e : String) := Except.error e\ndef f := fun _ => True",
            "| .ok v => let fallback := Outcome.err e\n  fun _ => True",
            "| .ok v => fun _ => True",
            // Comments.
            "// Err(_) => true\nmatch out { Ok(v) => *v == 1, Err(e) => *e == E::A }",
            "/* Err(_) => true */ match out { Ok(v) => *v == 1, Err(e) => *e == E::A }",
            "/* outer /* Err(_) => true */ still comment */ out.is_ok()",
            "-- | .err _ => True\n| .err e => e = E.a",
            "/- | .ub => True -/ | .ub => False",
            "/- outer /- | .ub => True -/ -/ | .ub => False",
            "/// `Err(_) => true` would be a wildcard.\nfn post() {}",
            // String, raw-string, byte-string, C-string, and character literals.
            "let s = \"Err(_) => true\"; out == Ok(1)",
            "let s = r#\"| .err _ => True\"#; out == Ok(1)",
            "let s = r\"Err(_) => true\"; out == Ok(1)",
            "let s = b\"Err(_) => true\"; out == Ok(1)",
            "let s = c\"Err(_) => true\"; out == Ok(1)",
            "let s = cr#\"quote \" Err(_) => true \"#; out == Ok(1)",
            "let s = \"quote \\\" Err(_) => true\"; out == Ok(1)",
            "| .ok c => c = '\"' ∧ s = \"| .err _ => True\"",
            // Catch-all arms outside an `Ok` match.
            "match x { 0 => out == 1, _ => true }",
            "| 0 => out = 1 | _ => True",
            // `matches!` with constrained or guarded patterns.
            "matches!(out, Ok(_))",
            "matches!(out, Err(E::Overflow))",
            "matches!(out, Ok(v) if v == 3)",
            "matches!(out, Err(_) if x == u32::MAX)",
            "matches!(classify(Err(1)), Ok(_))",
            // A previous arm's body is not a pattern alternative.
            "| .none => r = .err | .some w => True",
            "| .ok v => if v = 1 then True else False | .err e => e = .a",
            // Lean primes (including `b'`), Rust lifetimes, and character literals lex cleanly.
            "| .ok v' => v' = f x' | .err e => e = g x'",
            "| .ok b' => b' = x' | .err e => e = b'",
            "|out: &'a Result<u8, E>| match out { Ok(c) => *c == b'x', Err(e) => *e == E::A }",
            "match c { 'a' => true, '\\n' => false, _ => false }",
            "",
        ] {
            assert_eq!(detect_error_branch_wildcard(src), None, "{src:?}");
        }
    }

    #[test]
    fn wildcard_scanner_fails_closed_on_malformed_source() {
        for malformed in [
            "/* unclosed Err(_) => false",
            "/- unclosed | .ub => False",
            "\"unclosed string",
            "match out { Ok(v) => v == 1, Err(e) => e == \"oops }",
            "r#\"unclosed raw\"",
            "cr#\"unclosed raw c\"",
            "'\\n\nfn f<'a>() {}",
            "Err(_) => true /* unclosed",
        ] {
            assert_eq!(
                detect_error_branch_wildcard(malformed),
                Some(ErrorWildcardPattern::UnclosedLiteralOrComment),
                "{malformed:?}"
            );
            assert_eq!(
                scan_error_branch_wildcard(malformed, SpecSyntax::Any),
                Err(SpecScanError::UnclosedLiteralOrComment),
                "{malformed:?}"
            );
        }
    }

    #[test]
    fn wildcard_scanner_respects_the_source_dialect() {
        // In Rust `--` continues the expression; in Lean it starts a comment.
        let src = "Err(_) => true -- && x == 3";
        assert_eq!(
            scan_error_branch_wildcard(src, SpecSyntax::Lean),
            Ok(Some(ErrorWildcardPattern::ErrArmTrue))
        );
        assert_eq!(scan_error_branch_wildcard(src, SpecSyntax::Rust), Ok(None));
        // Unknown dialect: flag (fail-closed towards reporting).
        assert_eq!(
            detect_error_branch_wildcard(src),
            Some(ErrorWildcardPattern::ErrArmTrue)
        );
        // A Lean wildcard hidden behind a Rust-style comment marker is not
        // hidden from the Lean scanner.
        let lean = "| .err _ => True // ∧ False";
        assert_eq!(scan_error_branch_wildcard(lean, SpecSyntax::Lean), Ok(None));
        assert_eq!(
            scan_error_branch_wildcard(lean, SpecSyntax::Rust),
            Ok(Some(ErrorWildcardPattern::ErrArmTrue))
        );
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

    #[test]
    fn wildcard_scanner_agrees_with_the_parity_vectors() {
        for (dialect, src, expected) in WILDCARD_PARITY_VECTORS {
            let syntax = match *dialect {
                "rust" => SpecSyntax::Rust,
                "lean" => SpecSyntax::Lean,
                "any" => SpecSyntax::Any,
                other => panic!("unknown dialect {other:?}"),
            };
            let found = scan_error_branch_wildcard(src, syntax)
                .expect("parity vectors are well-formed")
                .map_or("", ErrorWildcardPattern::as_str);
            assert_eq!(found, *expected, "{dialect}: {src:?}");
        }
    }

    #[test]
    fn wildcard_scanner_scope_tracking_is_bounded_and_fails_closed() {
        use std::string::String;
        let depth = MAX_OK_SCOPE_DEPTH + 8;
        let opens = "{ ".repeat(depth);
        let closes = " }".repeat(depth);
        // Beyond the tracked capacity a catch-all is reported (fail closed).
        let deep = std::format!("{opens}match x {{ 0 => false, _ => true }}{closes}");
        assert_eq!(
            detect_error_branch_wildcard(&deep),
            Some(ErrorWildcardPattern::CatchAllArmTrue)
        );
        // The stack unwinds: after the nest, scopes are tracked exactly again.
        let after = std::format!("{opens}{closes} match y {{ 0 => false, _ => true }}");
        assert_eq!(detect_error_branch_wildcard(&after), None);
        let after_ok = std::format!("{opens}{closes} match out {{ Ok(v) => *v == 1, _ => true }}");
        assert_eq!(
            detect_error_branch_wildcard(&after_ok),
            Some(ErrorWildcardPattern::CatchAllArmTrue)
        );
        // Sequential Lean matches never accumulate scopes.
        let mut many = String::new();
        for _ in 0..(4 * MAX_OK_SCOPE_DEPTH) {
            many.push_str("(match a with | 0 => False | _ => True) ∧ ");
        }
        let clean = std::format!("{many}(match r with | .ok v => v = 1 | .err e => e = 2)");
        assert_eq!(
            scan_error_branch_wildcard(&clean, SpecSyntax::Lean),
            Ok(None)
        );
        let dirty = std::format!("{many}(match r with | .ok v => v = 1 | _ => True)");
        assert_eq!(
            scan_error_branch_wildcard(&dirty, SpecSyntax::Lean),
            Ok(Some(ErrorWildcardPattern::CatchAllArmTrue))
        );
        // Closers of brackets opened before the snippet are tolerated.
        assert_eq!(
            detect_error_branch_wildcard("} ) ] } match out { Ok(v) => *v == 1, _ => true }"),
            Some(ErrorWildcardPattern::CatchAllArmTrue)
        );
        assert_eq!(
            detect_error_branch_wildcard("} ) ] } match x { 0 => false, _ => true }"),
            None
        );
    }

    #[test]
    fn wildcard_pattern_wire_ids_are_distinct() {
        let all = [
            ErrorWildcardPattern::ErrArmTrue,
            ErrorWildcardPattern::UbArmTrue,
            ErrorWildcardPattern::UnsupportedArmTrue,
            ErrorWildcardPattern::MatchesAnyErr,
            ErrorWildcardPattern::CatchAllArmTrue,
            ErrorWildcardPattern::UnclosedLiteralOrComment,
        ];
        for (i, a) in all.iter().enumerate() {
            for b in &all[i + 1..] {
                assert_ne!(a.as_str(), b.as_str());
            }
            assert_eq!(std::format!("{a}"), a.as_str());
        }
    }

    // ---- Guard 3: dynamic error-branch wildcard checks ---------------------

    fn checked_incr(x: &u32) -> Result<u32, ()> {
        x.checked_add(1).ok_or(())
    }

    /// `Ok(v) => v == x + 1, Err(_) => true`.
    fn incr_wildcard_post(x: &u32, ret: &Result<u32, ()>) -> bool {
        match ret {
            Ok(v) => x.checked_add(1) == Some(*v),
            Err(_) => true,
        }
    }

    /// `Ok(v) => v == x + 1, Err(()) => x == u32::MAX`.
    fn incr_guarded_post(x: &u32, ret: &Result<u32, ()>) -> bool {
        match ret {
            Ok(v) => x.checked_add(1) == Some(*v),
            Err(()) => *x == u32::MAX,
        }
    }

    /// `awsm2`: the wildcard postcondition passes the base contract check and
    /// is deterministically killed by the error-escape probe.
    #[test]
    fn error_wildcard_passes_base_check_and_is_killed_by_the_guard() {
        let base = check_contract(config(), |_: &u32| true, checked_incr, incr_wildcard_post);
        assert!(base.is_strong(), "{base:?}");

        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |_: &u32| true,
            checked_incr,
            incr_wildcard_post,
        );
        let violation = outcome.violation().copied().expect("violation");
        assert_eq!(violation.guard, SpecBoundaryGuardClass::ErrorBranchWildcard);
        assert_eq!(violation.vacuity_class(), VacuityClass::SurvivedAllMutants);
        assert_eq!(
            violation.kind,
            ErrorWildcardViolationKind::ErrorEscapeAccepted { trial_idx: 0 }
        );
        assert_eq!(
            outcome.vacuity_class(),
            Some(VacuityClass::SurvivedAllMutants)
        );
        assert_eq!(
            outcome.guard_class(),
            Some(SpecBoundaryGuardClass::ErrorBranchWildcard)
        );
        assert!(!outcome.is_strong());
        // The counterexample input is one on which the function succeeds.
        let input = replay_trial_input::<u32>(config(), violation.counterexample_trial())
            .expect("replayable trial");
        assert!(checked_incr(&input).is_ok());
        assert_eq!(violation.stats.base, base.stats());
        // Deterministic: the same configuration reports the same violation.
        assert_eq!(
            outcome,
            check_result_contract_no_error_wildcard(
                config(),
                |_: &u32| true,
                checked_incr,
                incr_wildcard_post,
            )
        );
    }

    #[test]
    fn guarded_result_contract_is_strong() {
        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |_: &u32| true,
            checked_incr,
            incr_guarded_post,
        );
        let ErrorWildcardCheckOutcome::Strong(stats) = outcome else {
            panic!("expected a strong contract, got {outcome:?}");
        };
        assert_eq!(outcome.vacuity_class(), None);
        assert_eq!(outcome.guard_class(), None);
        assert_eq!(outcome.violation(), None);
        assert!(stats.ok_hits > 0);
        // `u32::MAX` is a boundary input, so the error branch is exercised.
        assert!(stats.err_hits > 0);
        assert_eq!(stats.ok_hits + stats.err_hits, stats.base.precondition_hits);
        // `()` has one boundary payload plus two seeded draws per `Ok` hit.
        assert_eq!(stats.error_escape_probes, stats.ok_hits * 3);
        // `()` is a subsingleton: there is no payload mutant to test.
        assert_eq!(stats.err_payload_mutants_tested, 0);
        assert_eq!(stats.fault_probes, 0);
    }

    fn coded_incr(x: &u32) -> Result<u32, u8> {
        x.checked_add(1).ok_or(7)
    }

    #[test]
    fn unconstrained_error_payload_is_rejected() {
        // The error is required exactly when `x == u32::MAX`, but any code is
        // accepted: the constant-wrong-code mutant survives.
        let payload_wildcard = |x: &u32, ret: &Result<u32, u8>| match ret {
            Ok(v) => x.checked_add(1) == Some(*v),
            Err(_) => *x == u32::MAX,
        };
        let base = check_contract(config(), |_: &u32| true, coded_incr, payload_wildcard);
        assert!(base.is_strong(), "{base:?}");

        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |_: &u32| true,
            coded_incr,
            payload_wildcard,
        );
        let violation = outcome.violation().copied().expect("violation");
        let ErrorWildcardViolationKind::ErrorPayloadUnconstrained { trial_idx } = violation.kind
        else {
            panic!("unexpected violation {violation:?}");
        };
        assert_eq!(
            replay_trial_input::<u32>(config(), trial_idx),
            Some(u32::MAX)
        );
        assert!(violation.stats.err_payload_mutants_tested > 0);
        assert_eq!(violation.stats.err_payload_mutants_killed, 0);
        assert_eq!(violation.vacuity_class(), VacuityClass::SurvivedAllMutants);

        // Pinning the code repairs the contract.
        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |_: &u32| true,
            coded_incr,
            |x: &u32, ret: &Result<u32, u8>| match ret {
                Ok(v) => x.checked_add(1) == Some(*v),
                Err(code) => *x == u32::MAX && *code == 7,
            },
        );
        let ErrorWildcardCheckOutcome::Strong(stats) = outcome else {
            panic!("expected a strong contract, got {outcome:?}");
        };
        assert!(stats.err_hits > 0);
        assert!(stats.err_payload_mutants_killed >= stats.err_hits);
    }

    #[test]
    fn wrong_error_payload_escape_on_ok_inputs_is_rejected() {
        // Accepts `Err(0)` everywhere: an error escape with a specific code.
        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |_: &u32| true,
            coded_incr,
            |x: &u32, ret: &Result<u32, u8>| match ret {
                Ok(v) => x.checked_add(1) == Some(*v),
                Err(code) => *code == 0 || (*x == u32::MAX && *code == 7),
            },
        );
        assert_eq!(
            outcome.violation().map(|violation| violation.kind),
            Some(ErrorWildcardViolationKind::ErrorEscapeAccepted { trial_idx: 0 })
        );
    }

    type IncrOutcome = SemanticOutcome<u32, ()>;

    fn semantic_incr(x: &u32) -> IncrOutcome {
        SemanticOutcome::from_result(checked_incr(x))
    }

    fn semantic_guarded_post(x: &u32, ret: &IncrOutcome) -> bool {
        match ret {
            SemanticOutcome::Ok(v) => x.checked_add(1) == Some(*v),
            SemanticOutcome::Err(()) => *x == u32::MAX,
            SemanticOutcome::Ub | SemanticOutcome::Unsupported => false,
        }
    }

    #[test]
    fn semantic_outcome_contract_must_reject_ub_and_unsupported() {
        let strong = check_semantic_outcome_no_error_wildcard(
            config(),
            |_: &u32| true,
            semantic_incr,
            semantic_guarded_post,
        );
        let ErrorWildcardCheckOutcome::Strong(stats) = strong else {
            panic!("expected a strong contract, got {strong:?}");
        };
        assert_eq!(stats.fault_probes, 2 * stats.base.precondition_hits);
        assert!(stats.ok_hits > 0 && stats.err_hits > 0);

        // `| .ub => True`.
        let ub_wildcard = check_semantic_outcome_no_error_wildcard(
            config(),
            |_: &u32| true,
            semantic_incr,
            |x: &u32, ret: &IncrOutcome| {
                matches!(ret, SemanticOutcome::Ub) || semantic_guarded_post(x, ret)
            },
        );
        assert_eq!(
            ub_wildcard.violation().map(|violation| violation.kind),
            Some(ErrorWildcardViolationKind::UbAccepted { trial_idx: 0 })
        );
        assert_eq!(
            ub_wildcard.vacuity_class(),
            Some(VacuityClass::SurvivedAllMutants)
        );

        // `| .unsupported => True`.
        let unsupported_wildcard = check_semantic_outcome_no_error_wildcard(
            config(),
            |_: &u32| true,
            semantic_incr,
            |x: &u32, ret: &IncrOutcome| {
                matches!(ret, SemanticOutcome::Unsupported) || semantic_guarded_post(x, ret)
            },
        );
        assert_eq!(
            unsupported_wildcard
                .violation()
                .map(|violation| violation.kind),
            Some(ErrorWildcardViolationKind::UnsupportedAccepted { trial_idx: 0 })
        );

        // `| .err _ => True` on the semantic outcome type.
        let err_wildcard = check_semantic_outcome_no_error_wildcard(
            config(),
            |_: &u32| true,
            semantic_incr,
            |x: &u32, ret: &IncrOutcome| {
                matches!(ret, SemanticOutcome::Err(())) || semantic_guarded_post(x, ret)
            },
        );
        assert_eq!(
            err_wildcard.violation().map(|violation| violation.kind),
            Some(ErrorWildcardViolationKind::ErrorEscapeAccepted { trial_idx: 0 })
        );
    }

    #[test]
    fn live_fault_accepted_by_the_postcondition_is_rejected() {
        // The body has undefined behavior on `x == 3` and the postcondition
        // waves it through.
        let body = |x: &u32| {
            if *x == 3 {
                IncrOutcome::Ub
            } else {
                semantic_incr(x)
            }
        };
        let outcome = check_semantic_outcome_no_error_wildcard(
            config(),
            |_: &u32| true,
            body,
            |x: &u32, ret: &IncrOutcome| {
                if *x == 3 {
                    matches!(ret, SemanticOutcome::Ub)
                } else {
                    semantic_guarded_post(x, ret)
                }
            },
        );
        let violation = outcome.violation().copied().expect("violation");
        let ErrorWildcardViolationKind::UbAccepted { trial_idx } = violation.kind else {
            panic!("unexpected violation {violation:?}");
        };
        assert_eq!(replay_trial_input::<u32>(config(), trial_idx), Some(3));

        // With the guarded postcondition the same body is a plain live
        // violation of the base check.
        let outcome = check_semantic_outcome_no_error_wildcard(
            config(),
            |_: &u32| true,
            body,
            semantic_guarded_post,
        );
        let ErrorWildcardCheckOutcome::BaseFailed(failure) = outcome else {
            panic!("expected a base failure, got {outcome:?}");
        };
        assert_eq!(failure.class, VacuityClass::SpecViolation);
        assert_eq!(outcome.vacuity_class(), Some(VacuityClass::SpecViolation));
        assert_eq!(outcome.guard_class(), None);
    }

    #[test]
    fn base_failures_are_reported_before_any_probe() {
        // Dead precondition.
        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |_: &u32| false,
            checked_incr,
            incr_guarded_post,
        );
        let ErrorWildcardCheckOutcome::BaseFailed(failure) = outcome else {
            panic!("expected a base failure, got {outcome:?}");
        };
        assert_eq!(failure.class, VacuityClass::DeadPrecondition);

        // Degenerate configuration.
        let outcome = check_result_contract_no_error_wildcard(
            config().with_max_trials(0),
            |_: &u32| true,
            checked_incr,
            incr_wildcard_post,
        );
        let ErrorWildcardCheckOutcome::BaseFailed(failure) = outcome else {
            panic!("expected a base failure, got {outcome:?}");
        };
        assert_eq!(
            failure.detail,
            FailureDetail::Violation(ViolationKind::DegenerateConfig)
        );

        // A trivially true postcondition is the base check's finding.
        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |_: &u32| true,
            checked_incr,
            |_: &u32, _: &Result<u32, ()>| true,
        );
        assert_eq!(
            outcome.vacuity_class(),
            Some(VacuityClass::TrivialPostcondition)
        );
    }

    #[test]
    fn fallible_checks_treat_a_trapping_probe_as_a_rejection() {
        // The postcondition traps (instead of returning `false`) on every
        // outcome it does not expect.
        let trapping_post = |x: &u32, ret: &Result<u32, ()>| -> Result<bool, ()> {
            match ret {
                Ok(v) if x.checked_add(1) == Some(*v) => Ok(true),
                Err(()) if *x == u32::MAX => Ok(true),
                _ => Err(()),
            }
        };
        let outcome = check_result_contract_no_error_wildcard_fallible(
            config(),
            |_: &u32| Ok(true),
            |x: &u32| Ok(checked_incr(x)),
            trapping_post,
        );
        assert!(outcome.is_strong(), "{outcome:?}");

        // A trapping body is a live violation of the base check.
        let outcome = check_result_contract_no_error_wildcard_fallible(
            config(),
            |_: &u32| Ok(true),
            |x: &u32| {
                if *x == 2 {
                    Err(())
                } else {
                    Ok(checked_incr(x))
                }
            },
            trapping_post,
        );
        assert_eq!(outcome.vacuity_class(), Some(VacuityClass::SpecViolation));

        // The fallible semantic form rejects a `Ub` wildcard as well.
        let outcome = check_semantic_outcome_no_error_wildcard_fallible(
            config(),
            |_: &u32| Ok(true),
            |x: &u32| Ok(semantic_incr(x)),
            |x: &u32, ret: &IncrOutcome| {
                Ok(matches!(ret, SemanticOutcome::Ub) || semantic_guarded_post(x, ret))
            },
        );
        assert_eq!(
            outcome.violation().map(|violation| violation.kind),
            Some(ErrorWildcardViolationKind::UbAccepted { trial_idx: 0 })
        );
    }

    #[test]
    fn precondition_restricts_the_probed_inputs() {
        // Under `x < 100` the function never fails, so `Err` is rejected on
        // every hit and no `Err` hit exists.
        let outcome = check_result_contract_no_error_wildcard(
            config(),
            |x: &u32| *x < 100,
            checked_incr,
            |x: &u32, ret: &Result<u32, ()>| matches!(ret, Ok(v) if *v == *x + 1),
        );
        let ErrorWildcardCheckOutcome::Strong(stats) = outcome else {
            panic!("expected a strong contract, got {outcome:?}");
        };
        assert_eq!(stats.err_hits, 0);
        assert_eq!(stats.ok_hits, stats.base.precondition_hits);
    }
}
