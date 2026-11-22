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
    /// Zero distinct mutants were tested (e.g. `max_mutants_per_hit == 0` or
    /// every custom mutant equaled the actual output, however often the bank
    /// repeats it).
    NoDistinctMutantsTested,
    /// All tested mutants satisfied the postcondition; includes probe telemetry.
    AllMutantsSurvived {
        /// Number of inputs on which the classification probe evaluated `post`.
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
/// classification probe so very large `max_trials` budgets do not turn failure
/// classification into an unbounded scan.
const MAX_PROBE_INPUTS: usize = 256;

/// Scales a vacuity-classification probe's input budget deterministically with
/// both `boundary_count` and `max_trials`:
///
/// - Never exceeds `max_trials`, so shrinking `max_trials` to bound callback
///   cost also bounds classification probes.
/// - Covers the entire boundary corpus plus at least [`MIN_PROBE_PRNG_DRAWS`]
///   PRNG draws whenever `max_trials` and [`MAX_PROBE_INPUTS`] permit, so
///   3-tuple, 4-tuple, and compound stateful inputs whose `BOUNDARY_COUNT >= 64`
///   neither truncate their boundary corpus nor draw zero PRNG samples.
/// - Scales smoothly with larger `max_trials` (`max_trials / 4`) up to
///   [`MAX_PROBE_INPUTS`].
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
