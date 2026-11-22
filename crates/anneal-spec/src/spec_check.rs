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
    /// Postcondition evaluated to `true` across all probed `(input, output)` pairs.
    TrivialPostcondition,
    /// Postcondition depends on inputs (evaluates to `false` for some input)
    /// yet appears independent of the output (or mutated post-state).
    UnboundReturnOutput,
    /// Postcondition varies with the output somewhere in the unconstrained
    /// domain (or no distinct mutants were tested), yet every tested mutant
    /// survived on precondition-admissible inputs.
    SurvivedAllMutants,
}

impl VacuityClass {
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
    // Up to 3^4 = 81 representative 4-tuples followed by diagonal `(i, i, i, i)`.
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
        cross.saturating_add(diag)
    };

    fn sample_at(trial_idx: usize, rng: &mut SplitMix64) -> Self {
        let ka = min_usize(A::BOUNDARY_COUNT, 3);
        let kb = min_usize(B::BOUNDARY_COUNT, 3);
        let kc = min_usize(C::BOUNDARY_COUNT, 3);
        let kd = min_usize(D::BOUNDARY_COUNT, 3);
        let cross = ka * kb * kc * kd;
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
        } else if trial_idx < Self::BOUNDARY_COUNT
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
                emit(v.wrapping_add(1));
                emit(v.wrapping_sub(1));
                emit(v ^ 1);
                emit(!v);
                emit(0);
                emit(1);
                emit(<$ty>::MAX);
                emit(<$ty>::MAX.wrapping_sub(1));
                emit(v >> 1);
                emit(v.wrapping_mul(2));
                // Stratified small PRNG draw + full-width PRNG draw.
                let r1: $ty = $full_draw(rng);
                emit(r1 & (0x3F as $ty));
                emit($full_draw(rng));
                emit(v.wrapping_add(2));
                emit(v.wrapping_sub(2));
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
                emit(v.wrapping_add(1));
                emit(v.wrapping_sub(1));
                emit(v ^ 1);
                emit(!v);
                emit(v.wrapping_neg());
                emit(0);
                emit(1);
                emit(-1);
                emit(<$ty>::MIN);
                emit(<$ty>::MAX);
                emit(<$ty>::MAX.wrapping_sub(1));
                emit(v >> 1);
                emit(v.wrapping_mul(2));
                let r1 = rng.next_u64();
                emit(((r1 & 0x7F) as $ty).wrapping_sub(64));
                emit($full_draw(rng));
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
                emit(None);
                v.visit_mutants(rng, |m| emit(Some(m)));
            }
            None => {
                emit(Some(T::sample_at(0, rng)));
                emit(Some(T::sample_at(1, rng)));
                emit(Some(T::sample_at(2, rng)));
                emit(Some(T::sample_at(T::BOUNDARY_COUNT, rng)));
                emit(Some(T::sample_at(T::BOUNDARY_COUNT.saturating_add(1), rng)));
            }
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
        match self {
            Ok(v) => {
                emit(Err(E::sample_at(0, rng)));
                emit(Err(E::sample_at(1, rng)));
                emit(Err(E::sample_at(E::BOUNDARY_COUNT, rng)));
                v.visit_mutants(rng, |m| emit(Ok(m)));
            }
            Err(e) => {
                emit(Ok(T::sample_at(0, rng)));
                emit(Ok(T::sample_at(1, rng)));
                emit(Ok(T::sample_at(T::BOUNDARY_COUNT, rng)));
                e.visit_mutants(rng, |m| emit(Err(m)));
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

impl<A: ReturnMutants + Clone, B: ReturnMutants + Clone> ReturnMutants for (A, B) {
    const IS_SUBSINGLETON: bool = A::IS_SUBSINGLETON && B::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        let per_axis_cap = if A::IS_SUBSINGLETON || B::IS_SUBSINGLETON {
            16
        } else {
            5
        };

        let mut first_a: Option<A> = None;
        let mut second_a: Option<A> = None;
        let mut a_emitted = 0usize;
        self.0.visit_mutants(rng, |a_mut| {
            if a_emitted < per_axis_cap {
                if first_a.is_none() {
                    first_a = Some(a_mut.clone());
                } else if second_a.is_none() {
                    second_a = Some(a_mut.clone());
                }
                emit((a_mut, self.1.clone()));
                a_emitted += 1;
            }
        });

        let mut b_emitted = 0usize;
        self.1.visit_mutants(rng, |b_mut| {
            if b_emitted < per_axis_cap {
                emit((self.0.clone(), b_mut.clone()));
                match b_emitted {
                    0 => {
                        if let Some(a1) = first_a.as_ref() {
                            emit((a1.clone(), b_mut));
                        }
                    }
                    1 => {
                        if let Some(a2) = second_a.as_ref().or(first_a.as_ref()) {
                            emit((a2.clone(), b_mut));
                        }
                    }
                    2 => {
                        if let Some(a1) = first_a.as_ref() {
                            emit((a1.clone(), b_mut));
                        }
                    }
                    _ => {}
                }
                b_emitted += 1;
            }
        });
    }
}

impl<A: ReturnMutants + Clone, B: ReturnMutants + Clone, C: ReturnMutants + Clone> ReturnMutants
    for (A, B, C)
{
    const IS_SUBSINGLETON: bool = A::IS_SUBSINGLETON && B::IS_SUBSINGLETON && C::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        let active_axes = (!A::IS_SUBSINGLETON as usize)
            + (!B::IS_SUBSINGLETON as usize)
            + (!C::IS_SUBSINGLETON as usize);
        let per_axis_cap = if active_axes <= 1 { 16 } else { 4 };

        let mut first_a: Option<A> = None;
        let mut a_emitted = 0usize;
        self.0.visit_mutants(rng, |a_mut| {
            if a_emitted < per_axis_cap {
                if first_a.is_none() {
                    first_a = Some(a_mut.clone());
                }
                emit((a_mut, self.1.clone(), self.2.clone()));
                a_emitted += 1;
            }
        });

        let mut first_b: Option<B> = None;
        let mut b_emitted = 0usize;
        self.1.visit_mutants(rng, |b_mut| {
            if b_emitted < per_axis_cap {
                if first_b.is_none() {
                    first_b = Some(b_mut.clone());
                }
                emit((self.0.clone(), b_mut.clone(), self.2.clone()));
                if b_emitted == 0
                    && let Some(a1) = first_a.as_ref()
                {
                    emit((a1.clone(), b_mut, self.2.clone()));
                }
                b_emitted += 1;
            }
        });

        let mut c_emitted = 0usize;
        self.2.visit_mutants(rng, |c_mut| {
            if c_emitted < per_axis_cap {
                emit((self.0.clone(), self.1.clone(), c_mut.clone()));
                if c_emitted == 0 {
                    if let Some(b1) = first_b.as_ref() {
                        emit((self.0.clone(), b1.clone(), c_mut.clone()));
                    }
                    if let (Some(a1), Some(b1)) = (first_a.as_ref(), first_b.as_ref()) {
                        emit((a1.clone(), b1.clone(), c_mut));
                    }
                }
                c_emitted += 1;
            }
        });
    }
}

impl<T: ReturnMutants + Clone, const N: usize> ReturnMutants for [T; N] {
    const IS_SUBSINGLETON: bool = (N == 0) || T::IS_SUBSINGLETON;

    fn visit_mutants<F: FnMut(Self)>(&self, rng: &mut SplitMix64, mut emit: F) {
        if Self::IS_SUBSINGLETON {
            return;
        }

        // Select up to 3 distinct representative element positions: `0`, `N/2`, `N-1`.
        let indices: [Option<usize>; 3] = [
            Some(0),
            if N >= 3 { Some(N / 2) } else { None },
            if N >= 2 {
                Some(N.saturating_sub(1))
            } else {
                None
            },
        ];
        let active_positions = indices.iter().filter(|idx| idx.is_some()).count();
        let per_pos_cap = if active_positions <= 1 { 16 } else { 4 };

        let mut first_front_mut: Option<T> = None;
        for maybe_pos in indices {
            let Some(pos) = maybe_pos else {
                continue;
            };
            let mut emitted = 0usize;
            self[pos].visit_mutants(rng, |elem_mut| {
                if emitted < per_pos_cap {
                    if pos == 0 && first_front_mut.is_none() {
                        first_front_mut = Some(elem_mut.clone());
                    }
                    let mut mutated = self.clone();
                    mutated[pos] = elem_mut;
                    emit(mutated);
                    emitted += 1;
                }
            });
        }

        if N >= 2 {
            let mut swapped = self.clone();
            swapped.swap(0, N - 1);
            emit(swapped);

            let mut reversed = self.clone();
            reversed.reverse();
            emit(reversed);

            let mut rotated = self.clone();
            rotated.rotate_left(1);
            emit(rotated);

            if let Some(m0) = first_front_mut {
                let mut both_ends = self.clone();
                both_ends[0] = m0.clone();
                both_ends[N - 1] = m0;
                emit(both_ends);
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

/// Configuration parameters controlling dynamic contract checking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpecCheckConfig {
    /// Deterministic PRNG seed for [`SplitMix64`].
    pub seed: u64,
    /// Total number of input trials to execute (must be `>= 1`).
    pub max_trials: usize,
    /// Minimum number of precondition-admissible trials required (must be `>= 1`).
    pub min_precondition_hits: usize,
    /// Maximum number of distinct output mutants evaluated per precondition hit.
    pub max_mutants_per_hit: usize,
    /// Optional syntactic hint refining `mutants_killed == 0` diagnostics.
    pub syntactic_hint: Option<SyntacticBindingHint>,
    /// For [`check_stateful_contract`], require both non-subsingleton axes
    /// (mutated post-state `S` and return value `R`) to independently kill at
    /// least one mutant.
    pub require_both_state_and_return_kills: bool,
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
}

/// Identifies which phase trapped during [`check_contract_fallible`].
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
    /// Checker configuration had a zero trial or zero hit budget (fail-closed).
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
    /// every custom mutant equaled the actual output).
    NoDistinctMutantsTested,
    /// All tested mutants satisfied the postcondition; includes domain probe telemetry.
    AllMutantsSurvived {
        probed_inputs: usize,
        saw_any_false: bool,
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
    /// Total number of distinct output/state mutants evaluated.
    pub mutants_tested: usize,
    /// Total number of mutants rejected (`post == false`).
    pub mutants_killed: usize,
    /// True iff the return type `R` is a subsingleton (`R::IS_SUBSINGLETON`).
    pub subsingleton_return: bool,
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

/// Runs the deterministic domain-wide classification probe when
/// `mutants_tested > 0 && mutants_killed == 0` on a non-subsingleton return.
fn classify_all_mutants_survived<I, R, Post>(
    config: SpecCheckConfig,
    anchor_ret: R,
    extra_outputs: &[R],
    post: &mut Post,
) -> (VacuityClass, FailureDetail)
where
    I: SampleInput,
    R: ReturnMutants + PartialEq,
    Post: FnMut(&I, &R) -> Result<bool, ()>,
{
    if let Some(hint) = config.syntactic_hint {
        let class = match hint {
            SyntacticBindingHint::ReturnUnused => VacuityClass::UnboundReturnOutput,
            SyntacticBindingHint::SyntacticallyTautological => VacuityClass::TrivialPostcondition,
        };
        return (
            class,
            FailureDetail::AllMutantsSurvived {
                probed_inputs: 0,
                saw_any_false: false,
                saw_output_sensitivity: false,
            },
        );
    }

    let mut probe_rng = SplitMix64::new(config.seed ^ 0xA5A5_5A5A_C3C3_3C3C);
    let probe_input_count = if I::BOUNDARY_COUNT > 64 {
        min_usize(I::BOUNDARY_COUNT, 128)
    } else {
        64
    };

    let mut probed_inputs = 0usize;
    let mut saw_any_false = false;
    let mut saw_output_sensitivity = false;
    let mut false_witness_x: Option<I> = None;
    let mut true_witness_x: Option<I> = None;

    for idx in 0..probe_input_count {
        let x_probe = I::sample_at(idx, &mut probe_rng);
        probed_inputs += 1;
        let mut saw_true_here = false;
        let mut saw_false_here = false;

        if let Ok(holds) = post(&x_probe, &anchor_ret) {
            if holds {
                saw_true_here = true;
            } else {
                saw_false_here = true;
                saw_any_false = true;
            }
        }

        for r in extra_outputs {
            if saw_true_here && saw_false_here {
                break;
            }
            if let Ok(holds) = post(&x_probe, r) {
                if holds {
                    saw_true_here = true;
                } else {
                    saw_false_here = true;
                    saw_any_false = true;
                }
            }
        }

        if !(saw_true_here && saw_false_here) {
            anchor_ret.visit_mutants(&mut probe_rng, |cand| {
                if saw_true_here && saw_false_here {
                    return;
                }
                if let Ok(holds) = post(&x_probe, &cand) {
                    if holds {
                        saw_true_here = true;
                    } else {
                        saw_false_here = true;
                        saw_any_false = true;
                    }
                }
            });
        }

        if saw_true_here && saw_false_here {
            saw_output_sensitivity = true;
            break;
        }

        if saw_false_here && false_witness_x.is_none() {
            false_witness_x = Some(x_probe);
        } else if saw_true_here && true_witness_x.is_none() {
            true_witness_x = Some(x_probe);
        }
    }

    // If `post` evaluated to `false` on some input outside `pre` (or `true` on
    // some input) without yet observing output sensitivity, walk a bounded
    // mutant chain from `anchor_ret` so point-equality clauses such as
    // `x < 10 || r == 42` are deterministically classified as `SurvivedAllMutants`.
    if !saw_output_sensitivity && (false_witness_x.is_some() || true_witness_x.is_some()) {
        let mut cur = anchor_ret;
        let mut seen: [Option<R>; 4] = [None, None, None, None];
        let mut prev_cur: Option<R> = None;

        for _ in 0..128 {
            if saw_output_sensitivity {
                break;
            }
            let mut next_cur: Option<R> = None;
            cur.visit_mutants(&mut probe_rng, |cand| {
                if saw_output_sensitivity {
                    return;
                }
                if let Some(fx) = false_witness_x.as_ref()
                    && matches!(post(fx, &cand), Ok(true))
                {
                    saw_output_sensitivity = true;
                    return;
                }
                if let Some(tx) = true_witness_x.as_ref()
                    && matches!(post(tx, &cand), Ok(false))
                {
                    saw_any_false = true;
                    saw_output_sensitivity = true;
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
    }

    let class = if !saw_any_false {
        VacuityClass::TrivialPostcondition
    } else if !saw_output_sensitivity {
        VacuityClass::UnboundReturnOutput
    } else {
        VacuityClass::SurvivedAllMutants
    };

    (
        class,
        FailureDetail::AllMutantsSurvived {
            probed_inputs,
            saw_any_false,
            saw_output_sensitivity,
        },
    )
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

    // Fail-closed guard against zero-trial or zero-hit budgets.
    if config.max_trials == 0 || config.min_precondition_hits == 0 {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::DeadPrecondition,
            stats,
            detail: FailureDetail::Violation(ViolationKind::DegenerateConfig),
        });
    }

    let mut rng = SplitMix64::new(config.seed);
    let mut mutant_rng = rng.fork();
    let mut anchor_ret: Option<R> = None;

    for trial_idx in 0..config.max_trials {
        let input = I::sample_at(trial_idx, &mut rng);
        stats.trials_run += 1;

        let pre_holds = match pre(&input) {
            Ok(holds) => holds,
            Err(()) => {
                return SpecCheckOutcome::Failed(SpecCheckFailure {
                    class: VacuityClass::SpecViolation,
                    stats,
                    detail: FailureDetail::Violation(ViolationKind::ExecutionTrapped {
                        trial_idx,
                        trap: TrapKind::PreconditionPanicked,
                    }),
                });
            }
        };

        if !pre_holds {
            continue;
        }

        stats.precondition_hits += 1;

        let ret_ok = match body(&input) {
            Ok(ret) => ret,
            Err(()) => {
                return SpecCheckOutcome::Failed(SpecCheckFailure {
                    class: VacuityClass::SpecViolation,
                    stats,
                    detail: FailureDetail::Violation(ViolationKind::ExecutionTrapped {
                        trial_idx,
                        trap: TrapKind::BodyPanicked,
                    }),
                });
            }
        };

        let post_ok = match post(&input, &ret_ok) {
            Ok(holds) => holds,
            Err(()) => {
                return SpecCheckOutcome::Failed(SpecCheckFailure {
                    class: VacuityClass::SpecViolation,
                    stats,
                    detail: FailureDetail::Violation(ViolationKind::ExecutionTrapped {
                        trial_idx,
                        trap: TrapKind::PostconditionPanicked,
                    }),
                });
            }
        };

        if !post_ok {
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class: VacuityClass::SpecViolation,
                stats,
                detail: FailureDetail::Violation(ViolationKind::PostconditionFalse { trial_idx }),
            });
        }

        if !R::IS_SUBSINGLETON && config.max_mutants_per_hit > 0 {
            let mut tested_this_hit = 0usize;
            if let Some(slice) = custom_mutants {
                for ret_bad in slice {
                    if tested_this_hit >= config.max_mutants_per_hit {
                        break;
                    }
                    if ret_bad == &ret_ok {
                        continue;
                    }
                    if let Ok(holds) = post(&input, ret_bad) {
                        tested_this_hit += 1;
                        stats.mutants_tested += 1;
                        if !holds {
                            stats.mutants_killed += 1;
                        }
                    }
                }
            } else {
                ret_ok.visit_mutants(&mut mutant_rng, |ret_bad| {
                    if tested_this_hit >= config.max_mutants_per_hit {
                        return;
                    }
                    if ret_bad == ret_ok {
                        return;
                    }
                    if let Ok(holds) = post(&input, &ret_bad) {
                        tested_this_hit += 1;
                        stats.mutants_tested += 1;
                        if !holds {
                            stats.mutants_killed += 1;
                        }
                    }
                });
            }
        }

        if anchor_ret.is_none() {
            anchor_ret = Some(ret_ok);
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
                detail: FailureDetail::AllMutantsSurvived {
                    probed_inputs: 0,
                    saw_any_false: false,
                    saw_output_sensitivity: false,
                },
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
        let (class, detail) = match anchor_ret {
            Some(ret) => classify_all_mutants_survived(config, ret, extra, &mut post),
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
/// Any candidate in `mutants` equal to the actual output `ret_ok` is skipped
/// and never counted toward `mutants_tested`; if zero distinct mutants are
/// tested on a non-subsingleton return type, the check fails closed with
/// [`VacuityClass::SurvivedAllMutants`].
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

/// Probes whether `post` varies with `ret` (holding `(old_s, args, new_s)` fixed).
fn probe_stateful_return_axis<S, A, R, Post>(
    config: SpecCheckConfig,
    anchor_new_s: &S,
    anchor_ret: R,
    post: &mut Post,
) -> VacuityClass
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Post: FnMut(&S, &A, &S, &R) -> bool,
{
    if let Some(hint) = config.syntactic_hint {
        return match hint {
            SyntacticBindingHint::ReturnUnused => VacuityClass::UnboundReturnOutput,
            SyntacticBindingHint::SyntacticallyTautological => VacuityClass::TrivialPostcondition,
        };
    }

    let mut probe_rng = SplitMix64::new(config.seed ^ 0x51A7_E001_C3C3_3C3C);
    let mut saw_sensitivity = false;
    let mut false_witness: Option<(S, A, S)> = None;
    let mut true_witness: Option<(S, A, S)> = None;

    for idx in 0..64 {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
        let probe_new_s = if idx % 2 == 0 {
            anchor_new_s.clone()
        } else {
            old_s.clone()
        };
        let base = post(&old_s, &args, &probe_new_s, &anchor_ret);
        let mut varied = false;
        anchor_ret.visit_mutants(&mut probe_rng, |cand| {
            if varied {
                return;
            }
            if post(&old_s, &args, &probe_new_s, &cand) != base {
                varied = true;
            }
        });
        if varied {
            saw_sensitivity = true;
            break;
        }
        if !base && false_witness.is_none() {
            false_witness = Some((old_s, args, probe_new_s));
        } else if base && true_witness.is_none() {
            true_witness = Some((old_s, args, probe_new_s));
        }
    }

    if !saw_sensitivity && (false_witness.is_some() || true_witness.is_some()) {
        let mut cur = anchor_ret;
        let mut seen: [Option<R>; 4] = [None, None, None, None];
        let mut prev_cur: Option<R> = None;

        for _ in 0..128 {
            if saw_sensitivity {
                break;
            }
            let mut next_cur: Option<R> = None;
            cur.visit_mutants(&mut probe_rng, |cand| {
                if saw_sensitivity {
                    return;
                }
                if let Some((os, a, ns)) = false_witness.as_ref()
                    && post(os, a, ns, &cand)
                {
                    saw_sensitivity = true;
                    return;
                }
                if let Some((os, a, ns)) = true_witness.as_ref()
                    && !post(os, a, ns, &cand)
                {
                    saw_sensitivity = true;
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
    }

    if saw_sensitivity {
        VacuityClass::SurvivedAllMutants
    } else {
        VacuityClass::UnboundReturnOutput
    }
}

/// Probes whether `post` varies with `new_s` (holding `(old_s, args, ret)` fixed).
fn probe_stateful_state_axis<S, A, R, Post>(
    config: SpecCheckConfig,
    anchor_new_s: S,
    anchor_ret: &R,
    post: &mut Post,
) -> VacuityClass
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Post: FnMut(&S, &A, &S, &R) -> bool,
{
    if let Some(hint) = config.syntactic_hint {
        return match hint {
            SyntacticBindingHint::ReturnUnused => VacuityClass::UnboundReturnOutput,
            SyntacticBindingHint::SyntacticallyTautological => VacuityClass::TrivialPostcondition,
        };
    }

    let mut probe_rng = SplitMix64::new(config.seed ^ 0x51A7_E002_C3C3_3C3C);
    let mut saw_sensitivity = false;
    let mut false_witness: Option<(S, A)> = None;
    let mut true_witness: Option<(S, A)> = None;

    for idx in 0..64 {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
        let base = post(&old_s, &args, &anchor_new_s, anchor_ret);
        let mut varied = post(&old_s, &args, &old_s, anchor_ret) != base;
        if !varied {
            anchor_new_s.visit_mutants(&mut probe_rng, |cand_s| {
                if varied {
                    return;
                }
                if post(&old_s, &args, &cand_s, anchor_ret) != base {
                    varied = true;
                }
            });
        }
        if varied {
            saw_sensitivity = true;
            break;
        }
        if !base && false_witness.is_none() {
            false_witness = Some((old_s, args));
        } else if base && true_witness.is_none() {
            true_witness = Some((old_s, args));
        }
    }

    if !saw_sensitivity && (false_witness.is_some() || true_witness.is_some()) {
        let mut cur = anchor_new_s;
        let mut seen: [Option<S>; 4] = [None, None, None, None];
        let mut prev_cur: Option<S> = None;

        for _ in 0..128 {
            if saw_sensitivity {
                break;
            }
            let mut next_cur: Option<S> = None;
            cur.visit_mutants(&mut probe_rng, |cand_s| {
                if saw_sensitivity {
                    return;
                }
                if let Some((os, a)) = false_witness.as_ref()
                    && post(os, a, &cand_s, anchor_ret)
                {
                    saw_sensitivity = true;
                    return;
                }
                if let Some((os, a)) = true_witness.as_ref()
                    && !post(os, a, &cand_s, anchor_ret)
                {
                    saw_sensitivity = true;
                    return;
                }
                if next_cur.is_none()
                    && cand_s != cur
                    && prev_cur.as_ref() != Some(&cand_s)
                    && !seen.iter().any(|slot| slot.as_ref() == Some(&cand_s))
                {
                    next_cur = Some(cand_s);
                }
            });
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
    }

    if saw_sensitivity {
        VacuityClass::SurvivedAllMutants
    } else {
        VacuityClass::UnboundReturnOutput
    }
}

/// Probes both `(new_s, ret)` output axes jointly when zero mutants were killed
/// across both axes of a stateful contract.
fn classify_stateful_all_survived<S, A, R, Post>(
    config: SpecCheckConfig,
    anchor_new_s: S,
    anchor_ret: R,
    post: &mut Post,
) -> (VacuityClass, FailureDetail)
where
    S: SampleInput + ReturnMutants + Clone + PartialEq,
    A: SampleInput,
    R: ReturnMutants + PartialEq,
    Post: FnMut(&S, &A, &S, &R) -> bool,
{
    if let Some(hint) = config.syntactic_hint {
        let class = match hint {
            SyntacticBindingHint::ReturnUnused => VacuityClass::UnboundReturnOutput,
            SyntacticBindingHint::SyntacticallyTautological => VacuityClass::TrivialPostcondition,
        };
        return (
            class,
            FailureDetail::AllMutantsSurvived {
                probed_inputs: 0,
                saw_any_false: false,
                saw_output_sensitivity: false,
            },
        );
    }

    let mut probe_rng = SplitMix64::new(config.seed ^ 0x51A7_E003_C3C3_3C3C);
    let mut probed_inputs = 0usize;
    let mut saw_any_false = false;
    let mut saw_output_sensitivity = false;
    let mut false_witness: Option<(S, A)> = None;
    let mut true_witness: Option<(S, A)> = None;

    for idx in 0..64 {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(idx, &mut probe_rng);
        probed_inputs += 1;
        let mut saw_true_here = false;
        let mut saw_false_here = false;

        let base = post(&old_s, &args, &anchor_new_s, &anchor_ret);
        if base {
            saw_true_here = true;
        } else {
            saw_false_here = true;
            saw_any_false = true;
        }

        if !S::IS_SUBSINGLETON {
            if post(&old_s, &args, &old_s, &anchor_ret) {
                saw_true_here = true;
            } else {
                saw_false_here = true;
                saw_any_false = true;
            }
            if !(saw_true_here && saw_false_here) {
                anchor_new_s.visit_mutants(&mut probe_rng, |cand_s| {
                    if saw_true_here && saw_false_here {
                        return;
                    }
                    if post(&old_s, &args, &cand_s, &anchor_ret) {
                        saw_true_here = true;
                    } else {
                        saw_false_here = true;
                        saw_any_false = true;
                    }
                });
            }
        }

        if !R::IS_SUBSINGLETON && !(saw_true_here && saw_false_here) {
            anchor_ret.visit_mutants(&mut probe_rng, |cand_r| {
                if saw_true_here && saw_false_here {
                    return;
                }
                if post(&old_s, &args, &anchor_new_s, &cand_r) {
                    saw_true_here = true;
                } else {
                    saw_false_here = true;
                    saw_any_false = true;
                }
            });
        }

        if saw_true_here && saw_false_here {
            saw_output_sensitivity = true;
            break;
        }

        if saw_false_here && false_witness.is_none() {
            false_witness = Some((old_s, args));
        } else if saw_true_here && true_witness.is_none() {
            true_witness = Some((old_s, args));
        }
    }

    if !saw_output_sensitivity && (false_witness.is_some() || true_witness.is_some()) {
        if !S::IS_SUBSINGLETON {
            let mut cur_s = anchor_new_s.clone();
            let mut seen_s: [Option<S>; 4] = [None, None, None, None];
            let mut prev_s: Option<S> = None;

            for _ in 0..128 {
                if saw_output_sensitivity {
                    break;
                }
                let mut next_s: Option<S> = None;
                cur_s.visit_mutants(&mut probe_rng, |cand_s| {
                    if saw_output_sensitivity {
                        return;
                    }
                    if let Some((os, a)) = false_witness.as_ref()
                        && post(os, a, &cand_s, &anchor_ret)
                    {
                        saw_output_sensitivity = true;
                        return;
                    }
                    if let Some((os, a)) = true_witness.as_ref()
                        && !post(os, a, &cand_s, &anchor_ret)
                    {
                        saw_any_false = true;
                        saw_output_sensitivity = true;
                        return;
                    }
                    if next_s.is_none()
                        && cand_s != cur_s
                        && prev_s.as_ref() != Some(&cand_s)
                        && !seen_s.iter().any(|slot| slot.as_ref() == Some(&cand_s))
                    {
                        next_s = Some(cand_s);
                    }
                });
                let Some(next) = next_s else {
                    break;
                };
                if let Some(slot) = seen_s.iter_mut().find(|slot| slot.is_none()) {
                    *slot = Some(cur_s);
                } else {
                    prev_s = Some(cur_s);
                }
                cur_s = next;
            }
        }

        if !saw_output_sensitivity && !R::IS_SUBSINGLETON {
            let mut cur_r = anchor_ret;
            let mut seen_r: [Option<R>; 4] = [None, None, None, None];
            let mut prev_r: Option<R> = None;

            for _ in 0..128 {
                if saw_output_sensitivity {
                    break;
                }
                let mut next_r: Option<R> = None;
                cur_r.visit_mutants(&mut probe_rng, |cand_r| {
                    if saw_output_sensitivity {
                        return;
                    }
                    if let Some((os, a)) = false_witness.as_ref()
                        && post(os, a, &anchor_new_s, &cand_r)
                    {
                        saw_output_sensitivity = true;
                        return;
                    }
                    if let Some((os, a)) = true_witness.as_ref()
                        && !post(os, a, &anchor_new_s, &cand_r)
                    {
                        saw_any_false = true;
                        saw_output_sensitivity = true;
                        return;
                    }
                    if next_r.is_none()
                        && cand_r != cur_r
                        && prev_r.as_ref() != Some(&cand_r)
                        && !seen_r.iter().any(|slot| slot.as_ref() == Some(&cand_r))
                    {
                        next_r = Some(cand_r);
                    }
                });
                let Some(next) = next_r else {
                    break;
                };
                if let Some(slot) = seen_r.iter_mut().find(|slot| slot.is_none()) {
                    *slot = Some(cur_r);
                } else {
                    prev_r = Some(cur_r);
                }
                cur_r = next;
            }
        }
    }

    let class = if !saw_any_false {
        VacuityClass::TrivialPostcondition
    } else if !saw_output_sensitivity {
        VacuityClass::UnboundReturnOutput
    } else {
        VacuityClass::SurvivedAllMutants
    };

    (
        class,
        FailureDetail::AllMutantsSurvived {
            probed_inputs,
            saw_any_false,
            saw_output_sensitivity,
        },
    )
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
    let mut stats = SpecCheckStats {
        subsingleton_return: R::IS_SUBSINGLETON,
        ..SpecCheckStats::default()
    };

    if config.max_trials == 0 || config.min_precondition_hits == 0 {
        return SpecCheckOutcome::Failed(SpecCheckFailure {
            class: VacuityClass::DeadPrecondition,
            stats,
            detail: FailureDetail::Violation(ViolationKind::DegenerateConfig),
        });
    }

    let mut rng = SplitMix64::new(config.seed);
    let mut ret_mutant_rng = rng.fork();
    let mut state_mutant_rng = rng.fork();

    let mut return_mutants_tested = 0usize;
    let mut return_mutants_killed = 0usize;
    let mut state_mutants_tested = 0usize;
    let mut state_mutants_killed = 0usize;
    let mut anchor: Option<(S, R)> = None;

    for trial_idx in 0..config.max_trials {
        let (old_s, args) = <(S, A) as SampleInput>::sample_at(trial_idx, &mut rng);
        stats.trials_run += 1;

        if !pre(&old_s, &args) {
            continue;
        }

        stats.precondition_hits += 1;

        let mut new_s = old_s.clone();
        let ret_ok = body(&mut new_s, &args);

        if !post(&old_s, &args, &new_s, &ret_ok) {
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class: VacuityClass::SpecViolation,
                stats,
                detail: FailureDetail::Violation(ViolationKind::PostconditionFalse { trial_idx }),
            });
        }

        // Return-value mutant perturbation axis.
        if !R::IS_SUBSINGLETON && config.max_mutants_per_hit > 0 {
            let mut tested_this_hit = 0usize;
            ret_ok.visit_mutants(&mut ret_mutant_rng, |ret_bad| {
                if tested_this_hit >= config.max_mutants_per_hit {
                    return;
                }
                if ret_bad == ret_ok {
                    return;
                }
                tested_this_hit += 1;
                return_mutants_tested += 1;
                stats.mutants_tested += 1;
                if !post(&old_s, &args, &new_s, &ret_bad) {
                    return_mutants_killed += 1;
                    stats.mutants_killed += 1;
                }
            });
        }

        // State-mutation perturbation axis (always includes pre-state revert
        // whenever `new_s != old_s`).
        if !S::IS_SUBSINGLETON && config.max_mutants_per_hit > 0 {
            let mut tested_this_hit = 0usize;
            let tested_pre_revert = if new_s != old_s {
                tested_this_hit += 1;
                state_mutants_tested += 1;
                stats.mutants_tested += 1;
                if !post(&old_s, &args, &old_s, &ret_ok) {
                    state_mutants_killed += 1;
                    stats.mutants_killed += 1;
                }
                true
            } else {
                false
            };

            new_s.visit_mutants(&mut state_mutant_rng, |bad_s| {
                if tested_this_hit >= config.max_mutants_per_hit {
                    return;
                }
                if bad_s == new_s || (tested_pre_revert && bad_s == old_s) {
                    return;
                }
                tested_this_hit += 1;
                state_mutants_tested += 1;
                stats.mutants_tested += 1;
                if !post(&old_s, &args, &bad_s, &ret_ok) {
                    state_mutants_killed += 1;
                    stats.mutants_killed += 1;
                }
            });
        }

        if anchor.is_none() {
            anchor = Some((new_s, ret_ok));
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
                detail: FailureDetail::AllMutantsSurvived {
                    probed_inputs: 0,
                    saw_any_false: false,
                    saw_output_sensitivity: false,
                },
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
            Some((anchor_new_s, anchor_ret)) => {
                classify_stateful_all_survived(config, anchor_new_s, anchor_ret, &mut post)
            }
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
            let class = if return_mutants_tested == 0 {
                VacuityClass::SurvivedAllMutants
            } else if let Some((anchor_new_s, anchor_ret)) = anchor {
                probe_stateful_return_axis(config, &anchor_new_s, anchor_ret, &mut post)
            } else {
                VacuityClass::SurvivedAllMutants
            };
            return SpecCheckOutcome::Failed(SpecCheckFailure {
                class,
                stats,
                detail: axis_detail,
            });
        }

        if !S::IS_SUBSINGLETON && state_mutants_killed == 0 {
            let class = if state_mutants_tested == 0 {
                VacuityClass::SurvivedAllMutants
            } else if let Some((anchor_new_s, anchor_ret)) = anchor {
                probe_stateful_state_axis(config, anchor_new_s, &anchor_ret, &mut post)
            } else {
                VacuityClass::SurvivedAllMutants
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
