<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Test suites and meta-validation canaries (`tests/`)

This directory holds `AnnealTests.*` (`tests/Smoke.lean` and
`tests/trusted-boundary/positive.lean`): pure, effect-free Lean regression and
canary modules that test both Anneal's semantic models and its
[`trusted/`](../trusted/README.md) containment boundary.

## Test categories

1. **`trusted/` boundary and auditor regressions (`tests/trusted-boundary/` and
   `trusted/cargo-anneal/src/self_test.rs`):**
   Positive and negative fixtures verifying that
   [`trusted/cargo-anneal/`](../trusted/cargo-anneal/README.md) and
   [`trusted/audit/TrustedBoundary.lean`](../trusted/audit/README.md) reject:
   - Any dependency from `trusted/lean/` onto `theory/` or unpinned modules,
   - Any reference to `theory/` (`Anneal.*`) inside the **type (`ci.type`)** of
     a `Trusted.CrateTheorem` or `VerificationResult` theorem
     (Statement-vs.-Proof Origin Separation),
   - Unapproved axioms, `sorryAx`, `unsafe`, `partial`, `native_decide`,
     `implemented_by`, recursor-rule/opaque-body leaks, Cargo workspace members
     or path dependencies outside `trusted/`, and tampered
     `CaptureManifest.json` digests.
2. **Structural non-vacuity and Rust adequacy canaries
   (`theory/Anneal/MirLemmas.lean`, `theory/Anneal/FunctionalTranslation.lean`,
   and `tests/Smoke.lean`):**
   Positive and negative canary theorems verifying that:
   - `MirMachine` satisfies `TotalStep` and `InhabitedDemonic` (ruling out
     silent stuck states and empty demonic choices),
   - Uninitialized return places (`uninitReturnBody`) violate
     `MirLang.WellFormed`, and wrong return values (`wrongReturnZeroBody`,
     `wrongAtomicLoadZeroBody`) or unguarded overflows (`unguardedSubBody`)
     violate their specifications,
   - Pure infinite loops (`loopBody`) satisfy `MirLang.WellFormed`, and
   - Aliased `&usize` arguments are accepted while aliased `&mut usize`
     arguments are vacuously outside `argValidAt`.
3. **End-to-end pipeline and policy tests
   (`trusted/cargo-anneal/tests/verify_id.rs`):**
   Tests exercising end-to-end `cargo anneal verify` capture, proof generation,
   and kernel verification across Rust functions and crates, including negative
   tests for false specifications, unsupported MIR constructs, post-capture
   `Mir.lean` tampering, and spoofed `Proof.verify_crate` theorem types.

## Axiom policy in `tests/`

Every module in `tests/`, `theory/`, and `examples/` is checked under the strict
zero-custom-axiom policy (`{propext, Quot.sound, Classical.choice}` only; zero
custom `axiom` declarations, `sorryAx`, `unsafe`, or `partial` constants) and
replayed in `base.toKernelEnv.replay`.
