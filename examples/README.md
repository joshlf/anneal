<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Worked examples (`examples/`)

This directory holds `AnnealExamples.*`: worked language instances and vertical
verification slices that exercise [`trusted/lean/`](../trusted/lean/README.md)
and [`theory/`](../theory/README.md) ([#100](https://github.com/joshlf/anneal/issues/100)
§§5–8, [#83](https://github.com/joshlf/anneal/issues/83),
[#103](https://github.com/joshlf/anneal/issues/103)).

## Contents of `examples/Smoke.lean`

1. **`unitMachine_non_vacuous`:** Minimal Layer 1B small-step machine witness
   exercising `non_vacuity_at_every_depth`.
2. **`HoareExamples`:** Hoare Logic / Chlipala Fiat / Dijkstra WP embedding into
   `Query → Partial (Out → Prop)` (`le_iff_wp_imp`) and separation of safety
   preconditions (`.defined`) from functional preconditions (`.val`) on
   `binary_search` (`binarySearchSpec_wf`, `misplacedBinarySearchSpec_not_wf`,
   `unsafeSpec_wfOn`).
3. **`AeneasExamples`:** Aeneas functional-translation total (`DWP`,
   `AeneasTotalLang`) vs. partial (`DWLP`, `AeneasPartialLang`) verification
   modes (`loopProg_partial_wf`, `loopProg_not_total_wf`).
4. **`Alive2Examples`:** LLVM / Alive2 two-tiered undefinedness (`poison` in
   `.val` vs. immediate `UB` in `.defined`: `alive_freeze_compiles_poison`,
   `alive_ub_does_not_compile_poison`).
5. **`IrisExamples`:** Iris / `iris-lean` step-indexed `NotStuck` adequacy
   (`iris_adequacy_iff_le_wellFormed`).
6. **`CompCertExamples`:** CompCert whole-program prefix-indexed trace
   improvement (`compcert_goesWrong_prefix_improves`,
   `compcert_safe_prefix_preserved`).
7. **`TrueConcurrencyExamples`:** Language without a single deterministic
   sequence of execution states (partial-order causal event structures equipped
   with `Preorder` on `ScopedConcurrentEvent p`: `syncedParallelProg_wf`,
   `unsyncedParallelProg_not_wf`).
8. **`PrefixPreservationExamples`:** Non-time-traveling UB after an externally
   observable effect (`emitThenUb_step1_defined`,
   `compiler_preserves_well_defined_prefix_before_ub`,
   `emitThenUb_step2_not_defined`).
9. **`SelectiveTimeTravelExamples`:** Selective time-traveling UB with two UB
   kinds (`UBA`, `UBB`) and two observable behaviors (`BA`, `BB`), where `UBA`
   time-travels over `BA` (`uba_time_travels_over_ba`) but is blocked by `BB`
   (`uba_blocked_by_bb`), while `UBB` time-travels over `BB`
   (`ubb_time_travels_over_bb`) but is blocked by `BA` (`ubb_blocked_by_ba`).
10. **`LibraryConditionality`:** Safe vs. `unsafe` library verification
    (`DESIGN.md` "Libraries"), proving `VerificationResult` for `safeDivOrZero`
    with partial/vacuous functional specifications (`safeDiv_verified`) and
    `VerificationResultOn` for `unsafeDiv` under caller safety precondition
    `pre := fun q => q.d > 0` (`unsafeDiv_verifiedOn`,
    `unsafeDiv_not_unconditionally_wf`).

## Single Lake workspace for interactive InfoView editing

All example modules share a single Lake workspace (`examples/lakefile.toml`)
that depends on `Trusted` (`../trusted/lean`) and `Anneal` (`../theory`).
Opening `examples/` in VSCode (or any editor running `lake serve` or
`lean-lsp-mcp`) provides live Lean 4 InfoView goal states and diagnostics across
every example without duplicating builds of `Trusted` or `Anneal`.

## Axiom policy

All modules in `examples/` are audited under the **`strict` zero-custom-axiom
policy** (`{propext, Quot.sound, Classical.choice}` only; zero `sorryAx`,
`unsafe`, or `partial` declarations).
