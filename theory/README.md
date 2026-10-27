<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Untrusted Lean verification library (`theory/`)

This directory holds the `Anneal.*` Lean library: all derived definitions,
meta-theorems, program transformations, certificate checkers, program logics,
and tactics built on top of [`trusted/lean/`](../trusted/lean/README.md)
([#100](https://github.com/joshlf/anneal/issues/100),
[#99](https://github.com/joshlf/anneal/issues/99),
[#103](https://github.com/joshlf/anneal/issues/103)).

## Why `theory/` is untrusted ("Lean said it was fine, so it is fine")

Nothing in `theory/` is part of Anneal's Trusted Computing Base (TCB):

1. **Used only in proof terms (`ci.value?`), never in theorem statements
   (`ci.type`):**
   [`trusted/audit/`](../trusted/audit/README.md) enforces that the theorem
   statement `ci.type` of `Proof.verify_crate : Trusted.CrateTheorem Mir.crate`
   has zero transitive dependencies on `Anneal.*`. Definitions in `theory/` may
   be used only inside the proof witness `ci.value?` to discharge
   `Trusted.CrateTheorem`.
2. **Checked by the Lean kernel and replayed from scratch:**
   Every module in `theory/` is checked under the strict zero-custom-axiom
   policy (`{propext, Quot.sound, Classical.choice}` only; zero `sorryAx`,
   `unsafe`, `partial`, or compiler overrides) and replayed in
   `base.toKernelEnv.replay`. A bug in `theory/` can cause a tactic or proof to
   fail to typecheck, but it can never allow a false `Trusted.CrateTheorem`
   theorem to be accepted.

## Planned module groups under `theory/Anneal/`

- **Y-diagram composition and step-tree meta-theory (`Anneal/Refinement.lean`,
  `Anneal/StepResult.lean`):**
  `pass_trans` (`Compiles.comp`, `Abstracts.comp`, `Compiler.SoundOn.verify`,
  `verify_through_passes`, `Compiler.Verified.mono`,
  `Compiler.Verified.with_wellFormedOn`), `Partial` functorial and lattice laws
  (`Partial.map`, `Partial.monotone_map`, `ub_top`, `ub_le_iff`,
  `le_specOn_iff`, `le_wellFormedOn_iff`, `le_wellFormed_iff`,
  `specOn_le_wellFormedOn`, `spec_le_wellFormed`,
  `not_specOn_le_wellFormed_of_not_pre`), forward-to-backward simulation flip
  lemmas, and `TotalStep` + `InhabitedDemonic` (`non_vacuity_at_every_depth`)
  structural non-vacuity theorems
  ([#100](https://github.com/joshlf/anneal/issues/100) §2–§6).
- **Derived layout arithmetic and validators (`Anneal/Layout/`):**
  Alignment rounding, checked extent arithmetic, repeated sequence geometry,
  and boolean layout validators proved sound against `Trusted.Layout` and
  `Trusted.Sequence` ([#88](https://github.com/joshlf/anneal/issues/88)).
- **Concrete memory and aliasing models (`Anneal/Memory/`):**
  `BasicMemory` and `TreeBorrowsMemory` instances proved to satisfy the
  `Trusted` memory interface and non-vacuity laws
  ([#101](https://github.com/joshlf/anneal/issues/101)).
- **Verified normalization passes and certificate checkers (`Anneal/Passes/`,
  `Anneal/Functional/`):**
  Proved `VerifierPass` and `ExactPass` transformations (such as
  `eliminateForwarder`, CFG compaction, loop structuring) and `VerifiedChecker`s
  validating per-function Aeneas-style functional translations (`foo_func`)
  against `MirSem` ([#99](https://github.com/joshlf/anneal/issues/99) §7–§9,
  [#103](https://github.com/joshlf/anneal/issues/103) §3.3).
- **Program logics and proof automation (`Anneal/Logic/`, `Anneal/Tactics/`):**
  Small-step weakest precondition (`WP`), separation-logic frame rules,
  `TCBAllHold` monotonicity helpers, and Lean 4 tactics.
