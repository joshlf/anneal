<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Untrusted Lean verification library (`theory/`)

This directory holds the `Anneal.*` Lean library: all derived definitions,
meta-theorems, program transformations, symbolic evaluators, and proof helpers
built on top of [`trusted/lean/`](../trusted/lean/README.md).

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

## Modules under `theory/Anneal/`

- **Y-diagram composition and step-tree meta-theory (`Anneal/Refinement.lean`,
  `Anneal/StepResult.lean`):**
  `pass_trans` (`Compiles.comp`, `Abstracts.comp`, `Compiler.SoundOn.verify`,
  `verify_through_passes`, `Compiler.Verified.mono`,
  `Compiler.Verified.with_wellFormedOn`), `Partial` functorial and lattice laws
  (`Partial.map`, `Partial.monotone_map`, `ub_top`, `ub_le_iff`,
  `le_specOn_iff`, `le_wellFormedOn_iff`, `le_wellFormed_iff`,
  `specOn_le_wellFormedOn`, `spec_le_wellFormed`,
  `not_specOn_le_wellFormed_of_not_pre`), and `TotalStep` + `InhabitedDemonic`
  (`non_vacuity_at_every_depth`) structural non-vacuity theorems.
- **MIR adequacy, memory ownership, and crate composition
  (`Anneal/MirLemmas.lean`):**
  `TotalStep` and `InhabitedDemonic` proofs for `MirMachine`, `View` lattice
  monotonicity lemmas, non-atomic exclusive (`OwnLoc`) and shared (`ReadOwnLoc`)
  location ownership helpers across reads, writes, and atomic loads, single- and
  multi-function `CrateTheorem` composition helpers (`verify_single_fn_crate`,
  `verify_two_fn_crate`), and positive/negative adequacy canaries.
- **Plan-guided shallow functional translation
  (`Anneal/FunctionalTranslation.lean`):**
  Three-valued functional outcome representation (`AeneasRes`), `FuncLang` and
  its monotone embedding `pi_func : FuncLang.Behavior → MirLang.Behavior`, the
  unified `LoanEntry` ownership model, the plan-guided symbolic evaluator
  (`evalSym`, `evalSymWith`) and forward/backward mutable-return lenses
  (`evalMutReturnFwd`, `evalMutReturnBack`), the universal hint-independent
  relational soundness theorems (`evalSym_sound`, `evalSymWith_sound`,
  `evalSymStateToReturn_sound`), the untrusted CFG/NLL planner (`computePlan`),
  and verified function specializations.
