<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trusted Lean definitions (`trusted/lean/`)

This directory holds the `Trusted.*` Lean source root: the minimal set of
primitive semantic and theorem definitions required to state
`Trusted.CrateTheorem` and `VerificationResult`.

## What belongs in `trusted/lean/`

Only definitions that must appear in (or be unfolded by) the **statement
(`ci.type`)** of `Trusted.CrateTheorem` belong here (pure definitions; zero
theorems):

- **`Trusted/Refinement.lean`:** The Layer 1A refinement preorder (`Preorder`
  (`≤`), `instPreorderProp`, `instPreorderFun`, `Partial`,
  `instPreorderPartial`, `Monotone`), `Language`
  (`Query → Partial (Out → Prop)`, `Language.SpecOn`, `Language.Spec`,
  `Language.WellFormedOn`, `Language.WellFormed`), `Compiles`, `Abstracts`,
  `Compiler`, `Compiler.Verified`, `VerificationResultOn`, and
  `VerificationResult`.
- **`Trusted/StepResult.lean`:** Layer 1B small-step / interaction-tree
  transition outcomes (`ChoiceKind`, `TerminationKind`, `FailureKind`,
  `StepResult`), execution prefix queries and outputs (`PrefixOutcome`,
  `ExecQuery`, `ExecOut`), and operational behavior (`SmallStepMachine`,
  `ReachesPrefix`, `BehaviorOf`, `SmallStepMachine.toLanguage`).
- **`Trusted/Memory.lean`:** Primitive happens-before views (`Timestamp`,
  `View`, `instPreorderView`), modification-order messages (`AtomicMsg`), and
  mixed non-atomic/atomic memory state (`MemState`) backed by verbatim Rust
  Reference citations.
- **`Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`:** The owned MIR AST
  (`MirBody`, `CapturedFn`, `Crate`), operational semantics (`MirMachine`,
  `MirSem`), and target / compilation contracts (`TargetSem`, `π_c`, `rustc`,
  `TCBItem`, `RustcCompiler`, `CrateTheorem`).

## Why intermediate IRs and proof calculi stay outside `trusted/lean/`

In `Trusted/Refinement.lean` and `Trusted/MirSemantics.lean`,
`Compiler.Verified` and `CrateTheorem` state their guarantees directly over
`MirSem` (and `TargetSem` when binary lowering is enabled) using only
definitions in `trusted/lean/`.

When a proof in `Proof.lean` lowers `MirBody` through normalized CFGs,
structured loops, or an Aeneas-style functional representation (`evalSym`),
those intermediate representations (`Prog_k`, `Sem_k`), their `Abstracts` /
`Compiles` theorems, and their proof helpers appear **only inside the proof term
(`ci.value?`)** via `verify_through_passes`. They therefore live entirely in
[`theory/`](../../theory/README.md) outside the TCB.

## Authoring rules

1. Every module uses `prelude` and imports only `trusted/lean/` modules and the
   pinned foundation lock (`foundation-lock.json`).
2. Zero `axiom`, `sorry`, `unsafe`, `partial`, `native_decide`,
   `implemented_by`, `csimp`, or `extern` declarations are permitted.
3. Every top-level declaration must be explicitly named (including `instance`
   declarations) and carry an explicit in-place trust attribute: either
   `@[vetted]` or `@[candidate <feature>]` (where `<feature>` is one of
   `refinement`, `step_result`, `memory`, `mir_ast`, `mir_semantics`).
   Constructors of a `@[vetted] inductive` inherit `@[vetted]` by default or may
   carry an explicit `@[vetted]` or `@[candidate <feature>]` override;
   constructors of a `@[candidate <feature>] inductive` cannot be marked
   `@[vetted]`.
4. **Non-contamination:** A `@[vetted]` declaration may never reference a
   `@[candidate <feature>]` constant in its type (`ci.type`), and in its body
   (`ci.value?`) may only reference a `@[candidate <feature>]` constant inside a
   `Trusted.candidate "<feature>" (...)` match arm corresponding to a
   `@[candidate <feature>]` constructor.
5. Every declaration that models a Rust guarantee must include an adjacent
   documentation comment with verbatim quotations and versioned citations
   following [`agent_docs/trusted-rust.md`](../../agent_docs/trusted-rust.md).
