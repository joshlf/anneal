# Trusted Lean definitions (`trusted/lean/`)

This directory holds the `Trusted.*` Lean source root: the minimal set of
primitive semantic and theorem definitions required to state
`Trusted.CrateTheorem` and `VerificationResult`
([#100](https://github.com/joshlf/anneal/issues/100),
[#103](https://github.com/joshlf/anneal/issues/103),
[#109](https://github.com/joshlf/anneal/issues/109)).

## What belongs in `trusted/lean/`

Only definitions that must appear in (or be unfolded by) the **statement
(`ci.type`)** of `Trusted.CrateTheorem` belong here (pure definitions; zero
theorems):

- **`Trusted/Refinement.lean`:** The Layer 1A refinement preorder (`Preorder`
  (`≤`), `instPreorderProp`, `instPreorderFun`, `Partial`, `instPreorderPartial`,
  `Monotone`), `Language` (`Query → Partial (Out → Prop)`, `Language.SpecOn`,
  `Language.Spec`, `Language.WellFormedOn`, `Language.WellFormed`), `Compiles`,
  `Abstracts`, `Compiler`, `Compiler.Verified`, `VerificationResultOn`, and
  `VerificationResult`
  ([#100](https://github.com/joshlf/anneal/issues/100) §2,
  [#103](https://github.com/joshlf/anneal/issues/103) §4).
- **`Trusted/StepResult.lean`:** Layer 1B small-step / interaction-tree
  transition outcomes (`ChoiceKind`, `TerminationKind`, `FailureKind`,
  `StepResult`), execution prefix queries and outputs (`PrefixOutcome`,
  `ExecQuery`, `ExecOut`), and operational behavior (`SmallStepMachine`,
  `ReachesPrefix`, `BehaviorOf`, `SmallStepMachine.toLanguage`)
  ([#100](https://github.com/joshlf/anneal/issues/100) §5).
- **`Trusted/Layout.lean` and `Trusted/Memory.lean`:** Primitive value/type
  layout contracts (`Target`, `Geometry`, `Model`, `SequenceLayout`) and memory
  interface definitions backed by verbatim Rust Reference citations
  ([#88](https://github.com/joshlf/anneal/issues/88),
  [#101](https://github.com/joshlf/anneal/issues/101)).
- **`Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`:** The owned MIR AST
  (`MirBody`, `CapturedFn`, `Crate`), operational semantics (`MirMachine`,
  `MirSem`), and target / compilation contracts (`TargetSem`, `π_c`, `rustc`)
  ([#99](https://github.com/joshlf/anneal/issues/99),
  [#103](https://github.com/joshlf/anneal/issues/103)).

## Why intermediate IRs and proof calculi stay outside `trusted/lean/`

In `Trusted/Refinement.lean` and `Trusted/MirSemantics.lean`, `FunctionVerified`
and `CrateTheorem` state their guarantees directly over `MirSem` (and `TargetSem`
when binary lowering is enabled) using only definitions in `trusted/lean/`.

When a proof in `Proof.lean` lowers `MirBody` through normalized CFGs,
structured loops, or an Aeneas-style functional representation (`foo_func`),
those intermediate representations (`Prog_k`, `Sem_k`), their `VerifierPass` /
`ExactPass` theorems, `VerifiedChecker`s, and `WP` calculi appear **only inside
the proof term (`ci.value?`)** via `verify_through_passes`. They therefore live
entirely in [`theory/`](../../theory/README.md) outside the TCB.

## Authoring rules

1. Every module uses `prelude` and imports only `trusted/lean/` modules and the
   pinned foundation lock (`foundation-lock.json`).
2. Zero `axiom`, `sorry`, `unsafe`, `partial`, `native_decide`,
   `implemented_by`, `csimp`, or `extern` declarations are permitted.
3. Every declaration that models a Rust guarantee must include an adjacent
   documentation comment with verbatim quotations and versioned citations
   following [`agent_docs/trusted-rust.md`](../../agent_docs/trusted-rust.md).
