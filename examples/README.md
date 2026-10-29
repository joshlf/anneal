# Worked examples (`examples/`)

This directory holds worked abstract-to-concrete Lean instantiations of
[`trusted/lean/`](../trusted/lean/README.md) and [`theory/`](../theory/README.md)
([#100](https://github.com/joshlf/anneal/issues/100) §7,
[#103](https://github.com/joshlf/anneal/issues/103)).

## Example modules

- **`examples/Smoke.lean` (`Smoke`):** Minimal smoke example importing `Anneal`
  and exercising `DWLP` adequacy over `ITree`.
- **`examples/refinement/ToyYDiagram.lean` (`ToyYDiagram`):** Concrete Layer 1A
  Y-diagram instance instantiating `GuardedRefines.trans` and
  `anneal_is_correct`.
- **`examples/step-result/ToyMachine.lean` (`ToyMachine`):** Concrete Layer 1B
  coalgebraic `ITreeMachine` pair across two distinct open effect signatures
  (`SrcEffect` with `FailE`, `ObsE`, and demonic `PickE Bool` lowered to
  deterministic `TgtEffect`), exercising automatic `InhabitedDemonic` synthesis
  (`srcMachine_non_vacuous`), cross-effect `WeakObsRef` simulation
  (`compileProgPass` and `compileProgCompiles`), and end-to-end Y-diagram
  composition (`example_machine_compiled_correct`).
- **`examples/pass/ToyCFG.lean` (`ToyCFG`):** Concrete Layer 2 control-flow graph
  language instantiating both resolved-label `CFGSystem` (with `Bool` certificate
  checker `checkForwarder_sound` and `example_cfg_end_to_end`) and `.tau`-erasing
  `TauCFGSystem` (`tauCfg_eliminateForwarder_eutt` and
  `tauCfg_eliminateForwarder_exact`).
- **`examples/mir/MirVerification.lean` (`MirVerification`):** Self-contained
  worked vertical slices of `Runtime(PostCleanup)` MIR verification over
  `ITree MirEffect MirOutcome` across all five trusted gates
  (`VerificationResult`, `StatefulVerificationResult`, `TraceVerificationResult`,
  `TotalVerificationResult`, and `ModularVerificationResult`); see
  [`examples/mir/README.md`](mir/README.md) for the slice index.

## Tutor crates

The [Anneal Tutor](../docs/tutor/README.md) works through one Rust crate,
`frame_tutor`, that grows chapter by chapter. Each chapter's crate is checked in
so you can open, run, and diff the code the chapter refers to:

| Crate | Chapter | What it contains |
| --- | --- | --- |
| [`tutor-ch1/`](tutor-ch1/) | [1](../docs/tutor/01-basic-usage-and-outputs.md) | `magic_version` only, no dependencies. |
| [`tutor-ch2/`](tutor-ch2/) | [2](../docs/tutor/02-rust-specifications.md) | Annotated safe functions, a `#[model]` helper, an `#[invariant]` newtype; no proofs. |
| [`tutor-ch3/`](tutor-ch3/) | [3](../docs/tutor/03-assumptions-and-incremental-adoption.md) | Two items; `pin_magic` deferred to a scoped `Assumptions` axiom. |
| [`tutor-ch4/`](tutor-ch4/) | [4](../docs/tutor/04-manual-proof-workflow.md) | Four safe items with kernel-checked proofs and a `refineSafeSpec` specification. |
| [`tutor/`](tutor/) | [5](../docs/tutor/05-verifying-unsafe-rust.md), [6](../docs/tutor/06-agentic-proof-workflow.md) | The complete companion crate, adding `unsafe` items with stateful proofs. |

## End-to-end user-journey showcase (`examples/wireframe-demo/`)

[`wireframe-demo/`](wireframe-demo/) is a self-contained zero-copy binary packet
and frame codec crate demonstrating four end-to-end human and agent workflows:
bootstrapping verification on safe Rust, refuting and repairing an `unsafe`
undefined-behavior bug, keeping code authors and reviewers in check via locked
specifications and `refineSafeSpec` / non-vacuity checks, and verifying an
iterative `safe -> unsafe` performance optimization against the safe function's
captured MIR as the behavioral specification.

## Single Lake workspace for interactive InfoView editing

All Lean example modules share a single Lake workspace (`examples/lakefile.toml`)
that depends on `Trusted` (`../trusted/lean`) and `Anneal` (`../theory`).
Opening `examples/` in VSCode (or any editor running `lake serve` or
`lean-lsp-mcp`) provides live Lean 4 InfoView goal states and diagnostics across
every example without duplicating builds of `Trusted` or `Anneal`.

## Axiom policy

All modules in `examples/` are audited under the **`strict` zero-custom-axiom
policy** (zero custom axioms, `sorryAx`, `unsafe`, or `partial` declarations).
