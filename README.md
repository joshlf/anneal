<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a deductive verification framework for Rust—including unsafe code—built
as a Lean 4 library paired with a thin `rustc_driver` capture frontend. See
[`PRINCIPLES.md`](PRINCIPLES.md) for the current project principles and
[`DESIGN.md`](DESIGN.md) for the durable design constraints derived from them.

- [Requirements, aspirations, and architectural decision ledger (#1)](https://github.com/joshlf/anneal/issues/1).
- [Top-level Y-diagram architecture and `GuardedRefines` foundation (#100)](https://github.com/joshlf/anneal/issues/100).
- [Owned `rustc` capture and verified lowering pipeline (#99)](https://github.com/joshlf/anneal/issues/99).
- [Library-centric verification, multi-modal specifications, and machine-checked TCB & trust-policy results (#103)](https://github.com/joshlf/anneal/issues/103).
- [Compiler-selected type layouts, dynamic extent, and layout portability (#88)](https://github.com/joshlf/anneal/issues/88).
- [Direct Lean operational semantics vs. MiniRust (#101)](https://github.com/joshlf/anneal/issues/101).
- [Inline assembly (`TerminatorKind::InlineAsm`) and foreign/ISA bridge (#102)](https://github.com/joshlf/anneal/issues/102).
- [Plan-guided functional translation for safe Rust MIR (#109)](https://github.com/joshlf/anneal/issues/109).

## Correctness policy and `trusted/`

[`PRINCIPLES.md`](PRINCIPLES.md) promises that if the code in a verification
result's TCB audit log is correct, its assumptions are valid, and Anneal emits
no errors, then the verified code is correct. [`DESIGN.md`](DESIGN.md) defines a
**verification result** as asserting that:
1. its **TCB** satisfies its **trust policy**, and
2. if the trusted code in its **TCB** is correct, and its trusted assumptions
   are jointly valid, then its requested **claim** holds.

The [`trusted/`](trusted/README.md) directory isolates every part of Anneal on
which those two assertions depend without checked evidence. The invariant of
`trusted/` is that **auditing `trusted/` alone is sufficient to verify that
Anneal upholds [`PRINCIPLES.md`](PRINCIPLES.md) and [`DESIGN.md`](DESIGN.md)**:
an auditor never needs to inspect code outside `trusted/` to trust a
verification result. This must remain true in the face of adversarial
implementations in any other part of the repository.

(Currently, `.github` is an exception to this rule, although we aim to tighten
that as well.)

## Repository layout and trust boundary

| Path | Trust status | Role |
| --- | --- | --- |
| [`trusted/`](trusted/README.md) | **Trusted (human-audited TCB)** | Everything required to state and gate a true verification claim: primitive Lean semantic and theorem definitions in [`trusted/lean/`](trusted/lean/README.md) (`Trusted/Refinement.lean` over `Std.IsPreorder` / `Std.IsPartialOrder` with `TrustPolicy`, constructive coinductive containers and open interaction trees in `Trusted/{CoInd,Effect,ITree}.lean`, `Trusted/Sequence.lean`, `Trusted/VerificationResult.lean` including program-to-program `RefinesStatefulMir`, `NonVacuousPre`, and whole-crate `CrateTheorem` gates, and dialect-scoped `Trusted/Rustc/V2026_06_01/{Layout,MirAst,MirSemantics}`), the `.olean` environment and boundary auditor ([`trusted/audit/`](trusted/audit/README.md)), and the thin `rustc_driver` MIR/attribute serializer ([`trusted/rustc-capture/`](trusted/rustc-capture/README.md)). |
| [`theory/`](theory/README.md) | **Untrusted (kernel-checked)** | Derived Lean library (`Anneal.*`) built on Lean 4's `Init` and `Std`: Y-diagram composition (`Anneal/Refinement.lean`), open-effect algebra (`Anneal/Effect.lean`), coinductive interaction-tree equivalences, `LawfulMonad`, Smyth tree refinement, and temporal modalities (`Anneal/ITree.lean`), `ITreeMachine` trace projections and CFG pass frameworks (`Anneal/Pass.lean`), open-effect Dijkstra predicate transformers integrated with `Std.Do` (`Anneal/{EffectWP,ITreeWP}.lean`), byte-level bit validity, unsafe obligations, and `PartialHeap` separation logic (`Anneal/{Scalars,Memory,BitValidity,UnsafeObligations,SepLogic}.lean`), MIR verification bridges, caller–callee linking, and fast symbolic evaluation (`Anneal/Rustc/V2026_06_01/{Lower,SymbolicEval}.lean`), and plan-guided functional translation (`Anneal/FunctionalTranslation.lean`). |
| [`crates/`](crates/README.md) | **Untrusted (manifest- and audit-gated)** | Rust specification macros (`crates/anneal-spec`, `crates/anneal-spec-macros`: `#[spec]`, `#[embed_spec]`, `#[external_spec]`, `#[model]`, `#[invariant]`, `#[unsafe_trait]`, `#[unsafe_impl]`) and CLI orchestrator (`crates/cargo-anneal`: `setup`, `extract`, `scaffold`, `verify`, `lock-specs`, `agent-context`, `agent-verify`, `agent-sandbox`). |
| [`tools/anneal-lsp/`](tools/anneal-lsp/) | **Untrusted (developer & agent tooling)** | Warm Lean 4 (`lake serve`) and Rust LSP MCP server (`mcp_server.py`) plus `PreToolUse` and `PostToolUse` hook scripts (`hooks/pre_tool_use.py`, `hooks/post_tool_use.py`) for interactive proof feedback and `.anneal/spec-lock.json` write enforcement across Claude Code, Gemini CLI, and Jetski. |
| [`examples/`](examples/README.md) | **Untrusted (kernel-checked)** | Worked language and MIR verification instances (`Smoke`, `ToyYDiagram`, `ToyMachine`, `ToyCFG`, `MirVerification`) in a single Lake workspace, the [`examples/tutor/`](examples/tutor/) (`frame_tutor`) tutorial crates, and the [`examples/wireframe-demo/`](examples/wireframe-demo/) end-to-end zero-copy codec showcase across bootstrap, bug finding, locked authoring/review, and verified `safe -> unsafe` optimization. |
| [`docs/`](docs/project-owner-guide.md), [`docs/tutor/`](docs/tutor/README.md) | **User, maintainer & agent guides** | [**Project Owner Guide**](docs/project-owner-guide.md) (adopting Anneal in Rust crates and reviewing verification PRs), [**Agent Harness Setup**](docs/agent-harness-setup.md) (configuring `anneal-lsp` MCP, hooks, and anti-cheating sandboxes), [**Agentic Proof Construction Workflow**](docs/agent-proof-workflow.md), and the six-chapter step-by-step [**Anneal Tutor**](docs/tutor/README.md). |
| [`tests/`](tests/README.md) | **Untrusted (test suites & canaries)** | Positive and negative verification tests, structural non-vacuity, Smyth lattice, temporal stream, and `Std.Do.Triple` adequacy canaries (`tests/step-result/Canaries.lean`), symbolic-evaluation and functional-translation tests, and `trusted/` boundary regressions. |
| [`AGENTS.md`](AGENTS.md), [`agent_docs/`](agent_docs/development.md) | **Contributor guidance** | Entry point, development workflow, writing policy, and Rust correspondence citation rules. |

## Guides for project owners and agent harnesses

- [**Project owner guide: Adopting Anneal in a Rust codebase**](docs/project-owner-guide.md) — Installing the prebuilt toolchain (`cargo anneal setup`), writing contracts in Rust (`#[anneal_spec::*]`, `safe_total`, `equivalent_to`), understanding verification tiers (`UNCONDITIONAL`, `CONDITIONAL`, `UB_EXCEPTION`, `PROVISIONAL_NATIVE`), and reviewing verification PRs without reading Lean tactic scripts.
- [**Agent harness setup and anti-cheating configuration**](docs/agent-harness-setup.md) — Configuring the warm Lean 4 LSP MCP server (`tools/anneal-lsp/`), `PreToolUse`/`PostToolUse` hooks, out-of-tree and git-ref specification locks (`--lock-file`, `--lock-git-ref`), `bwrap` sandboxing (`cargo anneal agent-sandbox`), and parallel multi-agent sharding.
- [**Agentic proof construction workflow and anti-cheating safeguards**](docs/agent-proof-workflow.md) — Threat model and four-layer defense-in-depth architecture for autonomous proof construction.

## Getting started: The Anneal Tutor

New to Anneal? Start with [**The Anneal Tutor**](docs/tutor/README.md) and its
companion runnable crate in [`examples/tutor/`](examples/tutor/) (`frame_tutor`):

1. [Chapter 1: Basic Tool Usage & Interpreting Outputs](docs/tutor/01-basic-usage-and-outputs.md)
2. [Chapter 2: Adding Specifications in Rust](docs/tutor/02-rust-specifications.md)
3. [Chapter 3: Explicit Assumptions & Incremental Adoption](docs/tutor/03-assumptions-and-incremental-adoption.md)
4. [Chapter 4: Completing a Manual Proof Workflow](docs/tutor/04-manual-proof-workflow.md)
5. [Chapter 5: Working with `unsafe` Code, Tree Borrows & Separation Logic](docs/tutor/05-verifying-unsafe-rust.md)
6. [Chapter 6: Guided Agentic Proof Workflow](docs/tutor/06-agentic-proof-workflow.md)
