<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a deductive verification framework for Rust—including unsafe code—built
as a Lean 4 library paired with a thin `rustc_driver` capture frontend. See
[`PRINCIPLES.md`](PRINCIPLES.md) for the project principles,
[`THREAT_MODEL.md`](THREAT_MODEL.md) for the threat model,
[`META_PRINCIPLES.md`](META_PRINCIPLES.md) for the invariant goals that govern
them, and [`DESIGN.md`](DESIGN.md) for the durable design constraints derived
from them.

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
no errors, then the verified code is sound and satisfies any stated
specifications. [`DESIGN.md`](DESIGN.md) defines a **verification result** as
asserting that:
1. its **TCB** satisfies its **trust policy**, and
2. if the trusted code in its **TCB** is correct, and its trusted assumptions
   are jointly valid, then its requested **claim** (baseline soundness and any
   stated specifications) holds.

The [`trusted/`](trusted/README.md) directory isolates every first-party
component of Anneal on which those two assertions depend without checked
evidence. The invariant of `trusted/` is that **auditing `trusted/` and its
explicit, pinned dependency manifest is sufficient to verify that Anneal upholds
[`META_PRINCIPLES.md`](META_PRINCIPLES.md), [`PRINCIPLES.md`](PRINCIPLES.md),
[`THREAT_MODEL.md`](THREAT_MODEL.md), and [`DESIGN.md`](DESIGN.md)**: an auditor never needs to inspect first-party code
outside `trusted/` to trust a verification result. This must remain true in the
face of adversarial implementations in any other part of the repository.

To keep the human audit surface tractable and reliable, `trusted/` permits
battle-tested, widely-used external libraries for routine utilities (such as
command-line flag parsing, serialization, and trace logging). Using established
libraries for generic infrastructure is strongly preferred over hand-rolling
bespoke implementations inside `trusted/`, which inflates audit burden and
invites defect-prone reinvented wheels.

(Currently, `.github` is an exception to this rule, although we aim to tighten
that as well.)

## Design documentation

- [`META_PRINCIPLES.md`](META_PRINCIPLES.md): The invariant goals governing
  [`PRINCIPLES.md`](PRINCIPLES.md) and [`THREAT_MODEL.md`](THREAT_MODEL.md)—the
  end-to-end sufficiency of bounded human review, the prohibition on security
  theater, and the hierarchy of governing documents.
- [`PRINCIPLES.md`](PRINCIPLES.md): Anneal's mission, correctness promise, and
  decision-making priority order.
- [`THREAT_MODEL.md`](THREAT_MODEL.md): Threat model, the division of labor
  between bounded human review (stated specifications and the TCB audit log)
  and automated verification, and the explicit assumptions and in-scope threats
  Anneal defends against.
- [`DESIGN.md`](DESIGN.md): Durable architectural design contract and invariants.
- [`docs/design.md`](docs/design.md): Overall system design, end-to-end
  verification workflow, library-centric verification, multi-modal
  specifications, and incremental adoption.
- [`docs/architecture.md`](docs/architecture.md): The three-stage MIR pipeline,
  repository layout, `rustc` extraction lifecycle, and multi-version toolchain
  strategy.
- [`docs/trust-model.md`](docs/trust-model.md): How Anneal's internal `trusted/`
  vs. `theory/` boundary and `trusted/audit/` implement and enforce
  [`META_PRINCIPLES.md`](META_PRINCIPLES.md), [`PRINCIPLES.md`](PRINCIPLES.md),
  and [`THREAT_MODEL.md`](THREAT_MODEL.md).

## Repository checks

See [the Codex review policy and diagnostics guide](docs/codex-review.md) for
the manual merge gates, live ruleset state, read-only diagnostics, and evaluator
tests.

## Repository layout and trust boundary

| Path | Trust status | Role |
| --- | --- | --- |
| [`trusted/`](trusted/README.md) | **Trusted (human-audited TCB)** | Everything required to state and gate a true verification claim: primitive Lean semantic and theorem definitions in [`trusted/lean/`](trusted/lean/README.md) (`Trusted/Refinement.lean` over `Std.IsPreorder` / `Std.IsPartialOrder` with `TrustPolicy`, constructive coinductive containers and open interaction trees in `Trusted/{CoInd,Effect,ITree}.lean`, `Trusted/Sequence.lean`, `Trusted/VerificationResult.lean` including program-to-program `RefinesStatefulMir`, `NonVacuousPre`, and whole-crate `CrateTheorem` gates, and dialect-scoped `Trusted/Rustc/V2026_06_01/{Layout,MirAst,MirSemantics}`), the `.olean` environment and boundary auditor ([`trusted/audit/`](trusted/audit/README.md)), and the thin `rustc_driver` MIR/attribute serializer ([`trusted/rustc-capture/`](trusted/rustc-capture/README.md)). |
| [`theory/`](theory/README.md) | **Untrusted (kernel-checked)** | Derived Lean library (`Anneal.*`) built on Lean 4's `Init` and `Std`: Y-diagram composition (`Anneal/Refinement.lean`), open-effect algebra (`Anneal/Effect.lean`), coinductive interaction-tree equivalences, `LawfulMonad`, Smyth tree refinement, and temporal modalities (`Anneal/ITree.lean`), `ITreeMachine` trace projections and CFG pass frameworks (`Anneal/Pass.lean`), open-effect Dijkstra predicate transformers integrated with `Std.Do` (`Anneal/{EffectWP,ITreeWP}.lean`), byte-level bit validity, unsafe obligations, and `PartialHeap` separation logic (`Anneal/{Scalars,Memory,BitValidity,UnsafeObligations,SepLogic}.lean`), MIR verification bridges, caller–callee linking, and fast symbolic evaluation (`Anneal/Rustc/V2026_06_01/{Lower,SymbolicEval}.lean`), and plan-guided functional translation (`Anneal/FunctionalTranslation.lean`). |
| [`crates/`](crates/README.md) | **Untrusted (manifest- and audit-gated)** | Rust specification macros (`crates/anneal-spec`, `crates/anneal-spec-macros`: `#[spec]`, `#[embed_spec]`, `#[external_spec]`, `#[model]`, `#[invariant]`, `#[unsafe_trait]`, `#[unsafe_impl]`) and CLI orchestrator (`crates/cargo-anneal`: `setup`, `extract`, `scaffold`, `verify`, `lock-specs`, `agent-context`, `agent-verify`, `agent-sandbox`). |
| [`tools/anneal-lsp/`](tools/anneal-lsp/) | **Untrusted (developer & agent tooling)** | Warm Lean 4 (`lake serve`) and Rust LSP MCP server (`mcp_server.py`) plus `PreToolUse` and `PostToolUse` hook scripts (`hooks/pre_tool_use.py`, `hooks/post_tool_use.py`) for interactive proof feedback and `.anneal/spec-lock.json` write enforcement across Claude Code, Gemini CLI, and Antigravity. |
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

## Acknowledgments

Anneal builds on decades of work and research in formal verification and the
study of programming languages, among other fields. It is only possible thanks
to the work of countless researchers and software engineers. Some of the most
significant influences are listed here, but this list is far from exhaustive.

- Son Ho and Jonathan Protzenko's [Aeneas] inspired PureLift's translation of
  Rust borrows and updates into pure computations. Early Anneal used Aeneas
  to translate Rust into Lean and [Charon] to extract Rust programs for
  analysis. Charon is by Son Ho, Guillaume Boisseau, Lucas Franceschino, Yoann
  Prak, Aymeric Fromherz, and Jonathan Protzenko. Son Ho, Aymeric Fromherz, and
  Jonathan Protzenko's [work on symbolic borrow checking][symbolic-borrows]
  informed Anneal's study of the semantics behind this translation.
- PureLift uses lawful bidirectional lenses. J. Nathan Foster, Michael B.
  Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt developed
  these foundations in [Combinators for Bidirectional Tree
  Transformations][tree-lenses].
- Anneal's proof-lifting experiments drew on Magnus O. Myreen, Michael J. C.
  Gordon, and Konrad Slind's [decompilation into logic][decompilation] to
  reason about one basic block at a time. [Tree Borrows][tree-borrows] by
  Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung guided
  experiments on how to account for mutable borrow permissions.
- Anneal's MIR correspondence proofs use a pinned copy of [lean-miri]. Yuichi
  Nishiwaki's port builds on the Rust compiler's MIR interpreter and the work of
  the [Miri developers and contributors][Miri]. Ralf Jung's [MiniRust] and the
  Rust Unsafe Code Guidelines contributors' [discussion of moved
  values][ucg-moves] helped inform Anneal's treatment of moves. Xavier Leroy
  and the [CompCert] contributors' work on simulation proofs provided a
  comparison for how Anneal relates its model to its reference semantics.
- [Lean 4], by Leonardo de Moura, Sebastian Ullrich, and the Lean
  contributors, checks Anneal's proofs. Lean's
  [declaration replay][lean-replay], [environment importer][lean-env],
  compiler-attribute handling, and kernel reduction behavior guided Anneal's
  auditor and PureLift's combinators.
- The Rust contributors' [compiler source][rustc] (including
  [`rustc_const_eval`][rustc-const-eval] and [a padding-clearing
  issue][rust-148470]) and [Rust Reference] guided Anneal's MIR capture and
  model of Rust behavior. The earlier memory model also drew on the
  [standard library documentation][rust-std]. The LLVM contributors'
  [language reference][llvm-linkage] guided Anneal's treatment of Rust's
  linkage attributes.
- Early design work drew on
  [research into security risks in Rust][rust-security] by Xiaoye Zheng,
  Zhiyuan Wan, Yun Zhang, Rui Chang, and David Lo. Lars Bergstrom's
  [Rust Nation UK talk][rust-nation], Jeff Vander Stoep's
  [Android delivery data][android-rust], and Hongliang Tian's
  [account of the Asterinas kernel][asterinas] gave the early design concrete
  examples of Rust development and the work involved in writing unsafe code.
- The [Fuchsia] and [Starnix eBPF][starnix-ebpf] contributors' production Rust
  crates and build integration shaped Anneal's out-of-tree verification
  interface and end-to-end verification tests.

[Aeneas]: https://arxiv.org/abs/2206.07185
[Charon]: https://link.springer.com/chapter/10.1007/978-3-031-98685-7_18
[symbolic-borrows]: https://arxiv.org/abs/2404.02680
[tree-lenses]: https://doi.org/10.1145/1232420.1232424
[decompilation]: https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf
[tree-borrows]: https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf
[lean-miri]: https://github.com/proofs-rs/lean-miri
[Miri]: https://github.com/rust-lang/miri
[MiniRust]: https://github.com/minirust/minirust
[ucg-moves]: https://github.com/rust-lang/unsafe-code-guidelines/issues/188
[CompCert]: https://compcert.org/
[Lean 4]: https://lean-lang.org/papers/lean4.pdf
[lean-replay]: https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean
[lean-env]: https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean
[rustc]: https://github.com/rust-lang/rust/tree/main/compiler
[rustc-const-eval]: https://github.com/rust-lang/rust/tree/main/compiler/rustc_const_eval/src/interpret
[rust-148470]: https://github.com/rust-lang/rust/issues/148470
[Rust Reference]: https://doc.rust-lang.org/reference/
[rust-std]: https://doc.rust-lang.org/std/
[llvm-linkage]: https://llvm.org/docs/LangRef.html#linkage-types
[rust-security]: https://arxiv.org/abs/2308.15046
[rust-nation]: https://www.youtube.com/watch?v=QrrH2lcl9ew
[android-rust]: https://blog.google/security/rust-in-android-move-fast-fix-things/
[asterinas]: https://asterinas.github.io/2025/06/04/kernel-memory-safety-mission-accomplished.html
[Fuchsia]: https://fuchsia.dev/
[starnix-ebpf]: https://fuchsia.googlesource.com/fuchsia/+/823a15538f191b9dbd9ebafaa6ba23220b87d2e1/src/starnix/lib/ebpf/core/src
