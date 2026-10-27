<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a deductive verification system for Rust, including unsafe code,
built as a Lean 4 library paired with a thin `rustc_driver` capture frontend.

- [Requirements, aspirations, and architectural decision ledger](https://github.com/joshlf/anneal/issues/1).
- [Top-level Y-diagram architecture and `Partial` refinement foundation (#100)](https://github.com/joshlf/anneal/issues/100).
- [Owned `rustc` capture and verified lowering pipeline (#99)](https://github.com/joshlf/anneal/issues/99).
- [Library-centric verification, multi-modal specifications, and machine-checked TCB & trust-policy results (#103)](https://github.com/joshlf/anneal/issues/103).
- [Compiler-selected type layouts, dynamic extent, and layout portability (#88)](https://github.com/joshlf/anneal/issues/88).
- [Direct Lean operational semantics vs. MiniRust (#101)](https://github.com/joshlf/anneal/issues/101).
- [Inline assembly (`TerminatorKind::InlineAsm`) and foreign/ISA bridge (#102)](https://github.com/joshlf/anneal/issues/102).
- [Minimal end-to-end verification slice (`pub fn id(x: usize) -> usize { x }`) (#109)](https://github.com/joshlf/anneal/issues/109).

## Repository layout and trust boundary

Anneal isolates every component whose bugs could cause a false verification
result—including **all effectful code**—inside [`trusted/`](trusted/README.md).
Everything outside `trusted/` is mechanically restricted to pure, effect-free
Lean definitions and proofs checked by the Lean 4 kernel and
[`trusted/audit/`](trusted/audit/README.md).

Within [`trusted/`](trusted/README.md), semantic definitions and `rustc` capture
components are decorated in place along two trust tiers:

- **Vetted (`@[vetted]`):** Audited against verbatim Rust Reference citations
  and stabilized for both `alpha` and `stable` releases.
- **Candidate Trusted (`@[candidate <feature>]`):** Part of the TCB by the
  Failure-Mode Test, but not yet fully vetted. Disabled by default (`VettedOnly`
  trust policy); usable only in `alpha` releases when the target crate
  explicitly opts in via `[package.metadata.anneal.trust-policy]`
  (`allow-candidate-features`) or `--allow-candidate-features`, and surfaced in
  a dedicated `Candidate-Trusted TCB (Unvetted / Alpha)` section of the TCB
  audit log.

| Path | Trust status | Role |
| --- | --- | --- |
| [`trusted/`](trusted/README.md) | **Trusted (`@[vetted]` & `@[candidate <feature>]` TCB)** | All primitive semantic definitions and all effectful code required to state and gate a verification claim: primitive Lean semantic and theorem definitions ([`trusted/lean/`](trusted/lean/README.md)), the `.olean` kernel-environment inspector ([`trusted/audit/`](trusted/audit/README.md)), the CLI orchestrator and boundary/manifest audit runner ([`trusted/cargo-anneal/`](trusted/cargo-anneal/README.md)), and the thin `rustc` MIR/attribute serializer and pure proof-script generator ([`trusted/rustc-capture/`](trusted/rustc-capture/README.md)). |
| [`theory/`](theory/README.md) | **Untrusted (pure, kernel-checked)** | Derived, effect-free Lean library (`Anneal.*`): `pass_trans` (`verify_through_passes`), layout arithmetic and validators, `VerifierPass` / `ExactPass` normalizations, functional translations and `VerifiedChecker`s, `WP` program logics, and tactics. |
| [`examples/`](examples/README.md) | **Untrusted (pure, kernel-checked)** | Worked language and MIR verification instances (`AnnealExamples.*`) in a single Lake workspace for interactive Lean InfoView editing. |
| [`tests/`](tests/README.md) | **Untrusted (pure test suites & canaries)** | Pure Lean positive and negative verification tests, structural non-vacuity and Rust adequacy canaries (`MetaValidation`), and `trusted/` boundary fixture inputs. |
| [`AGENTS.md`](AGENTS.md), [`agent_docs/`](agent_docs/development.md) | **Contributor guidance** | Entry point, development workflow, writing policy, and Rust correspondence citation rules. |

## Historical research archive

Earlier bounded research experiments and design probes that informed the
architecture in [#100](https://github.com/joshlf/anneal/issues/100) and its
child issues remain archived in place:

- [Research agenda](docs/rust-opsem/research-agenda.md),
  [versioned Rust documentation clauses](docs/rust-opsem/clauses.md), and
  [atomic-contract reading](docs/rust-opsem/atomic-contract.md).
- [Early static-premise findings](docs/rust-opsem/early/static-premises.md),
  [choice/execution findings](docs/rust-opsem/early/choices-and-execution.md),
  and the
  [original twelve questions](docs/rust-opsem/early/original-questions.json).
- [Finite executable witness probe](experiments/finite-witness/README.md).
- [First checked milestone](docs/rust-opsem/first-milestone.md),
  [representation/memory transfers](docs/rust-opsem/representation-transfers.md),
  and [memory correspondence plus borrowing/cleanup
  probes](docs/rust-opsem/correspondence-experiment.md).
- [Archived `AnnealResearch` Lean sources and result
  manifests](experiments/opsem/README.md).
