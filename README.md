<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a deductive verification system for Rust, including unsafe code,
built as a Lean 4 library paired with a thin `rustc` MIR capture frontend.

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
| [`theory/`](theory/README.md) | **Untrusted (pure, kernel-checked)** | Derived, effect-free Lean library (`Anneal.*`): Y-diagram composition (`verify_through_passes`), small-step non-vacuity (`non_vacuity_at_every_depth`), MIR ownership and adequacy lemmas (`MirLemmas`), and plan-guided shallow functional translation (`FunctionalTranslation`). |
| [`examples/`](examples/README.md) | **Untrusted (pure, kernel-checked)** | Worked language and MIR verification instances (`AnnealExamples.*`) in a single Lake workspace for interactive Lean InfoView editing. |
| [`tests/`](tests/README.md) | **Untrusted (pure test suites & canaries)** | Pure Lean positive and negative verification tests, structural non-vacuity and Rust adequacy canaries, and `trusted/` boundary fixture inputs. |
| [`AGENTS.md`](AGENTS.md), [`agent_docs/`](agent_docs/development.md) | **Contributor guidance** | Entry point, development workflow, and Rust correspondence citation rules. |
