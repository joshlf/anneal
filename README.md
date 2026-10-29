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
result—including **all effectful code**—inside `trusted/`. Everything outside
`trusted/` (`theory/`) is mechanically restricted to pure, effect-free Lean
definitions and proofs checked by the Lean 4 kernel and
[`trusted/audit/TrustedBoundary.lean`](trusted/audit/TrustedBoundary.lean).

Within `trusted/`, semantic definitions and `rustc` capture components are
decorated in place along two trust tiers:

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
| [`trusted/lean/`](trusted/lean/Trusted.lean) | **Trusted (`@[vetted]` & `@[candidate <feature>]` TCB)** | Primitive Lean semantic and theorem definitions (`Refinement`, `StepResult`, `Memory`, `MirAst`, `MirSemantics`) required to state `Trusted.CrateTheorem` and `VerificationResult`. |
| [`trusted/audit/`](trusted/audit/TrustedBoundary.lean) | **Trusted (TCB)** | The `.olean` kernel-environment inspector (`TrustedBoundary.lean`) enforcing foundation-lock containment, `@[vetted]` vs. `@[candidate <feature>]` non-contamination, module-origin closure, pure syntax preflight, zero custom axioms, and kernel replay. |
| [`trusted/cargo-anneal/`](trusted/cargo-anneal) | **Trusted (TCB)** | The CLI orchestrator (`cargo anneal`) and boundary/crate verification runner (`audit.rs`). |
| [`trusted/rustc-capture/`](trusted/rustc-capture) | **Trusted (TCB)** | The thin `rustc` MIR/attribute serializer and pure proof-script generator (`proof_gen.rs`) emitting `.anneal/Mir.lean` and candidate `.anneal/Proof.lean` scripts. |
| [`theory/`](theory/Anneal.lean) | **Untrusted (pure, kernel-checked)** | Derived, effect-free Lean library (`Anneal.*`): Y-diagram composition (`verify_through_passes`), small-step non-vacuity (`non_vacuity_at_every_depth`), MIR ownership and adequacy lemmas (`MirLemmas`), and plan-guided shallow functional translation (`FunctionalTranslation`). |
| [`AGENTS.md`](AGENTS.md) | **Contributor guidance** | Entry point, architecture, and Rust correspondence citation rules. |
