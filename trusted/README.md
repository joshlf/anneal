<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trusted boundary (`trusted/`)

This directory isolates every component of Anneal whose bugs could cause
`cargo anneal verify` to exit `0` (with Lean's kernel accepting a proof) while
the guarantee the user expects to hold of their compiled Rust binary is false or
weaker than claimed.

## The boundary criterion

Anneal separates **trusted** code (`trusted/`) from **untrusted** code
([`theory/`](../theory/README.md), [`examples/`](../examples/README.md),
[`tests/`](../tests/README.md)) using two complementary rules:

> **1. Failure-Mode Test (Semantic Commitments):**
> *If a component contains a bug, can `cargo anneal verify` still exit `0`—with
> the Lean kernel and boundary auditor accepting
> `Proof.verify_crate : Trusted.CrateTheorem Mir.crate`—while the real-world
> property claimed of the compiled Rust program is false?*
>
> - **Yes:** The component is part of the human-audited Trusted Computing Base
>   (TCB) and must live under `trusted/`.
> - **No** (a bug in a pure Lean definition or proof either fails to typecheck
>   in the Lean kernel or is rejected by `trusted/audit/`): The component is
>   untrusted ("Lean said it was fine, so it is fine") and must live **outside**
>   `trusted/`.
>
> **2. Pure vs. Effectful Separation:**
> All effectful code—filesystem and process I/O, CLI orchestration, `rustc` MIR
> extraction, and `.olean` environment auditing—lives inside `trusted/`. Code
> outside `trusted/` (`theory/`, `examples/`, `tests/`) is mechanically
> restricted to pure, effect-free Lean definitions and proofs checked by the
> Lean kernel; it cannot execute arbitrary processes, mutate files, or bypass
> the boundary auditor.

## Subdirectories of `trusted/`

Every human-audited surface in the repository lives in one of four
subdirectories under `trusted/`:

| Subdirectory | Language | Responsibility |
| --- | --- | --- |
| [`trusted/lean/`](lean/README.md) | Lean 4 (`Trusted.*`) | Primitive semantic commitments and top-level theorem definitions that appear in the **type (`ci.type`)** of `Trusted.CrateTheorem`: `Trusted/Refinement.lean` (`Preorder` (`≤`), `Partial`, `Language`, `Language.SpecOn`, `Language.Spec`, `Language.WellFormedOn`, `Language.WellFormed`, `Compiles`, `Abstracts`, `Compiler`, `VerificationResultOn`, `VerificationResult`), `Trusted/StepResult.lean` (`ChoiceKind`, `TerminationKind`, `FailureKind`, `StepResult`, `ExecQuery`, `ExecOut`, `SmallStepMachine`, `ReachesPrefix`, `BehaviorOf`), `Trusted/Memory.lean`, `Trusted/MirAst.lean`, and `Trusted/MirSemantics.lean` (`TCBItem`, `RustcCompiler`, `CrateTheorem`). |
| [`trusted/audit/`](audit/README.md) | Lean 4 | The `.olean` kernel-environment inspector (`TrustedBoundary.lean`), invoked by [`trusted/cargo-anneal/`](cargo-anneal/README.md) to enforce containment, Statement-vs.-Proof Origin Separation, `@[vetted]` vs. `@[candidate <feature>]` non-contamination, axiom limits, and `toKernelEnv.replay` at `trustLevel := 0`. |
| [`trusted/cargo-anneal/`](cargo-anneal/README.md) | Rust | The CLI orchestrator (`cargo-anneal`), boundary/manifest audit runner (`audit.rs`), and 14-group regression self-test suite (`self_test.rs`). Coordinates `anneal-rustc-capture` and `TrustedBoundary.lean` verification without external runtime dependencies. |
| [`trusted/rustc-capture/`](rustc-capture/README.md) | Rust | The thin, mechanical `rustc` capture adapter and pure proof-script generator (`proof_gen.rs`) that extracts MIR and specification attributes, emitting read-only `Mir.lean` modules, `CaptureManifest.json`, and candidate `Proof.lean` scripts. |

## Vetted (`@[vetted]`) vs. Candidate Trusted (`@[candidate <feature>]`)

To allow incremental development on `main` without weakening the stability or
correctness guarantees of audited definitions, code in
[`trusted/lean/`](lean/README.md) and
[`trusted/rustc-capture/`](rustc-capture/README.md) is divided into two explicit
trust tiers:

1. **Exhaustive Per-Declaration Trust Tiers in `trusted/lean/`:**
   - Every top-level declaration in `trusted/lean/` (including named `instance`
     declarations) must carry either `@[vetted]` or `@[candidate <feature>]`
     (for one of the registered subsystem feature IDs: `refinement`,
     `step_result`, `memory`, `mir_ast`, `mir_semantics`, `rustc_capture`).
   - Inside a `@[vetted] inductive`, individual constructors inherit `@[vetted]`
     by default or may carry an explicit `@[vetted]` or `@[candidate <feature>]`
     override. Constructors of a `@[candidate <feature>] inductive` cannot be
     marked `@[vetted]`.
   - `trusted/rustc-capture/` records `"candidate_features": ["rustc_capture"]`
     in `CaptureManifest.json`, and `trusted/cargo-anneal/` checks the target
     crate's `CrateTrustPolicy` before invoking `anneal-rustc-capture` and
     during `verify_crate_with_policy`.
2. **Non-Contamination and Guarded Dispatch (`Trusted.candidate`):**
   - A `@[vetted]` Lean declaration may never reference a
     `@[candidate <feature>]` constant in its type (`ci.type`).
   - In its body (`ci.value?`), a `@[vetted]` Lean declaration may reference a
     `@[candidate <feature>]` constant only inside a guarded match arm wrapped
     in `Trusted.candidate "<feature>" (...)` corresponding to a
     `@[candidate <feature>]` constructor.
3. **Release Channels and Opt-In Trust Policy (`allow-candidate-features`):**
   - **Stable releases (`ReleaseChannel::Stable`):** Hard-lock the trust policy
     to `VettedOnly` (`allow-candidate-features = []`). Any candidate capture
     path or candidate Lean constant in a crate's verification closure is
     rejected.
   - **Alpha releases (`ReleaseChannel::Alpha`):** Default to `VettedOnly`,
     rejecting candidate features with a diagnostic naming the required feature
     ID unless the target crate explicitly opts in via
     `[package.metadata.anneal.trust-policy] allow-candidate-features = [...]`
     in `Cargo.toml` or `--allow-candidate-features` on the CLI.
   - **TCB Audit Log & Unused-Feature Warnings:** Candidate features exercised
     by a verified crate are reported in a dedicated
     `Candidate-Trusted TCB (Unvetted / Alpha)` section of the TCB audit log.
     Named features in `allow-candidate-features` that are not exercised by the
     crate emit an unused-feature warning.

## Mechanical guarantees that code outside `trusted/` is untrusted

[`trusted/cargo-anneal/`](cargo-anneal/README.md) and
[`trusted/audit/TrustedBoundary.lean`](audit/README.md) enforce five mechanical
invariants in CI and during verification so that code outside `trusted/`
(`theory/`, `examples/`, and `tests/`) cannot execute effects or silently become
trusted:

1. **Direct import and constant containment for `trusted/lean/`:**
   `trusted/lean/` is compiled in an isolated staging directory against a pinned
   foundation lock (`foundation-lock.json`, starting from `Init.Core`). No
   declaration in `trusted/lean/` may import or reference any module in
   `theory/`, `examples/`, or `tests/`.
2. **Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation:**
   In Lean's compiled `.olean` `Environment`, a theorem's statement (`ci.type`)
   and its proof term (`ci.value?`) are distinct. `TrustedBoundary.lean` walks
   the transitive constant closure of `ci.type` for
   `Proof.verify_crate : Trusted.CrateTheorem Mir.crate` (including unfolded
   `Mir.crate`) and **rejects any reference to `theory/` (`Anneal.*`)**.
   `theory/` may be referenced **only** inside the proof term (`ci.value?`).
   Consequently, a definition in `theory/` can never alter the meaning of a
   theorem statement.
3. **Pure, effect-free syntax preflight, zero custom axioms, and kernel replay
   (`toKernelEnv.replay`):**
   Across `trusted/lean/`, `theory/`, `examples/`, `tests/`, `Mir.lean`, and
   `Proof.lean`, syntax preflight rejects `unsafe`, `partial`, `axiom`,
   `native_decide`, `implemented_by`, `csimp`, `extern`, `by_elab`, `run_tac`,
   and top-level evaluation commands (`#eval`, `#reduce`, `#check`), preventing
   elaboration-time side effects. In the compiled `.olean` environment,
   `TrustedBoundary.lean` rejects `sorryAx`, `isUnsafe`, `isPartial`, and any
   axiom outside `{propext, Quot.sound, Classical.choice}`, then replays all
   constants from scratch in `base.toKernelEnv.replay`.
4. **Cargo workspace containment under `trusted/`:**
   The boundary auditor verifies that every member in root `Cargo.toml` resides
   under `trusted/` and that no workspace crate has a path dependency outside
   `trusted/`.
5. **Cryptographic `CaptureManifest.json` handshake and final exit gating:**
   `trusted/rustc-capture/` writes read-only `Mir.lean` modules alongside a
   `CaptureManifest.json` recording the target items, `compilation_succeeded`,
   and SHA-256 digests of all `.rs` sources and `Mir.lean` files.
   `trusted/cargo-anneal/` verifies all manifest digests and compilation
   completion before compiling `.olean` proofs, running `TrustedBoundary.lean`,
   and returning the final process exit code.

## Review obligations for `trusted/`

Passing automated containment and replay checks proves that `trusted/` is
self-contained and that untrusted code is pure and axiom-free; it does **not**
prove that `trusted/lean/` accurately models Rust, that `trusted/rustc-capture/`
faithfully serializes `rustc` queries, or that `trusted/audit/` and
`trusted/cargo-anneal/` check a strong enough policy. Every change under
`trusted/` requires careful human review and must follow
[the Rust correspondence comment policy](../agent_docs/trusted-rust.md).
