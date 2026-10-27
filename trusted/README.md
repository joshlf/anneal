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
| [`trusted/lean/`](lean/README.md) | Lean 4 (`Trusted.*`) | Primitive semantic commitments and top-level theorem definitions that appear in the **type (`ci.type`)** of `Trusted.CrateTheorem`: `Trusted/Refinement.lean` (`Preorder` (`≤`), `Partial`, `Language`, `Language.SpecOn`, `Language.Spec`, `Language.WellFormedOn`, `Language.WellFormed`, `Compiles`, `Abstracts`, `Compiler`, `VerificationResultOn`, `VerificationResult`), `Trusted/StepResult.lean` (`ChoiceKind`, `TerminationKind`, `FailureKind`, `StepResult`, `ExecQuery`, `ExecOut`, `SmallStepMachine`, `ReachesPrefix`, `BehaviorOf`), `Trusted/Layout.lean`, `Trusted/Memory.lean`, `Trusted/MirAst.lean`, and `Trusted/MirSemantics.lean` (`TCBItem`, `RustcCompiler`, `CrateTheorem`). |
| [`trusted/audit/`](audit/README.md) | Lean 4 | The `.olean` kernel-environment inspector (`TrustedBoundary.lean`), invoked by [`trusted/cargo-anneal/`](cargo-anneal/README.md) to enforce containment, Statement-vs.-Proof Origin Separation, axiom limits, and `toKernelEnv.replay` at `trustLevel := 0`. |
| [`trusted/cargo-anneal/`](cargo-anneal/README.md) | Rust | The CLI orchestrator (`cargo-anneal`), boundary/manifest audit runner (`audit.rs`), and 15-group regression self-test suite (`self_test.rs`). Coordinates `anneal-rustc-capture`, proof script emission, and `TrustedBoundary.lean` verification without external runtime dependencies. |
| [`trusted/rustc-capture/`](rustc-capture/README.md) | Rust | The thin, mechanical `rustc` capture adapter that extracts MIR, queried layouts, and specification attributes, emitting read-only `Mir.lean` modules and `CaptureManifest.json`. |

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
3. **Pure, effect-free syntax preflight, zero custom axioms, and kernel replay (`toKernelEnv.replay`):**
   Across `trusted/lean/`, `theory/`, `examples/`, `Mir.lean`, and `Proof.lean`,
   syntax preflight rejects `unsafe`, `partial`, `axiom`, `native_decide`,
   `implemented_by`, `csimp`, `extern`, `by_elab`, `run_tac`, and top-level
   evaluation commands (`#eval`, `#reduce`, `#check`), preventing elaboration-time
   side effects. In the compiled `.olean` environment, `TrustedBoundary.lean`
   rejects `sorryAx`, `isUnsafe`, `isPartial`, and any axiom outside
   `{propext, Quot.sound, Classical.choice}`, then replays all constants from
   scratch in `base.toKernelEnv.replay`.
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
