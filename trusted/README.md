# Trusted boundary (`trusted/`)

This directory isolates every component of Anneal whose bugs could cause
`cargo anneal verify` to exit `0` (with Lean's kernel accepting a proof) while
the guarantee the user expects to hold of their compiled Rust binary is false or
weaker than claimed.

## The boundary criterion

Anneal separates **trusted** code (`trusted/`) from **untrusted** code
([`theory/`](../theory/README.md), [`crates/`](../crates/README.md),
[`examples/`](../examples/README.md), [`tests/`](../tests/README.md)) using one
failure-mode test:

> **Failure-Mode Test:**
> *If a component contains a bug, can `cargo anneal verify` still exit `0`—with
> the Lean kernel and `trusted/audit/` accepting `prove_<item> : VerificationResult ...`—while
> the real-world property claimed of the compiled Rust program is false?*
>
> - **Yes:** The component is part of the human-audited Trusted Computing Base
>   (TCB) and must live under `trusted/`.
> - **No** (a bug either fails to typecheck in the Lean kernel or is rejected by
>   `trusted/audit/`): The component is untrusted ("Lean said it was fine, so it
>   is fine") and must live **outside** `trusted/`.

## Subdirectories of `trusted/`

Every human-audited surface in the repository lives in one of three
subdirectories under `trusted/`:

| Subdirectory | Language | Responsibility |
| --- | --- | --- |
| [`trusted/lean/`](lean/README.md) | Lean 4 (`Trusted.*`) | Primitive semantic commitments and top-level theorem definitions that appear in the **type (`ci.type`)** of verification certificates: Layer 1A (`Trusted/Refinement.lean`: `LE`, `Std.IsPreorder`, `Std.IsPartialOrder`, `Semantics`, `Spec`, `Partial`, `Language`, `GuardedRefines`), constructive coinductive containers and open interaction trees (`Trusted/{CoInd,Effect,ITree}.lean`), sequence lookup/update helpers (`Trusted/Sequence.lean`), dialect-scoped Rust MIR coalgebras (`Trusted/Rustc/V2026_06_01/{Layout,MirAst,MirSemantics}` with default re-export aliases `Trusted/{Layout,MirAst,MirSemantics}.lean`), and top-level claim gates (`Trusted/VerificationResult.lean`: `VerificationResult`, `StatefulVerificationResult`, `ModularVerificationResult`, `TraceVerificationResult`, `TotalVerificationResult`). |
| [`trusted/audit/`](audit/README.md) | Lean 4 & Python | The `.olean` kernel-environment inspector (`TrustedBoundary.lean` / `Audit.lean`) and boundary runner (`check_trusted.py`) that enforce containment in CI and serve as the final `trustLevel := 0` acceptance gate for every `cargo anneal verify` invocation. |
| [`trusted/rustc-capture/`](rustc-capture/README.md) | Rust (`rustc_driver`) | The thin, mechanical `rustc` driver adapter (`src/{lib,manifest,lean_emit}.rs` and dialect backend `src/rustc_2026_06_01/{driver,layout_lower,mir_lower,mod}.rs`) that extracts `Runtime(PostCleanup)` MIR, queried layouts, and `#[doc = "anneal:spec_v1:..."]` marker metadata on `DefId`s, emitting read-only `Mir/<Item>.lean` modules and `UnitCaptureManifest.json` / `CaptureManifest.json`. |

## Mechanical guarantees that code outside `trusted/` is untrusted

[`trusted/audit/`](audit/README.md) enforces five mechanical invariants in CI
and during verification so that code outside `trusted/` (`theory/` and `crates/`)
cannot silently become trusted:

1. **Direct import and constant containment for `trusted/lean/`:**
   `trusted/lean/` is compiled in an isolated staging directory against the
   SHA-256-verified Lean 4.34.1 toolchain (`foundation-lock.json`) and its
   standard library (`Init.*`, `Std.*`). No declaration in `trusted/lean/` may
   import or reference any module in `theory/`, `examples/`, or `tests/`.
2. **Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation:**
   In Lean's compiled `.olean` `Environment`, a theorem's statement (`ci.type`)
   and its proof term (`ci.value?`) are distinct. `trusted/audit/` walks the
   transitive constant closure of `ci.type` for every claim theorem (including
   unfolded `Mir.<Item>.claim`, `Crate.capture`, and `ProjectPolicy.policy`) and
   **rejects any reference to `theory/` (`Anneal.*`)**. `theory/` may be
   referenced **only** inside the proof term (`ci.value?`). Consequently, a
   definition in `theory/` can never alter the meaning of a theorem statement.
3. **Zero custom axioms, syntax preflight, and kernel replay (`toKernelEnv.replay`):**
   Across both `trusted/lean/` and the transitive closure of every proof term
   (`ci.value?`), `trusted/audit/` rejects `sorryAx`, `isUnsafe`, `isPartial`,
   `native_decide`, `implemented_by`, `csimp`, `extern`, and any axiom outside
   `{propext, Quot.sound, Classical.choice}`, and replays `trusted/lean/`
   constants from scratch in `base.toKernelEnv.replay`.
4. **Cargo workspace dependency containment for `trusted/rustc-capture/`:**
   CI verifies via `cargo metadata` that `trusted/rustc-capture/` has zero
   dependency edges to workspace crates in `crates/`.
5. **Cryptographic `CaptureManifest.json` handshake and final exit gating:**
   `trusted/rustc-capture/` writes read-only `Mir/<Item>.lean` modules alongside
   a `CaptureManifest.json` recording the target `DefId` list, `compilation_succeeded`,
   and SHA-256 digests of all `.rs` sources and `Mir/<Item>.lean` files.
   Untrusted tools in `crates/` may write `View/<Item>.lean` or `Proof/<Item>.lean`,
   never `Mir/<Item>.lean`. `trusted/audit/` verifies all manifest digests and
   compilation completion before checking `.olean` proofs and returning the
   final process exit code.

## Review obligations for `trusted/`

Passing automated containment and replay checks proves that `trusted/` is
self-contained and free of unapproved axioms; it does **not** prove that
`trusted/lean/` accurately models Rust, that `trusted/rustc-capture/` faithfully
serializes `rustc` queries, or that `trusted/audit/` checks a strong enough
policy. Every change under `trusted/` requires careful human review and must
follow [the Rust correspondence comment policy](../agent_docs/trusted-rust.md).
