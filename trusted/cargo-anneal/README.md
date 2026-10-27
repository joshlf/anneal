# Trusted CLI orchestrator and boundary audit runner (`trusted/cargo-anneal/`)

This directory holds the `cargo-anneal` binary and library crate, including the
deterministic boundary and manifest auditor (`src/audit.rs`) and its 15-group
regression self-test suite (`src/self_test.rs`)
([#103](https://github.com/joshlf/anneal/issues/103),
[#109](https://github.com/joshlf/anneal/issues/109)).

## Why `trusted/cargo-anneal/` is in `trusted/`

Anneal places **all effectful code** inside [`trusted/`](../README.md) so that
untrusted repository code ([`theory/`](../../theory/README.md),
[`examples/`](../../examples/README.md), [`tests/`](../../tests/README.md)) is
mechanically restricted to pure, effect-free Lean definitions and proofs checked
by the Lean kernel. Because `cargo-anneal` spawns processes, manages staging
directories, orchestrates `rustc` MIR capture, and determines the final process
exit code of `cargo anneal verify`, it resides in `trusted/cargo-anneal/` and
uses zero external third-party crates or Python runtime dependencies.

## Subcommands and modules

- **`cargo-anneal [anneal] verify [crate-dir]` (`src/lib.rs`, `src/main.rs`):**
  Runs the three-stage verification pipeline on a Rust crate:
  1. Invokes [`anneal-rustc-capture`](../rustc-capture/README.md) to extract
     `Runtime(PostCleanup)` MIR into `.anneal/Mir.lean` and write SHA-256
     source/output digests into `.anneal/CaptureManifest.json`.
  2. Emits a candidate `.anneal/Proof.lean` proof script for
     `theorem verify_crate : Trusted.CrateTheorem Mir.crate` (unless
     `--keep-proof` is passed). Soundness does not rely on the proof script
     generator; `Proof.lean` is treated as untrusted input to Stage 3.
  3. Runs `audit::Checker::verify_crate` in-process to verify the manifest
     digests, compile `Trusted`, `Anneal`, `Mir`, and `Proof` in an isolated
     staging directory, and check `Proof.verify_crate` in
     [`trusted/audit/TrustedBoundary.lean`](../audit/README.md) at
     `trustLevel := 0` with full `base.toKernelEnv.replay`.
- **`cargo-anneal [anneal] verify-crate <crate-dir>` (`src/audit.rs`):**
  Runs Stage 3 directly on an already-captured crate directory and prints the
  verified target list and TCB audit log.
- **`cargo-anneal [anneal] audit-repo` (`src/audit.rs`):**
  Audits the Anneal repository checkout in CI: checks Cargo workspace DAG
  containment under `trusted/`, snapshots and compiles `trusted/lean/` against
  `trusted/lean/foundation-lock.json`, and audits downstream `theory/`,
  `examples/`, and `tests/` modules for Statement-vs.-Proof Origin Separation,
  axiom limits, and kernel replay.
- **`cargo-anneal [anneal] audit-self-test` (`src/self_test.rs`):**
  Runs all 15 bounded positive and negative regression fixture groups against
  `audit::Checker` and `TrustedBoundary.lean`.
