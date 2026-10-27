<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trusted CLI orchestrator and boundary audit runner (`trusted/cargo-anneal/`)

This directory holds the `cargo-anneal` binary and library crate, including the
deterministic boundary and manifest auditor (`src/audit.rs`) and its 14-group
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
exit code of `cargo anneal verify`, it resides in `trusted/cargo-anneal/`.

## Subcommands and modules

- **`cargo-anneal [anneal] verify [crate-dir]` (`src/lib.rs`, `src/main.rs`):**
  Runs the verification pipeline on a Rust crate (accepting
  `--allow-candidate-features <feat1,feat2|*>` and
  `--release-channel <alpha|stable>`, merged with
  `[package.metadata.anneal.trust-policy]` in `Cargo.toml`):
  1. Invokes [`anneal-rustc-capture`](../rustc-capture/README.md) under the
     crate's `CapturePolicy` to extract `Runtime(PostCleanup)` MIR into
     `.anneal/Mir.lean`, write SHA-256 source/output digests and exercised
     `candidate_features` into `.anneal/CaptureManifest.json`, and emit a
     candidate `.anneal/Proof.lean` proof script for
     `theorem verify_crate : Trusted.CrateTheorem Mir.crate` (unless
     `--keep-proof` is passed). Soundness does not rely on the proof-script
     generator; `Proof.lean` is treated as untrusted input to the audit gate.
  2. Runs `audit::Checker::verify_crate_with_policy` in-process to verify the
     manifest digests and candidate-feature policy, compile `Trusted`, `Anneal`,
     `Mir`, and `Proof` in an isolated staging directory, and check
     `Proof.verify_crate` in
     [`trusted/audit/TrustedBoundary.lean`](../audit/README.md) at
     `trustLevel := 0` with full `base.toKernelEnv.replay`.
- **`cargo-anneal [anneal] verify-crate <crate-dir>` (`src/audit.rs`):**
  Runs the audit gate directly on an already-captured crate directory and prints
  the verified target list, the `TCBItem` audit log, the
  `Candidate-Trusted TCB (Unvetted / Alpha)` section, and any unused
  `allow-candidate-features` warnings.
- **`cargo-anneal [anneal] audit-repo` (`src/audit.rs`):**
  Audits the Anneal repository checkout in CI: checks Cargo workspace DAG
  containment under `trusted/`, snapshots and compiles `trusted/lean/` against
  `trusted/lean/foundation-lock.json` (enforcing `@[vetted]` vs.
  `@[candidate <feature>]` non-contamination), and audits downstream `theory/`,
  `examples/`, and `tests/` modules for Statement-vs.-Proof Origin Separation,
  axiom limits, and kernel replay.
- **`cargo-anneal [anneal] audit-self-test` (`src/self_test.rs`):**
  Runs all 14 bounded positive and negative regression fixture groups against
  `audit::Checker` and `TrustedBoundary.lean`.
