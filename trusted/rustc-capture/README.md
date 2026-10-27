<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trusted `rustc` capture serializer (`trusted/rustc-capture/`)

This directory holds the thin, mechanical `rustc` capture adapter that extracts
typed `Runtime(PostCleanup)` MIR and inline specification annotations from
`rustc`, along with the pure proof-script generator (`src/proof_gen.rs`).

## Why `trusted/rustc-capture/` is in `trusted/`

Lean's kernel checks that `Proof.verify_crate` in `Proof.lean` proves
`Trusted.CrateTheorem Mir.crate` over `Mir.lean`. It cannot check whether the
`MirBody` and `CapturedFn` structures serialized into `Mir.lean` match the Rust
program compiled by `rustc`. A bug here could serialize the wrong instruction or
attach a specification to the wrong item.

To make human auditing tractable, `trusted/rustc-capture/` is kept strictly
mechanical and self-contained:

1. **Zero program transformations or VC generation in MIR capture:** All CFG
   cleanup, control-flow structuring, functional translation, and
   weakest-precondition generation happen outside MIR capture (checked by the
   Lean kernel against [`theory/`](../../theory/README.md)).
2. **Direct extraction from `rustc`:**
   - Captures `Runtime(PostCleanup)` MIR bodies emitted by `rustc`.
   - Reads inline `// anneal:spec` specification annotations attached to target
     functions.
3. **Fail-closed serialization and `CaptureManifest.json`:**
   - Rejects unsupported `rustc` versions, target triples, MIR phases, or
     unrecognized MIR statement/terminator variants.
   - Emits read-only `Mir.lean` modules (`def crate : Trusted.Crate := ...`) and
     `CaptureManifest.json` recording SHA-256 digests of all `.rs` inputs and
     `Mir.lean` outputs, marking `compilation_succeeded = true` only after
     `rustc` completes compilation.
4. **Candidate-feature recording:** `capture_crate_with_options` records
   `"candidate_features": ["rustc_capture"]` in `CaptureManifest.json`, which
   `cargo-anneal` enforces against the target crate's `CrateTrustPolicy` and
   active release channel.
5. **Zero workspace dependencies:** `trusted/rustc-capture/` has zero Cargo
   dependencies. Every extraction function that interprets `rustc` MIR
   structures must follow
   [`agent_docs/trusted-rust.md`](../../agent_docs/trusted-rust.md).
