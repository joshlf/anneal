# Trusted `rustc` capture serializer (`trusted/rustc-capture/`)

This directory holds the thin, mechanical `rustc_driver` adapter that extracts
typed `Runtime(PostCleanup)` MIR, compiler-queried layouts and ABIs, and
specification companion items from `rustc`
([#99](https://github.com/joshlf/anneal/issues/99) §3,
[#103](https://github.com/joshlf/anneal/issues/103) §2–§3).

## Why `trusted/rustc-capture/` is in `trusted/`

Lean's kernel checks that a proof in `Proof/<Item>.lean` proves the `Claim` in
`Obligations/<Item>.lean` over `Mir/<Item>.lean`. It cannot check whether the
`CapturedMir` and layout tables serialized into `Mir/<Item>.lean` match the Rust
program compiled by `rustc`. A bug here could serialize the wrong instruction,
query a layout under the wrong `TypingEnv`, or attach a specification to the
wrong `DefId`.

To make human auditing tractable, `trusted/rustc-capture/` is kept strictly
mechanical and isolated from [`crates/`](../../crates/README.md):

1. **Toolchain-agnostic protocol vs. version-scoped backend:**
   - `src/{lib,manifest,lean_emit}.rs` (pure stable Rust) owns
     `UnitCaptureManifest`, `CaptureManifest`, SHA-256 hashing, and deterministic
     Lean 4 `CapturedMir` emission (`IrCapturedMir`).
   - `src/rustc_2026_06_01/{driver,layout_lower,mir_lower,mod}.rs` (pinned to
     `rustc 1.98.0-nightly (14210df0e 2026-05-31)`) owns `#![feature(rustc_private)]`
     extraction.
2. **Direct `tcx` extraction on resolved `DefId`s:**
   - Queries `tcx.optimized_mir` (for functions/methods) and `tcx.mir_for_ctfe`
     (for constants/statics) to obtain `Runtime(PostCleanup)` MIR bodies.
   - Queries `tcx.layout_of(...)` and `tcx.fn_abi_of_instance(...)` under
     `TypingEnv::post_analysis(tcx, def_id)`
     ([#88](https://github.com/joshlf/anneal/issues/88)).
   - Classifies items into `Subject`, `InlineSpecRequires`
     (`__anodized_fn_requires_*`), `InlineSpecEnsures`
     (`__anodized_fn_ensures_*`), `InlineSpecQualifiers`
     (`__anodized_fn_qualifiers_*`), `ExternalSpec`
     (`__ANNEAL_EXT_SPEC_TARGET_*`), and `Model` (`__ANNEAL_MODEL_*`), linking
     companion contracts to their target subject `DefId` and inlining synthetic
     `anodized` closure wrappers so contract MIR evaluates directly in `MirSem`.
3. **Fail-closed serialization and `UnitCaptureManifest.json` / `CaptureManifest.json`:**
   - Emits per-unit `UnitCaptureManifest.json` and read-only `Mir/<Crate>/<Item>.lean`
     modules recording SHA-256 digests of `.rs` inputs and `.lean` outputs,
     marking `compilation_succeeded = true` only after `rustc` completes
     analysis.
4. **Zero dependencies on `crates/`:** `trusted/audit/check_trusted.py` enforces
   that `trusted/rustc-capture/` has zero dependency edges to workspace crates in
   `crates/`. Every extraction path that interprets `rustc_middle` or `rustc_abi`
   types follows [`agent_docs/trusted-rust.md`](../../agent_docs/trusted-rust.md).
