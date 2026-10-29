# Untrusted Rust CLI and tooling crates (`crates/`)

This directory holds the untrusted Rust crates that orchestrate Cargo, Lake,
interactive editing, and optional heuristic code generators
([#99](https://github.com/joshlf/anneal/issues/99),
[#103](https://github.com/joshlf/anneal/issues/103) §2).

## Why `crates/` is outside `trusted/`

Unlike `anneal/v1`—where the Rust CLI parsed specifications with `syn`,
generated verification conditions in Rust (`generate.rs`), and scanned Lean
files with regular expressions (`validate.rs`)—all semantic extraction lives in
[`trusted/rustc-capture/`](../trusted/rustc-capture/README.md) and all proof
checking and audit gating live in the Lean kernel and
[`trusted/audit/`](../trusted/audit/README.md).

Crates in `crates/` are kept outside the TCB by two architectural invariants:

1. **Read-only capture boundary (`CaptureManifest.json`):**
   `trusted/rustc-capture/` writes `Mir/<Item>.lean` and records its SHA-256
   digests and target `DefId` list in `CaptureManifest.json`. Code in `crates/`
   may scaffold user/agent `Proof/<Item>.lean` files or propose untrusted
   functional views (`View/<Item>.lean` paired with simulation witnesses for a
   Lean `VerifiedChecker` in [`theory/`](../theory/README.md)), but any
   modification to `Mir/<Item>.lean` or omission of a target item is rejected by
   `trusted/audit/`.
2. **Final gate owned by `trusted/audit/`:**
   At the end of `cargo anneal verify`, `cargo-anneal` delegates final acceptance
   and exit status to `trusted/audit/`, which verifies `CaptureManifest.json`
   and replays the compiled `.olean` proofs at `trustLevel := 0`.

## Crates in `crates/`

- **`crates/anneal-spec` and `crates/anneal-spec-macros`:**
  User-facing Rust specification attributes (`#[spec]`, `#[embed_spec]`,
  `#[external_spec]`, and `#[model]`) built on `anodized` and `anodized-core`
  (`Mode::EmbedSpecs`). These macros preserve runtime assertion semantics via
  `anodized::spec` while embedding `#[doc = "anneal:spec_v1:..."]` marker
  payloads (`requires`, `ensures`, `maintains`, `binds`, and Lean specification
  target names) for `trusted/rustc-capture` to read on resolved `DefId`s.
- **`crates/cargo-anneal`:**
  User-facing Cargo subcommand (`cargo anneal extract`, `cargo anneal scaffold`,
  `cargo anneal verify`) that invokes `trusted/rustc-capture` via
  `RUSTC_WORKSPACE_WRAPPER`, aggregates per-unit `UnitCaptureManifest.json`
  files into `CaptureManifest.json`, generates disposable verification glue in
  `.anneal/generated/{Mir,Obligations,Verify}/`, scaffolds non-destructive user
  proof stubs in `anneal/proofs/{Specs,Proof}/`, runs `lake build`, and
  delegates final verification gating to `trusted/audit/`. The `lake build` it
  spawns opts into Lake's local artifact cache (`LAKE_ARTIFACT_CACHE=true`,
  `LAKE_RESTORE_ARTIFACTS=true`, unless already set in the environment), so the
  `Trusted` and `Anneal` libraries compile once per Lean toolchain rather than
  once per verified crate.
