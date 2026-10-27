# Trusted `.olean` environment inspector (`trusted/audit/`)

This directory holds `TrustedBoundary.lean`: the Lean 4 `.olean` kernel-environment
inspector invoked by [`trusted/cargo-anneal/`](../cargo-anneal/README.md) to
enforce the [`trusted/` boundary](../README.md) in CI (`cargo-anneal audit-repo`
and `cargo-anneal audit-self-test`) and to serve as the final `trustLevel := 0`
kernel acceptance gate for `cargo anneal verify`
([#103](https://github.com/joshlf/anneal/issues/103) §5).

## Dual responsibilities

### 1. Repository boundary gate in CI (`cargo-anneal audit-repo`)
During Anneal CI, [`trusted/cargo-anneal/src/audit.rs`](../cargo-anneal/README.md)
snapshots and compiles [`trusted/lean/`](../lean/README.md) in a clean temporary
directory against `foundation-lock.json`, then invokes `TrustedBoundary.lean` on
the compiled `.olean` `Environment` and [`theory/`](../../theory/README.md),
[`examples/`](../../examples/README.md), and [`tests/`](../../tests/README.md)
to verify:

- **Import and provenance containment:** Every declaration in `trusted/lean/`
  depends only on `trusted/lean/` and `foundation-lock.json` (walking types,
  bodies, opaque values, recursor rules, constructor parents, mutual blocks,
  projections, and literals).
- **Syntax preflight:** Rejects `unsafe`, `partial`, `axiom`, `native_decide`,
  `implemented_by`, `csimp`, `extern`, `by_elab`, `run_tac`, and top-level
  evaluation commands (`#eval`, `#reduce`, `#check`), ensuring untrusted Lean
  modules are pure and side-effect-free.
- **Axiom containment and kernel replay:** Verifies that only `{propext,
  Quot.sound, Classical.choice}` are reachable in strict targets and replays all
  declarations in a fresh `base.toKernelEnv.replay`.
- **Cargo workspace DAG containment:** Verifies that every Cargo workspace
  member in root `Cargo.toml` resides under `trusted/` and that no workspace
  crate has a path dependency outside `trusted/`.

### 2. Per-invocation verification gate (`cargo anneal verify`)
When verifying a Rust crate, [`trusted/cargo-anneal/`](../cargo-anneal/README.md)
and `TrustedBoundary.lean` run as the final gate on `CaptureManifest.json` and
the compiled `.olean` modules (`Mir` and `Proof`) at `trustLevel := 0`:

1. **Manifest and input digest verification:** Confirms `compilation_succeeded == true`
   in `CaptureManifest.json` and verifies the SHA-256 digests of all `.rs`
   sources and generated `Mir.lean` modules.
2. **Exact theorem signature check:** Looks up `Proof.verify_crate` in the
   compiled `.olean` `Environment`, confirms it is a `.thmInfo` constant, and
   checks that its kernel type `ci.type` is literally the AST application
   `Expr.app (Expr.const ``Trusted.CrateTheorem []) (Expr.const ``Mir.crate [])`.
3. **Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation:** Walks
   the transitive constant closure of `ci.type` (unfolding `Mir` declarations)
   and rejects any constant originating in `theory/` (`Anneal.*`) or `Proof`.
   `theory/` constants are permitted only inside the proof term (`ci.value?`).
4. **Zero custom axioms and kernel replay:** Confirms that `Mir` contains only
   data declarations (no `axiom` or `theorem` declarations) and that the
   transitive closure of `Proof.verify_crate` uses only `{propext, Quot.sound,
   Classical.choice}` with zero `sorryAx`, `unsafe`, or `partial` constants,
   then replays the declarations in `base.toKernelEnv.replay`.
5. **Deterministic TCB Audit Log emission:** Evaluates and renders the crate's
   `TCBItem` audit log when verification succeeds.
