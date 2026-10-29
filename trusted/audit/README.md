# Trusted environment and boundary auditor (`trusted/audit/`)

This directory contains the Lean `.olean` environment inspector and Python
runner that enforce the [`trusted/` boundary](../README.md) in CI and serve as
the final `trustLevel := 0` acceptance gate for `cargo anneal verify`
([#103](https://github.com/joshlf/anneal/issues/103) §5).

## Dual responsibilities

### 1. Repository boundary gate in CI
During Anneal CI, `trusted/audit/` snapshots and compiles
[`trusted/lean/`](../lean/README.md) in a clean temporary directory against the
SHA-256-pinned Lean 4.34.1 toolchain (`foundation-lock.json`) and its standard
library (`Init.*`, `Std.*`), then inspects the compiled `.olean` `Environment`
and [`theory/`](../../theory/README.md), [`examples/`](../../examples/README.md),
and [`tests/`](../../tests/README.md) to verify:

- **Import and provenance containment:** Every declaration in `trusted/lean/`
  depends only on `trusted/lean/` and the pinned Lean 4.34.1 standard library
  (`Init.*`, `Std.*`), walking types, bodies, opaque values, recursor rules,
  constructor parents, mutual blocks, projections, and literals.
- **Syntax preflight:** Rejects `unsafe`, `partial`, `axiom` (unless explicitly
  opted into `file-local-axioms` in isolated test modules), `native_decide`,
  `implemented_by`, `csimp`, `extern`, `by_elab`, `run_tac`, and top-level
  evaluation commands.
- **Axiom containment and kernel replay:** Verifies that only `{propext,
  Quot.sound, Classical.choice}` are reachable and replays `trusted/lean/`
  declarations in a fresh `base.toKernelEnv.replay`.
- **Cargo workspace DAG containment:** Verifies via `cargo metadata` that
  [`trusted/rustc-capture/`](../rustc-capture/README.md) has no dependency edges
  to workspace crates in [`crates/`](../../crates/README.md).

### 2. Per-invocation verification gate (`cargo anneal verify`)
When verifying a Rust crate, `trusted/audit/` is invoked as the final gate on
`CaptureManifest.json` and the compiled Lake `.olean` modules at
`trustLevel := 0`:

1. **Manifest and input digest verification:** Confirms `compilation_succeeded == true`
   in `CaptureManifest.json` and verifies the SHA-256 digests of all `.rs`
   sources, policy files, out-of-line `Specs/<Item>.lean` files, and generated
   `Mir/<Item>.lean` modules.
2. **Exact theorem signature check:** For every target `<item>` in
   `CaptureManifest.json`, looks up `Proof.<Item>.prove_<item>`, confirms it is
   a `.thmInfo` constant, and checks that its kernel type `ci.type` equals
   `VerificationResult ... ProjectPolicy.policy Crate.capture Mir.<Item>.claim`.
3. **Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation:** Walks
   the transitive constant closure of `ci.type` (including unfolded
   `Mir.<Item>.claim`, `Crate.capture`, and `ProjectPolicy.policy`) and rejects
   any constant originating in `theory/` (`Anneal.*`) or `Proof.<Item>`.
   `theory/` constants are permitted only inside the proof term (`ci.value?`).
4. **Zero custom axioms:** Confirms that the transitive closure of `ci.value?`
   uses only `{propext, Quot.sound, Classical.choice}` with zero `sorryAx`,
   `unsafe`, or `partial` constants.
5. **Deterministic TCB Audit Log emission:** Evaluates
   `(Mir.<Item>.claim.tcb).map (TCBEntry.render Crate.capture)` and emits the
   audit log.
