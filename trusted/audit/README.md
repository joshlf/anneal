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

## Waiver pins, claim non-vacuity, read-only staging, and base snapshots

`check_trusted.py` also embeds (as a single stdlib-only file; the section between
the `BEGIN/END SHARED WAIVER-PIN & 3-AXIS AUDITOR` banners is byte-identical to the
one in `tools/anneal-lsp/server/proof_health.py`) the `S0`-`S3` waiver auditor:

- **`waiver-pin` (exit 1):** every `anneal:` waiver (`trusted reason = "..."`,
  `allow_compile_time_guard`, `documented_intent <rationale>`,
  `pinned_compiler_coupled <reason>`, the `trusted/rustc-capture/src/spec.rs`
  grammar) in staged `trusted/lean/**/*.lean`, `trusted/rustc-capture/**/*.rs`,
  staged `DOWNSTREAM_TARGETS`, and `CaptureManifest.json` `rust_sources` /
  `Mir/<Item>.lean` targets must carry a standalone `pin:sha256:<12hex>` doc line
  whose pre-image (canonical directives + normalized item, including any Lean
  `<command> in` prefixes such as `set_option ... in` above the docstring, since
  `cmd in decl` is one command) still matches. Unpinned,
  malformed, drifted, dangling (module-doc), and unauditable (computed `#[doc]`)
  waivers fail. `python3 tools/anneal-lsp/server/proof_health.py --compute-pins FILE`
  prints the expected pins.
- **`vacuity-audit` (exit 1):** theorems carrying 3-axis metadata (`Kind:`,
  `Witness:`, `Assumes:`, `Subject:`) or an `anneal:` waiver docstring, and `Proof/`
  claim theorems (`verified`, `prove_*`), must not have syntactically contradictory
  hypotheses, trivial conclusions, tautological implications, unused subjects,
  invalid or conflicting metadata, or `S0` padding-pin tier mismatches; all theorems
  are also checked for syntactically contradictory named hypotheses (`vacuity_scope="annotated"`).
- **Read-only staging:** staged copies of `TrustedBoundary.lean`, `trusted/lean/`,
  and downstream sources are `0444` from the moment they are copied.
- **`--base-snapshot DIR` / `ANNEAL_TRUSTED_BASE_SNAPSHOT` (`base-snapshot`):**
  `DIR` mirrors checkout-relative paths of the TCB files
  (`trusted/audit/{check_trusted.py,TrustedBoundary.lean}`, `trusted/lean/` lock
  files, `lean-toolchain`, `Trusted.lean`, `Trusted/**/*.lean`,
  `trusted/rustc-capture/Cargo.toml`) and must be read-only (exit 2 otherwise). Any
  TCB file missing, added, or changed relative to it fails with exit 1 unless listed
  with `--expected-tcb-drift RELPATH`.
- **`--audit-vacuity`:** runs only the pure-Python waiver and vacuity audit over the
  checkout (no Lean process).
- **`CaptureManifest.json` paths:** relative `rust_sources` must not climb above the
  manifest root; absolute entries (rustc-capture records primary-package sources outside
  its working directory that way) are digest-checked as recorded and audited as Rust
  whatever their extension; `mir_module_path` must be a relative `.lean` path inside the
  root. Final-component symlinks are rejected for both.
- The embedded auditor never splices findings across scans here
  (`INCREMENTAL_SPLICING = False`): every staged file gets one cold, full audit.
