# Trusted boundary in GitHub Actions

The `Trusted boundary` job runs the production boundary gate, its 16-group
regression suite, and `cargo check --workspace` on every pull request (including
GHerrit PRs targeting another PR branch), on pushes to `main`, and on
merge-queue groups. PR retargeting triggers a new check of the updated merge
tree. There are no path filters, draft skips, or job-level conditions that could
turn a missing check into a passing skip. Obsolete runs for the same PR are
canceled.

The workflow uses the `macos-15` ARM runner and downloads the official Lean
4.34.1 release archive with a fixed SHA-256 (`trusted/lean/foundation-lock.json`
also pins the official Linux `x86_64` Lean 4.34.1 binary so local Linux checks
validate against the exact same pinned toolchain and standard library). It then
runs:

1. `python3 -B trusted/audit/check_trusted.py`:
   - Verifies that [`trusted/rustc-capture/`](../trusted/rustc-capture/README.md)
     has zero Cargo dependency edges to untrusted crates in [`crates/`](../crates/README.md),
   - Compiles and audits [`trusted/lean/`](../trusted/lean/README.md) against
     `foundation-lock.json` and the pinned Lean 4.34.1 standard library
     (`Init.*`, `Std.*`) with full `ConstantInfo` provenance checks and
     `toKernelEnv.replay`, and
   - Compiles and audits [`theory/`](../theory/README.md),
     [`examples/`](../examples/README.md), and [`tests/`](../tests/README.md),
     enforcing Statement (`ci.type`) vs. Proof (`ci.value?`) Origin Separation
     and axiom containment.
2. `python3 -B trusted/audit/check_trusted.py --self-test`:
   Runs all 16 positive and negative regression fixture groups in
   `tests/trusted-boundary/test_boundary.py`.
3. `cargo check --workspace`:
   Checks that the Rust workspace compiles cleanly.

Failed runs upload `$RUNNER_TEMP/anneal-trusted-logs/` (including raw streams,
subprocess statuses, and staged snapshots) as a seven-day workflow artifact.

## Review boundary-policy changes

Give changes to these files extra scrutiny:

- `trusted/lean/`, including `foundation-lock.json` and `lean-toolchain`;
- `trusted/audit/check_trusted.py` and `trusted/audit/TrustedBoundary.lean`;
- `trusted/rustc-capture/`;
- `tests/trusted-boundary/`; and
- `.github/workflows/trusted-boundary.yml` and this file.

A PR runs its proposed checker, policy, and workflow. Passing CI cannot by
itself justify a patch that weakens those checks.
