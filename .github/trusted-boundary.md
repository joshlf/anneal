# Trusted boundary in GitHub Actions

The `Trusted boundary` job runs the production boundary gate, its 14-group
regression suite, and `cargo test --workspace --locked` on every pull request
(including GHerrit PRs targeting another PR branch), on pushes to `main`, and on
merge-queue groups. PR retargeting triggers a new check of the updated merge
tree. There are no path filters, draft skips, or job-level conditions that could
turn a missing check into a passing skip. Obsolete runs for the same PR are
canceled.

The workflow uses the `macos-15` ARM runner and downloads the official Lean
4.34.1 release archive with a fixed SHA-256 (`trusted/lean/foundation-lock.json`
also pins the official Linux `x86_64` Lean 4.34.1 binary so local Linux checks
validate the exact same 30 foundation artifact parts). It then runs:

1. `cargo run --locked -p cargo-anneal -- audit-repo`:
   - Verifies that every Cargo workspace member in `Cargo.toml` resides under
     [`trusted/`](../trusted/README.md) and has zero path dependencies outside
     `trusted/`,
   - Compiles and audits [`trusted/lean/`](../trusted/lean/README.md) against
     `foundation-lock.json` with full `ConstantInfo` provenance checks and
     `toKernelEnv.replay`, and
   - Compiles and audits [`theory/`](../theory/README.md),
     [`examples/`](../examples/README.md), and [`tests/`](../tests/README.md),
     enforcing pure syntax preflight, Statement (`ci.type`) vs. Proof
     (`ci.value?`) Origin Separation, axiom containment, and kernel replay.
2. `cargo run --locked -p cargo-anneal -- audit-self-test`:
   Runs all 14 positive and negative regression fixture groups in
   [`trusted/cargo-anneal/src/self_test.rs`](../trusted/cargo-anneal/README.md).
3. `cargo check --workspace --locked`:
   Checks that the Rust workspace compiles cleanly.

Failed runs upload `$RUNNER_TEMP/anneal-trusted-logs/` (including raw streams,
subprocess statuses, and staged snapshots) as a seven-day workflow artifact.

## Review boundary-policy changes

Give changes to these files extra scrutiny:

- `trusted/lean/`, including `foundation-lock.json` and `lean-toolchain`;
- `trusted/audit/TrustedBoundary.lean`;
- `trusted/cargo-anneal/`;
- `trusted/rustc-capture/`;
- `tests/trusted-boundary/`; and
- `.github/workflows/trusted-boundary.yml` and this file.

A PR runs its proposed checker, policy, and workflow. Passing CI cannot by
itself justify a patch that weakens those checks.
