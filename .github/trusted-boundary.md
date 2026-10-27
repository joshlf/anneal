<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Trusted boundary in GitHub Actions

The `Trusted boundary` job runs the production boundary gate, its 12-group
regression suite, and `cargo test --workspace --locked` on every pull request
(including GHerrit PRs targeting another PR branch), on pushes to `main`, and on
merge-queue groups. PR retargeting triggers a new check of the updated merge
tree. There are no path filters, draft skips, or job-level conditions that could
turn a missing check into a passing skip. Obsolete runs for the same PR are
canceled.

The workflow uses the Nix-packaged Anneal toolchain (which pins the official
Lean 4.34.1 release and `trusted/lean/foundation-lock.json` across Linux
`x86_64` and macOS `aarch64`) and runs:

1. `cargo run --locked -p cargo-anneal -- audit-repo`:
   - Verifies that every Cargo workspace member in `Cargo.toml` resides under
     [`trusted/`](../trusted/README.md) and has zero path dependencies outside
     `trusted/`,
   - Compiles and audits [`trusted/lean/`](../trusted/lean/README.md) against
     `foundation-lock.json` with full `ConstantInfo` provenance checks,
     `@[vetted]` vs. `@[candidate <feature>]` non-contamination checks, and
     `toKernelEnv.replay`, and
   - Compiles and audits [`theory/`](../theory/README.md),
     [`examples/`](../examples/README.md), and [`tests/`](../tests/README.md),
     enforcing pure syntax preflight, Statement (`ci.type`) vs. Proof
     (`ci.value?`) Origin Separation, axiom containment, and kernel replay.
2. `cargo run --locked -p cargo-anneal -- audit-self-test`:
   Runs all 12 positive and negative regression fixture groups in
   [`trusted/cargo-anneal/src/self_test.rs`](../trusted/cargo-anneal/README.md).
3. `cargo test --workspace --locked` and
   `cargo publish --dry-run -p cargo-anneal`:
   Compiles and tests the Rust workspace, including the end-to-end
   `cargo-anneal verify` integration suite against the pinned Lean 4.34.1
   kernel.

## Review boundary-policy changes

Give changes to these files extra scrutiny:

- `trusted/lean/`, including `foundation-lock.json` and `lean-toolchain`;
- `trusted/audit/TrustedBoundary.lean`;
- `trusted/cargo-anneal/`;
- `trusted/rustc-capture/`;
- `tests/trusted-boundary/`; and
- `.github/workflows/ci.yml` and this file.

A PR runs its proposed checker, policy, and workflow. Passing CI cannot by
itself justify a patch that weakens those checks.
