<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# BRIEF-0 End-to-End Reproduction Guide

*Authored by an AI agent acting on markdittmer's behalf.*

This guide reproduces the full integrated verification suite for `BRIEF-0`
(integrating `BRIEF-1` operational MIR & intrinsic semantics, `BRIEF-2` Option 1B
first-class polymorphism & trait-method dispatch, `BRIEF-3` default whole-graph
cross-crate & `core` MIR lowering with explicit `#[external_spec]` overrides, and
`BRIEF-4` rich signature obligations, symbolic proof calculus, `wireframe-demo`,
and in-place Fuchsia `usercopy` verification) from a clean shell.

## 0. Clean-Shell Environment & Branch Check

Integrated branches:
- `sup/brief-0` (worktree `<path/to/anneal>`)
- `adv/brief-0-integrated` (fast-forward alias at the same commit)
- `sup/brief-4` (worktree `<path/to/anneal>`)
- `fuchsia-wt-brief-4-3` (worktree `<path/to/anneal>`, `6c6d2dcd`)

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1
cd <path/to/anneal>
git status --porcelain
git rev-parse HEAD sup/brief-0 adv/brief-0-integrated sup/brief-4
```

Expected: empty `git status --porcelain`, and identical commit SHAs for `HEAD`,
`sup/brief-0`, `adv/brief-0-integrated`, and `sup/brief-4`.

## 1. Environment A — Anneal Trusted Boundary & Compiler Capture

```bash
cd <path/to/anneal>
(cd trusted/lean && anneal-lean-run --mode build --concurrency 2 -- lake build)
anneal-lean-run --mode build --concurrency 2 -- python3 trusted/audit/check_trusted.py
anneal-lean-run --mode build --concurrency 2 -- cargo test -p anneal-rustc-capture
./ci/check_todo.sh
```

Expected:
- `lake build` exits `0` across `Trusted.Rustc.V2026_06_01.*` and `Trusted.Rustc.V2026_08_01.*`.
- `check_trusted.py` exits `0` (`PASS: kernel dependency closure, statement-origin separation, and Cargo DAG boundary`, `0` `sorryAx` / custom axioms).
- `anneal-rustc-capture` tests exit `0` (`18 passed; 0 failed; 0 ignored`).
- `./ci/check_todo.sh` exits `0`.

## 2. Environment B — Anneal Theory, Correspondence & Differential Harnesses

```bash
cd <path/to/anneal>
(cd theory && anneal-lean-run --mode build --concurrency 2 -- lake build)
(cd examples && anneal-lean-run --mode build --concurrency 2 -- lake build Trusted Anneal Correspondence Smoke ToyYDiagram ToyMachine ToyCFG MirVerification)
(cd examples && anneal-lean-run --mode file --concurrency 2 -- lake env lean -DwarningAsError=true ../tests/mir/SymbolicEvalTests.lean)
(cd examples && anneal-lean-run --mode file --concurrency 2 -- lake env lean -DwarningAsError=true ../tests/mir/FunctionalTranslationTests.lean)
(cd examples && anneal-lean-run --mode file --concurrency 2 -- lake env lean -DwarningAsError=true ../tests/mir/FunctionalTranslationEquivTests.lean)
anneal-lean-run --mode build --concurrency 2 -- cargo test --test end_to_end_miri_diff -p cargo-anneal
anneal-lean-run --mode build --concurrency 2 -- cargo test --workspace
```

Expected:
- All Lean builds and MIR test suites exit `0` with `0` warnings or errors.
- `end_to_end_miri_diff` exits `0` (`77/77`: `32` verified pass, `9` verified panic, `30` verified strict UB, `6` ratcheted known bugs, `42` kernel-audited certificate modules).
- `cargo test --workspace` exits `0` across all unit, integration, and doc tests with `0 failed` and `0 ignored`.

## 3. Environment C — End-to-End Polymorphic & Cross-Crate / `core` Verification

```bash
cd <path/to/anneal>
anneal-lean-run --mode build --concurrency 2 -- cargo test -p cargo-anneal --lib -- driver::tests::multi_crate_transitive_callees_and_external_spec_override_end_to_end --exact --nocapture
anneal-lean-run --mode build --concurrency 2 -- cargo test --test end_to_end_demo_journeys -p cargo-anneal
```

Expected:
- Both commands exit `0`, stepping through polymorphic `core::slice::*` / cross-crate `defaultCallees`, abstracting `#[external_spec]` overrides, and verifying `examples/wireframe-demo` end-to-end.

## 4. Environment D — Fuchsia `usercopy` In-Place Verification Pilot

```bash
cd <path/to/anneal>
export PATH="$(pwd)/target/debug:$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
anneal-lean-run --mode build --concurrency 2 -- cargo build -p cargo-anneal -p anneal-rustc-capture
anneal-lean-run --mode build --concurrency 2 -- cargo run --manifest-path Cargo.toml -p cargo-anneal -- \
  agent-verify --manifest-path <path/to/anneal>/examples/fuchsia-usercopy/Cargo.toml
```

Expected:
- Exits `0` with `Totals: 8 unconditional, 0 conditional, 1 ub_exception` and `TrustedBoundary kernel replay: PASS` (`0 sorryAx`).
