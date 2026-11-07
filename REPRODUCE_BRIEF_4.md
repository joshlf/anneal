<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# BRIEF-4 Reproduction Guide

This document provides exact, copy-pasteable commands to reproduce and verify
Workstream 4 (`BRIEF-4`, integrating `BRIEF-4.1`, `BRIEF-4.2`, and `BRIEF-4.3`
along with `BRIEF-1`, `BRIEF-2`, `BRIEF-3`, and `unstable`) in
`/usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4` on branch
`sup/brief-4`.

## 1. Environment Setup

```bash
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4
git status --porcelain
git log --oneline -15
```

## 2. Lean 4 Trusted Verification Surface, `MirSemantics`, & Theory Libraries

Build `Trusted`, `Anneal`, `Correspondence`, `Smoke`, `ToyYDiagram`,
`ToyMachine`, `ToyCFG`, and `MirVerification`:

```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4/examples
anneal-lean-run --mode build --concurrency 2 -- lake build Trusted Anneal Correspondence Smoke ToyYDiagram ToyMachine ToyCFG MirVerification
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4
```

## 3. Symbolic Evaluator, Functional Translation, & Tactic Automation

Verify single-pass CPS symbolic execution (`wpMirSym`,
`wpMirFrameAndTraitsModularSym`, `verifyPolyMirNoPanicSym`,
`verifyPolyExternalSpecWithCalleesMirSym`,
`linkVerifiedPolyContractMirCalleeWithCalleesSym`, `evalPtrOffsetBinOpSymTree`),
functional translation (`translateFuncWithFuel`), and `O(1)` lookup context
witnesses (`BlockCtx`, `CalleeCtx`):

```bash
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4/examples
anneal-lean-run --mode file --concurrency 2 -- lake env lean -DwarningAsError=true ../tests/mir/SymbolicEvalTests.lean
anneal-lean-run --mode file --concurrency 2 -- lake env lean -DwarningAsError=true ../tests/mir/FunctionalTranslationTests.lean
anneal-lean-run --mode file --concurrency 2 -- lake env lean -DwarningAsError=true ../tests/mir/FunctionalTranslationEquivTests.lean
cd /usr/local/google/Projects/anneal-workspace/anneal-wt-brief-4
```

## 4. Scaffolded Proof Emission & End-to-End Multi-Crate / `core` Verification

Verify scaffolded Lean 4 spec and proof generation
(`crates/cargo-anneal/src/scaffold.rs`), transitive `defaultCallees` and
`defaultSpecCallees` population, `#[external_spec]` override emission, Miri
differential testing (`tests/miri-diff/manifest.toml`), and end-to-end
multi-crate and Lean 4 kernel verification (`crates/cargo-anneal/src/driver.rs`
and `examples/wireframe-demo`):

```bash
anneal-lean-run --mode build --concurrency 2 -- cargo test -p cargo-anneal --lib
anneal-lean-run --mode build --concurrency 2 -- cargo test -p cargo-anneal --lib -- driver::tests::multi_crate_transitive_callees_and_external_spec_override_end_to_end --exact --nocapture
anneal-lean-run --mode build --concurrency 2 -- cargo test --workspace
```

## 5. Trusted Boundary & Repository Hygiene Gates

```bash
anneal-lean-run --mode build --concurrency 2 -- python3 trusted/audit/check_trusted.py
./ci/check_todo.sh
```
