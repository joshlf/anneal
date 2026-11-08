# Anneal Fleet Workstream Hand-Off Document: `ws-diff-d-valid-range`

## Workstream Overview
- **Workstream ID**: `ws-diff-d-valid-range`
- **Title**: Resolve Miri-difftest Root Cause D: Typed Load Validity Check for bool
- **Objective ID**: `OBJ-1-SHRINK-UNSUPPORTED-MIR`
- **Track**: `unstable`
- **Priority**: `P0`
- **Current Node**: `cpl-black-age-5796.c.googlers.com`
- **Posted By**: `markdittmer`
- **Current State**: `MERGED_UNSTABLE`
- **Active Branch**: `ws-diff-d-valid-range` (merged into `unstable`)

## Problem & Root Cause Analysis
- **Root Cause D**: Untyped byte copies (`copy_nonoverlapping`) and raw byte stores (`*mut u8`) correctly do not check target type validity. However, typed `Operand.copy` or `Operand.move` loads MUST validate `ScalarLayout.validRange` (e.g. `0..=1` for `bool`).
- **Manifest Bug**: `ub_transmute_invalid_bool_through_ptr` (in `tests/miri-diff/manifest.toml` and `corpus/src/lib.rs:317`). Writing `3u8` through a `*mut u8` pointer cast from `&mut bool` stores an out-of-range scalar (`3`) into the `bool` local. When subsequently loading `b` as an operand, the invalid discriminant is checked against `validRange [0, 1]`, flagging undefined behavior (`.ub`).
- **Target Files**:
  - `trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Places.lean`
  - `trusted/lean/Trusted/Rustc/V2026_06_01/MirSemantics/Statements.lean`
  - `trusted/lean/Trusted/Rustc/V2026_08_01/MirSemantics/Places.lean`
  - `trusted/lean/Trusted/Rustc/V2026_08_01/MirSemantics/Statements.lean`

## Verification Summary
- **Differential Test Suite**: All 77 tests in `cargo test -p cargo-anneal --test end_to_end_miri_diff` passed in 34.82s.
- **Gate 5 TCB Audit**: `gate5_tcb_zero_contamination_and_hygiene_audit` passed in 36.98s (all 32 targets clean, zero contamination).
- **Lake Kernel Builds**: `anneal-lean-run --mode build --concurrency 3 -- lake build` in `examples/` succeeded across all 74 targets with 0 errors, 0 warnings, and 0 sorry.
- **Workspace Test Suite**: `cargo test --workspace` passed 100% cleanly across all packages including `end_to_end_pipeline` and `end_to_end_rust_only_adoption`.

## Live Wave Tracker
- [x] Workstream lease acknowledged & workspace synced from `origin/unstable` (`a60d5c84`).
- [x] Swarm initialized with title and role assignments.
- [x] `HANDOFF.md` resurrected and tracked.
- [x] Wave 1: Architectural design of typed load validity check completed.
- [x] Wave 2: Implementation landed across V2026_06_01 and V2026_08_01.
- [x] Wave 3: Verified with Lake builds and full workspace differential test suite (`cargo test --workspace`).
- [x] Wave 4: Exported delta bundle to x20, merged into `markdittmer`'s `unstable`, and pushed to x20.
