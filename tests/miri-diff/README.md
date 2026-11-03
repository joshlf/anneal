# Anneal <-> Miri Differential Testing Suite

`tests/miri-diff/` checks Anneal's MIR-in-Lean operational semantics
(`Trusted.Rustc.V2026_06_01.MirSemantics`) against upstream Miri at the pinned
compiler commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
(`rustc 1.98.0-nightly (14210df0e 2026-05-31)`).

## Architecture & Verdict Alignment

Every test in [`corpus/src/lib.rs`](corpus/src/lib.rs) is a self-contained,
`#![no_std]`, zero-argument function harvested from upstream Miri's `tests/pass/`,
`tests/panic/`, and `tests/fail/` suites. Each test entry in
[`manifest.toml`](manifest.toml) is evaluated under two engines:

1. **Upstream Miri Oracle (`miri -Zmiri-tree-borrows`)**:
   Executed via [`corpus/examples/miri_eval.rs`](corpus/examples/miri_eval.rs)
   and [`sync_miri_suite.py`](sync_miri_suite.py), recording the reference
   verdict (`pass:unit`, `pass:scalar:<bits>:<sizeBytes>`, `panic`, or `ub`)
   and, for every `ub` test, the fault source position (`miri_ub_span`).
2. **Anneal MIR-in-Lean Kernel Verification (`cargo_anneal::miri_diff`)**:
   Captures `Runtime(PostCleanup)` MIR from `corpus/` using Miri-matching
   compiler flags (`-Zmir-opt-level=0 -C debug-assertions=off -C overflow-checks=on`)
   and generates Lean 4 proof and refutation obligations in
   `Anneal.Rustc.V2026_06_01.SymbolicEval`:
   - **`pass` (`TotalVerificationResult`)**: Proved via
     `verifyTotalMirUnitPointBounded` or `verifyTotalMirScalarPointBounded`,
     certifying that execution terminates normally without UB or panic and
     returns the exact scalar or unit value produced by Miri.
   - **`panic` (`StatefulVerificationResult ∧ ¬ TotalClaim.holds`)**: Proved
     via `verifySafePanicMirPointBounded`, certifying that execution unwinds
     cleanly via `MirOutcome.panic` without exhibiting Undefined Behavior
     while refuting total normal termination.
   - **`ub` (`¬ StatefulClaim.holds ∧ ¬ TotalClaim.holds`)**: Proved via
     `refuteMirPointByStrictUB`, which requires
     `reachesStrictUBBounded = true` (`MirOutcome.fault .ub`), and checked
     via `MiriOracleProbe.lean` (`probeMirDiffExecBounded`) to ensure Anneal's
     active MIR statement span contains `miri_ub_span`. Neither
     `FailureKind.unsupported` nor `FailureKind.outOfFuel` satisfies
     `reachesStrictUBBounded`, preventing model gaps from masquerading as UB
     detections.

All generated modules and their whole-crate rollup (`CrateVerify`) are checked
by `trusted/audit/TrustedBoundary.lean` in `verify-audit` mode (enforcing
statement-origin isolation, zero `sorryAx`, zero unapproved axioms, and full
Lean 4 kernel replay at `trustLevel := 0`).

## Policy on `known_anneal_bug` Entries

> **Every `[tests.known_anneal_bug]` block in [`manifest.toml`](manifest.toml)
> documents an unfixed bug in Anneal's MIR-in-Lean semantics or MIR capture
> pipeline — never a "disagreement we have decided to admit permanently."**

`known_anneal_bug` entries act strictly as a two-way regression ratchet:

1. **No silent regressions**: Any test without a `known_anneal_bug` block must
   agree 100% between Miri and Anneal (including UB fault source location).
2. **Automatic ratchet on bug fixes**: For every test with a `known_anneal_bug`
   block, `cargo_anneal::miri_diff` emits a `known_anneal_bug_ratchet` theorem
   asserting that `evalMirDiffTagBounded` (or `probeMirDiffExecBounded` when
   `observed_anneal_ub_span` is recorded) equals the exact current
   `observed_anneal_tag` (and `observed_anneal_ub_span`) (`by rfl`). As soon as
   an Anneal bug is fixed so that Anneal agrees with Miri,
   `known_anneal_bug_ratchet` fails to compile until the `known_anneal_bug`
   block is deleted from `manifest.toml`, ratcheting the open bug count down
   toward zero. Also, `parse_miri_diff_manifest` rejects any `known_anneal_bug`
   whose `observed_anneal_tag` already matches `miri_verdict` (or whose
   `ub_location_mismatch` `observed_anneal_ub_span` already contains
   `miri_ub_span`).

### Summary of Open Anneal Bugs Exposed by the Suite

| Bug Class | Suspected Component | Affected Corpus Tests | Root Cause |
| :--- | :--- | :--- | :--- |
| Soundness (false negative on UB) | `MirSemantics.Places` / `Operands` | `ub_ptr_offset_oob_read`, `ub_ptr_offset_oob_write`, `ub_ptr_offset_negative_before_start`, `ub_unaligned_ptr_read_u32` | `BinOp.offset` updates `ProvenancePtr.offsetBytes` without checking allocation bounds or negative wrapping, and `readPlace`/`writePlaceValue` ignore `ptr.offsetBytes` and pointer alignment. |
| Soundness (false negative on UB) | `MirSemantics.Places` | `ub_transmute_invalid_bool_through_ptr` | Writing `3u8` through `*mut u8` cast from `&mut bool` stores an out-of-range scalar into the `bool` local without re-checking `[0, 1]` validity on write or subsequent read. |
| Completeness (wrong return value) | `MirSemantics.Places` | `pass_ptr_offset_within_array` | `readPlace` ignores `ProvenancePtr.offsetBytes` after `BinOp.offset`, reading field 0 instead of field 1. |
| Completeness (false-positive UB) | `MirSemantics.Places` | `pass_copy_nonoverlapping_uninit_bytes_to_uninit` | Union storage for `Uninit<[u8; 4]>` is represented as a 1-field `.unit` aggregate rather than union byte storage, causing `copy_nonoverlapping` on union fields to fault with `.ub`. |
| Completeness (false-positive UB) | `MirSemantics.Memory` | `pass_tb_unsafe_cell_shared_mutation` | `BorrowKind.shared` unconditionally assigns Tree Borrows `Permission.frozen` without checking for `UnsafeCell` (`!Freeze` interior mutability). |
| Completeness (false-positive UB) | `MirSemantics.Places` | `tb_child_write_then_parent_read`, `tb_child_write_then_parent_write`, `safe_reborrow_then_parent_write` | `updateBorrowPerm` disables every other borrow on write (including ancestors), causing subsequent legal parent reads or writes to fault with `.ub`. |
| UB location mismatch (faults early) | `MirSemantics.Places` | `ub_tb_use_frozen_mut_after_parent_read`, `ub_tb_conflicting_active_mut_borrows` | Because `updateBorrowPerm` disables ancestor tags when a child writes, Anneal faults one statement early on the legal parent access instead of faulting on the subsequent illegal child access as Miri does. |
| Incompleteness (unmodeled intrinsic / call) | `MirSemantics.Terminators` / `Memory` | `pass_exact_div_valid`, `ub_exact_div_non_multiple`, `pass_direct_fn_call`, `panic_explicit_macro` | `core::intrinsics::exact_div` and `core::panicking::panic_fmt` are not yet interpreted in `evalCallTerminator`, and `initMachineState` leaves `Memory.callees` empty by default. |

## Running the Suite

Run the hermetic Lean 4 differential verification and `TrustedBoundary` audit:

```bash
cargo test -p cargo-anneal --test end_to_end_miri_diff --locked
```

Validate `manifest.toml` against `corpus/`, an optional public checkout of
upstream Miri (`https://github.com/rust-lang/rust` `src/tools/miri/tests` or
`https://github.com/rust-lang/miri` `tests` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), and the live `miri` oracle:

```bash
python3 tests/miri-diff/sync_miri_suite.py \
  --miri-tests-dir /path/to/miri/tests \
  --eval-miri
```
