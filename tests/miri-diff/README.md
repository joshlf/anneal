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
     returns the exact scalar or unit value produced by Miri. A test whose MIR
     calls other functions captured from `corpus/` (such as
     `pass_direct_fn_call` calling `helper_add_ten`) is instead proved via
     `verifyTotalMirBounded` with those captured bodies linked as the claim's
     `callees`.
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

Every theorem and probe generated for a test links the same callee table: the
`defaultCallees` list that scaffolding records for the test's item, which holds
only bodies captured from `corpus/`. A call to any other function remains an
uninterpreted external call.

## Corpus Coverage

The corpus holds 89 tests: 41 `pass`, 10 `panic` (including the tracked
`panic_explicit_macro` bug), and 38 `ub`, grouped into eight categories that
`// Category N` comments in [`corpus/src/lib.rs`](corpus/src/lib.rs) mark.
Category 8 covers layout-sensitive types and raw-pointer retags:

| Theme | Tests |
| :--- | :--- |
| Niche-encoded scalars and `#[repr(transparent)]` wrappers | `pass_nonzero_u32_transmute_roundtrip`, `ub_nonzero_u32_transmute_zero`, `pass_option_nonzero_none_niche`, `pass_transparent_wrapper_transmute`, `ub_transparent_nonzero_wrapper_zero`, `pass_option_some_niche_and_single_c_mut` |
| Univariant `#[repr(C)]` enums | `pass_single_c_enum_match_reinit`, `ub_single_c_enum_invalid_tag`, `pass_option_some_niche_and_single_c_mut` |
| Union overlays and uninitialized bytes | `pass_union_overlay_word_bytes`, `ub_union_uninit_bytes_partial_read` |
| `Retag(Raw)` (`&raw const` / `&raw mut`) interleavings | `pass_raw_ref_disjoint_fields`, `ub_raw_mut_after_parent_write` |

Category 8 leaves out constructs on which Anneal currently disagrees with
Miri. The negative controls in
[`miri_difftest_oracle.rs`](../../crates/anneal-difftest/tests/miri_difftest_oracle.rs)
pin each of these divergences, and `miri-difftest` mutators avoid them:

- `transmute` producing a valid nonzero (`Some`) `Option<NonZeroU32>`, or a
  valid `Option<bool>` or `Option<ColorTag>`: Anneal reports UB where Miri
  passes. Only the all-zero `None` of `Option<NonZeroU32>` decodes.
- `transmute` producing a univariant `#[repr(C)]` enum whose `ScalarPair`
  payload violates a niche `valid_range` (such as `SingleCNonZero::Only` with
  valid tag `0` and invalid `NonZeroU32` payload `0`): Miri reports UB at the
  `transmute`, and Anneal passes (`missed_ub`).
- Writing zero into a `NonZeroU32` through a `*mut u32` and then copying it:
  Miri reports UB at the copy, and Anneal passes.
- Writing into a `SingleC` through a `*mut u32` or `*mut [u32; 2]`: Anneal
  reports UB at the write, even for a valid payload. Miri passes, or for an
  invalid tag reports UB at the next copy.
- Writing field `f` through a `&mut *m` reborrow created after
  `&raw mut (*m).f`, then writing through that raw pointer: Miri passes,
  because Tree Borrows lets the raw pointer keep `m`'s tag, but Anneal reports
  UB at the raw write. A raw pointer to the whole place, `&raw mut *m`, agrees.

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
| Incompleteness (unmodeled intrinsic / call) | `MirSemantics.Terminators` | `panic_explicit_macro` | `panic!("...")` first calls `core::fmt::Arguments::<'a>::from_str`, which `Trusted` does not model and the corpus does not capture, so evaluation stops at that external call before reaching `core::panicking::panic_fmt`. |

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
