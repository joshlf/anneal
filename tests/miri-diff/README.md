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
   - **`panic` after an external call
     (`ModularVerificationResult ∧ ¬ TotalClaim.holds`)**: A test whose MIR
     calls a function that `corpus/` does not capture before it panics (such
     as `panic_explicit_macro`, whose `panic!("...")` calls
     `core::fmt::Arguments::<'a>::from_str` before
     `core::panicking::panic_fmt`) is proved via
     `verifyModularSafePanicMirBounded`. Its `StatefulClaim` is false, because
     the claim lets the external call return a memory with a corrupted call
     frame on which the caller can fault. The certificate instead assumes only
     that every external call returns or unwinds to the caller's call frame
     (`callFramePreserved`), or aborts, and certifies that under that
     assumption execution never faults and never returns normally. The
     statement spells out that frame-preserving contract with `Trusted.*`
     constants only.
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

The corpus holds 108 tests: 50 `pass`, 12 `panic` (11 certified via
`verifySafePanicMirPointBounded` and `panic_explicit_macro` via
`verifyModularSafePanicMirBounded`), and 46 `ub`, grouped into nine categories
that `// Category N` comments in [`corpus/src/lib.rs`](corpus/src/lib.rs) mark.
Anneal agrees with Miri on all 108 tests: `manifest.toml` records no open
`known_anneal_bug` entry.
Category 8 adds 12 tests covering layout-sensitive types and raw-pointer retags
(`pass_option_some_niche_and_single_c_mut` exercises both niche encoding and
`&mut SingleC` projection/reinit):

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

Category 9 adds 19 tests covering `Operand::Move` deinitialization, reference
arguments across `#[inline(never)]` multi-callee chains, and inline scalar and
memory intrinsics:

| Theme | Tests |
| :--- | :--- |
| `Operand::Move` vs. explicit assignment | `pass_move_deinit_preserves_reserved_child`, `pass_move_deinit_subplace_preserves_sibling_frozen`, `ub_move_deinit_read_source_uninit`, `ub_assign_after_reborrow_disables_child` |
| Reference arguments, reborrow return, and unwinding across call chains | `pass_fn_entry_protector_two_stage_reborrow_chain`, `pass_fn_entry_shared_reborrow_chain`, `pass_fn_entry_returns_reborrowed_child`, `ub_frozen_reborrow_write_in_callee_frame`, `panic_multi_callee_unwind_chain`, `panic_multi_callee_unwind_cleanup_guard` (`UnwindAction::Cleanup`) |
| Scalar intrinsics | `pass_intrinsics_bit_count_and_reverse`, `pass_intrinsics_saturating_and_wrapping`, `pass_intrinsics_three_way_compare_and_exact_div`, `ub_ctlz_nonzero_zero`, `ub_cttz_nonzero_zero`, `ub_exact_div_non_exact_u32`, `ub_exact_div_signed_min_overflow_i8` |
| Memory intrinsics | `pass_intrinsics_write_bytes_copy_and_arith_offset` (`write_bytes!` emulation: `core::intrinsics::write_bytes` is not interpreted inline), `ub_copy_nonoverlapping_partial_overlap_array` |

### Category 9 engine gaps

Category 9 leaves out the following constructs, on which Anneal currently
disagrees with Miri. `ep1_category9_templates_engine_gap_pins_and_witness_polarity_verify_live`
in [`miri_difftest_oracle.rs`](../../crates/anneal-difftest/tests/miri_difftest_oracle.rs)
pins each one, kernel-confirmed, with its exact Miri and Anneal outcomes.
`miri-difftest` mutators avoid them all: no Category 9 helper or template
accesses memory through a pointer into its caller's frame, so the call-chain
tests check reference passing, reborrow return, frame cleanup, and unwinding,
but not Anneal's `FnEntry` protector enforcement.

**Frame-relative pointer resolution.** A borrow entry's `targetLocal` is a
local index into the *running* frame (`get? locals entry.targetLocal`, falling
back to `memory.callerLocals`, which `pushCalleeFrame` never populates). Inside
a callee, a reference or raw pointer to the caller's local `_k` therefore
resolves to the callee's own local `_k`:

- Silent wrong values (`wrong_value`, `value_mismatch`): when the caller's `x`
  and a `u32` parameter `pad2` of the callee are both local `_3`, a callee read
  through a raw pointer to `x` returns `pad2` (Anneal `200`, Miri `10`), and a
  callee write through it lands in `pad2` and leaves `x` unchanged (Anneal `13`,
  Miri `11`).
- False UB (`false_positive_ub`): a callee dereferencing a reference argument
  (`fn f(r: &u32, bonus: u32) -> u32 { *r + bonus }` called as `f(&x, 1)`, with
  `x` and `r` both local `_1`) reads its own 8-byte `r` as a `u32` and faults.
  A callee writing through `raw = &raw mut x` while the caller holds an unused
  shared borrow of `x` (`let _r = &x; f(raw)`) faults at `*alias = 7` because
  `evalRvalueRawPtr` mints a separate root `BorrowEntry` (`tag = 1`,
  `parentTag = .none`, `perm = .active`) for `raw`, and `Retag([default] _r)` on
  the sibling root borrow `_r` (`tag = 2`, `parentTag = .none`) runs
  `freezeTreeBorrowsOnReadAtProj` with `readerTag = .some 2`, which treats the
  initial read of `_r` as a foreign read to `raw` and freezes `raw.perm` to
  `.frozen` before the call; without `let _r = &x`, `raw.perm` stays `.active`
  and the write instead overwrites `alias` in the callee frame (`wrong_value`,
  Anneal `13`, Miri `10`). Both pass in Miri.
- Missed UB (`missed_ub`, `unsound_missed_fault`): Miri reports a
  `RetagKind::FnEntry` protector violation when a callee writes through `raw`
  while `&*raw` (or `&mut *raw`) is one of its arguments. In Anneal the write
  lands in the callee's local with `x`'s index (the pin pads the callee so that
  local is a `u32`), never reaching `x` or its borrow tree; the MIR capture
  also emits no `Retag(FnEntry)`, so no protector would exist anyway. When the
  colliding local is instead an 8-byte reference whose `ScalarLayout` has
  `validRange.end_ = u64::MAX`, the 4-byte write sends the Lean kernel's
  `by rfl` confirmation into byte-level re-decoding, which exhausts memory.
  Passing `&x` or `&mut x` directly agrees with Miri (both report UB at the
  write), but only because of the false-UB item above, not because of a
  protector.

**Other gaps.**

- A write to `x` through `raw = &raw mut x` in the caller after a callee that
  received `&x` has returned: Miri passes (the protector is released on
  return), and Anneal reports UB at the write by the same sibling-root
  `freezeTreeBorrowsOnReadAtProj` mechanism (creating and retag-reading the
  call argument `&x` freezes `raw`'s sibling root `BorrowEntry` to `.frozen`
  before the call begins). This gap does not depend on local-index collisions:
  it reproduces with a callee whose only locals are `_0` and `_r`.
- A raw-pointer read of a moved-from local that is still in scope: Miri passes
  (it evaluates `Operand::Move` like `Operand::Copy`), and Anneal reports UB
  because it de-initializes the moved-from place.

`miri-difftest` confirms each divergence in the Lean kernel with
`lean -M 4096`. When the batched confirmation fails, every divergence is
re-confirmed on its own: an item that exhausts a resource (`-M`, heartbeats,
recursion depth, the stack, or a signal) is reported with
`kernel_confirmed = false`, and any other failure (a theorem the kernel
rejects, or an elaboration error) still aborts the run.

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
   toward zero. Because `evalMirDiffTagBounded` stops at the first external
   call, the ratchet of a `panic` test also asserts
   `reachesModularSafePanicBounded ... = false`, so it fails to compile as soon
   as `verifyModularSafePanicMirBounded` can certify the test. Also,
   `parse_miri_diff_manifest` rejects any `known_anneal_bug` whose
   `observed_anneal_tag` already matches `miri_verdict` (or whose
   `ub_location_mismatch` `observed_anneal_ub_span` already contains
   `miri_ub_span`).

### Summary of Open Anneal Bugs Exposed by the Suite

The suite currently exposes no open Anneal bug: all 108 tests agree with Miri.

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
