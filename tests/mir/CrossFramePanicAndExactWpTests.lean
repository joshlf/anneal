/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Anneal.ExactWpAndSmartCtors
import LeanMiriSpec.CrossFrameRefAndPanicLM
import LeanMiriSpec.ExactWpAndMemoryFrameLM

/-!
# Episode 2 Cross-Frame Panic & ExactWP End-to-End Tests and Cross-Root 3-Way Kernel Closure

Elaborated with `lake --dir examples env lean -DwarningAsError=true`, whose `LEAN_PATH` holds
`examples/.lake/build/lib/lean` (containing `Anneal.ExactWpAndSmartCtors`,
`LeanMiriSpec.CrossFrameRefAndPanicLM`, and `LeanMiriSpec.ExactWpAndMemoryFrameLM`). The root-package
modules (`Anneal.Mir.CrossFrameRefAndPanicDualSpec`, `MiniRustSpec.CrossFrameRefAndPanicMR`,
`Anneal.ExactWpAndSmartCtors`, `Trusted.*`) are loaded alongside `examples/.lake/build/lib/lean`
into a fresh kernel environment via `Lean.importModules` in §2.

1. **§1. Top-Level End-to-End Positive & Negative Witnesses**:
   - **§1a (`CrossFrameRefAndPanicLM`)**: cross-frame `&mut`/`&` calls, pointer `.cast`/`.offset`/
     `.wrapping_offset`, `FnEntry` strong protector UB vs. post-release success, `Frozen` `&T` write
     UB, dead-local UAR & OOB pointer arithmetic UB, `Assert` pass/fail, 4-way `UnwindAction`
     (`.cleanup`, `.continue_`, `.terminate`, `.unreachable`), 2-frame & 3-frame LIFO protector
     release with cleanup recovery, premature-parent-write UB contrast, root-frame unwind UB vs.
     catch-harness reconciliation, and out-of-range fail-closedness.
   - **§1b (`ExactWpAndMemoryFrameLM`)**: whole-body `Miri.Interpreter.Step.step` `ExactWP` safety VC
     discharge AND bidirectional `↔` UB/abort refutation on `translateBody`-lowered `CapturedMir`
     bodies, universal + concrete little-endian vs. big-endian disjoint `writeScalar`/`readScalar`/
     `writeUninit`/`writeBytes`/`copy` framing via `LeanMiriSpec.MemoryLemmas`, and multi-segment
     `TreeBorrowsWP` & `ProtectorReleaseWP` committed-prefix error states.
   - **§1c (`ExactWpAndSmartCtors`)**: `Bitprism` nested `O(1)` smart-constructor collapse vs. raw
     AST + `*_eq_raw`, negative UB non-erasure refutations (`0 & dead`, `0 & uninit`, `uninit * 0`,
     `addUnchecked` overflow), coalescing `mkMemWriteFrame` + dead-slot failure preservation,
     exhaustive 14-field `Memory` / 17-field `MachineState` `veil_frame` framing + downstream
     `anneal_veil_frame` tactic discharge, and bidirectional `AnnealExactWP` negation refutation.
2. **§2. Cross-Root 3-Way Kernel Closure (`run_cmd`)**:
   - Genuine `LmCrossFramePanicObs.rec.{1}` translation (zero mocks) closing
     `CrossFramePanicLmAuthority`, `CrossFramePanicDualContract`, `mkCrossFramePanicDualBundle`,
     and `ep1_cross_frame_ref_and_panic_dual_authority_capstone` with REAL
     `LeanMiriSpec.CrossFrameRefAndPanicLM.lmCrossFramePanicObserve` (transported along
     `lmCrossFramePanicObserveU.eq_src` + `lmCrossFramePanicObserve_out_of_range`).
   - Universal choice-free 3-way Tree Borrows permission bijection (`TreeBorrowPerm ↔
     Miri.TreeBorrows.Permission`) matching `preventsDeallocation` = MiniRust `prevents_deallocation`
     = vendored protected foreign write `Miri.TreeBorrows.performAccess`.
   - Closed **Master 6-Module Workstream Capstone** uniting Episode 1 + Episode 2 across all 6
     workstream modules.
   - **30 kernel-rejected negative forgery controls** (all boolean controls verified two-sided:
     `accepts (= false)` AND `rejects (= true)`; all value/Prop controls paired with accepted
     baselines), covering Ep1 observer/translator/mode/divergence/codec forgeries, permission-swap
     forgeries, Ep2 unsound `ExactWP` postconditions & cleanup-state erasure on error, clobbered
     `veil_frame` field overlaps, `Bitprism` uninit/dead-local erasure claims across `bitAnd`/
     `bitOr`/`mul`, Tree Borrows / `releaseProtector` committed-prefix forgeries, and LE/BE endian
     confusion.
   - Transitive import-isolation audit of `Anneal.ExactWpAndSmartCtors` (ZERO `Std.Do.*`,
     `Std.Tactic.Do.*`, `Std.WP.*`, `Lean.*`, `Miri.*`, `LeanMiriSpec.*`, `MiniRustSpec.*`),
     choice-free constructive audits, transitive constant reachability (`reachFrom`) across all
     6 modules, standard-3-axiom purity (`{propext, Classical.choice, Quot.sound}`), and auditor
     self-tests.
3. **§3. Test-Module Axiom Audit (`run_cmd`)**.
-/

namespace Anneal.Mir.CrossFramePanicAndExactWpTests

set_option Elab.async false

open Anneal.ExactWpAndSmartCtors
open LeanMiriSpec.CrossFrameRefAndPanicLM
open LeanMiriSpec.ExactWpAndMemoryFrameLM
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## §1. Top-Level End-to-End Positive & Negative Witnesses -/

/-! ### §1a. `CrossFrameRefAndPanicLM` End-to-End Positive & Negative Witnesses -/

/-- Read one cell out of a `List.range lmCanonicalCaseCount` (`28`) table equation. -/
theorem lm_ep1_cell {α : Type} {f : Nat → α} {l : List α}
    (h : (List.range lmCanonicalCaseCount).map f = l) (i : Nat) (hi : i < lmCanonicalCaseCount) :
    some (f i) = l[i]? := by
  subst h
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Direct cell accessor for the `treeBorrows = false` table (`0..27`). -/
theorem lm_ep1_basic (i : Nat) (hi : i < lmCanonicalCaseCount) :
    some (lmCrossFramePanicObserve false i) = lmExpectedBasicList[i]? :=
  lm_ep1_cell lmCrossFramePanicObserve_table.1 i hi

/-- Direct cell accessor for the `treeBorrows = true` table (`0..27`). -/
theorem lm_ep1_tb (i : Nat) (hi : i < lmCanonicalCaseCount) :
    some (lmCrossFramePanicObserve true i) = lmExpectedTbList[i]? :=
  lm_ep1_cell lmCrossFramePanicObserve_table.2 i hi

/-- Positive: cross-frame `&mut`/`&` calls (`0, 2, 7`), callee `.as_mut_ptr`/`.cast` (`1`),
in-bounds `BinOp.offset` (`3`), wrapping `arith_offset` in-bounds & OOB-without-deref round-trips
(`4, 5`), and post-return caller write after `FnEntry` protector release (`6`), in BOTH modes. -/
theorem lm_ep1_cross_frame_refs_and_ptr_arith_positive (tb : Bool) :
    lmCrossFramePanicObserve tb 0 = .okVal 42 42 ∧
    lmCrossFramePanicObserve tb 1 = .okVal 77 77 ∧
    lmCrossFramePanicObserve tb 2 = .okVal 99 99 ∧
    lmCrossFramePanicObserve tb 3 = .okVal 88 10088 ∧
    lmCrossFramePanicObserve tb 4 = .okVal 44 44033 ∧
    lmCrossFramePanicObserve tb 5 = .okVal 66 66055 ∧
    lmCrossFramePanicObserve tb 6 = .okVal 34 34 ∧
    lmCrossFramePanicObserve tb 7 = .okVal 20 20 := by
  cases tb
  · exact ⟨Option.some.inj (lm_ep1_basic 0 (by decide)),
           Option.some.inj (lm_ep1_basic 1 (by decide)),
           Option.some.inj (lm_ep1_basic 2 (by decide)),
           Option.some.inj (lm_ep1_basic 3 (by decide)),
           Option.some.inj (lm_ep1_basic 4 (by decide)),
           Option.some.inj (lm_ep1_basic 5 (by decide)),
           Option.some.inj (lm_ep1_basic 6 (by decide)),
           Option.some.inj (lm_ep1_basic 7 (by decide))⟩
  · exact ⟨Option.some.inj (lm_ep1_tb 0 (by decide)),
           Option.some.inj (lm_ep1_tb 1 (by decide)),
           Option.some.inj (lm_ep1_tb 2 (by decide)),
           Option.some.inj (lm_ep1_tb 3 (by decide)),
           Option.some.inj (lm_ep1_tb 4 (by decide)),
           Option.some.inj (lm_ep1_tb 5 (by decide)),
           Option.some.inj (lm_ep1_tb 6 (by decide)),
           Option.some.inj (lm_ep1_tb 7 (by decide))⟩

/-- Mode sensitivity & Tree Borrows protector/immutability UB (Cases `8` & `9`):
foreign write under active `FnEntry` protector and write through `Frozen` `&T`-derived raw pointer
both succeed in `treeBorrows = false` and fault with exact vendored Tree Borrows errors
(`.ProtectedDisabled .Unique` and `.ChildAccessForbidden .Frozen`) in `treeBorrows = true`. -/
theorem lm_ep1_tb_mode_sensitivity_and_protector_ub :
    lmCrossFramePanicObserve false 8 = .okVal 77 77 ∧
    lmCrossFramePanicObserve true 8 = .ub ∧
    lmCrossFramePanicObserve false 9 = .okVal 99 99 ∧
    lmCrossFramePanicObserve true 9 = .ub ∧
    lmCase true 8 = .error (.treeAccess (.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ProtectedDisabled .Unique)))) ∧
    lmCase true 9 = .error (.treeAccess (.AccessFailure ⟨0, 4⟩
      (.TransitionError 1 (.ChildAccessForbidden .Frozen)))) ∧
    (∀ idx, idx < lmCanonicalCaseCount →
      (lmCrossFramePanicObserve false idx ≠ lmCrossFramePanicObserve true idx ↔
        lmCaseModeSensitive idx = true)) :=
  ⟨lmCrossFramePanicObserve_mode_sensitivity.1,
   lmCrossFramePanicObserve_mode_sensitivity.2.1,
   lmCrossFramePanicObserve_mode_sensitivity.2.2.1,
   lmCrossFramePanicObserve_mode_sensitivity.2.2.2.1,
   lm_tb_exact_failure_diagnostics.1,
   lm_tb_exact_failure_diagnostics.2.1,
   lmCrossFramePanicObserve_mode_sensitivity.2.2.2.2⟩

/-- Negative UB witnesses in BOTH modes: callee dead-local UAR (`10`), positive/negative OOB
in-bounds `BinOp.offset` (`11, 12`), and OOB deref after wrapping offset (`13`), paired with exact
vendored Miri failure diagnostics. -/
theorem lm_ep1_uar_and_oob_ptr_arith_ub (tb : Bool) :
    lmCrossFramePanicObserve tb 10 = .ub ∧
    lmCrossFramePanicObserve tb 11 = .ub ∧
    lmCrossFramePanicObserve tb 12 = .ub ∧
    lmCrossFramePanicObserve tb 13 = .ub ∧
    lmCase tb 10 = .error (.access (.allocationLookup (.deadAllocation ⟨1, by decide⟩))) ∧
    lmCase tb 11 = .error (.pointerOffset (.access
      (.pointerOutOfBounds ⟨1, by decide⟩ ⟨8⟩ 0 12 .inboundsPointerArithmetic))) ∧
    lmCase tb 12 = .error (.pointerOffset (.access
      (.pointerOutOfBounds ⟨1, by decide⟩ ⟨8⟩ 0 (-4) .inboundsPointerArithmetic))) ∧
    lmCase tb 13 = .error (.access
      (.pointerOutOfBounds ⟨1, by decide⟩ ⟨4⟩ 400 4 .memoryAccess)) := by
  cases tb
  · exact ⟨Option.some.inj (lm_ep1_basic 10 (by decide)),
           Option.some.inj (lm_ep1_basic 11 (by decide)),
           Option.some.inj (lm_ep1_basic 12 (by decide)),
           Option.some.inj (lm_ep1_basic 13 (by decide)),
           lm_basic_exact_failure_diagnostics.1,
           lm_basic_exact_failure_diagnostics.2.1,
           lm_basic_exact_failure_diagnostics.2.2.1,
           lm_basic_exact_failure_diagnostics.2.2.2.1⟩
  · exact ⟨Option.some.inj (lm_ep1_tb 10 (by decide)),
           Option.some.inj (lm_ep1_tb 11 (by decide)),
           Option.some.inj (lm_ep1_tb 12 (by decide)),
           Option.some.inj (lm_ep1_tb 13 (by decide)),
           lm_tb_exact_failure_diagnostics.2.2.1,
           lm_tb_exact_failure_diagnostics.2.2.2.1,
           lm_tb_exact_failure_diagnostics.2.2.2.2.1,
           lm_tb_exact_failure_diagnostics.2.2.2.2.2.1⟩

/-- `Assert` pass/fail, `Unreachable`, and 4-way `UnwindAction` witnesses (`14..20`) in BOTH modes,
paired with universal 4-way `lm_cf_assert_four_way`. -/
theorem lm_ep1_assert_and_four_way_unwind_witnesses (tb : Bool) :
    lmCrossFramePanicObserve tb 14 = .okVal 101 101 ∧
    lmCrossFramePanicObserve tb 15 = .okVal 102 102 ∧
    lmCrossFramePanicObserve tb 16 = .ub ∧
    lmCrossFramePanicObserve tb 17 = .unwound 115 ∧
    lmCrossFramePanicObserve tb 18 = .abort ∧
    lmCrossFramePanicObserve tb 19 = .abort ∧
    lmCrossFramePanicObserve tb 20 = .ub ∧
    (type_of% @lm_cf_assert_four_way) := by
  cases tb
  · exact ⟨Option.some.inj (lm_ep1_basic 14 (by decide)),
           Option.some.inj (lm_ep1_basic 15 (by decide)),
           Option.some.inj (lm_ep1_basic 16 (by decide)),
           Option.some.inj (lm_ep1_basic 17 (by decide)),
           Option.some.inj (lm_ep1_basic 18 (by decide)),
           Option.some.inj (lm_ep1_basic 19 (by decide)),
           Option.some.inj (lm_ep1_basic 20 (by decide)),
           @lm_cf_assert_four_way⟩
  · exact ⟨Option.some.inj (lm_ep1_tb 14 (by decide)),
           Option.some.inj (lm_ep1_tb 15 (by decide)),
           Option.some.inj (lm_ep1_tb 16 (by decide)),
           Option.some.inj (lm_ep1_tb 17 (by decide)),
           Option.some.inj (lm_ep1_tb 18 (by decide)),
           Option.some.inj (lm_ep1_tb 19 (by decide)),
           Option.some.inj (lm_ep1_tb 20 (by decide)),
           @lm_cf_assert_four_way⟩

/-- Multi-frame LIFO protector release, cleanup recovery (`21, 23`), double-panic/terminate/unreachable
propagation (`22, 24, 25`), root-frame unwind UB (`26, 27`), premature-parent-write UB contrast,
catch-harness reconciliation, and out-of-range fail-closedness (`≥ 28`). -/
theorem lm_ep1_multiframe_lifo_cleanup_and_root_boundary (tb : Bool) :
    lmCrossFramePanicObserve tb 21 = .okCleanupRecovered 65 65 ∧
    lmCrossFramePanicObserve tb 22 = .abort ∧
    lmCrossFramePanicObserve tb 23 = .okCleanupRecovered 300 300 ∧
    lmCrossFramePanicObserve tb 24 = .abort ∧
    lmCrossFramePanicObserve tb 25 = .ub ∧
    lmCrossFramePanicObserve tb 26 = .ub ∧
    lmCrossFramePanicObserve tb 27 = .ub ∧
    lmCrossFramePanicObserve tb 28 = .invalidOrUnsupported ∧
    lmCrossFramePanicObserve tb 999 = .invalidOrUnsupported ∧
    (type_of% @lm_case21_premature_parent_write_ub_contrast) ∧
    (type_of% @lm_multiframe_lifo_protector_release_witness) ∧
    (type_of% @lm_root_unwind_boundary_vs_catch_harness) := by
  have h28 := lmCrossFramePanicObserve_out_of_range tb 28 (by decide)
  have h999 := lmCrossFramePanicObserve_out_of_range tb 999 (by decide)
  cases tb
  · exact ⟨Option.some.inj (lm_ep1_basic 21 (by decide)),
           Option.some.inj (lm_ep1_basic 22 (by decide)),
           Option.some.inj (lm_ep1_basic 23 (by decide)),
           Option.some.inj (lm_ep1_basic 24 (by decide)),
           Option.some.inj (lm_ep1_basic 25 (by decide)),
           Option.some.inj (lm_ep1_basic 26 (by decide)),
           Option.some.inj (lm_ep1_basic 27 (by decide)),
           h28, h999,
           @lm_case21_premature_parent_write_ub_contrast,
           @lm_multiframe_lifo_protector_release_witness,
           @lm_root_unwind_boundary_vs_catch_harness⟩
  · exact ⟨Option.some.inj (lm_ep1_tb 21 (by decide)),
           Option.some.inj (lm_ep1_tb 22 (by decide)),
           Option.some.inj (lm_ep1_tb 23 (by decide)),
           Option.some.inj (lm_ep1_tb 24 (by decide)),
           Option.some.inj (lm_ep1_tb 25 (by decide)),
           Option.some.inj (lm_ep1_tb 26 (by decide)),
           Option.some.inj (lm_ep1_tb 27 (by decide)),
           h28, h999,
           @lm_case21_premature_parent_write_ub_contrast,
           @lm_multiframe_lifo_protector_release_witness,
           @lm_root_unwind_boundary_vs_catch_harness⟩

/-- Linkage to Episode 1's full `CrossFrameRefAndPanicLM` capstone. -/
theorem lm_ep1_capstone_linked :
    type_of% @ep1_lean_miri_cross_frame_panic_capstone :=
  @ep1_lean_miri_cross_frame_panic_capstone

/-! ### §1b. `ExactWpAndMemoryFrameLM` End-to-End Positive & Negative Witnesses -/

/-- Positive & negative whole-body `ExactWP` discharges on real `translateBody`-lowered
`CapturedMir` bodies: normal return, passing assert, failing assert → abort, failing assert →
cleanup `_0 = 99` → `UnwindResume`, AND bidirectional `↔` UB/abort refutations (`¬ AnnealExactWP`). -/
theorem lm_ep2_whole_body_exactwp_positive_and_ub_refutation :
    (type_of% @miriBodyExactWP_normal_return) ∧
    (type_of% @miriBodyExactWP_unreachable_ub_refutation) ∧
    (type_of% @miriBodyExactWP_assert_pass_return) ∧
    (type_of% @miriBodyExactWP_assert_fail_terminate) ∧
    (type_of% @miriBodyExactWP_assert_cleanup_resume) ∧
    (type_of% @miriStepExactWP_iff) ∧
    (type_of% @miriAllowedStepExactWP_iff) ∧
    (type_of% @miriBodyExactWP_iff) ∧
    (type_of% @miriBodyExactWP_loop_invariant) ∧
    (type_of% @miriBodyExactWP_negation_refutation) :=
  ⟨@miriBodyExactWP_normal_return, @miriBodyExactWP_unreachable_ub_refutation,
   @miriBodyExactWP_assert_pass_return, @miriBodyExactWP_assert_fail_terminate,
   @miriBodyExactWP_assert_cleanup_resume, @miriStepExactWP_iff,
   @miriAllowedStepExactWP_iff, @miriBodyExactWP_iff,
   @miriBodyExactWP_loop_invariant, @miriBodyExactWP_negation_refutation⟩

/-- Little-endian & big-endian disjoint `writeScalar`/`readScalar`/`writeUninit`/`writeBytes`/`copy`
memory framing and round-trips bridged from `LeanMiriSpec.MemoryLemmas` into `AnnealExactWP`, plus
concrete LE vs. BE witness (`0x11223344`) and uninit-read `.invalidUninitBytes` fault. -/
theorem lm_ep2_le_vs_be_disjoint_memory_frame :
    (type_of% @allocEndian_le_vs_be_disjoint_frame_witness) ∧
    (type_of% @allocWriteScalar_then_readScalar_int_exactWP) ∧
    (type_of% @allocWriteScalar_then_readScalar_ptr_exactWP) ∧
    (type_of% @allocWriteScalar_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocWriteUninit_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocWriteBytes_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocCopy_disjoint_readScalar_frame_exactWP) ∧
    (type_of% @allocWriteScalar_disjoint_readScalar_frame_eq) ∧
    (type_of% @allocWriteUninit_disjoint_readScalar_frame_eq) ∧
    (type_of% @allocWriteBytes_disjoint_readScalar_frame_eq) ∧
    (type_of% @allocCopy_disjoint_readScalar_frame_eq) ∧
    (type_of% @allocReadScalar_uninit_exactWP) ∧
    (type_of% @allocMapExtra_preserves_readScalar_exactWP) ∧
    (type_of% @allocWithExtra_preserves_readScalar_exactWP) :=
  ⟨@allocEndian_le_vs_be_disjoint_frame_witness,
   @allocWriteScalar_then_readScalar_int_exactWP,
   @allocWriteScalar_then_readScalar_ptr_exactWP,
   @allocWriteScalar_disjoint_readScalar_frame_exactWP,
   @allocWriteUninit_disjoint_readScalar_frame_exactWP,
   @allocWriteBytes_disjoint_readScalar_frame_exactWP,
   @allocCopy_disjoint_readScalar_frame_exactWP,
   @allocWriteScalar_disjoint_readScalar_frame_eq, @allocWriteUninit_disjoint_readScalar_frame_eq,
   @allocWriteBytes_disjoint_readScalar_frame_eq, @allocCopy_disjoint_readScalar_frame_eq,
   @allocReadScalar_uninit_exactWP,
   @allocMapExtra_preserves_readScalar_exactWP,
   @allocWithExtra_preserves_readScalar_exactWP⟩

/-- `Std.Do`-free `TreeBorrowsWP` & `ProtectorReleaseWP`: bidirectional `↔` exactness plus real
2-segment 16-byte `BorrowTree` witnesses proving committed segment-0 state mutations survive inside
`result.tree` when segment 1 faults on a protected node! -/
theorem lm_ep2_tree_borrows_and_protector_committed_prefix_on_error :
    (type_of% @tbAccessExactWP_iff) ∧
    (type_of% @tbDeallocExactWP_iff) ∧
    (type_of% @tbDealloc_accessFailure_retains_tree) ∧
    (type_of% @protectorReleaseExactWP_iff) ∧
    (type_of% @protectorRelease_missingTag_exactWP) ∧
    (type_of% @tb_access_committed_prefix_on_error_witness) ∧
    (type_of% @protector_release_committed_prefix_on_error_witness) :=
  ⟨@tbAccessExactWP_iff, @tbDeallocExactWP_iff, @tbDealloc_accessFailure_retains_tree,
   @protectorReleaseExactWP_iff, @protectorRelease_missingTag_exactWP,
   @tb_access_committed_prefix_on_error_witness,
   @protector_release_committed_prefix_on_error_witness⟩

/-- Linkage to Episode 2's full `ExactWpAndMemoryFrameLM` capstone. -/
theorem lm_ep2_capstone_linked :
    type_of% @ep2_lean_miri_exact_wp_and_memory_frame_capstone :=
  @ep2_lean_miri_exact_wp_and_memory_frame_capstone

/-! ### §1c. `ExactWpAndSmartCtors` End-to-End Positive & Negative Witnesses -/

/-- `Bitprism` smart simplifying constructors: nested `O(1)` AST collapse vs. raw expression plus
all 10 exact scalar & pointer `*_eq_raw` laws. -/
theorem core_ep2_bitprism_smart_ctors_o1_collapse :
    (type_of% @bitprism_nested_collapse_o1) ∧
    (type_of% @mkAddSmart_eq_raw) ∧
    (type_of% @mkSubSmart_eq_raw) ∧
    (type_of% @mkMulSmart_eq_raw) ∧
    (type_of% @mkBitAndSmart_eq_raw) ∧
    (type_of% @mkBitOrSmart_eq_raw) ∧
    (type_of% @mkBitXorSmart_eq_raw) ∧
    (type_of% @mkShlSmart_eq_raw) ∧
    (type_of% @mkShrSmart_eq_raw) ∧
    (type_of% @mkPtrOffsetSmart_eq_raw) ∧
    (type_of% @mkWrappingPtrOffsetSmart_eq_raw) :=
  ⟨@bitprism_nested_collapse_o1, @mkAddSmart_eq_raw, @mkSubSmart_eq_raw, @mkMulSmart_eq_raw,
   @mkBitAndSmart_eq_raw, @mkBitOrSmart_eq_raw, @mkBitXorSmart_eq_raw, @mkShlSmart_eq_raw,
   @mkShrSmart_eq_raw, @mkPtrOffsetSmart_eq_raw, @mkWrappingPtrOffsetSmart_eq_raw⟩

/-- Critical UB non-erasure negative refutations (`0 & dead`, `0 & uninit`, `uninit * 0`,
`addUnchecked` overflow) proving operand-definedness and overflow-mode preconditions are strictly
necessary, plus coalescing `mkMemWriteFrame` exactness and dead-slot failure preservation. -/
theorem core_ep2_bitprism_negative_ub_non_erasure :
    (type_of% @bitAnd_zero_dead_local_preserves_ub) ∧
    (type_of% @bitAnd_zero_uninit_local_preserves_ub) ∧
    (type_of% @mul_zero_uninit_local_preserves_ub) ∧
    (type_of% @bitOr_allOnes_uninit_local_preserves_ub) ∧
    (type_of% @addUnchecked_overflow_preserves_ub) ∧
    (type_of% @mkAddSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkSubSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkBitAndSmartRvalue_zero_left_eq_raw) ∧
    (type_of% @mkBitAndSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkMulSmartRvalue_zero_left_eq_raw) ∧
    (type_of% @mkMulSmartRvalue_zero_right_eq_raw) ∧
    (type_of% @mkBitOrSmartRvalue_allOnes_left_eq_raw) ∧
    (type_of% @mkBitOrSmartRvalue_allOnes_right_eq_raw) ∧
    (type_of% @mkSmartRvalue_never_erases_ub) ∧
    (type_of% @bitprism_const_annihilators_fire) ∧
    (type_of% @bitprism_const_width_mismatch_preserves_unsupported) ∧
    (type_of% @mkMemWriteFrame_eq_raw) ∧
    (type_of% @mkMemWriteFrame_dead_slot_preserves_failure) :=
  ⟨@bitAnd_zero_dead_local_preserves_ub, @bitAnd_zero_uninit_local_preserves_ub,
   @mul_zero_uninit_local_preserves_ub, @bitOr_allOnes_uninit_local_preserves_ub,
   @addUnchecked_overflow_preserves_ub, @mkAddSmartRvalue_zero_right_eq_raw,
   @mkSubSmartRvalue_zero_right_eq_raw, @mkBitAndSmartRvalue_zero_left_eq_raw,
   @mkBitAndSmartRvalue_zero_right_eq_raw, @mkMulSmartRvalue_zero_left_eq_raw,
   @mkMulSmartRvalue_zero_right_eq_raw, @mkBitOrSmartRvalue_allOnes_left_eq_raw,
   @mkBitOrSmartRvalue_allOnes_right_eq_raw, @mkSmartRvalue_never_erases_ub,
   @bitprism_const_annihilators_fire, @bitprism_const_width_mismatch_preserves_unsupported,
   @mkMemWriteFrame_eq_raw, @mkMemWriteFrame_dead_slot_preserves_failure⟩

/-- Downstream test of the `anneal_veil_frame` tactic preserving a 3-field compound invariant
`(heap ∧ callerLocals ∧ globals)` across a 4-step sequence of real `Trusted.MirSemantics` actions
(`nop ; assign_const_local ; restoreCallerProtectors ; disableFrameBorrows`). -/
theorem core_ep2_veil_frame_downstream_tactic_test
    (dstLoc : Local) (ty : Ty) (sc : ScalarInt) (caller : SavedCallerFrame) (depth nLocals : Nat)
    (Pheap : AllocId → List CapturedAllocation → Prop) (Pcaller : List LocalSlot → Prop)
    (Pglob : List CapturedAllocation → Prop)
    (s : MachineState)
    (hInv : frame_heap Pheap s ∧ frame_callerLocals Pcaller s ∧ frame_globals Pglob s) :
    let act :=
      ExactAction.seq (evalStmtAction { kind := .nop, span := "t0" })
        (ExactAction.seq
          (evalStmtAction { kind := .assign ⟨dstLoc, []⟩ (.use (mkConstScalarOp ty sc)), span := "t1" })
          (ExactAction.seq (restoreCallerProtectorsAction caller)
            (disableFrameBorrowsAction depth nLocals)))
    AnnealExactWP act
      (fun _ s' => frame_heap Pheap s' ∧ frame_callerLocals Pcaller s' ∧ frame_globals Pglob s')
      (fun _ s' => frame_heap Pheap s' ∧ frame_callerLocals Pcaller s' ∧ frame_globals Pglob s') s := by
  have hMod0 := nop_modifiesOnlyFields "t0" .nil emptyLayoutTable
  have hMod1 := assign_const_local_modifiesOnlyFields dstLoc ty sc "t1" .nil emptyLayoutTable
  have hMod2 := restoreCallerProtectors_modifiesOnlyFields caller
  have hMod3 := disableFrameBorrows_modifiesOnlyFields depth nLocals
  have hMod23 := modifiesOnlyFields_seq hMod2 hMod3
  have hMod123 := modifiesOnlyFields_seq hMod1 hMod23
  have hMod := modifiesOnlyFields_seq hMod0 hMod123
  anneal_veil_frame

/-- Direct `AnnealExactWP` bidirectional `↔` negation refutation witness: a failing action
discharges `onError := (· = "ub")` AND refutes `onError := False` via `exactWP_negation_refutation`. -/
theorem core_ep2_exact_wp_direct_unsound_refutation (s : Nat) :
    AnnealExactWP (ExactAction.throw (S := Nat) (A := Unit) "ub")
      (fun _ _ => False) (fun e s' => e = "ub" ∧ s' = s) s ∧
    ¬ AnnealExactWP (ExactAction.throw (S := Nat) (A := Unit) "ub")
      (fun _ _ => True) (fun _ _ => False) s := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  exact (exactWP_negation_refutation (ExactAction.throw (S := Nat) (A := Unit) "ub") s).mpr
    ⟨"ub", s, rfl⟩

/-- Concrete whole-body `ExactBodySafetyVC` on REAL `Trusted.MirSemantics.stepMirFn` executions:
the `_0 = (); return` body discharges the normal-return VC with an unsatisfiable error branch, while
the `unreachable` and `unwindTerminate` bodies REFUTE the corresponding safety VCs. -/
theorem core_ep2_trusted_whole_body_vc_positive_and_refutation :
    ¬ ExactBodySafetyVC exactVcUnreachableBody 2 (fun _ _ => True) (fun _ _ => False)
        (initMachineStateWithCallees exactVcUnreachableBody [] []) ∧
    ExactBodySafetyVC exactVcReturnBody 4
      (fun out _ => exactVcIsNormal (.ok out (initMachineStateWithCallees exactVcReturnBody [] [])) = true)
      (fun _ _ => False) (initMachineStateWithCallees exactVcReturnBody [] []) :=
  ⟨exactBodySafetyVC_concrete_trusted_bodies.2.2.2.2.1, exactBodySafetyVC_concrete_trusted_bodies.2.1⟩

/-- Exhaustive 14-field `Memory` & 17-field `MachineState` extensionality + `ExactWpAndSmartCtors`
core capstone linkage. -/
theorem core_ep2_extensionality_and_capstone_linked :
    (type_of% @Memory.ext_allFields) ∧
    (type_of% @MachineState.ext_allFields) ∧
    (type_of% @exactWP_veil_frame) ∧
    (type_of% @anneal_veil_frame_multistep_demo) ∧
    (type_of% @ep2_exact_wp_smart_ctors_and_veil_frame_capstone) :=
  ⟨@Memory.ext_allFields, @MachineState.ext_allFields, @exactWP_veil_frame,
   @anneal_veil_frame_multistep_demo, @ep2_exact_wp_smart_ctors_and_veil_frame_capstone⟩

/-! ## §2. Cross-Root 3-Way Kernel Closure & Master 6-Module Audit (`run_cmd`) -/

open Lean Elab Command Meta in
run_cmd do
  let opts := (← getOptions).setBool `Elab.async false
  let sp : SearchPath := [System.FilePath.mk ".lake/build/lib/lean",
                          System.FilePath.mk "examples/.lake/build/lib/lean"]
  initSearchPath (← findSysroot) sp
  let baseEnv ← importModules
    #[{ module := `Anneal.Mir.CrossFrameRefAndPanicDualSpec },
      { module := `MiniRustSpec.CrossFrameRefAndPanicMR },
      { module := `Anneal.ExactWpAndSmartCtors },
      { module := `LeanMiriSpec.CrossFrameRefAndPanicLM },
      { module := `LeanMiriSpec.ExactWpAndMemoryFrameLM }]
    {} 0
  let ns := `Anneal.Mir.CrossFramePanicAndExactWpTests.CrossRoot
  let dsNs := `Anneal.Mir.CrossFrameRefAndPanicDualSpec
  let mrNs := `MiniRustSpec.CrossFrameRefAndPanicMR
  let lmNs := `LeanMiriSpec.CrossFrameRefAndPanicLM
  let ep2CoreNs := `Anneal.ExactWpAndSmartCtors
  let ep2LmNs := `LeanMiriSpec.ExactWpAndMemoryFrameLM

  let act : CoreM (Nat × Nat × Array Lean.Name) := do
    let addDef (name : Lean.Name) (val : Expr) : CoreM Unit := do
      let ty ← MetaM.run' <| inferType val
      addDecl <| .defnDecl {
        name, levelParams := [], type := ty, value := val,
        hints := .regular 0, safety := .safe }
    let addThm (name : Lean.Name) (ty pf : Expr) : CoreM Unit := do
      addDecl <| .thmDecl { name, levelParams := [], type := ty, value := pf }
    let elabIn (src : String) (expected? : Option Expr := none) : CoreM Expr := do
      let stx ← match Lean.Parser.runParserCategory (← getEnv) `term src with
        | .ok stx => pure stx
        | .error e => throwError "cross-root parse error: {e}"
      let logBefore ← Core.getMessageLog
      let e ← MetaM.run' <| Lean.Elab.Term.TermElabM.run' do
        let e ← Lean.Elab.Term.elabTermEnsuringType stx expected?
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        if e.hasMVar then throwError "cross-root: unresolved metavariables in {src}"
        pure e
      let logAfter ← Core.getMessageLog
      if logAfter.hasErrors && !logBefore.hasErrors then
        let msgs ← logAfter.toList.mapM (·.toString)
        throwError "cross-root elab error in {src}:\n{String.intercalate "\n" msgs}"
      pure e

    let boolTy := mkConst ``Bool
    let boolTrue := mkConst ``Bool.true
    let boolFalse := mkConst ``Bool.false
    let natTy := mkConst ``Nat
    let eqTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolTrue
    let reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolTrue
    let eqFalse (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolTy e boolFalse
    let reflFalse : Expr := mkApp2 (mkConst ``Eq.refl [1]) boolTy boolFalse
    let lmObsTy := mkConst (lmNs ++ `LmCrossFramePanicObs)
    let obsTy := mkConst (dsNs ++ `CrossFramePanicObs)
    let obsC (c : String) : Expr := mkConst (dsNs ++ `CrossFramePanicObs ++ Lean.Name.mkSimple c)

    -- 1. Genuine structural translator `LmCrossFramePanicObs → CrossFramePanicObs` via
    --    `LmCrossFramePanicObs.rec.{1}` (zero mocks), with forgery flags for negative controls.
    let mkTranslate
        (swapOkVal forgeCleanup forgeUnwound forgeAbort forgeUb : Bool := false) : MetaM Expr := do
      let motive := mkLambda `x .default lmObsTy obsTy
      let brOk ← withLocalDeclD `r natTy fun r => withLocalDeclD `ref natTy fun ref =>
        mkLambdaFVars #[r, ref]
          (if swapOkVal then mkApp2 (obsC "okVal") ref r else mkApp2 (obsC "okVal") r ref)
      let brClean ← withLocalDeclD `r natTy fun r => withLocalDeclD `ref natTy fun ref =>
        mkLambdaFVars #[r, ref]
          (if forgeCleanup then mkApp2 (obsC "okVal") r ref
           else mkApp2 (obsC "okCleanupRecovered") r ref)
      let brUnw ← withLocalDeclD `ref natTy fun ref =>
        mkLambdaFVars #[ref]
          (if forgeUnwound then obsC "abort" else mkApp (obsC "unwound") ref)
      let brAbort := if forgeAbort then obsC "ub" else obsC "abort"
      let brUb := if forgeUb then obsC "abort" else obsC "ub"
      withLocalDeclD `o lmObsTy fun o => do
        let recApp := mkAppN (mkConst (lmNs ++ `LmCrossFramePanicObs.rec) [1])
          #[motive, brOk, brClean, brUnw, brAbort, brUb, obsC "specPanic",
            obsC "invalidOrUnsupported", o]
        mkLambdaFVars #[o] recApp

    let mkObs (tr f : Expr) (invertMode shiftCase : Bool := false) : MetaM Expr :=
      withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx => do
        let tb' := if invertMode then mkApp (mkConst ``Bool.not) tb else tb
        let idx' := if shiftCase then mkApp2 (mkConst ``Nat.add) idx (mkNatLit 1) else idx
        mkLambdaFVars #[tb, idx] (mkApp tr (mkApp2 f tb' idx'))

    let translateName := ns ++ `translateLmObs
    addDef translateName (← MetaM.run' <| mkTranslate)
    let trC := mkConst translateName

    -- 2. Certify `lmAuthorityCheck` on the kernel-evaluable `lmCrossFramePanicObserveU` twin by
    --    `Eq.refl Bool.true`, then transport to the source `lmCrossFramePanicObserve` along
    --    `lmCrossFramePanicObserveU.eq_src`.
    let lmSrc := lmNs ++ `lmCrossFramePanicObserve
    let lmU := lmNs ++ `lmCrossFramePanicObserveU
    let lmEqSrc := lmU ++ `eq_src
    let crossObsU := ns ++ `crossRootLmObsU
    addDef crossObsU (← MetaM.run' <| mkObs trC (mkConst lmU))
    let crossObs := ns ++ `crossRootLmObs
    addDef crossObs (← MetaM.run' <| mkObs trC (mkConst lmSrc))
    let authCheckFn := dsNs ++ `lmAuthorityCheck
    let crossCheckU := ns ++ `crossRootLmObsCheckU
    addThm crossCheckU (eqTrue (mkApp (mkConst authCheckFn) (mkConst crossObsU))) reflTrue
    let srcTy ← MetaM.run' <| inferType (mkConst lmSrc)
    let F ← MetaM.run' <| withLocalDeclD `g srcTy fun g => do
      mkLambdaFVars #[g] (mkApp (mkConst authCheckFn) (← mkObs trC g))
    let congr := mkApp6 (mkConst ``congrArg [1, 1]) srcTy boolTy (mkConst lmSrc) (mkConst lmU) F
      (mkConst lmEqSrc)
    let checkPf := mkApp6 (mkConst ``Eq.trans [1]) boolTy
      (mkApp (mkConst authCheckFn) (mkConst crossObs))
      (mkApp (mkConst authCheckFn) (mkConst crossObsU)) boolTrue congr (mkConst crossCheckU)
    let crossCheck := ns ++ `crossRootLmObsCheck
    addThm crossCheck (eqTrue (mkApp (mkConst authCheckFn) (mkConst crossObs))) checkPf

    -- 3. Out-of-range fail-closedness of the SOURCE observer (all `idx ≥ 28`), transported
    --    through `translateLmObs` from `lmCrossFramePanicObserve_out_of_range`.
    let outName := ns ++ `crossRootLmOutOfRange
    let (outTy, outPf) ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb =>
      withLocalDeclD `idx natTy fun idx => do
        let hTy := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat)
          (mkConst (dsNs ++ `canonicalCaseCount)) idx
        withLocalDeclD `h hTy fun h => do
          let lmOut := mkApp3 (mkConst (lmNs ++ `lmCrossFramePanicObserve_out_of_range)) tb idx h
          let pf := mkApp6 (mkConst ``congrArg [1, 1]) lmObsTy obsTy
            (mkApp2 (mkConst lmSrc) tb idx)
            (mkConst (lmNs ++ `LmCrossFramePanicObs.invalidOrUnsupported)) trC lmOut
          let body := mkApp3 (mkConst ``Eq [1]) obsTy (mkApp2 (mkConst crossObs) tb idx)
            (obsC "invalidOrUnsupported")
          return (← mkForallFVars #[tb, idx, h] body, ← mkLambdaFVars #[tb, idx, h] pf)
    addThm outName outTy outPf

    -- 4. Instantiate REAL `CrossFramePanicLmAuthority`, `CrossFramePanicDualContract`, and
    --    `mkCrossFramePanicDualBundle` with REAL `LeanMiriSpec.CrossFrameRefAndPanicLM`!
    let authName := ns ++ `closedCrossFramePanicLmAuthority
    addDef authName (mkApp3 (mkConst (dsNs ++ `lmAuthorityOfCheck))
      (mkConst crossObs) (mkConst crossCheck) (mkConst outName))
    let contractName := ns ++ `closedCrossFramePanicDualContract
    addDef contractName (mkApp (mkConst (dsNs ++ `CrossFramePanicDualContract.mk)) (mkConst authName))
    let some (.defnInfo cInfo) := (← getEnv).find? contractName
      | throwError "cross-root: contract missing"
    unless cInfo.type.isConstOf (dsNs ++ `CrossFramePanicDualContract) do
      throwError "cross-root: {contractName} is not a CrossFramePanicDualContract"
    let bundleName := ns ++ `closedCrossFramePanicDualBundle
    addDef bundleName (mkApp (mkConst (dsNs ++ `mkCrossFramePanicDualBundle)) (mkConst contractName))
    let contractC := mkConst contractName

    let mut added : Array Lean.Name :=
      #[translateName, crossObsU, crossObs, crossCheckU, crossCheck, outName,
        authName, contractName, bundleName]

    -- 5. Instantiate EVERY named projection + closed Episode 1 Dual-Authority Capstone.
    for projName in [`CrossFramePanicDualContract.lm_matches_all,
                     `contract_mr_lm_total_eq,
                     `contract_lm_basic_eq,
                     `contract_lm_tb_eq,
                     `contract_wire_total_eq,
                     `contract_joint_mode_sensitivity,
                     `contract_three_way_and_root_ceiling_exact,
                     `bundle_unsupported_iff_abort,
                     `crossFramePanicDualBundle_projections,
                     `mrLmModeStepRel_not_mode_invariant,
                     `ep1_cross_frame_ref_and_panic_dual_authority_capstone] do
      let val := mkApp (mkConst (dsNs ++ projName)) contractC
      let ty ← MetaM.run' <| inferType val
      let outN := ns ++ projName
      addThm outN ty val
      added := added.push outN

    -- 6. Re-instantiate key root-package witnesses (MiniRust + Trusted bridge).
    for w in [`mrObserve_matches_expected, `mrObserve_out_of_range, `mrObserve_mode_sensitivity,
              `crossFramePanicOutcomeCodec_tight, `crossFramePanicOutcomeCodec_rejects_malformed,
              `applyUnwindAction_matches_evalRefFrameExit,
              `applyUnwindAction_matches_evalProtectedRefFrameExit,
              `preventsDeallocation_eq_mr,
              `disableFrameBorrows_preserves_outer_frames,
              `disableFramesAbove_preserves_surviving_frames,
              `hasFrameDeallocProtectorConflict_iff,
              `trusted_unwind_continue_chain_to_cleanup,
              `trusted_unwind_releases_callee_protector,
              `trusted_unwind_continue_chain_root_boundary,
              `trustedCrossFramePanicObserve_table,
              `trustedCrossFramePanicObserve_out_of_range,
              `trusted_case10_live_callee_teardown_disable_trace,
              `trusted_root_unwind_exact_outcome_dichotomy,
              `trusted_case21_live_unwind_protector_release_trace,
              `trusted_case23_three_frame_lifo_unwind_trace,
              `trusted_case21_premature_parent_write_ub_contrast,
              `canonical_cells_nondegenerate,
              `root_ceiling_divergence_reconciled_by_catch_harness] do
      let src := dsNs ++ w
      let some (.thmInfo v) := (← getEnv).find? src
        | throwError "cross-root: root witness {src} missing"
      let outN := ns ++ `root ++ w
      addThm outN v.type (mkConst src)
      added := added.push outN

    -- 7. Universal choice-free 3-way Tree Borrows permission bijection (`TreeBorrowPerm ↔
    --    Miri.TreeBorrows.Permission`) matching `preventsDeallocation` = MiniRust
    --    `prevents_deallocation` = vendored protected foreign write `Miri.TreeBorrows.performAccess`.
    let tbp := "Trusted.Rustc.V2026_06_01.MirSemantics.TreeBorrowPerm"
    let mp := "Miri.TreeBorrows.Permission"
    let mkEmbed (swapCellFrozen swapUniqueDisabled : Bool := false) : String :=
      s!"fun (p : {tbp}) => @{tbp}.casesOn (fun _ => {mp}) p " ++
      (if swapCellFrozen then s!"{mp}.Frozen" else s!"{mp}.Cell") ++
      s!" (fun c => {mp}.ReservedFrz c) {mp}.ReservedIM " ++
      (if swapUniqueDisabled then s!"{mp}.Disabled" else s!"{mp}.Unique") ++ " " ++
      (if swapCellFrozen then s!"{mp}.Cell" else s!"{mp}.Frozen") ++ " " ++
      (if swapUniqueDisabled then s!"{mp}.Unique" else s!"{mp}.Disabled")
    let embedName := ns ++ `embedTrustedPermInMiri
    addDef embedName (← elabIn (mkEmbed false false))
    let invEmbedName := ns ++ `embedMiriPermToTrusted
    addDef invEmbedName (← elabIn (s!"fun (q : {mp}) => @{mp}.casesOn (fun _ => {tbp}) q " ++
      s!"{tbp}.cell (fun c => {tbp}.reservedFrz c) {tbp}.reservedIM {tbp}.unique {tbp}.frozen {tbp}.disabled"))
    let embedCellFrozenForged ← elabIn (mkEmbed true false)
    let embedUniqueDisabledForged ← elabIn (mkEmbed false true)
    let blocksName := ns ++ `miriProtectedForeignWriteBlocks
    addDef blocksName (← elabIn (s!"fun (q : {mp}) => @Miri.TreeBorrows.AccessOutcome.casesOn " ++
      "(fun _ => Bool) (Miri.TreeBorrows.performAccess Miri.TreeBorrows.AccessKind.Write " ++
      "Miri.TreeBorrows.AccessRelatedness.ForeignAccess q Bool.true) " ++
      s!"(fun r => Bool.and ({mp}.isDisabled r) (Bool.not ({mp}.isDisabled q))) Bool.true Bool.true"))
    let prev := "Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation"
    let rtTrustedTy ← elabIn s!"∀ p : {tbp}, Eq ({invEmbedName} ({embedName} p)) p" (some (mkSort .zero))
    let rtTrustedPf ← elabIn (s!"fun (p : {tbp}) => @{tbp}.casesOn (fun (p : {tbp}) => Eq ({invEmbedName} ({embedName} p)) p) p " ++
      s!"(Eq.refl {tbp}.cell) (fun (c : Bool) => Eq.refl ({tbp}.reservedFrz c)) " ++
      s!"(Eq.refl {tbp}.reservedIM) (Eq.refl {tbp}.unique) (Eq.refl {tbp}.frozen) (Eq.refl {tbp}.disabled)") (some rtTrustedTy)
    let rtTrustedName := ns ++ `miriPerm_roundtrip_trusted
    addThm rtTrustedName rtTrustedTy rtTrustedPf
    let rtMiriTy ← elabIn s!"∀ q : {mp}, Eq ({embedName} ({invEmbedName} q)) q" (some (mkSort .zero))
    let rtMiriPf ← elabIn (s!"fun (q : {mp}) => @{mp}.casesOn (fun (q : {mp}) => Eq ({embedName} ({invEmbedName} q)) q) q " ++
      s!"(Eq.refl {mp}.Cell) (fun (c : Bool) => Eq.refl ({mp}.ReservedFrz c)) " ++
      s!"(Eq.refl {mp}.ReservedIM) (Eq.refl {mp}.Unique) (Eq.refl {mp}.Frozen) (Eq.refl {mp}.Disabled)") (some rtMiriTy)
    let rtMiriName := ns ++ `trustedPerm_roundtrip_miri
    addThm rtMiriName rtMiriTy rtMiriPf
    let motiveBody (x : String) : String := s!"Eq ({prev} {x}) ({blocksName} ({embedName} {x}))"
    let permEqTy ← elabIn s!"∀ p : {tbp}, {motiveBody "p"}" (some (mkSort .zero))
    let permEqPf ← elabIn (s!"fun (p : {tbp}) => @{tbp}.casesOn (fun (p : {tbp}) => {motiveBody "p"}) p " ++
      s!"(Eq.refl Bool.false) (fun (c : Bool) => @Bool.casesOn (fun (c : Bool) => " ++
      s!"{motiveBody s!"({tbp}.reservedFrz c)"}) c (Eq.refl Bool.true) (Eq.refl Bool.true)) " ++
      "(Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.false)") (some permEqTy)
    let permEqName := ns ++ `trustedPreventsDeallocation_eq_miri
    addThm permEqName permEqTy permEqPf
    let miriAllTy ← elabIn s!"∀ q : {mp}, Eq ({blocksName} q) ({prev} ({invEmbedName} q))" (some (mkSort .zero))
    let miriAllPf ← elabIn (s!"fun (q : {mp}) => Eq.trans (congrArg {blocksName} (Eq.symm ({rtMiriName} q))) " ++
      s!"(Eq.symm ({permEqName} ({invEmbedName} q)))") (some miriAllTy)
    let miriAllName := ns ++ `miriBlocks_eq_trustedPrevents
    addThm miriAllName miriAllTy miriAllPf
    let permMrTy ← elabIn (s!"∀ p : {tbp}, Eq (MiniRustSpec.Interp.PermissionProt.prevents_deallocation " ++
      s!"({dsNs}.trustedPermToMrProt p)) ({blocksName} ({embedName} p))") (some (mkSort .zero))
    let permMrPf ← elabIn (s!"fun (p : {tbp}) => Eq.trans (Eq.symm ({dsNs}.preventsDeallocation_eq_mr p)) " ++
      s!"({permEqName} p)") (some permMrTy)
    let permMrName := ns ++ `mrPreventsDeallocation_eq_miri
    addThm permMrName permMrTy permMrPf
    let permCheckName := ns ++ `permCorrCheck
    let consL (xs : List String) : String :=
      xs.foldr (fun x acc => s!"(List.cons {x} {acc})") s!"(@List.nil {tbp})"
    addDef permCheckName (← elabIn (s!"fun (e : {tbp} → {mp}) => List.all " ++
      consL [s!"{tbp}.cell", s!"({tbp}.reservedFrz Bool.false)", s!"({tbp}.reservedFrz Bool.true)",
        s!"{tbp}.reservedIM", s!"{tbp}.unique", s!"{tbp}.frozen", s!"{tbp}.disabled"] ++
      s!" (fun (p : {tbp}) => Bool.not (Bool.xor ({prev} p) ({blocksName} (e p))))"))
    let permCertName := ns ++ `permCorrCheckGenuine
    addThm permCertName (eqTrue (mkApp (mkConst permCheckName) (mkConst embedName))) reflTrue

    -- 8. Master 6-Module Workstream Capstone uniting Ep1 (3-way closed DualSpec + LM + universal
    --    permission bijection) AND Ep2 (ExactWpAndSmartCtors + ExactWpAndMemoryFrameLM).
    let masterName := ns ++ `closedMasterSixModuleCapstone
    let masterPf ← elabIn
      (s!"And.intro ({ns}.ep1_cross_frame_ref_and_panic_dual_authority_capstone) " ++
       s!"(And.intro ({lmNs}.ep1_lean_miri_cross_frame_panic_capstone) " ++
       s!"(And.intro {rtTrustedName} (And.intro {rtMiriName} (And.intro {permMrName} " ++
       s!"(And.intro {miriAllName} (And.intro ({ep2CoreNs}.ep2_exact_wp_smart_ctors_and_veil_frame_capstone) " ++
       s!"({ep2LmNs}.ep2_lean_miri_exact_wp_and_memory_frame_capstone)))))))")
    let masterTy ← MetaM.run' <| inferType masterPf
    addThm masterName masterTy masterPf

    for n in [embedName, invEmbedName, blocksName, rtTrustedName, rtMiriName,
              permEqName, miriAllName, permMrName, permCheckName, permCertName, masterName] do
      added := added.push n

    -- 9. Negative forgery controls on scratch copies (30 total: 14 two-sided boolean forgeries +
    --    16 value/Prop/type-level forgeries paired with accepted baselines).
    let saved ← getEnv
    let acceptsMsg (d : Declaration) : CoreM (Option String) := do
      let r ← try addDecl d; pure none catch e => pure (some (← e.toMessageData.toString))
      setEnv saved
      return r
    let accepts (d : Declaration) : CoreM Bool := return (← acceptsMsg d).isNone
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let lmObsU := mkConst lmU
    let authCheckExpr (o : Expr) : Expr := mkApp (mkConst authCheckFn) o
    let modeInv ← MetaM.run' <| mkObs trC lmObsU true false
    let caseShift ← MetaM.run' <| mkObs trC lmObsU false true
    let okValSwap ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate true false false false false) lmObsU
    let cleanupForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false true false false false) lmObsU
    let unwoundForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false false true false false) lmObsU
    let abortForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false false false true false) lmObsU
    let ubForged ← MetaM.run' <| mkObs (← MetaM.run' <| mkTranslate false false false false true) lmObsU
    -- Trusted passed off as LeanMiri: disagrees at basic-mode Cases 8/9 and root-ceiling Case 27!
    let trustedAsLm ← MetaM.run' <| withLocalDeclD `tb boolTy fun tb => withLocalDeclD `idx natTy fun idx =>
      mkLambdaFVars #[tb, idx] (mkApp (mkConst (dsNs ++ `trustedCrossFramePanicObserve)) idx)
    -- `veil_frame` clobbered-field overlap controls (`disjointFieldsBool` MUST reduce to `false`).
    let vfOverlapBorrows ← elabIn
      s!"{ep2CoreNs}.disjointFieldsBool (List.cons ({ep2CoreNs}.StateField.mem {ep2CoreNs}.MemoryField.borrows) (@List.nil {ep2CoreNs}.StateField)) (List.cons ({ep2CoreNs}.StateField.mem {ep2CoreNs}.MemoryField.borrows) (@List.nil {ep2CoreNs}.StateField))"
    let vfOverlapProt ← elabIn
      s!"{ep2CoreNs}.disjointFieldsBool (List.cons {ep2CoreNs}.StateField.frameLocals (List.cons ({ep2CoreNs}.StateField.mem {ep2CoreNs}.MemoryField.activeProtectors) (@List.nil {ep2CoreNs}.StateField))) (List.cons ({ep2CoreNs}.StateField.mem {ep2CoreNs}.MemoryField.activeProtectors) (@List.nil {ep2CoreNs}.StateField))"
    let vfOverlapGlobals ← elabIn
      s!"{ep2CoreNs}.disjointFieldsBool (List.cons ({ep2CoreNs}.StateField.mem {ep2CoreNs}.MemoryField.nextAllocId) (List.cons ({ep2CoreNs}.StateField.mem {ep2CoreNs}.MemoryField.globals) (@List.nil {ep2CoreNs}.StateField))) (List.cons ({ep2CoreNs}.StateField.mem {ep2CoreNs}.MemoryField.globals) (@List.nil {ep2CoreNs}.StateField))"
    -- `Bitprism` unsound scalar identity control (`0 & x ≠ x` at `x = 7`), built directly with
    -- `mkNatLit` (no `OfNat` instances in `importModules`).
    let bitprismBadId ← MetaM.run' <| do
      let envFn ← withLocalDeclD `_x natTy fun x => mkLambdaFVars #[x] (mkNatLit 7)
      let e0 := mkApp2 (mkConst (ep2CoreNs ++ `SmartScalarExpr.const)) (mkNatLit 4) (mkNatLit 0)
      let ex := mkApp2 (mkConst (ep2CoreNs ++ `SmartScalarExpr.var)) (mkNatLit 4) (mkNatLit 0)
      let smart := mkApp3 (mkConst (ep2CoreNs ++ `mkBitAndSmart)) (mkNatLit 4) e0 ex
      let evald := mkApp3 (mkConst (ep2CoreNs ++ `SmartScalarExpr.eval)) (mkNatLit 4) envFn smart
      pure (mkApp2 (mkConst ``Nat.beq) evald (mkNatLit 7))

    let thm (n : String) (ty pf : Expr) : Declaration :=
      .thmDecl { name := ns ++ `forged ++ Lean.Name.mkSimple n, levelParams := [], type := ty, value := pf }

    -- 9a. Two-sided boolean negative controls (kernel MUST accept `= false` AND reject `= true`).
    let boolForgeries : List (String × String × Expr) :=
      [ ("Ep1 mode-inverted LM observer (Bool.not tb, catching cases 8/9)", "modeInverted", authCheckExpr modeInv),
        ("Ep1 case-shifted LM observer (idx + 1)", "caseShifted", authCheckExpr caseShift),
        ("Ep1 okVal payload-swapped translator (catching cases 3/4/5)", "okValSwapped", authCheckExpr okValSwap),
        ("Ep1 okCleanupRecovered-to-okVal forged translator (catching cases 21/23)", "cleanupForged", authCheckExpr cleanupForged),
        ("Ep1 unwound-to-abort forged translator (catching case 17)", "unwoundForged", authCheckExpr unwoundForged),
        ("Ep1 abort-to-ub forged translator (catching cases 18/19/22/24)", "abortForged", authCheckExpr abortForged),
        ("Ep1 ub-to-abort forged translator (catching cases 8..13/16/20/25..27)", "ubForged", authCheckExpr ubForged),
        ("Ep1 Trusted observer passed off as LeanMiri (diverges on 8/9/27)", "trustedAsLm", authCheckExpr trustedAsLm),
        ("Ep1 cell/frozen-swapped Trusted→Miri permission embedding", "permSwapCellFrozen", mkApp (mkConst permCheckName) embedCellFrozenForged),
        ("Ep1 unique/disabled-swapped Trusted→Miri permission embedding", "permSwapUniqueDisabled", mkApp (mkConst permCheckName) embedUniqueDisabledForged),
        ("Ep2 veil_frame clobbered borrows field overlap", "vfOverlapBorrows", vfOverlapBorrows),
        ("Ep2 veil_frame clobbered activeProtectors field overlap", "vfOverlapProt", vfOverlapProt),
        ("Ep2 veil_frame clobbered globals field overlap", "vfOverlapGlobals", vfOverlapGlobals),
        ("Ep2 Bitprism unsound identity 0 & 7 == 7", "bitprismBadId", bitprismBadId) ]
    let mut rejected : Nat := 0
    for (what, tag, expr) in boolForgeries do
      unless ← accepts (thm (tag ++ "IsFalse") (eqFalse expr) reflFalse) do
        throwError "cross-root negative control VACUOUS: {what} did not kernel-reduce to Bool.false"
      unless ← rejects (thm tag (eqTrue expr) reflTrue) do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 9b. Value / Prop / Type-level forgeries paired with accepted baselines (built directly with
    --     `mkApp*` + `mkNatLit` + `mkStrLit` so zero `OfNat` instances are needed).
    let natProdTy := mkApp2 (mkConst ``Prod [0, 0]) natTy natTy
    let badTuple := mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natProdTy (mkNatLit 7)
      (mkApp4 (mkConst ``Prod.mk [0, 0]) natTy natTy (mkNatLit 0) (mkNatLit 0))
    let badDecode := mkApp (mkConst (dsNs ++ `crossFramePanicDecode)) badTuple
    let optObsTy := mkApp (mkConst ``Option [0]) obsTy
    let case27Tr := mkApp (mkConst (dsNs ++ `trustedCrossFramePanicObserve)) (mkNatLit 27)
    let case27Lm := mkApp2 (mkConst crossObsU) boolTrue (mkNatLit 27)
    let case8Basic := mkApp2 (mkConst crossObsU) boolFalse (mkNatLit 8)
    let case8Tb := mkApp2 (mkConst crossObsU) boolTrue (mkNatLit 8)
    let case28Oor := mkApp2 (mkConst crossObsU) boolFalse (mkNatLit 28)

    -- Ep2 ExactWP unsound postcondition forgeries on `bodyUnreachableUB` and `bodyAssertFailTerminate`:
    let emptyLay := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.emptyLayoutTable
    let stepErrTy := mkConst `Miri.Interpreter.StepError
    let unitTy := mkConst ``Unit
    let unitVal := mkConst ``Unit.unit
    let annealStTy := mkConst `LeanMiriSpec.Correspondence.AnnealStepState
    let mkWpCall (act st post onErr : Expr) : Expr :=
      mkAppN (mkConst (ep2CoreNs ++ `AnnealExactWP)) #[annealStTy, stepErrTy, unitTy, act, post, onErr, st]
    let mkRunFuel (hooks steps : Expr) : Expr :=
      mkAppN (mkConst (ep2LmNs ++ `miriRunFuelAction))
        #[mkConst `LeanMiriSpec.Correspondence.AnnealProv,
          mkConst `Miri.Interpreter.LocalLayout,
          unitTy,
          mkConst `LeanMiriSpec.Correspondence.AnnealMachine,
          unitTy,
          mkApp (mkConst `Miri.Interpreter.RuntimePlace) (mkConst `LeanMiriSpec.Correspondence.AnnealProv),
          hooks, unitVal, steps]
    let constFalsePost ← MetaM.run' <| withLocalDeclD `_a unitTy fun a =>
      withLocalDeclD `_s annealStTy fun s => mkLambdaFVars #[a, s] (mkConst ``False)
    let constTruePost ← MetaM.run' <| withLocalDeclD `_a unitTy fun a =>
      withLocalDeclD `_s annealStTy fun s => mkLambdaFVars #[a, s] (mkConst ``True)
    let constFalseErr ← MetaM.run' <| withLocalDeclD `_e stepErrTy fun e =>
      withLocalDeclD `_s annealStTy fun s => mkLambdaFVars #[e, s] (mkConst ``False)
    let mkErrEq (targetErr : Expr) : MetaM Expr :=
      withLocalDeclD `err stepErrTy fun err => withLocalDeclD `_s annealStTy fun s =>
        mkLambdaFVars #[err, s] (mkApp3 (mkConst ``Eq [1]) stepErrTy err targetErr)

    let bodyUb := mkConst (ep2LmNs ++ `bodyUnreachableUB)
    let hooksUb := mkApp2 (mkConst `LeanMiriSpec.Correspondence.annealStepHooks)
      (mkApp (mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir.localDecls) bodyUb) emptyLay
    let initUb := mkApp2 (mkConst (ep2LmNs ++ `initMiriStateForBody)) bodyUb emptyLay
    let actUb := mkRunFuel hooksUb (mkNatLit 3)
    let errUb := mkApp (mkConst `Miri.Interpreter.StepError.undefinedBehavior) (mkStrLit "Unreachable")
    let wpUbBaseTy := mkWpCall actUb initUb constFalsePost (← MetaM.run' <| mkErrEq errUb)
    let wpUbBasePf := mkApp2 (mkConst ``Eq.refl [1]) stepErrTy errUb
    let wpUbForgeTy := mkWpCall actUb initUb constTruePost constFalseErr

    let bodyAbort := mkConst (ep2LmNs ++ `bodyAssertFailTerminate)
    let hooksAbort := mkApp2 (mkConst (ep2LmNs ++ `annealUnwindStepHooks))
      (mkApp (mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir.localDecls) bodyAbort) emptyLay
    let initAbort := mkApp2 (mkConst (ep2LmNs ++ `initMiriStateForBody)) bodyAbort emptyLay
    let actAbort := mkRunFuel hooksAbort (mkNatLit 4)
    let errAbort := mkApp (mkConst `Miri.Interpreter.StepError.termination)
      (mkApp (mkConst `Miri.Concurrency.TerminationInfo.abort) (mkStrLit "unwindTerminate"))
    let wpAbortBaseTy := mkWpCall actAbort initAbort constFalsePost (← MetaM.run' <| mkErrEq errAbort)
    let wpAbortBasePf := mkApp2 (mkConst ``Eq.refl [1]) stepErrTy errAbort
    let wpAbortForgeTy := mkWpCall actAbort initAbort constTruePost constFalseErr

    -- Ep2 Bitprism UB-erasure forgeries (`0 & uninit` and `0 & dead` claiming `.ok 0` instead of `.ub`):
    let slotTy := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot
    let slotNil := mkApp (mkConst ``List.nil [0]) slotTy
    let slotCons (h t : Expr) : Expr := mkApp3 (mkConst ``List.cons [0]) slotTy h t
    let slotUninit := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot.uninit
    let slotDead := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.LocalSlot.dead
    let locsUninit := slotCons slotUninit (slotCons slotUninit slotNil)
    let locsDead := slotCons slotUninit (slotCons slotDead slotNil)
    let scZero := mkApp2 (mkConst `Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk) (mkNatLit 0) (mkNatLit 4)
    let opZero := mkApp2 (mkConst (ep2CoreNs ++ `mkConstScalarOp)) (mkConst (ep2CoreNs ++ `cU32Ty)) scZero
    let projNil := mkApp (mkConst ``List.nil [0]) (mkConst `Trusted.Rustc.V2026_06_01.MirAst.ProjectionElem)
    let opLoc1 := mkApp (mkConst `Trusted.Rustc.V2026_06_01.MirAst.Operand.copy)
      (mkApp2 (mkConst `Trusted.Rustc.V2026_06_01.MirAst.Place.mk) (mkNatLit 1) projNil)
    let emptyMem := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.emptyMemory
    let declNil := mkApp (mkConst ``List.nil [0]) (mkConst `Trusted.Rustc.V2026_06_01.MirAst.LocalDecl)
    let rvResTy := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult
    let rvUb := mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult.ub
    -- Evaluate the SMART constructor's output (not the raw `Rvalue`): the baseline certifies that
    -- `mkBitAndSmartRvalue` PRESERVES `.ub` on `0 & uninit` / `0 & dead`, and the forgery (claiming
    -- the smart constructor erased the UB to `.ok 0`) MUST be kernel-rejected.
    let rvSmartZeroAndLoc1 := mkApp3 (mkConst (ep2CoreNs ++ `mkBitAndSmartRvalue))
      (mkConst (ep2CoreNs ++ `cU32Ty)) opZero opLoc1
    let mkEvalRv (locs : Expr) : Expr :=
      mkAppN (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue)
        #[locs, rvSmartZeroAndLoc1, emptyMem, declNil, emptyLay]
    let mkRvOkZero (locs : Expr) : Expr :=
      mkApp3 (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult.ok)
        (mkApp (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.Value.scalar) scZero) locs emptyMem
    let bpUninitBaseTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRv locsUninit) rvUb
    let bpUninitBasePf := mkApp2 (mkConst ``Eq.refl [1]) rvResTy rvUb
    let bpUninitForgeTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRv locsUninit) (mkRvOkZero locsUninit)
    let bpDeadBaseTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRv locsDead) rvUb
    let bpDeadBasePf := mkApp2 (mkConst ``Eq.refl [1]) rvResTy rvUb
    let bpDeadForgeTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRv locsDead) (mkRvOkZero locsDead)

    -- Ep2 Bitprism `mkBitOrSmartRvalue` & `mkMulSmartRvalue` UB-erasure forgeries on `[.uninit, .uninit]`:
    let scAllOnes := mkApp2 (mkConst `Trusted.Rustc.V2026_06_01.MirAst.ScalarInt.mk)
      (mkApp (mkConst (ep2CoreNs ++ `allOnesMask)) (mkNatLit 4)) (mkNatLit 4)
    let opAllOnes := mkApp2 (mkConst (ep2CoreNs ++ `mkConstScalarOp)) (mkConst (ep2CoreNs ++ `cU32Ty)) scAllOnes
    let rvSmartOrAllOnes := mkApp3 (mkConst (ep2CoreNs ++ `mkBitOrSmartRvalue))
      (mkConst (ep2CoreNs ++ `cU32Ty)) opAllOnes opLoc1
    let rvSmartMulZero := mkApp3 (mkConst (ep2CoreNs ++ `mkMulSmartRvalue))
      (mkConst (ep2CoreNs ++ `cU32Ty)) opLoc1 opZero
    let mkEvalRvOf (rv locs : Expr) : Expr :=
      mkAppN (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue)
        #[locs, rv, emptyMem, declNil, emptyLay]
    let mkRvOkAllOnes (locs : Expr) : Expr :=
      mkApp3 (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult.ok)
        (mkApp (mkConst `Trusted.Rustc.V2026_06_01.MirSemantics.Value.scalar) scAllOnes) locs emptyMem
    let bpOrBaseTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRvOf rvSmartOrAllOnes locsUninit) rvUb
    let bpOrForgeTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRvOf rvSmartOrAllOnes locsUninit) (mkRvOkAllOnes locsUninit)
    let bpMulBaseTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRvOf rvSmartMulZero locsUninit) rvUb
    let bpMulForgeTy := mkApp3 (mkConst ``Eq [1]) rvResTy (mkEvalRvOf rvSmartMulZero locsUninit) (mkRvOkZero locsUninit)

    -- Ep2 `bodyAssertCleanupResume` committed-cleanup-state-on-error forgery (claiming `_0 = none`
    -- on error instead of committed `some 99`):
    let bodyClean := mkConst (ep2LmNs ++ `bodyAssertCleanupResume)
    let hooksClean := mkApp2 (mkConst (ep2LmNs ++ `annealUnwindStepHooks))
      (mkApp (mkConst `Trusted.Rustc.V2026_06_01.MirAst.CapturedMir.localDecls) bodyClean) emptyLay
    let initClean := mkApp2 (mkConst (ep2LmNs ++ `initMiriStateForBody)) bodyClean emptyLay
    let actClean := mkRunFuel hooksClean (mkNatLit 5)
    let optNatTy := mkApp (mkConst ``Option [0]) natTy
    let some99 := mkApp2 (mkConst ``Option.some [0]) natTy (mkNatLit 99)
    let noneNat := mkApp (mkConst ``Option.none [0]) natTy
    let mkCleanErrPred (targetOpt : Expr) : MetaM Expr :=
      withLocalDeclD `_e stepErrTy fun e => withLocalDeclD `s annealStTy fun s =>
        mkLambdaFVars #[e, s] (mkApp3 (mkConst ``Eq [1]) optNatTy
          (mkApp (mkConst (ep2LmNs ++ `activeLocal0Bits)) s) targetOpt)
    let wpCleanBaseTy := mkWpCall actClean initClean constFalsePost (← MetaM.run' <| mkCleanErrPred some99)
    let wpCleanBasePf := mkApp2 (mkConst ``Eq.refl [1]) optNatTy some99
    let wpCleanForgeTy := mkWpCall actClean initClean constFalsePost (← MetaM.run' <| mkCleanErrPred noneNat)
    let wpCleanForgePf := mkApp2 (mkConst ``Eq.refl [1]) optNatTy noneNat

    -- Ep2 Tree Borrows committed-prefix-on-error forgery (`performBorrowAccessRangeLMU` claiming
    -- segment 0 stayed `Frozen` instead of committing `Disabled` before segment 1 faults!):
    let permTy := mkConst `Miri.TreeBorrows.Permission
    let optPermTy := mkApp (mkConst ``Option [0]) permTy
    let someDisabled := mkApp2 (mkConst ``Option.some [0]) permTy (mkConst `Miri.TreeBorrows.Permission.newDisabled)
    let someFrozen := mkApp2 (mkConst ``Option.some [0]) permTy (mkConst `Miri.TreeBorrows.Permission.newFrozen)
    let tag4Val := mkApp3 (mkConst ``Option.getD [0])
      (mkConst `Miri.Memory.BorTag)
      (mkApp (mkConst `Miri.Memory.BorTag.ofUInt64) (mkApp (mkConst ``UInt64.ofNat) (mkNatLit 4)))
      (mkConst `Miri.Memory.BorTag.one)
    let tbAccessRes := mkAppN (mkConst (ep2LmNs ++ `performBorrowAccessRangeLMU))
      #[mkConst (ep2LmNs ++ `twoSegmentCommitPrefixTree),
        mkApp (mkConst `Miri.Memory.ProvenanceExtra.concrete) tag4Val,
        mkConst `Miri.ABI.Size.ZERO,
        mkApp (mkConst `Miri.ABI.Size.ofBytes) (mkApp (mkConst ``UInt64.ofNat) (mkNatLit 16)),
        mkConst `Miri.TreeBorrows.AccessKind.Write,
        mkConst (ep2LmNs ++ `twoSegmentProtectedTags),
        mkConst `Miri.TreeBorrows.Tree.ChildrenVisitMode.VisitChildrenOfAccessed]
    let tbSeg0After := mkApp (mkConst (ep2LmNs ++ `seg0Tag2Perm))
      (mkApp (mkConst `Miri.TreeBorrows.BorrowTree.BorrowTreeAccessResult.tree) tbAccessRes)
    let tbPrefixBaseTy := mkApp3 (mkConst ``Eq [1]) optPermTy tbSeg0After someDisabled
    let tbPrefixBasePf := mkApp2 (mkConst ``Eq.refl [1]) optPermTy someDisabled
    let tbPrefixForgeTy := mkApp3 (mkConst ``Eq [1]) optPermTy tbSeg0After someFrozen
    let tbPrefixForgePf := mkApp2 (mkConst ``Eq.refl [1]) optPermTy someFrozen

    -- Ep2 `releaseProtector` committed-prefix-on-error forgery (claiming `.Released` instead of faulting):
    let protRes := mkApp3 (mkConst (ep2LmNs ++ `releaseProtectorLMU))
      (mkConst (ep2LmNs ++ `twoSegmentCommitPrefixTree))
      tag4Val
      (mkConst (ep2LmNs ++ `twoSegmentProtectedTags))
    let protSeg0After := mkApp (mkConst (ep2LmNs ++ `seg0Tag2Perm))
      (mkApp (mkConst `Miri.TreeBorrows.BorrowTree.ProtectorReleaseResult.tree) protRes)
    let protStatus := mkApp (mkConst `Miri.TreeBorrows.BorrowTree.ProtectorReleaseResult.status) protRes
    let protStatusTy := mkConst `Miri.TreeBorrows.BorrowTree.ProtectorReleaseStatus
    let protBaseTy := mkApp3 (mkConst ``Eq [1]) optPermTy protSeg0After someDisabled
    let protBasePf := mkApp2 (mkConst ``Eq.refl [1]) optPermTy someDisabled
    let protForgeTy := mkApp3 (mkConst ``Eq [1]) protStatusTy protStatus
      (mkConst `Miri.TreeBorrows.BorrowTree.ProtectorReleaseStatus.Released)
    let protForgePf := mkApp2 (mkConst ``Eq.refl [1]) protStatusTy
      (mkConst `Miri.TreeBorrows.BorrowTree.ProtectorReleaseStatus.Released)

    -- Ep2 Endianness layout confusion forgery (`layoutLE64.endian = layoutBE64.endian`):
    let endianTy := mkConst `Miri.ABI.Endian
    let leEndian := mkApp (mkConst `Miri.ABI.TargetDataLayout.endian) (mkConst (ep2LmNs ++ `layoutLE64))
    let beEndian := mkApp (mkConst `Miri.ABI.TargetDataLayout.endian) (mkConst (ep2LmNs ++ `layoutBE64))
    let endianBaseTy := mkApp3 (mkConst ``Eq [1]) endianTy leEndian (mkConst `Miri.ABI.Endian.little)
    let endianBasePf := mkApp2 (mkConst ``Eq.refl [1]) endianTy (mkConst `Miri.ABI.Endian.little)
    let endianForgeTy := mkApp3 (mkConst ``Eq [1]) endianTy leEndian beEndian
    let endianForgePf := mkApp2 (mkConst ``Eq.refl [1]) endianTy leEndian

    let extraForged : List (String × Option Declaration × Declaration) :=
      [ ("ill-typed 0 = 1 sanity control", none,
          thm "zeroEqOne" (mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1))
            (mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0))),
        ("negated lmAuthorityCheck certificate (= false on genuine LM observer)", none,
          thm "lmCheckFalse" (eqFalse (authCheckExpr (mkConst crossObsU))) reflFalse),
        ("Ep1 forged Case 27 3-way agreement: Trusted 27 = LeanMiri 27",
          some (thm "case27LmIsUb" (mkApp3 (mkConst ``Eq [1]) obsTy case27Lm (obsC "ub"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "ub"))),
          thm "case27TrustedEqLm" (mkApp3 (mkConst ``Eq [1]) obsTy case27Tr case27Lm)
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy case27Lm)),
        ("Ep1 forged Case 8 basic=TB agreement: LM(false, 8) = LM(true, 8)",
          some (thm "case8BasicIsOk77"
            (mkApp3 (mkConst ``Eq [1]) obsTy case8Basic (mkApp2 (obsC "okVal") (mkNatLit 77) (mkNatLit 77)))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (mkApp2 (obsC "okVal") (mkNatLit 77) (mkNatLit 77)))),
          thm "case8BasicEqTb" (mkApp3 (mkConst ``Eq [1]) obsTy case8Basic case8Tb)
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy case8Tb)),
        ("Ep1 forged out-of-range cell (false, 28) = .ub",
          some (thm "case28IsInvalid"
            (mkApp3 (mkConst ``Eq [1]) obsTy case28Oor (obsC "invalidOrUnsupported"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "invalidOrUnsupported"))),
          thm "case28ForgedUb"
            (mkApp3 (mkConst ``Eq [1]) obsTy case28Oor (obsC "ub"))
            (mkApp2 (mkConst ``Eq.refl [1]) obsTy (obsC "ub"))),
        ("Ep1 forged malformed codec tuple (7, 0, 0) decodes to some .ub",
          some (thm "badDecodeIsNone"
            (mkApp3 (mkConst ``Eq [1]) optObsTy badDecode (mkApp (mkConst ``Option.none [0]) obsTy))
            (mkApp2 (mkConst ``Eq.refl [1]) optObsTy (mkApp (mkConst ``Option.none [0]) obsTy))),
          thm "badDecodeForgedUb"
            (mkApp3 (mkConst ``Eq [1]) optObsTy badDecode (mkApp2 (mkConst ``Option.some [0]) obsTy (obsC "ub")))
            (mkApp2 (mkConst ``Eq.refl [1]) optObsTy (mkApp2 (mkConst ``Option.some [0]) obsTy (obsC "ub")))),
        ("Ep2 forged unsound ExactWP on bodyUnreachableUB (claiming onError := False)",
          some (thm "wpUbBaseOk" wpUbBaseTy wpUbBasePf),
          thm "wpUbForgedSafe" wpUbForgeTy (mkConst ``True.intro)),
        ("Ep2 forged unsound ExactWP on bodyAssertFailTerminate (claiming onError := False)",
          some (thm "wpAbortBaseOk" wpAbortBaseTy wpAbortBasePf),
          thm "wpAbortForgedSafe" wpAbortForgeTy (mkConst ``True.intro)),
        ("Ep2 forged Bitprism uninit erasure (0 & uninit = .ok 0)",
          some (thm "bpUninitBaseUb" bpUninitBaseTy bpUninitBasePf),
          thm "bpUninitForgedOk" bpUninitForgeTy bpUninitBasePf),
        ("Ep2 forged Bitprism dead-local erasure (0 & dead = .ok 0)",
          some (thm "bpDeadBaseUb" bpDeadBaseTy bpDeadBasePf),
          thm "bpDeadForgedOk" bpDeadForgeTy bpDeadBasePf),
        ("Ep2 forged Bitprism bitOr uninit erasure (allOnes | uninit = .ok allOnes)",
          some (thm "bpOrBaseUb" bpOrBaseTy bpDeadBasePf),
          thm "bpOrForgedOk" bpOrForgeTy bpDeadBasePf),
        ("Ep2 forged Bitprism mul uninit erasure (uninit * 0 = .ok 0)",
          some (thm "bpMulBaseUb" bpMulBaseTy bpDeadBasePf),
          thm "bpMulForgedOk" bpMulForgeTy bpDeadBasePf),
        ("Ep2 forged cleanup-unwind discards committed `_0 = 99` on error",
          some (thm "wpCleanBase99" wpCleanBaseTy wpCleanBasePf),
          thm "wpCleanForgedNone" wpCleanForgeTy wpCleanForgePf),
        ("Ep2 forged Tree Borrows error rollback (claiming seg 0 stayed Frozen instead of Disabled)",
          some (thm "tbPrefixBaseDisabled" tbPrefixBaseTy tbPrefixBasePf),
          thm "tbPrefixForgedFrozen" tbPrefixForgeTy tbPrefixForgePf),
        ("Ep2 forged releaseProtector succeeds (claiming .Released on protected segment-1 conflict)",
          some (thm "protBaseDisabled" protBaseTy protBasePf),
          thm "protForgedReleased" protForgeTy protForgePf),
        ("Ep2 forged LE = BE endianness on TargetDataLayout",
          some (thm "endianLeBase" endianBaseTy endianBasePf),
          thm "endianLeEqBe" endianForgeTy endianForgePf) ]
    for (what, baseOpt, d) in extraForged do
      if let some baseDecl := baseOpt then
        if let some err ← acceptsMsg baseDecl then
          throwError "cross-root negative control VACUOUS: baseline for {what} failed: {err}"
      unless ← rejects d do
        throwError "cross-root negative control FAILED: kernel accepted {what}"
      rejected := rejected + 1

    -- 10. Comprehensive Audits:
    -- 10a. Transitive `Std.Do` & cross-root import isolation of `Anneal.ExactWpAndSmartCtors`!
    let env ← getEnv
    let some coreModIdx := env.getModuleIdx? `Anneal.ExactWpAndSmartCtors
      | throwError "cross-root isolation audit: Anneal.ExactWpAndSmartCtors module not loaded"
    let mut modSeen : NameSet := {}
    let mut modTodo : Array Lean.Name := #[`Anneal.ExactWpAndSmartCtors]
    while !modTodo.isEmpty do
      let m := modTodo.back!
      modTodo := modTodo.pop
      if modSeen.contains m then continue
      modSeen := modSeen.insert m
      if (`Std.Do).isPrefixOf m || (`Std.Tactic.Do).isPrefixOf m || (`Std.WP).isPrefixOf m ||
          (`Lean).isPrefixOf m || (`Miri).isPrefixOf m || (`LeanMiriSpec).isPrefixOf m ||
          (`MiniRustSpec).isPrefixOf m then
        throwError "ExactWpAndSmartCtors transitive import violation: {m} is forbidden!"
      if let some idx := env.getModuleIdx? m then
        if h : idx.toNat < env.header.moduleData.size then
          for imp in env.header.moduleData[idx.toNat].imports do
            if !modSeen.contains imp.module then
              modTodo := modTodo.push imp.module
    let _ := coreModIdx

    -- 10b. Choice-free constructive audit on Ep1 codecs, 3-way permission bijection, and
    --      Ep2 core WP algebraic laws (`[propext, Quot.sound]` ONLY).
    let choiceFreeDecls : List Lean.Name :=
      [ dsNs ++ `crossFramePanicOutcomeCodec, dsNs ++ `crossFramePanicOutcomeCodec_tight,
        dsNs ++ `crossFrameNormalRetCodec, dsNs ++ `crossFrameNormalRetCodec_tight,
        dsNs ++ `unwindAction4Codec, dsNs ++ `lmAuthorityCheck_sound, dsNs ++ `lmAuthorityOfCheck,
        embedName, invEmbedName, blocksName, rtTrustedName, rtMiriName,
        permEqName, miriAllName, permMrName, permCertName,
        ep2CoreNs ++ `exactWP_iff, ep2CoreNs ++ `exactWP_bind, ep2CoreNs ++ `exactWP_seq,
        ep2CoreNs ++ `exactWP_foldl, ep2CoreNs ++ `exactWP_consequence,
        ep2CoreNs ++ `exactWP_negation_refutation, ep2CoreNs ++ `exactWP_veil_frame,
        ep2CoreNs ++ `disjointFieldsBool_sound, ep2CoreNs ++ `bitprism_nested_collapse_o1 ]
    for c in choiceFreeDecls do
      unless env.contains c do throwError "cross-root choice-free audit: {c} missing"
      for a in ← collectAxioms c do
        unless a == ``propext || a == ``Quot.sound do
          throwError "cross-root choice-free audit: {c} must not depend on {a}"

    -- 10c. Non-triviality, safety, and standard-3-axiom purity across ALL added declarations +
    --      ALL 6 workstream modules!
    let isStdAx (a : Lean.Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let rec isTrivialProp : Expr → Bool
      | .forallE _ _ body _ => isTrivialProp body
      | .letE _ _ _ body _ => isTrivialProp body
      | e =>
        if e.isConstOf ``True then true
        else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
        else if e.isAppOfArity ``Iff 2 then e.appFn!.appArg! == e.appArg!
        else false
    let mut crAxioms : NameSet := {}
    for n in added do
      let some ci := env.find? n | throwError "cross-root: {n} missing"
      match ci with
      | .defnInfo v => if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo v => if isTrivialProp v.type then throwError "cross-root: {n} is a trivial theorem"
      | _ => throwError "cross-root: {n} is not a defn or thm"
      for a in ← collectAxioms n do
        if a == ``sorryAx || a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
          throwError "cross-root: {n} depends on forbidden axiom {a}"
        unless isStdAx a do throwError "cross-root: {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a

    let keyThms : List Lean.Name :=
      [ mrNs ++ `mrCrossFramePanicObserve_table, mrNs ++ `ep1_minirust_cross_frame_panic_capstone,
        lmNs ++ `lmCrossFramePanicObserve_table, lmNs ++ `lm_tb_exact_failure_diagnostics,
        lmNs ++ `ep1_lean_miri_cross_frame_panic_capstone,
        dsNs ++ `trustedCrossFramePanicObserve_table,
        dsNs ++ `ep1_cross_frame_ref_and_panic_dual_authority_capstone,
        ep2CoreNs ++ `exactWP_iff, ep2CoreNs ++ `bitprism_nested_collapse_o1,
        ep2CoreNs ++ `bitAnd_zero_uninit_local_preserves_ub,
        ep2CoreNs ++ `mkMemWriteFrame_eq_raw, ep2CoreNs ++ `anneal_veil_frame_multistep_demo,
        ep2CoreNs ++ `ep2_exact_wp_smart_ctors_and_veil_frame_capstone,
        ep2LmNs ++ `allocWriteScalar_disjoint_readScalar_frame_exactWP,
        ep2LmNs ++ `allocEndian_le_vs_be_disjoint_frame_witness,
        ep2LmNs ++ `tbAccessExactWP_iff, ep2LmNs ++ `protectorReleaseExactWP_iff,
        ep2LmNs ++ `tb_access_committed_prefix_on_error_witness,
        ep2LmNs ++ `protector_release_committed_prefix_on_error_witness,
        ep2LmNs ++ `miriStepExactWP_iff, ep2LmNs ++ `miriBodyExactWP_iff,
        ep2LmNs ++ `miriBodyExactWP_unreachable_ub_refutation,
        ep2LmNs ++ `ep2_lean_miri_exact_wp_and_memory_frame_capstone ]
    for n in keyThms do
      let some (.thmInfo v) := env.find? n | throwError "cross-root: required theorem {n} missing"
      if isTrivialProp v.type then throwError "cross-root: theorem {n} is trivial"
      for a in ← collectAxioms n do
        unless isStdAx a do throwError "cross-root: theorem {n} depends on non-standard axiom {a}"
        crAxioms := crAxioms.insert a

    -- 10d. Auditor self-tests: must catch sorryAx / ofReduceBool / trustCompiler and trivia.
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: sorryAx was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: Lean.ofReduceBool was not detected"
    unless !(← collectAxioms ``Lean.trustCompiler).all isStdAx do
      throwError "cross-root self-test: Lean.trustCompiler was not detected"
    let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
    unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq do
      throwError "cross-root self-test: trivial theorem detector failed"

    -- 10e. Transitive constant reachability (`reachFrom`) from `closedMasterSixModuleCapstone`
    --      to REAL MiniRustSpec.Interp, vendored Miri, LeanMiriSpec.MemoryLemmas,
    --      Anneal.ExactWpAndSmartCtors, and unmodified Trusted.Rustc.V2026_06_01.MirSemantics!
    let mut reach : NameSet := {}
    let mut todo : Array Lean.Name := #[masterName]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if reach.contains n then continue
      reach := reach.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !reach.contains d then todo := todo.push d
    let requiredReach : List Lean.Name :=
      [ outName, lmNs ++ `lmCrossFramePanicObserve_out_of_range,
        authName, contractName, crossObs, crossCheck,
        ns ++ `ep1_cross_frame_ref_and_panic_dual_authority_capstone,
        dsNs ++ `mkCrossFramePanicDualBundle,
        `Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle,
        lmNs ++ `lmCrossFramePanicObserve, lmNs ++ `lmCrossFramePanicObserveU,
        lmNs ++ `ep1_lean_miri_cross_frame_panic_capstone,
        mrNs ++ `mrCrossFramePanicObserve, mrNs ++ `ep1_minirust_cross_frame_panic_capstone,
        `MiniRustSpec.Interp.stepM, `MiniRustSpec.Interp.createFrameM,
        `MiniRustSpec.Interp.evalResumeUnwindM, `MiniRustSpec.Interp.evalTerminatorM,
        `MiniRustSpec.Interp.evalPtrOffsetM, `MiniRustSpec.Interp.Permission.transition,
        `MiniRustSpec.Interp.PermissionProt.prevents_deallocation,
        `Miri.Interpreter.Step.step, `Miri.Interpreter.ControlFlow.evalTerminator,
        `Miri.Interpreter.ControlFlow.returnFromCurrentFrame,
        `Miri.Interpreter.ControlFlow.unwindToBlock,
        `Miri.TreeBorrows.performAccess,
        `Miri.TreeBorrows.BorrowTree.performBorrowAccessRange,
        `Miri.TreeBorrows.BorrowTree.releaseProtector,
        `Miri.Memory.Allocation.readScalar, `Miri.Memory.Allocation.writeScalar,
        `Miri.Memory.Allocation.writeUninit, `Miri.Memory.Allocation.copy,
        `Miri.Memory.Allocation.readScalar_int_roundtrip,
        `Miri.Memory.Allocation.writeScalar_spec,
        `Miri.Memory.Allocation.writeUninit_spec,
        ep2CoreNs ++ `AnnealExactWP, ep2CoreNs ++ `mkBitAndSmart,
        ep2CoreNs ++ `mkMemWriteFrame, ep2CoreNs ++ `disjointFieldsBool,
        ep2CoreNs ++ `ep2_exact_wp_smart_ctors_and_veil_frame_capstone,
        ep2LmNs ++ `ep2_lean_miri_exact_wp_and_memory_frame_capstone,
        `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalTerminator,
        `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue,
        `Trusted.Rustc.V2026_06_01.MirSemantics.restoreCallerProtectors,
        `Trusted.Rustc.V2026_06_01.MirSemantics.disableFrameBorrows,
        `Trusted.Rustc.V2026_06_01.MirSemantics.hasFrameDeallocProtectorConflict,
        `Trusted.Rustc.V2026_06_01.MirSemantics.preventsDeallocation ]
    for req in requiredReach do
      unless reach.contains req do
        throwError "cross-root reachability failure: {masterName} does not reach {req}"

    return (added.size, rejected, crAxioms.toArray)

  let ctx : Core.Context :=
    { fileName := "<ep2-cross-frame-exactwp-cross-root>", fileMap := default,
      options := opts, maxHeartbeats := 0 }
  let ((addedCount, rejectedCount, crAxioms), _) ← liftCoreM <| act.toIO ctx { env := baseEnv }
  unless addedCount = 54 && rejectedCount = 30 do
    throwError "cross-root: unexpected counts (added={addedCount}, rejected={rejectedCount})"
  logInfo m!"cross-frame/exact-wp cross-root kernel closure: added {addedCount} declarations, rejected {rejectedCount} forged controls (14 two-sided boolean + 16 baseline-paired value/Prop), verified Std.Do-free ExactWpAndSmartCtors, reached all 6 modules + MiniRust+Miri+MemoryLemmas+Trusted, axioms {crAxioms}"

/-! ## §3. Test Module Axiom Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut theorems : Nat := 0
  for (c, info) in env.constants.map₂.toList do
    for a in ← liftCoreM <| Lean.collectAxioms c do
      if a == ``sorryAx then throwError "test audit failure: {c} uses sorryAx"
      if a == ``Lean.ofReduceBool || a == ``Lean.trustCompiler then
        throwError "test audit failure: {c} uses {a}"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "test audit failure: {c} uses non-standard axiom {a}"
    if (`Anneal.Mir.CrossFramePanicAndExactWpTests).isPrefixOf c && !c.isInternal then
      if let .thmInfo _ := info then theorems := theorems + 1
  if theorems < 16 then
    throwError "test audit is vacuous: only {theorems} §1 test theorems seen"
  logInfo m!"cross-frame/exact-wp test audit: {theorems} §1 theorems (0 sorryAx, 0 ofReduceBool, 0 trustCompiler)"

end Anneal.Mir.CrossFramePanicAndExactWpTests
