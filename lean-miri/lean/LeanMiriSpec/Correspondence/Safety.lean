/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM1_3
import LeanMiriSpec.Correspondence.ProjLM2_2
import LeanMiriSpec.Correspondence.EnumLM2_3
import LeanMiriSpec.Correspondence.SimLM2_2
import LeanMiriSpec.Correspondence.SimLM2_3
import LeanMiriSpec.Correspondence.UnionLM2_4
import LeanMiriSpec.Correspondence.SimLM2_4
import LeanMiriSpec.Correspondence.RefLM3_2
import LeanMiriSpec.Correspondence.SimLM3_2
import LeanMiriSpec.Correspondence.CallLM4_1

/-!
# `LM-4.3`: Whole-Program Safety Equivalence and Multi-Step `RunLoop` Simulation

This module composes the one-step correspondences of `LM-1` … `LM-4.2` into
whole-program statements relating

* Anneal's interaction-tree semantics `mirTree body s` (`ITree.cofix
  (stepMirState body) (.running s)`, `MirSemantics/Machine.lean`), judged by
  `Trusted.ITree.TreeSafe` (`MirNoUBTree`), `Trusted.ITree.ReachesRet`, and
  reachable faults (`Trusted.ITree.FaultNow`); and
* `lean-miri`'s scheduler loop `Miri.Interpreter.RunLoop.iteration` over
  concrete single-threaded `RunLoopHooks` (`annealRunLoopHooks`), packaged as a
  `Miri.OperationalSafety.System` (`miriSystem`).

## Contents

1. Reachability of coalgebraic trees: `CoStep` / `CoReach`; `treeSafe_cofix_iff`
   and `reachesRet_cofix_iff` characterize `TreeSafe` and `ReachesRet` of every
   `ITree.cofix` by its reachable coalgebra states.
2. `miriSystem H`: one transition is one `RunLoop.iteration` (through
   `RunLoop.stepCurrentThread` and `RunLoop.runOnStackEmpty`, `miriIter_eq`)
   that succeeds and leaves a nonempty stack. An iteration failing with `e` is
   terminal with `classifyError e`: `.undefinedBehavior` exactly when
   `RunLoop.reportsUB e`, `.unsupported` for unsupported operations, and
   `.blocked` otherwise (`classifyError_eq_ub_iff`,
   `classifyError_eq_unsupported_iff`, `classifyError_eq_blocked_iff`). An
   iteration that pops the root frame is terminal with `rootPopOutcome H m`:
   `.returned v` for the return operand `v` that `ControlHooks.returnOperand`
   reads from `_0`, or the classified error of that read. Every state can
   progress (`miriSystem_canProgress`, `miriSystem_completeFrom`), so `Safe`
   is "every reachable outcome is a return" (`miriSystem_safe_iff`). The
   iteration after a root pop is the scheduler's thread exit
   (`miriIter_after_root_pop`: `Step.step` reports no frame, `runOnStackEmpty`
   is `.ready`, and `terminateActiveThread` stops with `exit 0`).
3. The step-closed simulation engine. `Lockstep` relates one Anneal step and one
   `lean-miri` core step relative to an invariant `Inv` and a return relation
   `RetRel` (both continue into `Inv`; both return with `RetRel`-related values;
   or both fail with the same three-way `FaultClass`: undefined behavior,
   unsupported, or blocked, `FaultAgrees`). `StepClosedSim` asks every `Inv`
   pair to take a `Lockstep` step. From a `StepClosedSim` and one related pair:
   `step_universal_simulation` (master small-step theorem) and
   `step_faultClass_simulation`, `runLoop_universal_simulation` (master
   multi-step theorem over fuel), `treeSafe_iff_miriSafe` (with
   `treeSafe_imp_miriSafe`, `miriSafe_imp_treeSafe`,
   `mirNoUBTree_iff_miriSafe`), `treeSafe_imp_noUndefinedBehavior`,
   `reachesUB_iff_miriReachesUB`, `reachesFault_iff_miriReachesClass`, and
   `runLoop_ub_iff` (finite-step fault reachability in both directions, per
   failure class), `partialCorrect_iff_annealPostcondition`, and
   `infiniteRun_iff_anneal_forever`. When every fault of the invariant is
   undefined behavior (`UBOnlyFaults`), no unsupported or blocked outcome is
   reachable (`miri_outcomes_of_ubOnly`, `anneal_faults_ub_of_ubOnly`).
4. Run certificates (`MiriPath`, `AnnealPath`, `runLoopFuel` and
   `runAnnealBounded` observations, lassos, `wholeProgram_returns`,
   `wholeProgram_ub`) that turn concrete executions into whole-program facts.
   `runLoopFuel` reports a root pop whose return-operand read fails as
   `.stopped` (`popOutcome`), so its outcomes match `miriSystem`'s terminal
   outcomes one-to-one (`miri_safe_of_runLoopFuel_returned`,
   `miri_outcome_of_runLoopFuel_stopped`).
5. The unconditional closed fragment `InSafeScalarFragment`
   (`WellTypedBodyExt`): `LM-1.1` scalar statements, `LM-1.2` `bool`
   comparisons and `IntToInt` casts, `LM-1.4` immediate moves
   (`WellTypedScalarStmtExt`), and the terminators `Goto`, `Return`,
   `Unreachable`, `SwitchInt` on `bool` / integer discriminants, and `Assert`
   with `UnwindAction::Unreachable` (`WellTypedTerminatorExt`).
   `scalarFragmentExt_stepClosedSim` holds with no per-step hypothesis and
   `scalarFragment_entry` relates the entry states `initMachineState body []`
   and `miriEntryState body` of every body, so the whole-program theorems hold
   from entry for every fragment body, including conditional and diverging
   loops (`scalarFragment_infiniteRun_iff`); every fault of the fragment is
   undefined behavior (`scalarFragmentExt_ubOnly`, `scalarFragment_outcomes`).
6. Bridges from `StepObsRel`, `StepRel`, `StepRelLM2_2` with
   `StepRelStructReturnLM2_2` and scalar `StepRel` returns, `StepRelLM2_3` with
   `StepRelEnumReturnLM2_3`, `StepRelLM2_4` with `StepRelUnionReturnLM2_4`
   (including single-field and Stage-1 `D13a` overlay union returns),
   `StepRelLM3_1`, `StepObsRelLM3_1` (raw-pointer returns, `SwitchInt`),
   `StepRelLM3_2`, `StepObsRelLM3_2`, `StepRelLM3_2Tree`, `StepObsRelLM3_2Tree`,
   and `StepRelMultiFrame` to `Lockstep`, plus multi-step stack-unwinding
   liftings (`MiriUnwindSteps.toMiriPath_ok`, `MiriUnwindSteps.toMiriOutcome_error`);
   the liftings `stepClosedSim_of_stepRelLM2_2`, `stepClosedSim_of_stepRelLM2_3`,
   `stepClosedSim_of_stepRelLM2_3_enumReturn`, `stepClosedSim_of_stepRelLM2_4`,
   `stepClosedSim_of_stepRelLM2_4_unionReturn`, `stepClosedSim_of_stepRelLM3_1`,
   `stepClosedSim_of_stepObsRelLM3_1`, `stepClosedSim_of_stepRelLM3_2`,
   `stepClosedSim_of_stepObsRelLM3_2`, `stepClosedSim_of_stepRelLM3_2Tree`,
   `stepClosedSim_of_stepObsRelLM3_2Tree`, and
   `stepClosedSim_of_stepRelMultiFrame` turn any step-closed fragment of those
   relations into the whole-program theorems; and the entry pair is related by
   every relation (`stateRel_entry`, `stateRelLM2_2_entry`,
   `stateRelLM2_2_entry_env` for every struct environment and allocation
   budget, `stateRelLM2_3_entry` and `stateRelLM2_3_entry_of_budget`,
   `stateRelLM2_4_entry`, `stateRelLM3_1_entry`, `stateRelLM3_2_entry`,
   `stateRelLM3_2Tree_entry`, `treeBorrowsStateRel_entry`,
   `multiFrameStateRel_entry`).

## Correspondence Scope & Divergence Ledger (Stage-1 `Trusted`)

Anneal's side of every statement is Stage-1 `Trusted` `stepMirFn`. Stage-1 turned
several pre-Stage-1 divergences into lockstep steps (listed with the agreed
fragments below, with whole-program witnesses in `MiriDiffWitnesses`), and it
introduced new boundaries (tail calls and the external-call treatment of
`write_bytes`, `rotate_left`, and `rotate_right`), listed with the divergences.

Agreed fragments (kernel-certified per step over Stage-1 `stepMirFn`, lifted here):

* `LM-1.1` scalar statements, `LM-1.2` `bool` comparisons, `IntToInt` casts,
  and `SwitchInt`, `Assert` with `UnwindAction::Unreachable` on unprojected
  `bool` operands, and `LM-1.4` immediate moves, closed and unconditional
  (`InSafeScalarFragment`); `LM-1.3` checked arithmetic (projections of the
  `(T, bool)` result pair), `LM-1.4` storage, and `PlaceMention` per step.
* `LM-2.1` arrays (`Index`, `ConstantIndex`, `Len`, `Repeat`); `LM-2.2` structs
  and tuples with padding; `LM-2.3` multi-variant enums (`Downcast`,
  `SetDiscriminant`, `Discriminant`, `SwitchInt`); `LM-2.4` unions (initialized
  prefixes, uninitialized bytes, active fields `f < n`) and in-bounds array
  `Subslice` projections (`evalProjection_subslice_simulation`,
  `step_subslice_assign_simulation`). Stage-1 upgrades: projected field writes
  into uninitialized unions, sibling (type-punning) field reads, nonzero-field
  writes, narrower projected writes splicing raw-byte overlays
  (`UnionLocalRel.unionOverlay`, `step_union_narrower_field_write_simulation`,
  `step_union_overlay_field_read_simulation`), and union-valued root returns
  (`step_terminator_return_union_lm2_4_simulation`; whole-program
  `MiriDiffWitnesses.w2_union_overlay_type_punning_returns` and
  `MiriDiffWitnesses.w2_union_return`) step in lockstep
  (`step_union_field_write_uninit_simulation`,
  `step_union_type_punning_read_simulation`,
  `step_union_nonzero_field_write_simulation`).
* `LM-3.1` raw pointers (`&raw` on locals and `*ptr` deref reborrows, `*ptr`,
  `PlaceMention(*ptr)`, `StorageDead` use-after-free and revival, `PtrToPtr`,
  `PtrMetadata`, relational comparisons in same-allocation, `< 64` KiB
  cross-local `Eq`/`Ne`, and low `< 2 ^ 32` integer-vs-live regimes,
  `step_mir_lm3_1_state_simulation`), with null `*ptr` reads and writes undefined
  behavior in both machines, as before Stage-1 (`step_deref_read_simulation`,
  `step_deref_write_simulation`; from-entry whole-program
  `MiriDiffWitnesses.w3_deref_null_ptr_read_ub` and
  `MiriDiffWitnesses.w3_deref_null_ptr_write_ub`, modeled on `ub_deref_null_ptr_read`
  and `ub_deref_null_ptr_write`). Stage-1 upgrades of former divergences: `Offset`
  at every primitive stride including zero-count offsets and negative `isize`
  deltas (`step_binOp_offset_stride_simulation`, formerly
  `step_binOp_offset_stride_divergence`); RFC 2582 place-to-pointer reborrows
  `&raw (*p)` of a provenance-free pointer such as null, which step normally in both
  machines (`step_rawPtr_deref_null_simulation`, formerly
  `step_rawPtr_deref_null_divergence`, where Anneal reported undefined behavior;
  from-entry whole-program `MiriDiffWitnesses.w3_rawPtr_deref_null_reborrow_returns`);
  and out-of-bounds reads and writes, misaligned reads and writes, invalid-`bool` /
  invalid-`char` dereferences, and negative out-of-bounds `Offset`, which are
  undefined behavior in both machines (`step_deref_oob_simulation`,
  `step_deref_write_oob_simulation`, `step_deref_misaligned_simulation`,
  `step_deref_invalid_bool_simulation`, `step_binOp_offset_neg_oob_ub_simulation`).
  The from-entry whole programs `MiriDiffWitnesses.w3_deref_oob_ub`,
  `MiriDiffWitnesses.w3_deref_oob_write_ub`, `MiriDiffWitnesses.w3_deref_misaligned_ub`,
  `MiriDiffWitnesses.w3_ptr_offset_neg_before_start_ub`,
  `MiriDiffWitnesses.w3_invalid_bool_ptr_deref_ub`, and
  `MiriDiffWitnesses.w3_ptr_offset_stride_read_returns` cover the former
  `known_anneal_bug` ratchets `ub_ptr_offset_oob_read`, `ub_ptr_offset_oob_write`,
  `ub_unaligned_ptr_read_u32`, `ub_ptr_offset_negative_before_start`,
  `ub_transmute_invalid_bool_through_ptr`, and `pass_ptr_offset_within_array`.
* `LM-3.2` references and the Tree Borrows hierarchy (`step_mir_lm3_2_state_simulation`,
  `step_mir_lm3_2_tree_state_simulation`). Stage-1 upgrades: reborrows of
  dangling safe references and invalid scalars read through safe references are
  undefined behavior in both machines
  (`evalRvalue_reborrow_safeRef_dangling_simulation`,
  `step_safeRef_deref_read_invalid_scalar_simulation`; from-entry whole-program
  `MiriDiffWitnesses.w4_reborrow_dangling_safeRef_ub` and
  `MiriDiffWitnesses.w4_invalid_bool_ref_read_ub`). `LM-3.3` 6-state Tree Borrows
  (`I-10`, `I-11`, protectors, and `StorageDead` protector UB vs. unprotected
  local-borrow disable `sim_lm3_3_storage_dead_and_live_protector_step`) at the
  level of `Tree.NormalTreeState.performAccess` and `TreeBorrowsRel`.
* `LM-4.1` multi-frame `Call` / `Return` with `CallId` protectors and
  `GlobalState.endCall` (`StepRelMultiFrame`), projected `Drop`
  (`step_terminator_drop_projected_simulation`), multi-frame stack unwinding
  across `.continue_` frames to `.cleanup` landing pads or `.unreachable` UB
  (`step_terminator_unwindResume_callee_simulation`,
  `step_terminator_unwindResume_multiFrame_simulation`,
  `step_terminator_call_linked_panic_unwind_simulation`), diverging calls
  (`step_terminator_call_diverging_simulation`), non-constant `FnDef` local calls,
  and `ReifyFnPointer` + indirect `FnPtr` calls
  (`step_stmt_assign_reifyFnPointer_to_indirectFnPtrMovePre_simulation`,
  `step_terminator_call_indirect_fnPtr_move_simulation`), with from-entry
  whole-program witnesses `MiriDiffWitnesses.w5_call_return` (a direct call of a
  linked callee, modeled on the former `known_anneal_bug` ratchet
  `pass_direct_fn_call`), `MiriDiffWitnesses.w5_callee_unreachable_ub`,
  `MiriDiffWitnesses.w5_callee_uninit_return_ub`,
  `MiriDiffWitnesses.w5_unwind_cleanup_returns`,
  `MiriDiffWitnesses.w5_unwind_unreachable_ub`, and
  `MiriDiffWitnesses.w5_indirect_fnPtr_call_returns`.
* `LM-4.2` over Stage-1: `Assume` (`step_intrinsic_assume_simulation`),
  `exact_div` (`call_intrinsic_exact_div_simulation`), bit and saturating integer
  intrinsics (`call_intrinsic_bitops_simulation`), single-element `CopyNonOverlapping`
  between same-typed scalar locals (`step_intrinsic_copyNonOverlapping_stage1_simulation`;
  from-entry `MiriDiffWitnesses.w6_copy_nonoverlapping_disjoint_returns` and
  `MiriDiffWitnesses.w6_copy_nonoverlapping_overlap_ub`)
  and full-local multi-element `copyViaBytes` copies between distinct integer
  locals of equal width
  (`step_intrinsic_copyNonOverlapping_stage1_full_bytes_distinct_int_simulation`;
  from-entry `MiriDiffWitnesses.w6_copy_nonoverlapping_full_bytes_returns`),
  Stage-1 provenance preservation across raw-pointer `CopyNonOverlapping`
  (`stepMirFn_copyNonOverlapping_rawPtr_preserves_provenance`,
  `encodeUntypedValueToBytes_ptr_decode_roundtrip`), and `arith_offset` on
  provenance-carrying raw pointers (`call_intrinsic_arithOffset_stage1_simulation`;
  from-entry `MiriDiffWitnesses.w3_arith_offset_returns` and
  `MiriDiffWitnesses.w3_arith_offset_uninit_ub`).

Kernel-certified divergences (outside every agreed fragment, as of Stage-1). Every
`MiriDiffWitnesses.*` entry below is a whole program run from program entry
(`initMachineState` / `initMachineStateWithCallees` and `miriEntryState`); the
other entries are per-step divergence theorems over Stage-1 `stepMirFn`, most with
concrete real-step instances in the `Wit*` modules:

* `C2` (`cex_end_of_call_foreign_unique_frozen_divergence`): canonical Miri's
  end-of-call protector release performs an implicit read that freezes a
  foreign `Unique` sibling, which Stage-1's `Return` leaves `Unique`
  (`annealStepHooksLM4_1` itself steps in lockstep with Stage-1 here).
* `H4` (`wit_lm4_1_unscoped_borrow_cross_frame_divergence`): Anneal's
  `BorrowEntry.targetLocal` is not scoped by frame, so a callee borrow survives
  the return and aliases caller locals, whereas `Stack.cleanupStackFrame`
  deallocates the callee's locals.
* `H3` (`canonical_drop_no_glue_preserves_local_divergence`,
  `step_terminator_drop_projected_uninit_divergence`): Anneal's `Drop`
  deinitializes an unprojected local and validates projected `Drop` initialization;
  canonical `lean-miri` treats `Drop` without glue as `goToBlock` and keeps the
  value.
* `H1` (`wit_lm4_1_zst_unit_return_simulation`): a zero-sized `_0` returns as
  `.init .unit` in Anneal and as `.live (.immediate .uninit)` in `lean-miri`
  (`RemoveZsts`), a representation difference the relations absorb.
* `LM-4.1`: root-frame `UnwindResume` halts with `.retOutcome .panic` (`TreeSafe`)
  in Stage-1 Anneal while `lean-miri` reports undefined behavior
  (`step_terminator_unwindResume_root_panic_vs_ub_divergence`,
  `MiriDiffWitnesses.w5_unwind_root_panic_vs_ub_divergence`); `UnwindTerminate`
  aborts directly in Stage-1 while canonical `lean-miri` without linked `core`
  reports `.unsupported` (`step_terminator_unwindTerminate_abort_vs_unsupported`);
  Stage-1 ignores `FnAbi.canUnwind` when unwinding out of a nounwind callee
  (`wit_lm4_1_nounwind_callee_unwind_divergence`); and indirect `FnPtr` calls
  across `unsafe`-to-safe or `LayoutCompat`-only (`usize` vs. `u64`) signatures
  fault in Stage-1 while stepping in `lean-miri`
  (`step_terminator_call_indirect_unsafe_to_safe_fnPtr_divergence`,
  `step_terminator_call_indirect_layoutCompat_fnPtr_divergence`).
* `LM-1.4` (`annealStepHooks_storageDead_returnPlace`): `StorageDead(_0)` on
  the return place fails in `lean-miri` (as in rustc) with
  `StackError.cannotMakeReturnPlaceDead`, a blocked (non-UB) outcome, so the
  fragments exclude it (`WellTypedScalarStmtSyn.storageDead` requires a
  local other than `_0`); whole program from entry:
  `MiriDiffWitnesses.w1_storageDead_returnPlace_class_divergence` (`.blocked` in
  `lean-miri`, undefined behavior in Anneal).
* `LM-2.2` (`step_assign_self_copy_memory_struct_divergence`): a memory-backed
  struct self-copy `_1 = copy _1` steps in Anneal and is an overlapping-copy
  undefined behavior in `lean-miri`.
* `LM-2.3`: `SetDiscriminant` on an uninitialized enum
  (`step_setDiscriminant_uninit_divergence`), `Downcast` field reads and
  writes of an inactive or uninitialized variant
  (`evalProjection_downcast_field_initialized_divergence`,
  `step_downcast_field_write_inactive_divergence`,
  `step_downcast_field_write_uninit_divergence`), overlapping enum self-copies
  (`step_enum_self_copy_overlap_divergence`), and copies and returns of
  enums with an uninitialized discriminant
  (`step_enum_copy_move_uninitInd_divergence`,
  `step_return_enum_uninitInd_divergence`).
* `LM-2.4`: inverted and out-of-bounds `Subslice` projections
  (`evalProjection_subslice_inverted_divergence`,
  `evalProjection_subslice_fromEndFalse_oob_divergence`), overlapping union
  self-copies, indirect uninitialized copies, and smaller aggregate overwrites
  (`step_union_self_copy_overlap_divergence`,
  `step_union_copy_indirect_uninit_divergence`,
  `step_union_aggregate_smaller_overwrite_divergence`).
* `LM-3.1`: exposed-provenance casts, cross-local relational ordering, `≥ 64` KiB
  page-wrapping offsets, `≥ 2 ^ 32` scalar-pointer thresholds, and `Offset` on
  disabled live tags (`step_cast_with_exposed_provenance_divergence`,
  `step_rawPtr_cmp_ptr_divergence`,
  `wit_lm3_1_d12_cross_local_order_divergence_real_steps`,
  `wit_lm3_1_d12_page_wrap_eq_divergence_real_steps`,
  `wit_lm3_1_d12_scalar_threshold_divergence_real_steps`,
  `step_binOp_offset_disabled_stride_divergence`).
* `LM-3.2` / `LM-3.3`: reborrows of integer-valued raw pointers
  (`evalRvalue_reborrow_rawPtr_int_divergence`), dangling-reference copies
  validated eagerly by `lean-miri`
  (`step_safeRef_copy_dangling_validity_divergence`,
  `step_safeRef_use_dangling_post_validity_divergence`), and `StorageDead` on a
  local carrying a protected `Cell` borrow
  (`sim_lm3_3_storage_dead_protected_cell_divergence`).
* `LM-4.2` (Stage-1 `Trusted` behavior that `lean-miri/lean/**` cannot change):
  * `CopyNonOverlapping` from an uninitialized source and through a frozen
    borrow (`step_intrinsic_copyNonOverlapping_stage1_uninit_src_divergence`,
    `step_intrinsic_copyNonOverlapping_stage1_perm_divergence`), Stage-1's
    acceptance of zero-count misaligned copies, missing bounds check on distinct
    scalar locals (out-of-bounds acceptance, partial-copy clobbering, cross-type
    copies), and rejection of same-tag disjoint ranges (`WitLM4_2.lean` §6, §7,
    §14, §15), plus the `TyId 80` `lean-miri` encoding boundary on pointer-valued
    `CopyNonOverlapping` (`step_intrinsic_copyNonOverlapping_rawPtr_miri_unsupported`,
    `MiriDiffWitnesses.w6_copy_nonoverlapping_rawPtr_tyId80_boundary`);
  * `arith_offset` on a provenance-free scalar pointer
    (`call_intrinsic_arithOffset_stage1_scalar_ptr_divergence`), and non-canonical
    offset aliases (`core::intrinsics::wrapping_offset`, `std::intrinsics::*`)
    routed by Stage-1 to `MirStepNode.extCall`
    (`stepMirFn_stage1_std_offset_alias_extCall`);
  * the Stage-1 external-call boundary: Stage-1 hands `write_bytes`,
    `rotate_left`, and `rotate_right` to the environment (`MirStepNode.extCall`,
    `stepMirFn_stage1_unmodeled_intrinsic_extCall`,
    `call_intrinsic_rotate_stage1_boundary`), while `lean-miri` executes
    `write_bytes` and fails closed on the rotations. Whole programs:
    `MiriDiffWitnesses.w6_write_bytes_read_extCall_divergence` (from program entry:
    `lean-miri` is `System.Safe` and returns `0xABABABABABABABAB`, while Anneal
    returns the unchanged `42` when the environment returns `()`, and is not
    `TreeSafe` because the environment may unwind into `UnwindAction::Unreachable`),
    `MiriDiffWitnesses.w6_write_bytes_oob_extCall_divergence` (from program entry:
    undefined behavior in `lean-miri`, a normal return of the unchanged `42` in
    Anneal), `MiriDiffWitnesses.w6_write_bytes_extCall_boundary` (from program
    entry: `lean-miri` writes the bytes inline while Anneal returns `()` or reaches
    undefined behavior through the environment), and
    `MiriDiffWitnesses.w6_rotate_left_extCall_boundary` (from entry);
  * the inline intrinsics outside `AnnealIntrinsic` that Stage-1 evaluates and
    `annealCallHooks` fails closed on
    (`step_call_nonAnnealIntrinsic_miri_unsupported`).
* `LM-4.3`:
  * `MiriDiffWitnesses.w1_assert_continue_divergence`: a failing `Assert` with
    `UnwindAction::Continue` panics in Anneal (a defined outcome, so `TreeSafe`
    holds) while `annealTerminatorHooks.assertPanic` reports undefined behavior;
    unwinding `Assert`s are therefore excluded from the closed fragments.
  * `MiriDiffWitnesses.w1_tail_call_class_divergence`: Stage-1 evaluates
    `TerminatorKind.tailCall` and rejects a non-function callee with undefined
    behavior, while `annealTerminatorHooks` does not lower tail calls
    (`.unsupported`).
* Entry states: Anneal's `initLocalsAux` starts every non-argument local dead
  and `miriEntryState` mirrors it, whereas Miri starts locals without storage
  markers live.
* The open `known_anneal_bug` ratchet of `tests/miri-diff/manifest.toml`:
  `panic_explicit_macro` (an explicit `panic!` first calls
  `core::fmt::Arguments::from_str`, an external call that Stage-1 does not
  model, before the diverging `core::panicking::panic_fmt`;
  `MiriDiffWitnesses.w5_panic_explicit_macro_extCall_boundary`, from entry: Stage-1
  reaches the external call and, when the environment returns, panics in
  `panic_fmt`, while `lean-miri` reports `.unsupported`).

The multi-frame witnesses instantiate `annealStepHooksLM4_1` at the body of the
active `lean-miri` frame (`MiriDiffWitnesses.callHooks`), a function of the
`lean-miri` state alone; the `LM-4.1` per-step theorems instantiate it at
Anneal's `activeMirBody`.

Return correspondence: the certified single-frame root-return steps are
`step_terminator_goto_return_simulation` (and its `LM-2.2`, `LM-3.1`, `LM-3.2`
versions) for a sized immediate `_0`, `step_return_scalar_lm2_3_simulation`
(`LM-2.3`) and `step_terminator_return_lm2_4_simulation` (`LM-2.4`, with live
union locals) for a scalar `_0`, `step_terminator_return_rawPtr_lm3_1_simulation`
for a raw-pointer `_0` (`StepObsRelLM3_1`, `PtrRetRel`),
`step_terminator_goto_return_lm3_2_simulation` /
`step_terminator_goto_return_tree_simulation` for a safe-reference `_0`
(`StepObsRelLM3_2`, `StepObsRelLM3_2Tree`, `RefRetRel`), and the `LM-2.2` struct,
`LM-2.3` enum, and `LM-2.4` union (`step_terminator_return_union_lm2_4_simulation`,
`StepRelUnionReturnLM2_4`, `UnionRetRel`) aggregate returns; a zero-sized `()`
root return is certified for the `LM-4.1` interpreter
(`wit_lm4_1_zst_unit_return_simulation`). The union root return excludes an
uninitialized memory-backed `_0` (`hnot_uninit_ind`): `annealControlHooks.returnOperand`
returns the place of an indirect `_0` without reading its bytes, while Stage-1's
`Return` of an uninitialized `_0` is undefined behavior. The memory-backed return
relations (`StructRetRel`, `EnumRetRel`, `UnionRetRel`, and the indirect case of
`MultiFrameRetRel`) relate the returned place to Anneal's value under some
`AnnealMachine` (the return relation sees the returned operand, not the final
memory), so for memory-backed `_0` the whole-program theorems certify the returned
place's shape, and the per-step relations (`StepRelUnionReturnLM2_4.retRootUnion`,
`StepRelStructReturnLM2_2`, `StepRelEnumReturnLM2_3`) certify its contents in the
actual final machine.

Further boundaries of the whole-program agreement:

* `StatementKind.retag` and `StatementKind.deinit` step in Anneal but are not
  lowered to `lean-miri` steps (`annealStepHooks_retag_ne_ok`,
  `annealStepHooks_deinit_ne_ok`), so they are outside every fragment.
* The memory accesses of this `lean-miri` instantiation do not run the
  borrow tracker's access hooks (`annealMemoryCopyHooks_access_ok`): Tree
  Borrows permissions are certified per access through `TreeBorrowsRel`
  (`LM-3.3`), and a `miriSystem` run does not report the permission
  violations that make Anneal fault, Anneal's `TreeBorrowPerm` checks being
  stricter: `MiriDiffWitnesses.w4_disabled_read_divergence` reads through a
  `Disabled` reference, which is undefined behavior in Anneal, while
  `lean-miri`'s whole program is `System.Safe` and returns the read value, so
  `TreeSafe ↔ System.Safe` fails on that body.
* `CastKind.transmute` steps in Anneal but fails closed in `annealCastHooks`
  (`StepError.unsupported`): `MiriDiffWitnesses.w1_transmute_bool_divergence` (a
  valid `bool` transmute returns in Anneal; an invalid one is undefined behavior
  in Anneal; both are `.unsupported` in `lean-miri`). Of the
  `CastKind.pointerCoercion`s, only `ReifyFnPointer` is lowered, and only by the
  `LM-4.1` hooks (`annealCastHooksLM4_1`); `annealCastHooks` fails closed on the
  others.
* A `Call` to a function outside Anneal's `callees` (and, under Stage-1, a call
  to `write_bytes`, `rotate_left`, or `rotate_right`) is an external interaction
  (`MirCallE`, `MirStepNode.extCall`) whose responses (`MirCallAns.returned`,
  `panicked`, `aborted`) `TreeSafe` and `ReachesRet` quantify over; the `lean-miri`
  instantiations here model no external functions, so whole-program call
  agreement is stated for linked callees (`callHooks`), and the Stage-1
  external-call witnesses (`MiriDiffWitnesses.anneal_extCall_boundary`) fix the
  environment's response explicitly. Each response carries a whole `Memory`,
  including `Memory.callStack`: for a call with `UnwindAction::Continue`, a
  `MirCallAns.panicked` answer unwinds through the answer's `callStack`
  (`applyUnwindAction`, `unwindFromCallStack`), so an answer whose `callStack`
  holds a caller frame with `UnwindAction::Unreachable`, a frame the program never
  pushed, faults: every external call with `UnwindAction::Continue` that Anneal
  reaches by silent steps (`AnnealPath`) makes `MirReachesUB` hold and `TreeSafe` fail
  (`MiriDiffWitnesses.anneal_extCall_continue_unwind_ub`; instance
  `MiriDiffWitnesses.w5_panic_explicit_macro_extCall_boundary`).
* `AnnealMachine` has no function-pointer registry, so the `LM-4.1` hooks read
  function pointers from a static table (`annealStepHooksLM4_1 … fnPtrs`,
  `MiriDiffWitnesses.callHooks … fnPtrs`) instead of registering them at
  `ReifyFnPointer` time: the whole-program indirect-call witness
  `MiriDiffWitnesses.w5_indirect_fnPtr_call_returns` seeds that table with the entry
  (`fiveFnPtrEntry`) that Stage-1's `ReifyFnPointer` adds to `Memory.fnPtrs` during
  the run (`MiriDiffWitnesses.indirectCallFive_reify_fnPtrs`).
-/

namespace LeanMiriSpec.Correspondence.Safety

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 1. Reachability of coalgebraic interaction trees (`ITree.cofix`) -/

section Coalgebra

universe u

variable {E : Effect.{u}} {R S : Type u} [FaultEffect E]

/-- One transition of the coalgebra `step`: a silent `.tau`, or a non-fault
visible request answered by any `o`. These are exactly the edges along which
`Trusted.ITree.Reaches` explores `ITree.cofix step`. -/
inductive CoStep (step : S → ITreeF E R S) : S → S → Prop where
  | tau {x y : S} : step x = .tau y → CoStep step x y
  | vis {x : S} {i : E.I} {k : E.O i → S} :
      step x = .vis i k → ¬ FaultEffect.isFault i → (o : E.O i) → CoStep step x (k o)

/-- Finite reachability under `CoStep`. -/
inductive CoReach (step : S → ITreeF E R S) : S → S → Prop where
  | refl (x : S) : CoReach step x x
  | head {x y z : S} : CoStep step x y → CoReach step y z → CoReach step x z

/-- A node that immediately emits a fault request. -/
def IsFaultNode (n : ITreeF E R S) : Prop :=
  ∃ i k, n = .vis i k ∧ FaultEffect.isFault i

namespace CoReach

variable {step : S → ITreeF E R S}

theorem tail {x y z : S} (h : CoReach step x y) (hs : CoStep step y z) : CoReach step x z := by
  induction h with
  | refl x => exact .head hs (.refl z)
  | head h₁ _ ih => exact .head h₁ (ih hs)

theorem trans {x y z : S} (h₁ : CoReach step x y) (h₂ : CoReach step y z) : CoReach step x z := by
  induction h₁ with
  | refl _ => exact h₂
  | head h _ ih => exact .head h (ih h₂)

end CoReach

omit [FaultEffect E] in
theorem observe_cofix_eq (step : S → ITreeF E R S) (x : S) :
    (ITree.cofix step x).observe = (step x).map (ITree.cofix step) :=
  ITree.observe_cofix step x

/-- Every residual reachable from `ITree.cofix step x` is the unfolding of a
`CoReach`-reachable coalgebra state. -/
theorem reaches_cofix_inv {step : S → ITreeF E R S} {x : S} {tr : List (Event E)}
    {u : ITree E R} (h : Reaches (ITree.cofix step x) tr u) :
    ∃ y, CoReach step x y ∧ u = ITree.cofix step y := by
  generalize ht : ITree.cofix step x = t at h
  induction h generalizing x with
  | refl t => exact ⟨x, .refl x, ht.symm⟩
  | tau hobs _ ih =>
    subst ht
    rw [observe_cofix_eq] at hobs
    cases hx : step x with
    | ret r => rw [hx] at hobs; cases hobs
    | tau y =>
      rw [hx] at hobs
      injection hobs with hobs
      obtain ⟨z, hz, rfl⟩ := ih hobs
      exact ⟨z, .head (.tau hx) hz, rfl⟩
    | vis i k => rw [hx] at hobs; cases hobs
  | vis hobs hnf o _ ih =>
    subst ht
    rw [observe_cofix_eq] at hobs
    cases hx : step x with
    | ret r => rw [hx] at hobs; cases hobs
    | tau y => rw [hx] at hobs; cases hobs
    | vis i' k' =>
      rw [hx] at hobs
      cases hobs
      obtain ⟨z, hz, rfl⟩ := ih rfl
      exact ⟨z, .head (.vis hx hnf o) hz, rfl⟩

/-- Silent prefixes of `ITree.cofix step y` are unfoldings of `CoReach`-reachable states. -/
theorem tauStar_cofix_inv {step : S → ITreeF E R S} {y : S} {t' : ITree E R}
    (h : TauStar (ITree.cofix step y) t') :
    ∃ y', CoReach step y y' ∧ t' = ITree.cofix step y' := by
  generalize ht : ITree.cofix step y = t at h
  induction h generalizing y with
  | refl t => exact ⟨y, .refl y, ht.symm⟩
  | step hobs _ ih =>
    subst ht
    rw [observe_cofix_eq] at hobs
    cases hx : step y with
    | ret r => rw [hx] at hobs; cases hobs
    | tau y₁ =>
      rw [hx] at hobs
      injection hobs with hobs
      obtain ⟨z, hz, rfl⟩ := ih hobs
      exact ⟨z, .head (.tau hx) hz, rfl⟩
    | vis i k => rw [hx] at hobs; cases hobs

/-- Every `CoReach`-reachable coalgebra state unfolds to a residual reachable
from `ITree.cofix step x` along some trace. -/
theorem reaches_cofix_of_coReach {step : S → ITreeF E R S} {x y : S}
    (h : CoReach step x y) : ∃ tr, Reaches (ITree.cofix step x) tr (ITree.cofix step y) := by
  induction h with
  | refl x => exact ⟨[], .refl _⟩
  | head hs _ ih =>
    obtain ⟨tr, htr⟩ := ih
    cases hs with
    | tau hx =>
      exact ⟨tr, .tau (by rw [observe_cofix_eq, hx]; rfl) htr⟩
    | vis hx hnf o =>
      exact ⟨⟨_, o⟩ :: tr, .vis (by rw [observe_cofix_eq, hx]; rfl) hnf o htr⟩

/-- `TreeSafe` of a coalgebraic tree is exactly the absence of reachable fault nodes. -/
theorem treeSafe_cofix_iff {step : S → ITreeF E R S} {x : S} :
    TreeSafe (ITree.cofix step x) ↔ ∀ y, CoReach step x y → ¬ IsFaultNode (step y) := by
  constructor
  · rintro hsafe y hy ⟨i, k, hyk, hf⟩
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
    exact hsafe tr _ htr
      ⟨ITree.cofix step y, i, fun o => ITree.cofix step (k o), .refl _,
        by rw [observe_cofix_eq, hyk]; rfl, hf⟩
  · rintro h tr u hr ⟨t', i, k, hts, hobs, hf⟩
    obtain ⟨y, hy, rfl⟩ := reaches_cofix_inv hr
    obtain ⟨y', hy', rfl⟩ := tauStar_cofix_inv hts
    rw [observe_cofix_eq] at hobs
    cases hx : step y' with
    | ret r => rw [hx] at hobs; cases hobs
    | tau z => rw [hx] at hobs; cases hobs
    | vis i' k' =>
      rw [hx] at hobs
      cases hobs
      exact h y' (hy.trans hy') ⟨_, _, hx, hf⟩

/-- A coalgebraic tree reaches `.ret r` iff some reachable state returns `r`. -/
theorem reachesRet_cofix_iff {step : S → ITreeF E R S} {x : S} {r : R} :
    (∃ tr, ReachesRet (ITree.cofix step x) tr r) ↔ ∃ y, CoReach step x y ∧ step y = .ret r := by
  constructor
  · rintro ⟨tr, u, hr, hobs⟩
    obtain ⟨y, hy, rfl⟩ := reaches_cofix_inv hr
    rw [observe_cofix_eq] at hobs
    cases hx : step y with
    | ret r' =>
      rw [hx] at hobs
      injection hobs with hobs
      subst hobs
      exact ⟨y, hy, hx⟩
    | tau z => rw [hx] at hobs; cases hobs
    | vis i k => rw [hx] at hobs; cases hobs
  · rintro ⟨y, hy, hret⟩
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
    exact ⟨tr, _, htr, by rw [observe_cofix_eq, hret]; rfl⟩

end Coalgebra

/-! ## 2. `lean-miri` whole-program semantics over `RunLoop` (`miriSystem`) -/

/-- An Anneal-instantiated `lean-miri` interpreter: one `Step.step` driver
iteration (`coreStep`) and the root frame's return-operand read
(`ControlHooks.returnOperand`, which `ControlFlow.returnFromCurrentFrame` performs
before popping a frame). -/
structure AnnealMiriHooks : Type where
  coreStep : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool
  returnOperand : Unit → AnnealStepState →
    Miri.Interpreter.StepResult AnnealStepState (Miri.Interpreter.Operand AnnealProv)

/-- Package `StepHooks` and `ControlHooks` as an `AnnealMiriHooks` interpreter. -/
def AnnealMiriHooks.ofHooks {PV : Type}
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit PV)
    (control : Miri.Interpreter.ControlHooks AnnealProv Miri.Interpreter.LocalLayout Unit
      AnnealMachine Unit (Miri.Interpreter.Operand AnnealProv)) : AnnealMiriHooks where
  coreStep := Miri.Interpreter.Step.step hooks
  returnOperand := control.returnOperand

/-- The `LM-1` / `LM-3` / `LM-4.2` interpreter (`annealStepHooks`, `annealControlHooks`). -/
def annealMiriHooks (body : CapturedMir) : AnnealMiriHooks :=
  .ofHooks (annealStepHooks body.localDecls body.layouts) annealControlHooks

/-- `RunLoopHooks` of Anneal's single-threaded machine around `H.coreStep`.

The machine has one thread and no I/O: it is never interrupted, the scheduler
always executes a step, and nothing sleeps or polls. When the active stack is
empty the main thread has no pending callback (`StackEmptyPoll.ready`), and
terminating it stops the program with `TerminationInfo.exit 0 true`. -/
def annealRunLoopHooks (H : AnnealMiriHooks) :
    Miri.Interpreter.RunLoopHooks AnnealStepState Unit Unit where
  coreStep := H.coreStep
  takeStackEmptyCallback := fun s => (s, .ok ())
  invokeStackEmptyCallback := fun _ _ s => (s, .ok .ready)
  restoreStackEmptyCallback := fun _ s => (s, .ok ())
  terminateActiveThread := fun _ _ s => (s, .error (.termination (.exit 0 true)))
  interrupted := fun _ => false
  handleAbnormalTermination := fun s => s
  schedule := fun _ s => (s, .ok .executeStep)
  communicate := fun _ => false
  pollAndUnblock := fun _ _ s => (s, .ok ())
  sleep := fun _ _ s => (s, .ok ())

/-- One `RunLoop.iteration` of `lean-miri`'s scheduler on Anneal's machine. -/
def miriIter (H : AnnealMiriHooks) (m : AnnealStepState) :
    Miri.Interpreter.StepResult AnnealStepState Unit :=
  Miri.Interpreter.RunLoop.iteration (annealRunLoopHooks H) () m

/-- The result of `RunLoop.stepCurrentThread` as a function of the core step's result. -/
def stepToIteration :
    Miri.Interpreter.StepResult AnnealStepState Bool →
      Miri.Interpreter.StepResult AnnealStepState Unit
  | (m', .ok true) => (m', .ok ())
  | (m', .ok false) => (m', .error (.termination (.exit 0 true)))
  | (m', .error e) => (m', .error e)

/-- `RunLoop.iteration` (through `RunLoop.stepCurrentThread` and
`RunLoop.runOnStackEmpty`) of `annealRunLoopHooks H`. -/
theorem miriIter_eq (H : AnnealMiriHooks) (m : AnnealStepState) :
    miriIter H m = stepToIteration (H.coreStep () m) := by
  obtain ⟨core, ret⟩ := H
  unfold miriIter Miri.Interpreter.RunLoop.iteration Miri.Interpreter.RunLoop.stepCurrentThread
    Miri.Interpreter.RunLoop.runOnStackEmpty
  dsimp only [annealRunLoopHooks]
  rcases core () m with ⟨m', (e | (_ | _))⟩ <;> rfl

/-- `lean-miri` errors that report an unsupported operation. -/
def isUnsupportedError : Miri.Interpreter.StepError → Bool
  | .unsupported _ => true
  | .termination (.unsupportedInIsolation _) => true
  | .termination (.unsupportedForeignItem _) => true
  | _ => false

/-- Terminal outcomes of `miriSystem`: the root frame's return operand, the
undefined-behavior error, or the unsupported / blocked error. -/
abbrev MiriSafetyOutcome : Type :=
  Miri.OperationalSafety.Outcome (Miri.Interpreter.Operand AnnealProv) Miri.Interpreter.StepError
    Miri.Interpreter.StepError

/-- Classification of a `lean-miri` error: undefined behavior exactly when
`RunLoop.reportsUB` holds, unsupported for `isUnsupportedError`, and blocked
otherwise. -/
def classifyError (e : Miri.Interpreter.StepError) : MiriSafetyOutcome :=
  if Miri.Interpreter.RunLoop.reportsUB e = true then .undefinedBehavior e
  else if isUnsupportedError e = true then .unsupported e
  else .blocked e

theorem classifyError_not_isReturn (e : Miri.Interpreter.StepError) :
    ¬ (classifyError e).isReturn := by
  unfold classifyError
  split
  · exact id
  · split <;> exact id

theorem classifyError_ne_returned (e : Miri.Interpreter.StepError)
    (v : Miri.Interpreter.Operand AnnealProv) : classifyError e ≠ .returned v := by
  intro h
  have := classifyError_not_isReturn e
  rw [h] at this
  exact this trivial

theorem classifyError_eq_ub_iff {e e' : Miri.Interpreter.StepError} :
    classifyError e = .undefinedBehavior e' ↔
      Miri.Interpreter.RunLoop.reportsUB e = true ∧ e' = e := by
  unfold classifyError
  split
  · next h => exact ⟨fun h' => ⟨h, by injection h' with h'; exact h'.symm⟩,
      fun ⟨_, h'⟩ => by rw [h']⟩
  · next h =>
    constructor
    · intro h'; split at h' <;> cases h'
    · intro ⟨h', _⟩; exact absurd h' h

theorem classifyError_eq_unsupported_iff {e e' : Miri.Interpreter.StepError} :
    classifyError e = .unsupported e' ↔
      Miri.Interpreter.RunLoop.reportsUB e = false ∧ isUnsupportedError e = true ∧ e' = e := by
  unfold classifyError
  cases hub : Miri.Interpreter.RunLoop.reportsUB e <;> cases hun : isUnsupportedError e <;>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and, and_false, true_and,
      Miri.OperationalSafety.Outcome.unsupported.injEq, eq_comm]

theorem classifyError_eq_blocked_iff {e e' : Miri.Interpreter.StepError} :
    classifyError e = .blocked e' ↔
      Miri.Interpreter.RunLoop.reportsUB e = false ∧ isUnsupportedError e = false ∧ e' = e := by
  unfold classifyError
  cases hub : Miri.Interpreter.RunLoop.reportsUB e <;> cases hun : isUnsupportedError e <;>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and, and_false, true_and,
      Miri.OperationalSafety.Outcome.blocked.injEq, eq_comm]

/-- Outcome of popping the root frame: `.returned v` for the return operand `v`
that `ControlHooks.returnOperand` reads from the root frame's `_0`, or the
classified error when that read fails. -/
def rootPopOutcome (H : AnnealMiriHooks) (m : AnnealStepState) : MiriSafetyOutcome :=
  match (H.returnOperand () m).2 with
  | .ok v => .returned v
  | .error e => classifyError e

theorem rootPopOutcome_of_ok {H : AnnealMiriHooks} {m : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} (hop : (H.returnOperand () m).2 = .ok v) :
    rootPopOutcome H m = .returned v := by
  unfold rootPopOutcome; rw [hop]

theorem rootPopOutcome_of_error {H : AnnealMiriHooks} {m : AnnealStepState}
    {e : Miri.Interpreter.StepError} (hop : (H.returnOperand () m).2 = .error e) :
    rootPopOutcome H m = classifyError e := by
  unfold rootPopOutcome; rw [hop]

theorem rootPopOutcome_eq_returned_iff {H : AnnealMiriHooks} {m : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} :
    rootPopOutcome H m = .returned v ↔ (H.returnOperand () m).2 = .ok v := by
  unfold rootPopOutcome
  rcases (H.returnOperand () m).2 with e | v'
  · exact ⟨fun h => absurd h (classifyError_ne_returned e v), fun h => by cases h⟩
  · exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩

/-- Whole-program `Miri.OperationalSafety.System` of `lean-miri`'s interpreter on
Anneal's machine.

* A transition is one `RunLoop.iteration` that succeeds and leaves a nonempty
  call stack.
* An iteration that fails with `e` is terminal with outcome `classifyError e`.
* An iteration that succeeds and empties the call stack popped the root frame:
  it is terminal with outcome `rootPopOutcome H m`, i.e. `.returned v` for the
  return operand `v` that `ControlHooks.returnOperand` reads from the root
  frame's `_0`, or the classified error of that read.

Every state can progress (`miriSystem_canProgress`), so `System.CompleteFrom`
holds everywhere and `System.Safe` reduces to "every reachable outcome is a
return" (`miriSystem_safe_iff`). The iteration after a root pop runs
`RunLoop.runOnStackEmpty` and `terminateActiveThread`
(`miriIter_after_root_pop`). -/
def miriSystem (H : AnnealMiriHooks) :
    Miri.OperationalSafety.System AnnealStepState (Miri.Interpreter.Operand AnnealProv)
      Miri.Interpreter.StepError Miri.Interpreter.StepError where
  step m m' := miriIter H m = (m', .ok ()) ∧ m'.stack.frames ≠ #[]
  terminal m o :=
    (∃ e, (miriIter H m).2 = .error e ∧ o = classifyError e) ∨
    ((miriIter H m).2 = .ok () ∧ (miriIter H m).1.stack.frames = #[] ∧ o = rootPopOutcome H m)

section MiriSystemFacts

variable {H : AnnealMiriHooks}

theorem miriSystem_step_iff {m m' : AnnealStepState} :
    (miriSystem H).step m m' ↔ miriIter H m = (m', .ok ()) ∧ m'.stack.frames ≠ #[] :=
  Iff.rfl

/-- A core step that continues with a nonempty stack is a `miriSystem` transition. -/
theorem miriSystem_step_of_coreStep {m m' : AnnealStepState}
    (h : H.coreStep () m = (m', .ok true)) (hne : m'.stack.frames ≠ #[]) :
    (miriSystem H).step m m' :=
  ⟨by rw [miriIter_eq, h]; rfl, hne⟩

theorem miriSystem_step_det {m m₁ m₂ : AnnealStepState}
    (h₁ : (miriSystem H).step m m₁) (h₂ : (miriSystem H).step m m₂) : m₁ = m₂ := by
  have := h₁.1.symm.trans h₂.1
  injection this

theorem miriSystem_not_terminal_of_ok_nonempty {m m' : AnnealStepState}
    (hm : miriIter H m = (m', .ok ())) (hne : m'.stack.frames ≠ #[]) (o : MiriSafetyOutcome) :
    ¬ (miriSystem H).terminal m o := by
  rintro (⟨e, he, _⟩ | ⟨_, hemp, _⟩)
  · rw [hm] at he; cases he
  · rw [hm] at hemp; exact hne hemp

/-- A root pop is terminal with exactly `rootPopOutcome H m`. -/
theorem miriSystem_terminal_of_pop {m m' : AnnealStepState}
    (hm : miriIter H m = (m', .ok ())) (hemp : m'.stack.frames = #[]) (o : MiriSafetyOutcome) :
    (miriSystem H).terminal m o ↔ o = rootPopOutcome H m := by
  constructor
  · rintro (⟨e, he, _⟩ | ⟨_, _, ho⟩)
    · rw [hm] at he; cases he
    · exact ho
  · intro ho
    exact Or.inr ⟨by rw [hm], by rw [hm]; exact hemp, ho⟩

/-- A root pop whose return-operand read succeeds with `v₀` is terminal with
exactly `.returned v₀`. -/
theorem miriSystem_terminal_of_ok_empty {m m' : AnnealStepState}
    {v₀ : Miri.Interpreter.Operand AnnealProv}
    (hm : miriIter H m = (m', .ok ())) (hemp : m'.stack.frames = #[])
    (hop : (H.returnOperand () m).2 = .ok v₀) (o : MiriSafetyOutcome) :
    (miriSystem H).terminal m o ↔ o = .returned v₀ := by
  rw [miriSystem_terminal_of_pop hm hemp, rootPopOutcome_of_ok hop]

theorem miriSystem_terminal_of_error {m m' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (hm : miriIter H m = (m', .error e)) (o : MiriSafetyOutcome) :
    (miriSystem H).terminal m o ↔ o = classifyError e := by
  constructor
  · rintro (⟨e', he', ho⟩ | ⟨hv, _, _⟩)
    · rw [hm] at he'; injection he' with he'; subst he'; exact ho
    · rw [hm] at hv; cases hv
  · intro ho
    exact Or.inl ⟨e, by rw [hm], ho⟩

theorem miriSystem_not_step_of_error {m m' m'' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (hm : miriIter H m = (m', .error e)) : ¬ (miriSystem H).step m m'' := by
  rintro ⟨h, _⟩
  rw [hm] at h; cases h

theorem miriSystem_not_step_of_ok_empty {m m' m'' : AnnealStepState}
    (hm : miriIter H m = (m', .ok ())) (hemp : m'.stack.frames = #[]) :
    ¬ (miriSystem H).step m m'' := by
  rintro ⟨h, hne⟩
  rw [hm] at h
  injection h with h
  subst h
  exact hne hemp

/-- `System.Reaches` composed with a leading transition. -/
theorem miriSystem_reaches_head {a b c : AnnealStepState} (hab : (miriSystem H).step a b)
    (hbc : (miriSystem H).Reaches b c) : (miriSystem H).Reaches a c := by
  induction hbc with
  | refl => exact .step (.refl a) hab
  | step _ hs ih => exact .step ih hs

/-- In the deterministic `miriSystem`, every state reachable from `a` is `a`
itself or reachable from `a`'s unique successor. -/
theorem miriSystem_reaches_cases {a b c : AnnealStepState} (hab : (miriSystem H).step a b)
    (hac : (miriSystem H).Reaches a c) : c = a ∨ (miriSystem H).Reaches b c := by
  induction hac with
  | refl => exact Or.inl rfl
  | step hr hs ih =>
    rcases ih with rfl | hbr
    · exact Or.inr (by rw [miriSystem_step_det hs hab]; exact .refl _)
    · exact Or.inr (.step hbr hs)

/-- A state without a successor reaches only itself. -/
theorem miriSystem_reaches_of_no_step {a c : AnnealStepState}
    (hno : ∀ b, ¬ (miriSystem H).step a b) (hac : (miriSystem H).Reaches a c) : c = a := by
  induction hac with
  | refl => rfl
  | step _ hs ih => subst ih; exact absurd hs (hno _)

/-- **No unclassified dead ends.** Every state of `miriSystem H` can progress:
its `RunLoop.iteration` fails (terminal `classifyError e`), leaves a nonempty
stack (a transition), or pops the root frame (terminal `rootPopOutcome H m`). -/
theorem miriSystem_canProgress (m : AnnealStepState) : (miriSystem H).CanProgress m := by
  rcases h : miriIter H m with ⟨m', (e | u)⟩
  · exact Or.inr ⟨classifyError e, Or.inl ⟨e, by rw [h], rfl⟩⟩
  · cases u
    by_cases hemp : m'.stack.frames = #[]
    · exact Or.inr ⟨rootPopOutcome H m, Or.inr ⟨by rw [h], by rw [h]; exact hemp, rfl⟩⟩
    · exact Or.inl ⟨m', h, hemp⟩

/-- `System.CompleteFrom` holds from every state of `miriSystem H`. -/
theorem miriSystem_completeFrom (m : AnnealStepState) : (miriSystem H).CompleteFrom m :=
  fun m' _ => miriSystem_canProgress m'

/-- `System.Safe` of `miriSystem H` is exactly "every reachable outcome is a return". -/
theorem miriSystem_safe_iff (m : AnnealStepState) :
    (miriSystem H).Safe m ↔ ∀ o, (miriSystem H).ReachesOutcome m o → o.isReturn :=
  ⟨fun h => h.2, fun h => ⟨miriSystem_completeFrom m, h⟩⟩

/-- `miriSystem H` is deterministic in its terminal outcome. -/
theorem miriSystem_terminal_det {m : AnnealStepState} {o₁ o₂ : MiriSafetyOutcome}
    (h₁ : (miriSystem H).terminal m o₁) (h₂ : (miriSystem H).terminal m o₂) : o₁ = o₂ := by
  rcases h : miriIter H m with ⟨m', (e | u)⟩
  · rw [(miriSystem_terminal_of_error h _).1 h₁, (miriSystem_terminal_of_error h _).1 h₂]
  · cases u
    by_cases hemp : m'.stack.frames = #[]
    · rw [(miriSystem_terminal_of_pop h hemp _).1 h₁, (miriSystem_terminal_of_pop h hemp _).1 h₂]
    · exact absurd h₁ (miriSystem_not_terminal_of_ok_nonempty h hemp _)

end MiriSystemFacts

/-! ### The iteration after a root pop

`miriSystem` places the terminal `.returned v` at the iteration that pops the
root frame. The next `RunLoop.iteration` on the emptied stack is the
scheduler's thread-exit path: `Step.step` reports that no frame is left
(`.ok false`), `RunLoop.stepCurrentThread` runs `RunLoop.runOnStackEmpty`
(Anneal's main thread has no pending callback, `.ready`), and
`terminateActiveThread` stops the program with `TerminationInfo.exit 0 true`,
which `RunLoop.reportsUB` does not report as undefined behavior. -/

/-- `RunLoop.runOnStackEmpty` of `annealRunLoopHooks H`: no pending callback. -/
theorem runOnStackEmpty_annealRunLoopHooks (H : AnnealMiriHooks) (m : AnnealStepState) :
    Miri.Interpreter.RunLoop.runOnStackEmpty (annealRunLoopHooks H) () m = (m, .ok .ready) :=
  rfl

/-- `RunLoop.stepCurrentThread` after the core step reports an empty stack runs
`runOnStackEmpty` and then `terminateActiveThread`. -/
theorem stepCurrentThread_of_coreStep_false {H : AnnealMiriHooks} {m m' : AnnealStepState}
    (h : H.coreStep () m = (m', .ok false)) :
    Miri.Interpreter.RunLoop.stepCurrentThread (annealRunLoopHooks H) () m =
      (annealRunLoopHooks H).terminateActiveThread () false m' := by
  obtain ⟨core, ret⟩ := H
  unfold Miri.Interpreter.RunLoop.stepCurrentThread
  dsimp only [annealRunLoopHooks] at h ⊢
  rw [h]
  rfl

theorem miriIter_of_coreStep_false {H : AnnealMiriHooks} {m m' : AnnealStepState}
    (h : H.coreStep () m = (m', .ok false)) :
    miriIter H m = (m', .error (.termination (.exit 0 true))) := by
  rw [miriIter_eq, h]; rfl

/-- `Step.step` on an empty call stack reports that no frame is left. -/
theorem step_of_frames_empty {PV : Type}
    (hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit PV) {m : AnnealStepState} (hemp : m.stack.frames = #[]) :
    Miri.Interpreter.Step.step hooks () m = (m, .ok false) := by
  unfold Miri.Interpreter.Step.step
  have hcur : m.stack.currentFrame? = none := by
    unfold Miri.Interpreter.Stack.currentFrame?
    rw [hemp]; rfl
  rw [hcur]
  rfl

/-- **Post-return thread exit.** If an iteration of `annealMiriHooks body`
leaves an empty stack `m'` (the root frame was popped), the next
`RunLoop.iteration` from `m'` reports no frame left, runs
`RunLoop.runOnStackEmpty` (`.ready`), and terminates the main thread with
`TerminationInfo.exit 0 true`, which is not undefined behavior. -/
theorem miriIter_after_root_pop (body : CapturedMir) {m' : AnnealStepState}
    (hemp : m'.stack.frames = #[]) :
    (annealMiriHooks body).coreStep () m' = (m', .ok false) ∧
    Miri.Interpreter.RunLoop.runOnStackEmpty (annealRunLoopHooks (annealMiriHooks body)) () m' =
      (m', .ok .ready) ∧
    miriIter (annealMiriHooks body) m' = (m', .error (.termination (.exit 0 true))) ∧
    Miri.Interpreter.RunLoop.reportsUB (.termination (.exit 0 true)) = false := by
  have hcore : (annealMiriHooks body).coreStep () m' = (m', .ok false) :=
    step_of_frames_empty _ hemp
  exact ⟨hcore, rfl, miriIter_of_coreStep_false hcore, rfl⟩

/-- The memory-access hooks of this `lean-miri` instantiation
(`annealMemoryCopyHooks`) succeed without effect: no borrow-tracker check runs
on the accesses of `lean-miri`'s memory copies (the ledger's Tree Borrows
boundary). -/
theorem annealMemoryCopyHooks_access_ok :
    (∀ mach memory a b c d e,
      annealMemoryCopyHooks.beforeMemoryRead mach memory a b c d e =
        { memory := memory, hooks := mach, outcome := .ok () }) ∧
    (∀ mach memory a b c d e,
      annealMemoryCopyHooks.beforeMemoryWrite mach memory a b c d e =
        { memory := memory, hooks := mach, outcome := .ok () }) :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-! ## 3. Anneal's MIR coalgebra (`stepMirState`) -/

/-- Some finitely reachable residual of `t` immediately emits the
undefined-behavior fault `FailureKind.ub`. -/
def MirReachesUB (t : ITree MirEffect MirOutcome) : Prop :=
  ∃ tr u k, Reaches t tr u ∧ u.observe = .vis (.inl (.fail .ub)) k

/-- Some finitely reachable residual of `t` immediately fails with kind `k`. -/
def MirReachesFault (t : ITree MirEffect MirOutcome) (k : FailureKind) : Prop :=
  ∃ tr u kont, Reaches t tr u ∧ u.observe = .vis (.inl (.fail k)) kont

theorem mirReachesUB_iff_reachesFault {t : ITree MirEffect MirOutcome} :
    MirReachesUB t ↔ MirReachesFault t .ub :=
  Iff.rfl

theorem mir_isFault_inl (e : MirFailE.I) :
    FaultEffect.isFault (E := MirEffect) (.inl e) := trivial

theorem mir_not_isFault_inr (e : (SumE MirObsE MirCallE).I) :
    ¬ FaultEffect.isFault (E := MirEffect) (.inr e) := by
  rcases e with e | e <;> exact id

theorem isFaultNode_fail (k : FailureKind) :
    IsFaultNode (MirStepNode.fail k) :=
  ⟨.inl (.fail k), PEmpty.elim, rfl, mir_isFault_inl _⟩

theorem not_isFaultNode_emitStep (obs : MirObs) (s' : MachineState) :
    ¬ IsFaultNode (MirStepNode.emitStep obs s') := by
  rintro ⟨i, k, h, hf⟩
  cases obs with
  | silent => cases h
  | event tag =>
    simp only [MirStepNode.emitStep] at h
    cases h
    exact mir_not_isFault_inr _ hf

theorem not_isFaultNode_retNormal (v : Value) (mem : Memory) :
    ¬ IsFaultNode (MirStepNode.retNormal v mem) := by
  rintro ⟨i, k, h, _⟩
  cases h

theorem mirTree_eq_cofix (body : CapturedMir) (s : MachineState) :
    mirTree body s = ITree.cofix (stepMirState body) (.running s) := rfl

section NodeShapes

variable {body : CapturedMir} {s : MachineState}

theorem coStep_of_emitStep {obs : MirObs} {s' : MachineState}
    (hs : stepMirFn body s = .emitStep obs s') :
    CoStep (stepMirState body) (.running s) (.running s') := by
  cases obs with
  | silent => exact .tau hs
  | event tag =>
    have h : stepMirState body (.running s) =
        .vis (.inr (.inl (.emit (.event tag)))) (fun _ => .running s') := hs
    exact .vis h (mir_not_isFault_inr _) PUnit.unit

theorem coStep_emitStep_inv {obs : MirObs} {s' : MachineState} {y : MirExecState}
    (hs : stepMirFn body s = .emitStep obs s')
    (hy : CoStep (stepMirState body) (.running s) y) : y = .running s' := by
  cases hy with
  | tau h =>
    change stepMirFn body s = _ at h
    rw [hs] at h
    cases obs with
    | silent => injection h with h; exact h.symm
    | event tag => simp only [MirStepNode.emitStep] at h; cases h
  | vis h _ o =>
    change stepMirFn body s = _ at h
    rw [hs] at h
    cases obs with
    | silent => cases h
    | event tag =>
      simp only [MirStepNode.emitStep] at h
      cases h
      rfl

theorem not_coStep_retNormal {v : Value} {mem : Memory} {y : MirExecState}
    (hs : stepMirFn body s = .retNormal v mem) :
    ¬ CoStep (stepMirState body) (.running s) y := by
  intro hy
  cases hy with
  | tau h => change stepMirFn body s = _ at h; rw [hs] at h; cases h
  | vis h _ _ => change stepMirFn body s = _ at h; rw [hs] at h; cases h

theorem not_coStep_fail {k : FailureKind} {y : MirExecState}
    (hs : stepMirFn body s = .fail k) :
    ¬ CoStep (stepMirState body) (.running s) y := by
  intro hy
  cases hy with
  | tau h => change stepMirFn body s = _ at h; rw [hs] at h; cases h
  | vis h hnf _ =>
    change stepMirFn body s = _ at h
    rw [hs] at h
    cases h
    exact hnf (mir_isFault_inl _)

end NodeShapes

/-! ## 4. Step-closed simulation engine (`StepClosedSim`) -/

/-- Three-way failure class shared by Anneal's `FailureKind` and `lean-miri`'s
`StepError` classification (`classifyError`): undefined behavior, an
unsupported operation, or a blocked (non-UB, supported) failure. -/
inductive FaultClass : Type where
  | ub
  | unsupported
  | blocked
  deriving DecidableEq, Repr

/-- Failure class of Anneal's fault kind. A fuel bound (`outOfFuel`) is a
blocked failure: it is neither undefined behavior nor an unmodeled construct. -/
def annealFaultClass : FailureKind → FaultClass
  | .ub => .ub
  | .unsupported => .unsupported
  | .outOfFuel => .blocked

theorem annealFaultClass_injective {k k' : FailureKind}
    (h : annealFaultClass k = annealFaultClass k') : k = k' := by
  cases k <;> cases k' <;> first | rfl | cases h

/-- Failure class of a `lean-miri` error, following `classifyError`. -/
def miriErrorClass (e : Miri.Interpreter.StepError) : FaultClass :=
  if Miri.Interpreter.RunLoop.reportsUB e = true then .ub
  else if isUnsupportedError e = true then .unsupported
  else .blocked

/-- Failure class of a terminal outcome (`none` for a return). -/
def outcomeFaultClass : MiriSafetyOutcome → Option FaultClass
  | .returned _ => none
  | .undefinedBehavior _ => some .ub
  | .unsupported _ => some .unsupported
  | .blocked _ => some .blocked

theorem outcomeFaultClass_classifyError (e : Miri.Interpreter.StepError) :
    outcomeFaultClass (classifyError e) = some (miriErrorClass e) := by
  unfold classifyError miriErrorClass
  split
  · rfl
  · split <;> rfl

theorem outcomeFaultClass_eq_none_iff {o : MiriSafetyOutcome} :
    outcomeFaultClass o = none ↔ o.isReturn := by
  cases o <;> exact ⟨fun h => (by first | trivial | cases h), fun h => (by first | rfl | cases h)⟩

theorem outcomeFaultClass_eq_ub_iff {o : MiriSafetyOutcome} :
    outcomeFaultClass o = some .ub ↔ ∃ e, o = .undefinedBehavior e := by
  cases o <;> exact ⟨fun h => (by first | exact ⟨_, rfl⟩ | cases h),
    fun ⟨_, h⟩ => (by first | rfl | cases h)⟩

theorem miriErrorClass_eq_ub_iff {e : Miri.Interpreter.StepError} :
    miriErrorClass e = .ub ↔ Miri.Interpreter.RunLoop.reportsUB e = true := by
  unfold miriErrorClass
  cases Miri.Interpreter.RunLoop.reportsUB e <;> cases isUnsupportedError e <;> decide

/-- Anneal's fault kind and `lean-miri`'s error agree on their three-way failure
class: undefined behavior, unsupported, or blocked. -/
def FaultAgrees (k : FailureKind) (e : Miri.Interpreter.StepError) : Prop :=
  annealFaultClass k = miriErrorClass e

/-- Agreeing faults agree on undefined behavior. -/
theorem FaultAgrees.ub_iff {k : FailureKind} {e : Miri.Interpreter.StepError}
    (h : FaultAgrees k e) : k = .ub ↔ Miri.Interpreter.RunLoop.reportsUB e = true := by
  have h' : annealFaultClass k = miriErrorClass e := h
  rw [← miriErrorClass_eq_ub_iff, ← h']
  exact ⟨fun hk => by subst hk; rfl, fun hk => annealFaultClass_injective (k' := .ub) hk⟩

/-- Agreeing faults agree on unsupported operations. -/
theorem FaultAgrees.unsupported_iff {k : FailureKind} {e : Miri.Interpreter.StepError}
    (h : FaultAgrees k e) :
    k = .unsupported ↔ ∃ e', classifyError e = .unsupported e' := by
  have h' : annealFaultClass k = miriErrorClass e := h
  have hc := outcomeFaultClass_classifyError e
  rw [← h'] at hc
  constructor
  · intro hk
    subst hk
    generalize classifyError e = o at hc ⊢
    cases o <;> first | exact ⟨_, rfl⟩ | cases hc
  · rintro ⟨e', he'⟩
    rw [he'] at hc
    exact annealFaultClass_injective (k' := .unsupported) (by injection hc with hc; exact hc.symm)

/-- The terminal outcome `classifyError e` of an agreeing `lean-miri` failure
has the failure class of Anneal's fault kind. -/
theorem FaultAgrees.outcomeFaultClass {k : FailureKind} {e : Miri.Interpreter.StepError}
    (h : FaultAgrees k e) : outcomeFaultClass (classifyError e) = some (annealFaultClass k) := by
  have h' : annealFaultClass k = miriErrorClass e := h
  rw [outcomeFaultClass_classifyError, h']

/-- One-step lockstep correspondence, relative to a state invariant `Inv` and a
return-value relation `RetRel`, between Anneal's `stepMirFn` result and
`lean-miri`'s core-step result from `m`:

* both continue within the program, Anneal emitting `obs`, to an
  `Inv`-related pair with a nonempty `lean-miri` stack;
* Anneal returns normally from the root frame while `lean-miri` pops it, with
  `RetRel`-related return value and return operand; or
* both fail with the same three-way failure class (`FaultAgrees`: undefined
  behavior, unsupported, or blocked). -/
inductive Lockstep (H : AnnealMiriHooks) (Inv : MachineState → AnnealStepState → Prop)
    (RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop) (m : AnnealStepState) :
    MirStepNode → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  | emitStep (obs : MirObs) (s' : MachineState) (m' : AnnealStepState) :
      Inv s' m' → m'.stack.frames ≠ #[] →
      Lockstep H Inv RetRel m (MirStepNode.emitStep obs s') (m', .ok true)
  | retRoot (retVal : Value) (mem' : Memory) (m' : AnnealStepState)
      (v : Miri.Interpreter.Operand AnnealProv) :
      m'.stack.frames = #[] → (H.returnOperand () m).2 = .ok v → RetRel retVal v →
      Lockstep H Inv RetRel m (MirStepNode.retNormal retVal mem') (m', .ok true)
  | fault (k : FailureKind) (m' : AnnealStepState) (e : Miri.Interpreter.StepError) :
      FaultAgrees k e →
      Lockstep H Inv RetRel m (MirStepNode.fail k) (m', .error e)

/-- `Inv` is closed under single-step lockstep simulation of `stepMirFn body`
and `H.coreStep`: from every `Inv`-related pair, the two machines take one
`Lockstep`-related step. -/
structure StepClosedSim (body : CapturedMir) (H : AnnealMiriHooks)
    (Inv : MachineState → AnnealStepState → Prop)
    (RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop) : Prop where
  lockstep : ∀ s m, Inv s m → Lockstep H Inv RetRel m (stepMirFn body s) (H.coreStep () m)

section Engine

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- The three lockstep shapes, read off through `RunLoop.iteration`. -/
theorem lockstep_shapes (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    (∃ obs s' m', stepMirFn body s = .emitStep obs s' ∧ miriIter H m = (m', .ok ()) ∧
      m'.stack.frames ≠ #[] ∧ Inv s' m') ∨
    (∃ retVal mem m' v, stepMirFn body s = .retNormal retVal mem ∧
      miriIter H m = (m', .ok ()) ∧ m'.stack.frames = #[] ∧
      (H.returnOperand () m).2 = .ok v ∧ RetRel retVal v) ∨
    (∃ k m' e, stepMirFn body s = .fail k ∧ miriIter H m = (m', .error e) ∧ FaultAgrees k e) := by
  have h := hsim.lockstep s m hinv
  generalize ha : stepMirFn body s = aRes at h
  generalize hc : H.coreStep () m = mRes at h
  cases h with
  | emitStep obs s' m' hinv' hne =>
    exact Or.inl ⟨obs, s', m', rfl, by rw [miriIter_eq, hc]; rfl, hne, hinv'⟩
  | retRoot retVal mem m' v hemp hop hrel =>
    exact Or.inr (Or.inl ⟨retVal, mem, m', v, rfl, by rw [miriIter_eq, hc]; rfl, hemp, hop, hrel⟩)
  | fault k m' e hag =>
    exact Or.inr (Or.inr ⟨k, m', e, rfl, by rw [miriIter_eq, hc]; rfl, hag⟩)

/-- Forward simulation: every Anneal coalgebra transition from an `Inv`-related
pair is matched by a `miriSystem` transition to an `Inv`-related pair. -/
theorem forward_step (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) {y : MirExecState}
    (hy : CoStep (stepMirState body) (.running s) y) :
    ∃ s' m', y = .running s' ∧ Inv s' m' ∧ (miriSystem H).step m m' := by
  rcases lockstep_shapes hsim hinv with
    ⟨obs, s', m', ha, hm, hne, hinv'⟩ | ⟨_, _, _, _, ha, _⟩ | ⟨_, _, _, ha, _⟩
  · exact ⟨s', m', coStep_emitStep_inv ha hy, hinv', hm, hne⟩
  · exact absurd hy (not_coStep_retNormal ha)
  · exact absurd hy (not_coStep_fail ha)

/-- Backward simulation: every `miriSystem` transition from an `Inv`-related
pair is matched by an Anneal coalgebra transition to an `Inv`-related pair. -/
theorem backward_step (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m m' : AnnealStepState} (hinv : Inv s m) (hm : (miriSystem H).step m m') :
    ∃ s', CoStep (stepMirState body) (.running s) (.running s') ∧ Inv s' m' := by
  rcases lockstep_shapes hsim hinv with
    ⟨obs, s', m'', ha, hm', _, hinv'⟩ | ⟨_, _, _, _, _, hm', hemp, _⟩ | ⟨_, _, _, _, hm', _⟩
  · have : m'' = m' := by
      have := hm'.symm.trans hm.1
      injection this
    subst this
    exact ⟨s', coStep_of_emitStep ha, hinv'⟩
  · exact absurd hm (miriSystem_not_step_of_ok_empty hm' hemp)
  · exact absurd hm (miriSystem_not_step_of_error hm')

/-- Every Anneal state reachable from an `Inv`-related pair is a running state
`Inv`-related to a `miriSystem`-reachable state. -/
theorem coReach_to_miri (hsim : StepClosedSim body H Inv RetRel) {x y : MirExecState}
    (h : CoReach (stepMirState body) x y) :
    ∀ {s m}, x = .running s → Inv s m →
      ∃ s' m', y = .running s' ∧ Inv s' m' ∧ (miriSystem H).Reaches m m' := by
  induction h with
  | refl x => intro s m hx hinv; exact ⟨s, m, hx, hinv, .refl m⟩
  | head hs _ ih =>
    intro s m hx hinv
    subst hx
    obtain ⟨s₁, m₁, rfl, hinv₁, hstep₁⟩ := forward_step hsim hinv hs
    obtain ⟨s', m', hy, hinv', hr⟩ := ih rfl hinv₁
    exact ⟨s', m', hy, hinv', miriSystem_reaches_head hstep₁ hr⟩

/-- Every `miriSystem` state reachable from an `Inv`-related pair is
`Inv`-related to an Anneal state reachable from the running Anneal state. -/
theorem miri_to_coReach (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m m' : AnnealStepState} (hinv : Inv s m) (h : (miriSystem H).Reaches m m') :
    ∃ s', CoReach (stepMirState body) (.running s) (.running s') ∧ Inv s' m' := by
  induction h with
  | refl => exact ⟨s, .refl _, hinv⟩
  | step _ hstep ih =>
    obtain ⟨s₁, hco, hinv₁⟩ := ih
    obtain ⟨s', hs', hinv'⟩ := backward_step hsim hinv₁ hstep
    exact ⟨s', hco.tail hs', hinv'⟩

/-- **Master small-step theorem.** From an `Inv`-related pair `(s, m)`:

1. every Anneal coalgebra transition is matched by a `miriSystem` transition
   (one `RunLoop.iteration`) to an `Inv`-related pair, and conversely;
2. Anneal faults iff `lean-miri` reaches a non-return terminal outcome;
3. Anneal faults with undefined behavior iff `lean-miri` reports undefined
   behavior (`RunLoop.reportsUB`);
4. Anneal returns normally iff `lean-miri` pops the root frame with a
   `RetRel`-related return operand. -/
theorem step_universal_simulation (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    (∀ y, CoStep (stepMirState body) (.running s) y →
      ∃ s' m', y = .running s' ∧ Inv s' m' ∧ (miriSystem H).step m m') ∧
    (∀ m', (miriSystem H).step m m' →
      ∃ s', CoStep (stepMirState body) (.running s) (.running s') ∧ Inv s' m') ∧
    ((∃ k, stepMirFn body s = .fail k) ↔
      ∃ o, (miriSystem H).terminal m o ∧ ¬ o.isReturn) ∧
    (stepMirFn body s = .fail .ub ↔
      ∃ e, (miriSystem H).terminal m (.undefinedBehavior e)) ∧
    ((∃ retVal mem, stepMirFn body s = .retNormal retVal mem) ↔
      ∃ v, (miriSystem H).terminal m (.returned v)) ∧
    (∀ v, (miriSystem H).terminal m (.returned v) →
      ∃ retVal mem, stepMirFn body s = .retNormal retVal mem ∧ RetRel retVal v) := by
  refine ⟨fun y hy => forward_step hsim hinv hy, fun m' hm => backward_step hsim hinv hm,
    ?_, ?_, ?_, ?_⟩
  · rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, _⟩ |
        ⟨k, m', e, ha, hm, _⟩
    · refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨o, ho, _⟩ => ?_⟩
      · rw [ha] at hk; cases obs <;> cases hk
      · exact absurd ho (miriSystem_not_terminal_of_ok_nonempty hm hne o)
    · refine ⟨fun ⟨k, hk⟩ => ?_, fun ⟨o, ho, hnr⟩ => ?_⟩
      · rw [ha] at hk; cases hk
      · obtain rfl := (miriSystem_terminal_of_ok_empty hm hemp hop o).1 ho
        exact absurd trivial hnr
    · exact ⟨fun _ => ⟨classifyError e, (miriSystem_terminal_of_error hm _).2 rfl,
        classifyError_not_isReturn e⟩, fun _ => ⟨k, ha⟩⟩
  · rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, _⟩ |
        ⟨k, m', e, ha, hm, hag⟩
    · refine ⟨fun hk => ?_, fun ⟨e, he⟩ => ?_⟩
      · rw [ha] at hk; cases obs <;> cases hk
      · exact absurd he (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · refine ⟨fun hk => ?_, fun ⟨e, he⟩ => ?_⟩
      · rw [ha] at hk; cases hk
      · have h := (miriSystem_terminal_of_ok_empty hm hemp hop _).1 he
        cases h
    · rw [ha]
      constructor
      · intro hk
        injection hk with hk
        injection hk with hk
        injection hk with hk
        have hub : Miri.Interpreter.RunLoop.reportsUB e = true := hag.ub_iff.1 hk
        exact ⟨e, (miriSystem_terminal_of_error hm _).2
          (classifyError_eq_ub_iff.2 ⟨hub, rfl⟩).symm⟩
      · rintro ⟨e', he'⟩
        have h := (miriSystem_terminal_of_error hm _).1 he'
        have := (classifyError_eq_ub_iff.1 h.symm).1
        rw [hag.ub_iff.2 this]
  · rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, _⟩ |
        ⟨k, m', e, ha, hm, _⟩
    · refine ⟨fun ⟨_, _, hk⟩ => ?_, fun ⟨v, hv⟩ => ?_⟩
      · rw [ha] at hk; cases obs <;> cases hk
      · exact absurd hv (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · exact ⟨fun _ => ⟨v, (miriSystem_terminal_of_ok_empty hm hemp hop _).2 rfl⟩,
        fun _ => ⟨retVal, mem, ha⟩⟩
    · refine ⟨fun ⟨_, _, hk⟩ => ?_, fun ⟨v, hv⟩ => ?_⟩
      · rw [ha] at hk; cases hk
      · exact absurd ((miriSystem_terminal_of_error hm _).1 hv).symm (classifyError_ne_returned e v)
  · intro v hv
    rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v', ha, hm, hemp, hop, hrel⟩ |
        ⟨k, m', e, ha, hm, _⟩
    · exact absurd hv (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · have h := (miriSystem_terminal_of_ok_empty hm hemp hop _).1 hv
      injection h with h
      subst h
      exact ⟨retVal, mem, ha, hrel⟩
    · exact absurd ((miriSystem_terminal_of_error hm _).1 hv).symm (classifyError_ne_returned e v)

/-- **Small-step failure-class agreement.** From an `Inv`-related pair, Anneal
fails with kind `k` iff `lean-miri` reaches a terminal outcome whose failure
class (`outcomeFaultClass`) is `annealFaultClass k`: undefined behavior,
unsupported operations, and blocked failures correspond one-to-one. -/
theorem step_faultClass_simulation (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) (k : FailureKind) :
    stepMirFn body s = .fail k ↔
      ∃ o, (miriSystem H).terminal m o ∧ outcomeFaultClass o = some (annealFaultClass k) := by
  rcases lockstep_shapes hsim hinv with
    ⟨obs, s', m', ha, hm, hne, _⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, _⟩ |
      ⟨k', m', e, ha, hm, hag⟩
  · refine ⟨fun hk => ?_, fun ⟨o, ho, _⟩ => ?_⟩
    · rw [ha] at hk; cases obs <;> cases hk
    · exact absurd ho (miriSystem_not_terminal_of_ok_nonempty hm hne o)
  · refine ⟨fun hk => ?_, fun ⟨o, ho, hc⟩ => ?_⟩
    · rw [ha] at hk; cases hk
    · obtain rfl := (miriSystem_terminal_of_ok_empty hm hemp hop o).1 ho
      cases hc
  · rw [ha]
    refine ⟨fun hk => ?_, fun ⟨o, ho, hc⟩ => ?_⟩
    · injection hk with hk
      injection hk with hk
      injection hk with hk
      subst hk
      exact ⟨classifyError e, (miriSystem_terminal_of_error hm _).2 rfl, hag.outcomeFaultClass⟩
    · obtain rfl := (miriSystem_terminal_of_error hm _).1 ho
      rw [hag.outcomeFaultClass] at hc
      injection hc with hc
      rw [annealFaultClass_injective hc]

end Engine

/-! ## 5. Whole-program equivalence: `TreeSafe ↔ System.Safe`, UB, partial correctness -/

section WholeProgram

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- Anneal tree safety implies `lean-miri` whole-program safety. -/
theorem treeSafe_imp_miriSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) (hsafe : TreeSafe (mirTree body s)) :
    (miriSystem H).Safe m := by
  rw [mirTree_eq_cofix, treeSafe_cofix_iff] at hsafe
  refine ⟨fun m' hr => ?_, fun o ⟨final, hr, hterm⟩ => ?_⟩
  · obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, m'', _, hm, hne, _⟩ | ⟨_, _, _, v, _, hm, hemp, hop, _⟩ | ⟨k, _, _, ha, _, _⟩
    · exact Or.inl ⟨m'', hm, hne⟩
    · exact Or.inr ⟨.returned v, (miriSystem_terminal_of_ok_empty hm hemp hop _).2 rfl⟩
    · exact absurd (show IsFaultNode (stepMirState body (.running s')) by
        change IsFaultNode (stepMirFn body s'); rw [ha]; exact isFaultNode_fail k) (hsafe _ hco)
  · obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, _, _, hm, hne, _⟩ | ⟨_, _, _, _, _, hm, hemp, hop, _⟩ | ⟨k, _, _, ha, _, _⟩
    · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · obtain rfl := (miriSystem_terminal_of_ok_empty hm hemp hop _).1 hterm
      trivial
    · exact absurd (show IsFaultNode (stepMirState body (.running s')) by
        change IsFaultNode (stepMirFn body s'); rw [ha]; exact isFaultNode_fail k) (hsafe _ hco)

/-- `lean-miri` whole-program safety implies Anneal tree safety. -/
theorem miriSafe_imp_treeSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) (hsafe : (miriSystem H).Safe m) :
    TreeSafe (mirTree body s) := by
  rw [mirTree_eq_cofix, treeSafe_cofix_iff]
  intro y hy hfault
  obtain ⟨s', m', rfl, hinv', hr⟩ := coReach_to_miri hsim hy rfl hinv
  rcases lockstep_shapes hsim hinv' with
    ⟨obs, s'', _, ha, _, _, _⟩ | ⟨retVal, mem, _, _, ha, _⟩ | ⟨_, _, e, _, hm, _⟩
  · exact not_isFaultNode_emitStep obs s'' (ha ▸ hfault)
  · exact not_isFaultNode_retNormal retVal mem (ha ▸ hfault)
  · exact classifyError_not_isReturn e
      (hsafe.2 _ ⟨m', hr, (miriSystem_terminal_of_error hm _).2 rfl⟩)

/-- **Whole-program safety equivalence.** Under a step-closed simulation,
Anneal's all-prefix UB-freedom of `mirTree body s` (`TreeSafe`, i.e.
`MirNoUBTree`) holds iff `lean-miri`'s `RunLoop` semantics is
`Miri.OperationalSafety.System.Safe` from the related state `m`. -/
theorem treeSafe_iff_miriSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    TreeSafe (mirTree body s) ↔ (miriSystem H).Safe m :=
  ⟨treeSafe_imp_miriSafe hsim hinv, miriSafe_imp_treeSafe hsim hinv⟩

/-- `MirNoUBTree` form of `treeSafe_iff_miriSafe`. -/
theorem mirNoUBTree_iff_miriSafe (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    MirNoUBTree (mirTree body s) ↔ (miriSystem H).Safe m :=
  treeSafe_iff_miriSafe hsim hinv

/-- Anneal tree safety implies `lean-miri`'s UB freedom. -/
theorem treeSafe_imp_noUndefinedBehavior (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m)
    (hsafe : TreeSafe (mirTree body s)) : (miriSystem H).NoUndefinedBehavior m :=
  Miri.OperationalSafety.System.noUndefinedBehavior_of_safe _
    (treeSafe_imp_miriSafe hsim hinv hsafe)

/-- **Bidirectional finite-step UB reachability.** Some finitely reachable
residual of `mirTree body s` emits Anneal's undefined-behavior fault iff
`lean-miri` reaches an undefined-behavior outcome. -/
theorem reachesUB_iff_miriReachesUB (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    MirReachesUB (mirTree body s) ↔ ∃ e, (miriSystem H).ReachesOutcome m (.undefinedBehavior e) := by
  rw [mirTree_eq_cofix]
  constructor
  · rintro ⟨tr, u, k, hr, hobs⟩
    obtain ⟨y, hy, rfl⟩ := reaches_cofix_inv hr
    obtain ⟨s', m', rfl, hinv', hreach⟩ := coReach_to_miri hsim hy rfl hinv
    rw [observe_cofix_eq] at hobs
    rcases lockstep_shapes hsim hinv' with
      ⟨obs, _, _, ha, _⟩ | ⟨_, _, _, _, ha, _⟩ | ⟨k', _, e, ha, hm, hag⟩
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs
      cases obs with
      | silent => cases hobs
      | event tag => simp only [MirStepNode.emitStep, ITreeF.map] at hobs; cases hobs
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs; cases hobs
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs
      simp only [MirStepNode.fail, ITreeF.map] at hobs
      cases hobs
      have hub : Miri.Interpreter.RunLoop.reportsUB e = true := hag.ub_iff.1 rfl
      exact ⟨e, m', hreach, (miriSystem_terminal_of_error hm _).2
        (classifyError_eq_ub_iff.2 ⟨hub, rfl⟩).symm⟩
  · rintro ⟨e, final, hr, hterm⟩
    obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, _, _, hm, hne, _⟩ | ⟨_, _, _, _, _, hm, hemp, hop, _⟩ | ⟨k, _, e', ha, hm, hag⟩
    · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · have h := (miriSystem_terminal_of_ok_empty hm hemp hop _).1 hterm
      cases h
    · have h := (miriSystem_terminal_of_error hm _).1 hterm
      have hk : k = .ub := hag.ub_iff.2 (classifyError_eq_ub_iff.1 h.symm).1
      subst hk
      obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hco
      have hobs : (ITree.cofix (stepMirState body) (.running s')).observe =
          .vis (.inl (.fail .ub)) (fun o => ITree.cofix (stepMirState body) (PEmpty.elim o)) := by
        rw [observe_cofix_eq]
        change (stepMirFn body s').map _ = _
        rw [ha]
        rfl
      exact ⟨tr, _, _, htr, hobs⟩

/-- Anneal tree safety excludes reachable Anneal undefined behavior. -/
theorem not_reachesUB_of_treeSafe {t : ITree MirEffect MirOutcome} (h : TreeSafe t) :
    ¬ MirReachesUB t := by
  rintro ⟨tr, u, k, hr, hobs⟩
  exact h tr u hr ⟨u, _, k, .refl u, hobs, mir_isFault_inl _⟩

/-- **Class-wise bidirectional finite-step fault reachability.** Some finitely
reachable residual of `mirTree body s` fails with kind `k` iff `lean-miri`
reaches a terminal outcome of failure class `annealFaultClass k` (undefined
behavior, unsupported, or blocked). -/
theorem reachesFault_iff_miriReachesClass (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) (k : FailureKind) :
    MirReachesFault (mirTree body s) k ↔
      ∃ o, (miriSystem H).ReachesOutcome m o ∧ outcomeFaultClass o = some (annealFaultClass k) := by
  rw [mirTree_eq_cofix]
  constructor
  · rintro ⟨tr, u, kont, hr, hobs⟩
    obtain ⟨y, hy, rfl⟩ := reaches_cofix_inv hr
    obtain ⟨s', m', rfl, hinv', hreach⟩ := coReach_to_miri hsim hy rfl hinv
    rw [observe_cofix_eq] at hobs
    rcases lockstep_shapes hsim hinv' with
      ⟨obs, _, _, ha, _⟩ | ⟨_, _, _, _, ha, _⟩ | ⟨k', _, e, ha, hm, hag⟩
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs
      cases obs with
      | silent => cases hobs
      | event tag => simp only [MirStepNode.emitStep, ITreeF.map] at hobs; cases hobs
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs; cases hobs
    · change (stepMirFn body s').map _ = _ at hobs
      rw [ha] at hobs
      simp only [MirStepNode.fail, ITreeF.map] at hobs
      cases hobs
      exact ⟨classifyError e, ⟨m', hreach, (miriSystem_terminal_of_error hm _).2 rfl⟩,
        hag.outcomeFaultClass⟩
  · rintro ⟨o, ⟨final, hr, hterm⟩, hc⟩
    obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, _, _, hm, hne, _⟩ | ⟨_, _, _, _, _, hm, hemp, hop, _⟩ | ⟨k', _, e', ha, hm, hag⟩
    · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · obtain rfl := (miriSystem_terminal_of_ok_empty hm hemp hop _).1 hterm
      cases hc
    · obtain rfl := (miriSystem_terminal_of_error hm _).1 hterm
      rw [hag.outcomeFaultClass] at hc
      injection hc with hc
      have hk : k' = k := annealFaultClass_injective hc
      subst hk
      obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hco
      have hobs : (ITree.cofix (stepMirState body) (.running s')).observe =
          .vis (.inl (.fail k')) (fun o => ITree.cofix (stepMirState body) (PEmpty.elim o)) := by
        rw [observe_cofix_eq]
        change (stepMirFn body s').map _ = _
        rw [ha]
        rfl
      exact ⟨tr, _, _, htr, hobs⟩

/-- Every fault of `stepMirFn body` from an `Inv`-related state is undefined
behavior (no unsupported construct and no fuel failure is reachable). -/
def UBOnlyFaults (body : CapturedMir) (Inv : MachineState → AnnealStepState → Prop) : Prop :=
  ∀ s m, Inv s m → ∀ k, stepMirFn body s = .fail k → k = .ub

/-- Under a step-closed simulation whose faults are all undefined behavior,
every reachable `lean-miri` outcome is a return or undefined behavior: no
unsupported or blocked outcome is reachable. -/
theorem miri_outcomes_of_ubOnly (hsim : StepClosedSim body H Inv RetRel)
    (hub : UBOnlyFaults body Inv) {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    ∀ o, (miriSystem H).ReachesOutcome m o → o.isReturn ∨ ∃ e, o = .undefinedBehavior e := by
  rintro o ⟨final, hr, hterm⟩
  obtain ⟨s', _, hinv'⟩ := miri_to_coReach hsim hinv hr
  rcases lockstep_shapes hsim hinv' with
    ⟨_, _, _, _, hm, hne, _⟩ | ⟨_, _, _, _, _, hm, hemp, hop, _⟩ | ⟨k, _, e, ha, hm, hag⟩
  · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
  · obtain rfl := (miriSystem_terminal_of_ok_empty hm hemp hop _).1 hterm
    exact Or.inl trivial
  · obtain rfl := (miriSystem_terminal_of_error hm _).1 hterm
    have hk := hub s' final hinv' k ha
    exact Or.inr ⟨e, classifyError_eq_ub_iff.2 ⟨hag.ub_iff.1 hk, rfl⟩⟩

/-- Under a step-closed simulation whose faults are all undefined behavior,
every finitely reachable Anneal fault is undefined behavior. -/
theorem anneal_faults_ub_of_ubOnly (hsim : StepClosedSim body H Inv RetRel)
    (hub : UBOnlyFaults body Inv) {s : MachineState} {m : AnnealStepState} (hinv : Inv s m)
    {k : FailureKind} (hk : MirReachesFault (mirTree body s) k) : k = .ub := by
  obtain ⟨o, ho, hc⟩ := (reachesFault_iff_miriReachesClass hsim hinv k).1 hk
  rcases miri_outcomes_of_ubOnly hsim hub hinv o ho with hret | ⟨e, rfl⟩
  · rw [outcomeFaultClass_eq_none_iff.2 hret] at hc
    cases hc
  · injection hc with hc
    exact annealFaultClass_injective (k' := .ub) hc.symm

/-- **Partial-correctness equivalence.** For postconditions `postA` on Anneal
return values and `postM` on `lean-miri` return operands that agree along
`RetRel`, `lean-miri`'s `System.PartialCorrect` holds iff every Anneal
`ReachesRet` normal return satisfies `postA`. -/
theorem partialCorrect_iff_annealPostcondition (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m)
    (postA : Value → Prop) (postM : Miri.Interpreter.Operand AnnealProv → Prop)
    (hpost : ∀ retVal v, RetRel retVal v → (postA retVal ↔ postM v)) :
    (miriSystem H).PartialCorrect m postM ↔
      ∀ tr retVal mem, ReachesRet (mirTree body s) tr (.normal (retVal, mem)) → postA retVal := by
  constructor
  · intro hpc tr retVal mem hrr
    obtain ⟨y, hy, hret⟩ := reachesRet_cofix_iff.1 ⟨tr, hrr⟩
    obtain ⟨s', m', rfl, hinv', hreach⟩ := coReach_to_miri hsim hy rfl hinv
    change stepMirFn body s' = _ at hret
    rcases lockstep_shapes hsim hinv' with
      ⟨obs, _, _, ha, _⟩ | ⟨retVal', mem', _, v, ha, hm, hemp, hop, hrel⟩ | ⟨_, _, _, ha, _⟩
    · rw [ha] at hret; cases obs <;> cases hret
    · rw [ha] at hret
      injection hret with hret
      injection hret with hret
      injection hret with hrv _
      subst hrv
      exact (hpost retVal' v hrel).2
        (hpc v ⟨m', hreach, (miriSystem_terminal_of_ok_empty hm hemp hop _).2 rfl⟩)
    · rw [ha] at hret; cases hret
  · intro hA v ⟨final, hr, hterm⟩
    obtain ⟨s', hco, hinv'⟩ := miri_to_coReach hsim hinv hr
    rcases lockstep_shapes hsim hinv' with
      ⟨_, _, _, _, hm, hne, _⟩ | ⟨retVal, mem, _, v₀, ha, hm, hemp, hop, hrel⟩ |
        ⟨_, _, e, _, hm, _⟩
    · exact absurd hterm (miriSystem_not_terminal_of_ok_nonempty hm hne _)
    · have h := (miriSystem_terminal_of_ok_empty hm hemp hop _).1 hterm
      injection h with h
      subst v
      obtain ⟨tr, htr⟩ := reachesRet_cofix_iff.2 ⟨MirExecState.running s', hco, ha⟩
      exact (hpost retVal v₀ hrel).1 (hA tr retVal mem (by rw [mirTree_eq_cofix]; exact htr))
    · exact absurd ((miriSystem_terminal_of_error hm _).1 hterm).symm
        (classifyError_ne_returned e v)

end WholeProgram

/-! ## 6. Fuel-indexed multi-step `RunLoop` simulation -/

/-- Outcome of running `lean-miri`'s `RunLoop.iteration` for at most `fuel` iterations. -/
inductive MiriRunLoopOutcome : Type where
  /-- Still running after the iterations performed. -/
  | running (state : AnnealStepState)
  /-- An iteration popped the root frame, whose return operand is `retOperand`. -/
  | returned (state : AnnealStepState) (retOperand : Miri.Interpreter.Operand AnnealProv)
  /-- An iteration stopped with error `err`, or popped the root frame and reading
  its return operand failed with `err`. -/
  | stopped (state : AnnealStepState) (err : Miri.Interpreter.StepError)

/-- The `runLoopFuel` outcome of an iteration that popped the root frame, given
the result of reading the root frame's return operand (as `rootPopOutcome`). -/
def popOutcome (m' : AnnealStepState) :
    Except Miri.Interpreter.StepError (Miri.Interpreter.Operand AnnealProv) → MiriRunLoopOutcome
  | .ok v => .returned m' v
  | .error e => .stopped m' e

/-- Fuel-bounded execution of `lean-miri`'s scheduler loop (`RunLoop.iteration`). -/
def runLoopFuel (H : AnnealMiriHooks) : Nat → AnnealStepState → MiriRunLoopOutcome
  | 0, m => .running m
  | fuel + 1, m =>
    match miriIter H m with
    | (m', .ok _) =>
      if m'.stack.frames.isEmpty then popOutcome m' (H.returnOperand () m).2
      else runLoopFuel H fuel m'
    | (m', .error e) => .stopped m' e

/-- Multi-step lockstep relation between `runAnnealBounded` and `runLoopFuel`. -/
inductive RunLoopRel (Inv : MachineState → AnnealStepState → Prop)
    (RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop) :
    AnnealRunOutcome → MiriRunLoopOutcome → Prop where
  | running (s : MachineState) (m : AnnealStepState) :
      Inv s m → RunLoopRel Inv RetRel (.running s) (.running m)
  | returned (retVal : Value) (mem : Memory) (m : AnnealStepState)
      (v : Miri.Interpreter.Operand AnnealProv) :
      RetRel retVal v → RunLoopRel Inv RetRel (.returned retVal mem) (.returned m v)
  | fault (k : FailureKind) (m : AnnealStepState) (e : Miri.Interpreter.StepError) :
      FaultAgrees k e → RunLoopRel Inv RetRel (.faulted k) (.stopped m e)

theorem array_isEmpty_eq_false {α : Type} {a : Array α} (h : a ≠ #[]) : a.isEmpty = false := by
  rcases a with ⟨l⟩
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem array_isEmpty_eq_true {α : Type} {a : Array α} (h : a = #[]) : a.isEmpty = true := by
  subst h; rfl

section RunLoopSim

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- **Master multi-step theorem.** Under a step-closed simulation, after any
number `fuel` of steps, Anneal's `runAnnealBounded` and `lean-miri`'s
`RunLoop.iteration` loop (`runLoopFuel`) are both running in `Inv`-related
states, both returned with `RetRel`-related values, or both failed with the
same three-way failure class (`FaultAgrees`). -/
theorem runLoop_universal_simulation (hsim : StepClosedSim body H Inv RetRel) (fuel : Nat)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    RunLoopRel Inv RetRel (runAnnealBounded body fuel s) (runLoopFuel H fuel m) := by
  induction fuel generalizing s m with
  | zero => exact .running s m hinv
  | succ fuel ih =>
    rcases lockstep_shapes hsim hinv with
      ⟨obs, s', m', ha, hm, hne, hinv'⟩ | ⟨retVal, mem, m', v, ha, hm, hemp, hop, hrel⟩ |
        ⟨k, m', e, ha, hm, hag⟩
    · rw [runAnnealBounded_emitStep body fuel s s' obs ha]
      unfold runLoopFuel
      rw [hm]
      simp only [array_isEmpty_eq_false hne, Bool.false_eq_true, ↓reduceIte]
      exact ih hinv'
    · have hA : runAnnealBounded body (fuel + 1) s = .returned retVal mem := by
        unfold runAnnealBounded; rw [ha]; rfl
      rw [hA]
      unfold runLoopFuel
      rw [hm]
      simp only [array_isEmpty_eq_true hemp, ↓reduceIte, hop, popOutcome]
      exact .returned retVal mem m' v hrel
    · have hA : runAnnealBounded body (fuel + 1) s = .faulted k := by
        unfold runAnnealBounded; rw [ha]; rfl
      rw [hA]
      unfold runLoopFuel
      rw [hm]
      exact .fault k m' e hag

/-- Fuel-indexed form of bidirectional UB reachability. -/
theorem runLoop_ub_iff (hsim : StepClosedSim body H Inv RetRel) (fuel : Nat)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    runAnnealBounded body fuel s = .faulted .ub ↔
      ∃ m' e, runLoopFuel H fuel m = .stopped m' e ∧ Miri.Interpreter.RunLoop.reportsUB e = true := by
  have h := runLoop_universal_simulation hsim fuel hinv
  generalize runAnnealBounded body fuel s = aOut at h
  generalize runLoopFuel H fuel m = mOut at h
  cases h with
  | running => exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => (by cases h)⟩
  | returned => exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => (by cases h)⟩
  | fault k m' e hag =>
    constructor
    · intro h
      injection h with h
      exact ⟨m', e, rfl, hag.ub_iff.1 h⟩
    · rintro ⟨_, _, h, hub⟩
      injection h with h₁ h₂
      subst h₁ h₂
      rw [hag.ub_iff.2 hub]

/-- Fuel-indexed normal-return correspondence. -/
theorem runLoop_returned_iff (hsim : StepClosedSim body H Inv RetRel) (fuel : Nat)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m) :
    (∃ retVal mem, runAnnealBounded body fuel s = .returned retVal mem) ↔
      ∃ m' v, runLoopFuel H fuel m = .returned m' v := by
  have h := runLoop_universal_simulation hsim fuel hinv
  generalize runAnnealBounded body fuel s = aOut at h
  generalize runLoopFuel H fuel m = mOut at h
  cases h with
  | running => exact ⟨fun ⟨_, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => (by cases h)⟩
  | returned retVal mem m' v _ => exact ⟨fun _ => ⟨m', v, rfl⟩, fun _ => ⟨retVal, mem, rfl⟩⟩
  | fault => exact ⟨fun ⟨_, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => (by cases h)⟩

end RunLoopSim

/-! ## 7. Run certificates for concrete whole-program witnesses -/

theorem array_eq_empty_of_isEmpty {α : Type} {a : Array α} (h : a.isEmpty = true) : a = #[] := by
  rcases a with ⟨l⟩
  cases l with
  | nil => rfl
  | cons _ _ => cases h

theorem array_ne_empty_of_isEmpty {α : Type} {a : Array α} (h : a.isEmpty = false) :
    a ≠ #[] := by
  intro h'
  subst h'
  cases h

section MiriCertificates

variable {H : AnnealMiriHooks}

/-- Continue a `runLoopFuel` outcome that is still running. -/
def MiriRunLoopOutcome.andThen (o : MiriRunLoopOutcome)
    (f : AnnealStepState → MiriRunLoopOutcome) : MiriRunLoopOutcome :=
  match o with
  | .running m => f m
  | o => o

theorem runLoopFuel_succ (H : AnnealMiriHooks) (n : Nat) (m : AnnealStepState) :
    runLoopFuel H (n + 1) m =
      match miriIter H m with
      | (m', .ok _) =>
        if m'.stack.frames.isEmpty then popOutcome m' (H.returnOperand () m).2
        else runLoopFuel H n m'
      | (m', .error e) => .stopped m' e := rfl

theorem runLoopFuel_add (H : AnnealMiriHooks) (n k : Nat) (m : AnnealStepState) :
    runLoopFuel H (n + k) m = (runLoopFuel H n m).andThen (runLoopFuel H k) := by
  induction n generalizing m with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega, runLoopFuel_succ, runLoopFuel_succ]
    rcases miriIter H m with ⟨m', (e | _)⟩
    · rfl
    · dsimp only
      cases hemp : m'.stack.frames.isEmpty
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih m'
      · simp only [↓reduceIte]
        cases (H.returnOperand () m).2 <;> rfl

theorem runLoopFuel_running_of_le {n N : Nat} {m m' : AnnealStepState}
    (h : runLoopFuel H N m = .running m') (hle : n ≤ N) :
    ∃ x, runLoopFuel H n m = .running x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [runLoopFuel_add] at h
  cases hn : runLoopFuel H n m with
  | running x => exact ⟨x, rfl⟩
  | returned _ _ => rw [hn] at h; cases h
  | stopped _ _ => rw [hn] at h; cases h

/-- Leading `RunLoop` transition of a `runLoopFuel` run. -/
theorem runLoopFuel_of_step {n : Nat} {m m₁ : AnnealStepState}
    (h : H.coreStep () m = (m₁, .ok true)) (hne : m₁.stack.frames ≠ #[]) :
    runLoopFuel H (n + 1) m = runLoopFuel H n m₁ := by
  rw [runLoopFuel_succ, miriIter_eq, h]
  simp only [stepToIteration, array_isEmpty_eq_false hne, Bool.false_eq_true, ↓reduceIte]

/-- A `RunLoop` run that pops the root frame with return operand `v` is
`System.Safe`, reaches `.returned v`, and reaches no other outcome. -/
theorem miri_safe_of_runLoopFuel_returned {N : Nat} {m m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} (h : runLoopFuel H N m = .returned m' v) :
    (miriSystem H).Safe m ∧ (miriSystem H).ReachesOutcome m (.returned v) ∧
      ∀ o, (miriSystem H).ReachesOutcome m o → o = .returned v := by
  induction N generalizing m with
  | zero => cases h
  | succ N ih =>
    rw [runLoopFuel_succ] at h
    rcases hm : miriIter H m with ⟨m₁, (e | u)⟩
    · rw [hm] at h; cases h
    · cases u
      rw [hm] at h
      dsimp only at h
      cases hemp : m₁.stack.frames.isEmpty
      · rw [hemp] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hne := array_ne_empty_of_isEmpty hemp
        have hstep : (miriSystem H).step m m₁ := ⟨hm, hne⟩
        obtain ⟨hsafe, hreach, huniq⟩ := ih h
        have hcases : ∀ c, (miriSystem H).Reaches m c → c = m ∨ (miriSystem H).Reaches m₁ c :=
          fun c hc => miriSystem_reaches_cases hstep hc
        refine ⟨⟨fun c hc => ?_, fun o ⟨f, hf, ht⟩ => ?_⟩, ?_, fun o ⟨f, hf, ht⟩ => ?_⟩
        · rcases hcases c hc with rfl | hc'
          · exact Or.inl ⟨m₁, hstep⟩
          · exact hsafe.1 c hc'
        · rcases hcases f hf with rfl | hf'
          · exact absurd ht (miriSystem_not_terminal_of_ok_nonempty hm hne o)
          · exact hsafe.2 o ⟨f, hf', ht⟩
        · obtain ⟨f, hf, ht⟩ := hreach
          exact ⟨f, miriSystem_reaches_head hstep hf, ht⟩
        · rcases hcases f hf with rfl | hf'
          · exact absurd ht (miriSystem_not_terminal_of_ok_nonempty hm hne o)
          · exact huniq o ⟨f, hf', ht⟩
      · rw [hemp] at h
        simp only [↓reduceIte] at h
        have hv : (H.returnOperand () m).2 = .ok v := by
          generalize (H.returnOperand () m).2 = r at h ⊢
          cases r with
          | ok v' =>
            simp only [popOutcome, MiriRunLoopOutcome.returned.injEq] at h
            rw [h.2]
          | error e => simp [popOutcome] at h
        have hemp' := array_eq_empty_of_isEmpty hemp
        have hno : ∀ b, ¬ (miriSystem H).step m b := fun b => miriSystem_not_step_of_ok_empty hm hemp'
        have hterm : ∀ o, (miriSystem H).terminal m o ↔ o = .returned v :=
          miriSystem_terminal_of_ok_empty hm hemp' hv
        refine ⟨⟨fun c hc => ?_, fun o ⟨f, hf, ht⟩ => ?_⟩, ⟨m, .refl m, (hterm _).2 rfl⟩,
          fun o ⟨f, hf, ht⟩ => ?_⟩
        · rw [miriSystem_reaches_of_no_step hno hc]
          exact Or.inr ⟨.returned v, (hterm _).2 rfl⟩
        · rw [miriSystem_reaches_of_no_step hno hf] at ht
          rw [(hterm o).1 ht]
          trivial
        · rw [miriSystem_reaches_of_no_step hno hf] at ht
          exact (hterm o).1 ht

/-- A `RunLoop` run that stops with error `e` reaches `classifyError e` and is not safe. -/
theorem miri_outcome_of_runLoopFuel_stopped {N : Nat} {m m' : AnnealStepState}
    {e : Miri.Interpreter.StepError} (h : runLoopFuel H N m = .stopped m' e) :
    (miriSystem H).ReachesOutcome m (classifyError e) ∧ ¬ (miriSystem H).Safe m := by
  have hreach : (miriSystem H).ReachesOutcome m (classifyError e) := by
    induction N generalizing m with
    | zero => cases h
    | succ N ih =>
      rw [runLoopFuel_succ] at h
      rcases hm : miriIter H m with ⟨m₁, (e' | u)⟩
      · rw [hm] at h
        injection h with _ he
        subst he
        exact ⟨m, .refl m, (miriSystem_terminal_of_error hm _).2 rfl⟩
      · cases u
        rw [hm] at h
        dsimp only at h
        cases hemp : m₁.stack.frames.isEmpty
        · rw [hemp] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨f, hf, ht⟩ := ih h
          exact ⟨f, miriSystem_reaches_head ⟨hm, array_ne_empty_of_isEmpty hemp⟩ hf, ht⟩
        · rw [hemp] at h
          simp only [↓reduceIte] at h
          have hemp' := array_eq_empty_of_isEmpty hemp
          rcases hr : (H.returnOperand () m).2 with e'' | v
          · rw [hr] at h
            simp only [popOutcome, MiriRunLoopOutcome.stopped.injEq] at h
            obtain ⟨_, rfl⟩ := h
            exact ⟨m, .refl m,
              (miriSystem_terminal_of_pop hm hemp' _).2 (rootPopOutcome_of_error hr).symm⟩
          · rw [hr] at h
            simp [popOutcome] at h
  exact ⟨hreach, fun hsafe => classifyError_not_isReturn e (hsafe.2 _ hreach)⟩

/-- A `RunLoop` loop that keeps running forever has an infinite run, is
`System.Safe`, and reaches no terminal outcome. -/
theorem miri_infinite_of_forall_running {m : AnnealStepState}
    (h : ∀ n, ∃ m', runLoopFuel H n m = .running m') :
    Miri.OperationalSafety.InfiniteRun (miriSystem H) m ∧ (miriSystem H).Safe m ∧
      ∀ o, ¬ (miriSystem H).ReachesOutcome m o := by
  let run : Nat → AnnealStepState := fun n =>
    match runLoopFuel H n m with
    | .running x => x
    | _ => m
  have hrun : ∀ n, runLoopFuel H n m = .running (run n) := by
    intro n
    obtain ⟨x, hx⟩ := h n
    simp only [run, hx]
  have hstep : ∀ n, (miriSystem H).step (run n) (run (n + 1)) := by
    intro n
    have h1 := hrun (n + 1)
    rw [runLoopFuel_add, hrun n] at h1
    change runLoopFuel H 1 (run n) = _ at h1
    rw [runLoopFuel_succ] at h1
    rcases hm : miriIter H (run n) with ⟨x, (e | u)⟩
    · rw [hm] at h1; cases h1
    · cases u
      rw [hm] at h1
      dsimp only at h1
      cases hemp : x.stack.frames.isEmpty
      · rw [hemp] at h1
        simp only [Bool.false_eq_true, ↓reduceIte] at h1
        change MiriRunLoopOutcome.running x = _ at h1
        injection h1 with h1
        subst h1
        exact ⟨hm, array_ne_empty_of_isEmpty hemp⟩
      · rw [hemp] at h1
        simp only [↓reduceIte] at h1
        generalize (H.returnOperand () (run n)).2 = r at h1
        cases r <;> simp [popOutcome] at h1
  have h0 : run 0 = m := rfl
  have hreach : ∀ c, (miriSystem H).Reaches m c → ∃ n, c = run n := by
    intro c hc
    induction hc with
    | refl => exact ⟨0, h0.symm⟩
    | step _ hs ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, miriSystem_step_det hs (hstep n)⟩
  have hnoterm : ∀ n o, ¬ (miriSystem H).terminal (run n) o :=
    fun n o => miriSystem_not_terminal_of_ok_nonempty (hstep n).1 (hstep n).2 o
  refine ⟨⟨run, h0, hstep⟩, ⟨fun c hc => ?_, fun o ⟨f, hf, ht⟩ => ?_⟩, fun o ⟨f, hf, ht⟩ => ?_⟩
  · obtain ⟨n, rfl⟩ := hreach c hc
    exact Or.inl ⟨_, hstep n⟩
  · obtain ⟨n, rfl⟩ := hreach f hf
    exact absurd ht (hnoterm n o)
  · obtain ⟨n, rfl⟩ := hreach f hf
    exact hnoterm n o ht

/-- Lasso certificate: a run prefix reaching `mp` followed by a nonempty cycle
`mp → … → mp` runs forever. -/
theorem forall_running_of_lasso {p c : Nat} {m mp : AnnealStepState}
    (hp : runLoopFuel H p m = .running mp) (hc : runLoopFuel H (c + 1) mp = .running mp) :
    ∀ n, ∃ m', runLoopFuel H n m = .running m' := by
  have hcyc : ∀ q, ∃ x, runLoopFuel H q mp = .running x := by
    intro q
    induction q using Nat.strongRecOn with
    | ind q ih =>
      by_cases hq : q ≤ c + 1
      · exact runLoopFuel_running_of_le hc hq
      · obtain ⟨q', rfl⟩ : ∃ q', q = (c + 1) + q' := ⟨q - (c + 1), by omega⟩
        rw [runLoopFuel_add, hc]
        exact ih q' (by omega)
  intro n
  by_cases hn : n ≤ p
  · exact runLoopFuel_running_of_le hp hn
  · obtain ⟨q, rfl⟩ : ∃ q, n = p + q := ⟨n - p, by omega⟩
    rw [runLoopFuel_add, hp]
    exact hcyc q


/-! ### Decidable observations of `runLoopFuel` -/

/-- Unsigned bits of an immediate scalar return operand of `sizeBytes` bytes. -/
def operandScalarBits? (sizeBytes : Nat) : Miri.Interpreter.Operand AnnealProv → Option Nat
  | .immediate (.scalar s) =>
    match s.toScalarInt with
    | .ok sc =>
      if sc.size == Miri.ABI.Size.ofBytes (UInt64.ofNat sizeBytes) then some sc.data.toNat
      else none
    | .error _ => none
  | _ => none

/-- The return operand of a `runLoopFuel` outcome that popped the root frame. -/
def MiriRunLoopOutcome.returnedOperand? :
    MiriRunLoopOutcome → Option (Miri.Interpreter.Operand AnnealProv)
  | .returned _ v => some v
  | _ => none

/-- The error of a `runLoopFuel` outcome that stopped. -/
def MiriRunLoopOutcome.stoppedError? : MiriRunLoopOutcome → Option Miri.Interpreter.StepError
  | .stopped _ e => some e
  | _ => none

/-- Whether a `runLoopFuel` outcome is still running. -/
def MiriRunLoopOutcome.isRunning : MiriRunLoopOutcome → Bool
  | .running _ => true
  | _ => false

theorem MiriRunLoopOutcome.returnedOperand?_spec {o : MiriRunLoopOutcome}
    {v : Miri.Interpreter.Operand AnnealProv} (h : o.returnedOperand? = some v) :
    ∃ m', o = .returned m' v := by
  cases o with
  | running _ => cases h
  | returned m' v' => injection h with h; subst h; exact ⟨m', rfl⟩
  | stopped _ _ => cases h

theorem MiriRunLoopOutcome.stoppedError?_spec {o : MiriRunLoopOutcome}
    {e : Miri.Interpreter.StepError} (h : o.stoppedError? = some e) :
    ∃ m', o = .stopped m' e := by
  cases o with
  | running _ => cases h
  | returned _ _ => cases h
  | stopped m' e' => injection h with h; subst h; exact ⟨m', rfl⟩

theorem MiriRunLoopOutcome.isRunning_spec {o : MiriRunLoopOutcome} (h : o.isRunning = true) :
    ∃ m', o = .running m' := by
  cases o with
  | running m' => exact ⟨m', rfl⟩
  | returned _ _ => cases h
  | stopped _ _ => cases h

/-- Whole-program certificate from a decidable observation of a returning run. -/
theorem miri_returns_of_observation {H : AnnealMiriHooks} {N : Nat} {m : AnnealStepState}
    {post : Miri.Interpreter.Operand AnnealProv → Prop}
    (h : ∃ v, (runLoopFuel H N m).returnedOperand? = some v ∧ post v) :
    (miriSystem H).Safe m ∧ (miriSystem H).PartialCorrect m post ∧
      ∃ v, (miriSystem H).ReachesOutcome m (.returned v) ∧ post v := by
  obtain ⟨v, hv, hpost⟩ := h
  obtain ⟨m', hm'⟩ := MiriRunLoopOutcome.returnedOperand?_spec hv
  obtain ⟨hsafe, hreach, huniq⟩ := miri_safe_of_runLoopFuel_returned hm'
  refine ⟨hsafe, fun v' hv' => ?_, v, hreach, hpost⟩
  have := huniq _ hv'
  injection this with this
  rw [this]
  exact hpost

/-- Whole-program certificate from a decidable observation of an undefined-behavior stop. -/
theorem miri_ub_of_observation {H : AnnealMiriHooks} {N : Nat} {m : AnnealStepState}
    {e : Miri.Interpreter.StepError} (h : (runLoopFuel H N m).stoppedError? = some e)
    (hub : Miri.Interpreter.RunLoop.reportsUB e = true) :
    (miriSystem H).ReachesOutcome m (.undefinedBehavior e) ∧ ¬ (miriSystem H).Safe m := by
  obtain ⟨m', hm'⟩ := MiriRunLoopOutcome.stoppedError?_spec h
  have h' := miri_outcome_of_runLoopFuel_stopped hm'
  rw [classifyError_eq_ub_iff.2 ⟨hub, rfl⟩] at h'
  exact h'

/-- A `Step.step` iteration that continues (`.ok true`) started from a nonempty stack. -/
theorem frames_ne_of_step_ok_true {PV : Type}
    {hooks : Miri.Interpreter.StepHooks AnnealProv Miri.Interpreter.LocalLayout Unit AnnealMachine
      Unit PV}
    {m m' : AnnealStepState} (h : Miri.Interpreter.Step.step hooks () m = (m', .ok true)) :
    m.stack.frames ≠ #[] := by
  intro hemp
  have hcur : m.stack.currentFrame? = none := by
    unfold Miri.Interpreter.Stack.currentFrame?
    rw [hemp]
    rfl
  unfold Miri.Interpreter.Step.step at h
  rw [hcur] at h
  cases h

/-- A finite `lean-miri` execution path of core steps that keep a nonempty stack. -/
inductive MiriPath (H : AnnealMiriHooks) : AnnealStepState → AnnealStepState → Prop where
  | refl (m : AnnealStepState) : MiriPath H m m
  | step {m m₁ m₂ : AnnealStepState} :
      H.coreStep () m = (m₁, .ok true) → m₁.stack.frames ≠ #[] → MiriPath H m₁ m₂ →
      MiriPath H m m₂

theorem MiriPath.run_shift {m m' : AnnealStepState} (h : MiriPath H m m') :
    ∃ n, ∀ k, runLoopFuel H (n + k) m = runLoopFuel H k m' := by
  induction h with
  | refl m => exact ⟨0, fun k => by rw [Nat.zero_add]⟩
  | step hc hne _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun k => by rw [show n + 1 + k = (n + k) + 1 by omega, runLoopFuel_of_step hc hne, hn]⟩

theorem runLoopFuel_one_returned {m m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} (hret : H.coreStep () m = (m', .ok true))
    (hemp : m'.stack.frames = #[]) (hop : (H.returnOperand () m).2 = .ok v) :
    runLoopFuel H 1 m = .returned m' v := by
  rw [runLoopFuel_succ, miriIter_eq, hret]
  simp only [stepToIteration, array_isEmpty_eq_true hemp, ↓reduceIte, hop, popOutcome]

theorem runLoopFuel_one_stopped {m m' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (herr : H.coreStep () m = (m', .error e)) : runLoopFuel H 1 m = .stopped m' e := by
  rw [runLoopFuel_succ, miriIter_eq, herr]
  rfl

theorem MiriPath.trans {a b c : AnnealStepState} (h₁ : MiriPath H a b) (h₂ : MiriPath H b c) :
    MiriPath H a c := by
  induction h₁ with
  | refl _ => exact h₂
  | step hc hne _ ih => exact .step hc hne (ih h₂)

/-- A `MiriPath` is a `miriSystem` reachability path. -/
theorem MiriPath.reaches {m m' : AnnealStepState} (h : MiriPath H m m') :
    (miriSystem H).Reaches m m' := by
  induction h with
  | refl m => exact .refl m
  | step hc hne _ ih =>
    exact miriSystem_reaches_head ⟨by rw [miriIter_eq, hc]; rfl, hne⟩ ih

/-- A running `runLoopFuel` prefix is a `MiriPath`. -/
theorem MiriPath.of_runLoopFuel {n : Nat} {m m' : AnnealStepState}
    (h : runLoopFuel H n m = .running m') : MiriPath H m m' := by
  induction n generalizing m with
  | zero => cases h; exact .refl _
  | succ n ih =>
    rw [runLoopFuel_succ, miriIter_eq] at h
    rcases hc : H.coreStep () m with ⟨m₁, (e | (_ | _))⟩ <;> rw [hc] at h
    · cases h
    · cases h
    · simp only [stepToIteration] at h
      cases hemp : m₁.stack.frames.isEmpty
      · rw [hemp] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact .step hc (array_ne_empty_of_isEmpty hemp) (ih h)
      · rw [hemp] at h
        simp only [↓reduceIte] at h
        generalize (H.returnOperand () m).2 = r at h
        cases r <;> simp [popOutcome] at h

/-- Whole-program certificate: a path to a root-frame return with operand `v`. -/
theorem miri_safe_of_path_return {m mₙ m' : AnnealStepState}
    {v : Miri.Interpreter.Operand AnnealProv} (hpath : MiriPath H m mₙ)
    (hret : H.coreStep () mₙ = (m', .ok true)) (hemp : m'.stack.frames = #[])
    (hop : (H.returnOperand () mₙ).2 = .ok v) :
    (miriSystem H).Safe m ∧ (miriSystem H).ReachesOutcome m (.returned v) ∧
      ∀ o, (miriSystem H).ReachesOutcome m o → o = .returned v := by
  obtain ⟨n, hn⟩ := hpath.run_shift
  apply miri_safe_of_runLoopFuel_returned (N := n + 1) (m' := m')
  rw [hn 1, runLoopFuel_succ, miriIter_eq, hret]
  simp only [stepToIteration, array_isEmpty_eq_true hemp, ↓reduceIte, hop, popOutcome]

/-- Whole-program certificate: a path to a core step failing with `e`. -/
theorem miri_outcome_of_path_error {m mₙ m' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (hpath : MiriPath H m mₙ) (herr : H.coreStep () mₙ = (m', .error e)) :
    (miriSystem H).ReachesOutcome m (classifyError e) ∧ ¬ (miriSystem H).Safe m := by
  obtain ⟨n, hn⟩ := hpath.run_shift
  apply miri_outcome_of_runLoopFuel_stopped (N := n + 1) (m' := m')
  rw [hn 1, runLoopFuel_succ, miriIter_eq, herr]
  rfl

end MiriCertificates

section AnnealCertificates

variable {body : CapturedMir}

/-- A finite Anneal execution path through `emitStep` transitions. -/
inductive AnnealPath (body : CapturedMir) : MachineState → MachineState → Prop where
  | refl (s : MachineState) : AnnealPath body s s
  | step {s s₁ s₂ : MachineState} (obs : MirObs) :
      stepMirFn body s = .emitStep obs s₁ → AnnealPath body s₁ s₂ → AnnealPath body s s₂

theorem AnnealPath.coReach {s s' : MachineState} (h : AnnealPath body s s') :
    CoReach (stepMirState body) (.running s) (.running s') := by
  induction h with
  | refl s => exact .refl _
  | step obs hs _ ih => exact .head (coStep_of_emitStep hs) ih

/-- An Anneal path to a normal root-frame return is tree-safe and returns exactly that value. -/
theorem anneal_safe_of_path_return {s sₙ : MachineState} {retVal : Value} {mem : Memory}
    (hpath : AnnealPath body s sₙ) (hret : stepMirFn body sₙ = .retNormal retVal mem) :
    TreeSafe (mirTree body s) ∧ (∃ tr, ReachesRet (mirTree body s) tr (.normal (retVal, mem))) ∧
      ∀ tr r, ReachesRet (mirTree body s) tr r → r = .normal (retVal, mem) := by
  have hend : ∀ y, CoReach (stepMirState body) (.running sₙ) y → y = .running sₙ := by
    intro y hy
    cases hy with
    | refl _ => rfl
    | head hst _ => exact absurd hst (not_coStep_retNormal hret)
  have hpathStates : ∀ y, CoReach (stepMirState body) (.running s) y →
      ∃ s', y = .running s' ∧ ((∃ obs s'', stepMirFn body s' = .emitStep obs s'') ∨ s' = sₙ) := by
    intro y hy
    induction hpath generalizing y with
    | refl s => exact ⟨s, hend y hy, Or.inr rfl⟩
    | @step s s₁ s₂ obs hs hrest ih =>
      have hret' := hret
      cases hy with
      | refl _ => exact ⟨s, rfl, Or.inl ⟨obs, s₁, hs⟩⟩
      | head hst hy' =>
        rw [coStep_emitStep_inv hs hst] at hy'
        exact ih hret' hend y hy'
  rw [mirTree_eq_cofix]
  refine ⟨treeSafe_cofix_iff.2 fun y hy hf => ?_, reachesRet_cofix_iff.2 ⟨_, hpath.coReach, hret⟩,
    fun tr r hr => ?_⟩
  · obtain ⟨s', rfl, ⟨obs, s'', hs'⟩ | rfl⟩ := hpathStates y hy
    · exact not_isFaultNode_emitStep obs s'' (hs' ▸ hf)
    · exact not_isFaultNode_retNormal retVal mem (hret ▸ hf)
  · obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    obtain ⟨s', rfl, ⟨obs, s'', hs'⟩ | rfl⟩ := hpathStates y hy
    · change stepMirFn body s' = _ at hyr
      rw [hs'] at hyr
      cases obs <;> cases hyr
    · change stepMirFn body s' = _ at hyr
      rw [hret] at hyr
      injection hyr with hyr
      exact hyr.symm

/-- An Anneal path to a fault is not tree-safe; an undefined-behavior fault is
reachable undefined behavior. -/
theorem anneal_fault_of_path {s sₙ : MachineState} {k : FailureKind}
    (hpath : AnnealPath body s sₙ) (hfail : stepMirFn body sₙ = .fail k) :
    ¬ TreeSafe (mirTree body s) ∧ (k = .ub → MirReachesUB (mirTree body s)) := by
  rw [mirTree_eq_cofix]
  refine ⟨fun hsafe => ?_, fun hk => ?_⟩
  · exact treeSafe_cofix_iff.1 hsafe _ hpath.coReach
      (show IsFaultNode (stepMirFn body sₙ) by rw [hfail]; exact isFaultNode_fail k)
  · subst hk
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hpath.coReach
    have hobs : (ITree.cofix (stepMirState body) (.running sₙ)).observe =
        .vis (.inl (.fail .ub)) (fun o => ITree.cofix (stepMirState body) (PEmpty.elim o)) := by
      rw [observe_cofix_eq]
      change (stepMirFn body sₙ).map _ = _
      rw [hfail]
      rfl
    exact ⟨tr, _, _, htr, hobs⟩

/-- Invariant certificate for Anneal loops: if a set of states is closed under
`emitStep` transitions, every run from it is tree-safe and never returns. -/
theorem anneal_safe_of_closed {P : MachineState → Prop} {s : MachineState} (hs : P s)
    (hclosed : ∀ x, P x → ∃ obs x', stepMirFn body x = .emitStep obs x' ∧ P x') :
    TreeSafe (mirTree body s) ∧ ∀ tr r, ¬ ReachesRet (mirTree body s) tr r := by
  have hinv : ∀ y, CoReach (stepMirState body) (.running s) y → ∃ x, y = .running x ∧ P x := by
    intro y hy
    generalize hx : (MirExecState.running s) = x₀ at hy
    induction hy generalizing s with
    | refl _ => exact ⟨s, hx.symm, hs⟩
    | head hst _ ih =>
      subst hx
      obtain ⟨obs, x', hx', hPx'⟩ := hclosed s hs
      have hy_eq := coStep_emitStep_inv hx' hst
      subst hy_eq
      exact ih hPx' rfl
  rw [mirTree_eq_cofix]
  refine ⟨treeSafe_cofix_iff.2 fun y hy hf => ?_, fun tr r hr => ?_⟩
  · obtain ⟨x, rfl, hPx⟩ := hinv y hy
    obtain ⟨obs, x', hx', _⟩ := hclosed x hPx
    exact not_isFaultNode_emitStep obs x' (hx' ▸ hf)
  · obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    obtain ⟨x, rfl, hPx⟩ := hinv y hy
    obtain ⟨obs, x', hx', _⟩ := hclosed x hPx
    change stepMirFn body x = _ at hyr
    rw [hx'] at hyr
    cases obs <;> cases hyr


/-! ### `runAnnealBounded` certificates -/

/-- Anneal's bounded-run result for a terminal outcome. -/
def annealHaltOutcome : MirOutcome → AnnealRunOutcome
  | .normal (retVal, mem) => .returned retVal mem
  | out => .haltedOther out

theorem CoStep.not_fault_not_ret {E : Effect.{0}} {R S : Type} [FaultEffect E]
    {step : S → ITreeF E R S} {x y : S} (h : CoStep step x y) :
    ¬ IsFaultNode (step x) ∧ ∀ r, step x ≠ .ret r := by
  cases h with
  | tau h' =>
    refine ⟨fun ⟨_, _, hik, _⟩ => ?_, fun r hr => ?_⟩
    · rw [h'] at hik; cases hik
    · rw [h'] at hr; cases hr
  | vis h' hnf _ =>
    refine ⟨fun ⟨_, _, hik, hf⟩ => ?_, fun r hr => ?_⟩
    · rw [h'] at hik; cases hik; exact hnf hf
    · rw [h'] at hr; cases hr

theorem halted_coReach {body : CapturedMir} {out : MirOutcome} {y : MirExecState}
    (hy : CoReach (stepMirState body) (.halted out) y) : y = .halted out := by
  cases hy with
  | refl _ => rfl
  | head h _ =>
    cases h with
    | tau h => cases h
    | vis h _ _ => cases h

theorem halted_node (body : CapturedMir) (out : MirOutcome) :
    ¬ IsFaultNode (stepMirState body (.halted out)) ∧
      ∀ r, stepMirState body (.halted out) = .ret r → r = out := by
  refine ⟨fun ⟨_, _, h, _⟩ => ?_, fun r hr => ?_⟩
  · cases h
  · injection hr with hr; exact hr.symm

/-- Behaviour of one Anneal step from `.running s`, as seen by `runAnnealBounded`
and by the coalgebra reachability of `mirTree`. -/
theorem anneal_step_classify (body : CapturedMir) (s : MachineState) :
    (∃ s', (∀ n, runAnnealBounded body (n + 1) s = runAnnealBounded body n s') ∧
      ∀ y, CoStep (stepMirState body) (.running s) y ↔ y = .running s') ∨
    (∃ out, (∀ n, runAnnealBounded body (n + 1) s = annealHaltOutcome out) ∧
      (∀ y, CoReach (stepMirState body) (.running s) y →
        ¬ IsFaultNode (stepMirState body y) ∧ ∀ r, stepMirState body y = .ret r → r = out) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧ stepMirState body y = .ret out) ∨
    (∃ k, (∀ n, runAnnealBounded body (n + 1) s = .faulted k) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧
        ∃ f, stepMirState body y = .vis (.inl (.fail k)) f) ∨
    (∀ n, runAnnealBounded body (n + 1) s = .blocked) := by
  have hs : stepMirState body (.running s) = stepMirFn body s := rfl
  -- A unique halted successor yields a terminating, fault-free reachable set.
  have halted_succ : ∀ out, (∀ y, CoStep (stepMirState body) (.running s) y ↔ y = .halted out) →
      (∀ y, CoReach (stepMirState body) (.running s) y →
        ¬ IsFaultNode (stepMirState body y) ∧ ∀ r, stepMirState body y = .ret r → r = out) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧ stepMirState body y = .ret out := by
    intro out hsucc
    have hnode := ((hsucc _).2 rfl).not_fault_not_ret
    refine ⟨fun y hy => ?_, .halted out, .head ((hsucc _).2 rfl) (.refl _), rfl⟩
    cases hy with
    | refl _ => exact ⟨hnode.1, fun r hr => absurd hr (hnode.2 r)⟩
    | head h hy' =>
      rw [(hsucc _).1 h] at hy'
      rw [halted_coReach hy']
      exact halted_node body out
  match hst : stepMirFn body s with
  | .ret r =>
    refine Or.inr (Or.inl ⟨r, fun n => ?_, fun y hy => ?_, .running s, .refl _, by rw [hs, hst]⟩)
    · simp only [runAnnealBounded, hst]
      rcases r with ⟨retVal, mem⟩ | _ | _ <;> rfl
    · cases hy with
      | refl _ =>
        rw [hs, hst]
        refine ⟨fun ⟨_, _, h, _⟩ => ?_, fun r' hr' => ?_⟩
        · cases h
        · injection hr' with hr'; exact hr'.symm
      | head h _ =>
        cases h with
        | tau h => rw [hs, hst] at h; cases h
        | vis h _ _ => rw [hs, hst] at h; cases h
  | .tau (.running s') =>
    refine Or.inl ⟨s', fun n => by simp only [runAnnealBounded, hst], fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
    · cases h with
      | tau h => rw [hs, hst] at h; injection h with h; exact h.symm
      | vis h _ _ => rw [hs, hst] at h; cases h
    · subst h; exact .tau (by rw [hs, hst])
  | .tau (.halted out) =>
    refine Or.inr (Or.inl ⟨out, fun n => ?_, halted_succ out fun y => ⟨fun h => ?_, fun h => ?_⟩⟩)
    · simp only [runAnnealBounded, hst]
      rcases out with ⟨retVal, mem⟩ | _ | _ <;> rfl
    · cases h with
      | tau h => rw [hs, hst] at h; injection h with h; exact h.symm
      | vis h _ _ => rw [hs, hst] at h; cases h
    · subst h; exact .tau (by rw [hs, hst])
  | .tau (.faulted k) =>
    exact Or.inr (Or.inr (Or.inl ⟨k, fun n => by simp only [runAnnealBounded, hst], .faulted k,
      .head (.tau (by rw [hs, hst])) (.refl _), PEmpty.elim, rfl⟩))
  | .vis (.inl (.fail k)) f =>
    exact Or.inr (Or.inr (Or.inl ⟨k, fun n => by simp only [runAnnealBounded, hst], .running s, .refl _, f,
      by rw [hs, hst]⟩))
  | .vis (.inr (.inl (.emit ev))) f =>
    have hsucc : ∀ y, CoStep (stepMirState body) (.running s) y ↔ y = f PUnit.unit := by
      intro y
      constructor
      · intro h
        cases h with
        | tau h => rw [hs, hst] at h; cases h
        | vis h _ o =>
          rw [hs, hst] at h
          cases h
          cases o
          rfl
      · intro h
        subst h
        have hv : stepMirState body (.running s) = .vis (.inr (.inl (.emit ev))) f := by
          rw [hs, hst]
        exact .vis hv (mir_not_isFault_inr _) PUnit.unit
    match hk : f PUnit.unit with
    | .running s' =>
      refine Or.inl ⟨s', fun n => ?_, fun y => by rw [hsucc, hk]⟩
      simp only [runAnnealBounded, hst, hk]
    | .halted out =>
      refine Or.inr (Or.inl ⟨out, fun n => ?_, halted_succ out fun y => by rw [hsucc, hk]⟩)
      simp only [runAnnealBounded, hst, hk]
      rcases out with ⟨retVal, mem⟩ | _ | _ <;> rfl
    | .faulted k =>
      refine Or.inr (Or.inr (Or.inl ⟨k, fun n => ?_, .faulted k,
        .head ((hsucc _).2 hk.symm) (.refl _), PEmpty.elim, rfl⟩))
      simp only [runAnnealBounded, hst, hk]
  | .vis (.inr (.inr (.call req))) f =>
    exact Or.inr (Or.inr (Or.inr fun n => by simp only [runAnnealBounded, hst]))

/-- An Anneal bounded run that returns normally certifies tree safety and the return value. -/
theorem anneal_safe_of_runAnnealBounded_returned {body : CapturedMir} {N : Nat}
    {s : MachineState} {retVal : Value} {mem : Memory}
    (h : runAnnealBounded body N s = .returned retVal mem) :
    TreeSafe (mirTree body s) ∧ (∃ tr, ReachesRet (mirTree body s) tr (.normal (retVal, mem))) ∧
      ∀ tr r, ReachesRet (mirTree body s) tr r → r = .normal (retVal, mem) := by
  suffices hreach : (∀ y, CoReach (stepMirState body) (.running s) y →
      ¬ IsFaultNode (stepMirState body y) ∧
        ∀ r, stepMirState body y = .ret r → r = .normal (retVal, mem)) ∧
      ∃ y, CoReach (stepMirState body) (.running s) y ∧
        stepMirState body y = .ret (.normal (retVal, mem)) by
    rw [mirTree_eq_cofix]
    refine ⟨treeSafe_cofix_iff.2 fun y hy => (hreach.1 y hy).1, reachesRet_cofix_iff.2 hreach.2,
      fun tr r hr => ?_⟩
    obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    exact (hreach.1 y hy).2 r hyr
  induction N generalizing s with
  | zero => cases h
  | succ N ih =>
    rcases anneal_step_classify body s with
      ⟨s', hrun, hsucc⟩ | ⟨out, hrun, hall, hex⟩ | ⟨k, hrun, _⟩ | hrun
    · rw [hrun] at h
      obtain ⟨hall, hex⟩ := ih h
      have hnode := ((hsucc _).2 rfl).not_fault_not_ret
      refine ⟨fun y hy => ?_, ?_⟩
      · cases hy with
        | refl _ => exact ⟨hnode.1, fun r hr => absurd hr (hnode.2 r)⟩
        | head hst hy' =>
          rw [(hsucc _).1 hst] at hy'
          exact hall y hy'
      · obtain ⟨y, hy, hyr⟩ := hex
        exact ⟨y, .head ((hsucc _).2 rfl) hy, hyr⟩
    · rw [hrun] at h
      have hout : out = .normal (retVal, mem) := by
        rcases out with ⟨rv, mm⟩ | _ | _
        · injection h with h₁ h₂; subst h₁ h₂; rfl
        · cases h
        · cases h
      subst hout
      exact ⟨hall, hex⟩
    · rw [hrun] at h; cases h
    · rw [hrun] at h; cases h

/-- An Anneal bounded run that faults certifies the absence of tree safety, and
an undefined-behavior fault certifies reachable undefined behavior. -/
theorem anneal_fault_of_runAnnealBounded_faulted {body : CapturedMir} {N : Nat}
    {s : MachineState} {k : FailureKind} (h : runAnnealBounded body N s = .faulted k) :
    ¬ TreeSafe (mirTree body s) ∧ (k = .ub → MirReachesUB (mirTree body s)) := by
  suffices hreach : ∃ y, CoReach (stepMirState body) (.running s) y ∧
      ∃ f, stepMirState body y = .vis (.inl (.fail k)) f by
    obtain ⟨y, hy, f, hf⟩ := hreach
    rw [mirTree_eq_cofix]
    refine ⟨fun hsafe => treeSafe_cofix_iff.1 hsafe y hy ⟨_, f, hf, mir_isFault_inl _⟩,
      fun hk => ?_⟩
    subst hk
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
    exact ⟨tr, _, _, htr, by rw [observe_cofix_eq, hf]; rfl⟩
  induction N generalizing s with
  | zero => cases h
  | succ N ih =>
    rcases anneal_step_classify body s with
      ⟨s', hrun, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k', hrun, hex⟩ | hrun
    · rw [hrun] at h
      obtain ⟨y, hy, hf⟩ := ih h
      exact ⟨y, .head ((hsucc _).2 rfl) hy, hf⟩
    · rw [hrun] at h
      rcases out with ⟨rv, mm⟩ | _ | _ <;> cases h
    · rw [hrun] at h
      injection h with h
      subst h
      exact hex
    · rw [hrun] at h; cases h

/-- An Anneal bounded run that faults with kind `k` reaches a fault of kind `k`
(`MirReachesFault`), for every failure class. -/
theorem anneal_reachesFault_of_runAnnealBounded_faulted {body : CapturedMir} {N : Nat}
    {s : MachineState} {k : FailureKind} (h : runAnnealBounded body N s = .faulted k) :
    MirReachesFault (mirTree body s) k := by
  suffices hreach : ∃ y, CoReach (stepMirState body) (.running s) y ∧
      ∃ f, stepMirState body y = .vis (.inl (.fail k)) f by
    obtain ⟨y, hy, f, hf⟩ := hreach
    rw [mirTree_eq_cofix]
    obtain ⟨tr, htr⟩ := reaches_cofix_of_coReach hy
    exact ⟨tr, _, _, htr, by rw [observe_cofix_eq, hf]; rfl⟩
  induction N generalizing s with
  | zero => cases h
  | succ N ih =>
    rcases anneal_step_classify body s with
      ⟨s', hrun, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k', hrun, hex⟩ | hrun
    · rw [hrun] at h
      obtain ⟨y, hy, hf⟩ := ih h
      exact ⟨y, .head ((hsucc _).2 rfl) hy, hf⟩
    · rw [hrun] at h
      rcases out with ⟨rv, mm⟩ | _ | _ <;> cases h
    · rw [hrun] at h
      injection h with h
      subst h
      exact hex
    · rw [hrun] at h; cases h

/-- An Anneal execution that keeps running for every bound is tree-safe and never returns. -/
theorem anneal_safe_of_forall_running {body : CapturedMir} {s : MachineState}
    (h : ∀ n, ∃ s', runAnnealBounded body n s = .running s') :
    TreeSafe (mirTree body s) ∧ ∀ tr r, ¬ ReachesRet (mirTree body s) tr r := by
  -- Every reachable state is a running state from which every bounded run keeps running.
  have hinv : ∀ y, CoReach (stepMirState body) (.running s) y →
      ∃ x, y = .running x ∧ ∀ n, ∃ s', runAnnealBounded body n x = .running s' := by
    intro y hy
    generalize hx : (MirExecState.running s) = x₀ at hy
    induction hy generalizing s with
    | refl _ => exact ⟨s, hx.symm, h⟩
    | head hst _ ih =>
      subst hx
      rcases anneal_step_classify body s with
        ⟨s', hrun, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k, hrun, _⟩ | hrun
      · have hy_eq := (hsucc _).1 hst
        subst hy_eq
        exact ih (fun n => by obtain ⟨x, hx⟩ := h (n + 1); rw [hrun] at hx; exact ⟨x, hx⟩) rfl
      · obtain ⟨x, hx⟩ := h 1
        rw [hrun] at hx
        rcases out with ⟨rv, mm⟩ | _ | _ <;> cases hx
      · obtain ⟨x, hx⟩ := h 1; rw [hrun] at hx; cases hx
      · obtain ⟨x, hx⟩ := h 1; rw [hrun] at hx; cases hx
  have hnode : ∀ x, (∀ n, ∃ s', runAnnealBounded body n x = .running s') →
      ¬ IsFaultNode (stepMirFn body x) ∧ ∀ r, stepMirFn body x ≠ .ret r := by
    intro x hx
    rcases anneal_step_classify body x with
      ⟨s', _, hsucc⟩ | ⟨out, hrun, _, _⟩ | ⟨k, hrun, _⟩ | hrun
    · exact ((hsucc _).2 rfl).not_fault_not_ret
    · obtain ⟨y, hy⟩ := hx 1
      rw [hrun] at hy
      rcases out with ⟨rv, mm⟩ | _ | _ <;> cases hy
    · obtain ⟨y, hy⟩ := hx 1; rw [hrun] at hy; cases hy
    · obtain ⟨y, hy⟩ := hx 1; rw [hrun] at hy; cases hy
  rw [mirTree_eq_cofix]
  refine ⟨treeSafe_cofix_iff.2 fun y hy => ?_, fun tr r hr => ?_⟩
  · obtain ⟨x, rfl, hx⟩ := hinv y hy
    exact (hnode x hx).1
  · obtain ⟨y, hy, hyr⟩ := reachesRet_cofix_iff.1 ⟨tr, hr⟩
    obtain ⟨x, rfl, hx⟩ := hinv y hy
    exact (hnode x hx).2 r hyr

/-- `runAnnealBounded` composes along running prefixes. -/
theorem runAnnealBounded_add (body : CapturedMir) (n k : Nat) (x : MachineState) :
    runAnnealBounded body (n + k) x =
      match runAnnealBounded body n x with
      | .running x' => runAnnealBounded body k x'
      | o => o := by
  induction n generalizing x with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    rcases anneal_step_classify body x with
      ⟨x', hrun, _⟩ | ⟨out, hrun, _, _⟩ | ⟨k', hrun, _⟩ | hrun
    · rw [hrun, hrun, ih x']
    · rw [hrun, hrun]; rcases out with ⟨rv, mm⟩ | _ | _ <;> rfl
    · rw [hrun, hrun]
    · rw [hrun, hrun]

theorem AnnealPath.run_shift {body : CapturedMir} {s s' : MachineState}
    (h : AnnealPath body s s') :
    ∃ n, ∀ k, runAnnealBounded body (n + k) s = runAnnealBounded body k s' := by
  induction h with
  | refl s => exact ⟨0, fun k => by rw [Nat.zero_add]⟩
  | step obs hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun k => by
      rw [show n + 1 + k = (n + k) + 1 by omega, runAnnealBounded_emitStep _ _ _ _ obs hs, hn]⟩

theorem runAnnealBounded_one_retNormal {body : CapturedMir} {s : MachineState} {v : Value}
    {mem : Memory} (h : stepMirFn body s = .retNormal v mem) :
    runAnnealBounded body 1 s = .returned v mem := by
  unfold runAnnealBounded; rw [h]; rfl

theorem runAnnealBounded_one_fail {body : CapturedMir} {s : MachineState} {k : FailureKind}
    (h : stepMirFn body s = .fail k) : runAnnealBounded body 1 s = .faulted k := by
  unfold runAnnealBounded; rw [h]; rfl

/-- Lasso certificate for Anneal: a prefix reaching `sp` followed by a nonempty
cycle `sp → … → sp` runs forever. -/
theorem anneal_forall_running_of_lasso {body : CapturedMir} {p c : Nat} {s sp : MachineState}
    (hp : runAnnealBounded body p s = .running sp)
    (hc : runAnnealBounded body (c + 1) sp = .running sp) :
    ∀ n, ∃ s', runAnnealBounded body n s = .running s' := by
  have hadd := runAnnealBounded_add body
  have hle : ∀ {N n : Nat} {x x' : MachineState}, runAnnealBounded body N x = .running x' →
      n ≤ N → ∃ y, runAnnealBounded body n x = .running y := by
    intro N n x x' hN hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [hadd] at hN
    cases hx : runAnnealBounded body n x with
    | running y => exact ⟨y, rfl⟩
    | returned _ _ => rw [hx] at hN; cases hN
    | faulted _ => rw [hx] at hN; cases hN
    | haltedOther _ => rw [hx] at hN; cases hN
    | blocked => rw [hx] at hN; cases hN
  have hcyc : ∀ q, ∃ x, runAnnealBounded body q sp = .running x := by
    intro q
    induction q using Nat.strongRecOn with
    | ind q ih =>
      by_cases hq : q ≤ c + 1
      · exact hle hc hq
      · obtain ⟨q', rfl⟩ : ∃ q', q = (c + 1) + q' := ⟨q - (c + 1), by omega⟩
        rw [hadd, hc]
        exact ih q' (by omega)
  intro n
  by_cases hn : n ≤ p
  · exact hle hp hn
  · obtain ⟨q, rfl⟩ : ∃ q, n = p + q := ⟨n - p, by omega⟩
    rw [hadd, hp]
    exact hcyc q

/-! ### Two-machine whole-program certificates -/

/-- **Whole-program return agreement.** A running prefix of both machines
followed by explicit paths ending in a normal root return certifies Anneal's
`TreeSafe` and unique `ReachesRet`, and `lean-miri`'s `System.Safe` with the
unique outcome `.returned v`. -/
theorem wholeProgram_returns {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA preA sₙ : MachineState} {entryM preM mₙ m' : AnnealStepState} {p : Nat}
    {retVal : Value} {mem : Memory} {v : Miri.Interpreter.Operand AnnealProv}
    (hpa : runAnnealBounded body p entryA = .running preA)
    (hpm : runLoopFuel H p entryM = .running preM)
    (hA : AnnealPath body preA sₙ) (hAr : stepMirFn body sₙ = .retNormal retVal mem)
    (hM : MiriPath H preM mₙ) (hMr : H.coreStep () mₙ = (m', .ok true))
    (hemp : m'.stack.frames = #[]) (hop : (H.returnOperand () mₙ).2 = .ok v) :
    (TreeSafe (mirTree body entryA) ∧
      (∃ tr, ReachesRet (mirTree body entryA) tr (.normal (retVal, mem))) ∧
      ∀ tr r, ReachesRet (mirTree body entryA) tr r → r = .normal (retVal, mem)) ∧
    ((miriSystem H).Safe entryM ∧ (miriSystem H).ReachesOutcome entryM (.returned v) ∧
      ∀ o, (miriSystem H).ReachesOutcome entryM o → o = .returned v) := by
  refine ⟨?_, miri_safe_of_path_return ((MiriPath.of_runLoopFuel hpm).trans hM) hMr hemp hop⟩
  obtain ⟨n, hn⟩ := hA.run_shift
  apply anneal_safe_of_runAnnealBounded_returned (N := p + (n + 1))
  rw [runAnnealBounded_add, hpa]
  dsimp only
  rw [hn 1, runAnnealBounded_one_retNormal hAr]

/-- **Whole-program undefined-behavior agreement.** A running prefix of both
machines followed by explicit paths ending in Anneal's `.fail .ub` and a
`lean-miri` error that `RunLoop.reportsUB` certifies reachable undefined
behavior on both sides. -/
theorem wholeProgram_ub {body : CapturedMir} {H : AnnealMiriHooks}
    {entryA preA sₙ : MachineState} {entryM preM mₙ m' : AnnealStepState} {p : Nat}
    {e : Miri.Interpreter.StepError}
    (hpa : runAnnealBounded body p entryA = .running preA)
    (hpm : runLoopFuel H p entryM = .running preM)
    (hA : AnnealPath body preA sₙ) (hAf : stepMirFn body sₙ = .fail .ub)
    (hM : MiriPath H preM mₙ) (hMe : H.coreStep () mₙ = (m', .error e))
    (hub : Miri.Interpreter.RunLoop.reportsUB e = true) :
    (MirReachesUB (mirTree body entryA) ∧ ¬ TreeSafe (mirTree body entryA)) ∧
    ((miriSystem H).ReachesOutcome entryM (.undefinedBehavior e) ∧
      ¬ (miriSystem H).Safe entryM) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hA.run_shift
    have h : runAnnealBounded body (p + (n + 1)) entryA = .faulted .ub := by
      rw [runAnnealBounded_add, hpa]
      dsimp only
      rw [hn 1, runAnnealBounded_one_fail hAf]
    obtain ⟨hns, hreach⟩ := anneal_fault_of_runAnnealBounded_faulted h
    exact ⟨hreach rfl, hns⟩
  · have h := miri_outcome_of_path_error ((MiriPath.of_runLoopFuel hpm).trans hM) hMe
    rw [classifyError_eq_ub_iff.2 ⟨hub, rfl⟩] at h
    exact h

end AnnealCertificates

/-! ## 8. Infinite runs under a step-closed simulation -/

section InfiniteRuns

variable {body : CapturedMir} {H : AnnealMiriHooks}
  {Inv : MachineState → AnnealStepState → Prop}
  {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}

/-- `lean-miri` runs forever iff Anneal runs forever (under a step-closed simulation). -/
theorem runLoop_forever_iff (hsim : StepClosedSim body H Inv RetRel) {s : MachineState}
    {m : AnnealStepState} (hinv : Inv s m) :
    (∀ n, ∃ m', runLoopFuel H n m = .running m') ↔
      ∀ n, ∃ s', runAnnealBounded body n s = .running s' := by
  constructor
  · intro h n
    have hrel := runLoop_universal_simulation hsim n hinv
    obtain ⟨m', hm'⟩ := h n
    rw [hm'] at hrel
    generalize runAnnealBounded body n s = a at hrel
    cases hrel with
    | running s' _ _ => exact ⟨s', rfl⟩
  · intro h n
    have hrel := runLoop_universal_simulation hsim n hinv
    obtain ⟨s', hs'⟩ := h n
    rw [hs'] at hrel
    generalize runLoopFuel H n m = o at hrel
    cases hrel with
    | running _ m' _ => exact ⟨m', rfl⟩

/-- Under a step-closed simulation, an Anneal execution that never stops
gives `lean-miri` an infinite safe run with no terminal outcome. -/
theorem miri_infiniteRun_of_anneal_forever (hsim : StepClosedSim body H Inv RetRel)
    {s : MachineState} {m : AnnealStepState} (hinv : Inv s m)
    (h : ∀ n, ∃ s', runAnnealBounded body n s = .running s') :
    Miri.OperationalSafety.InfiniteRun (miriSystem H) m ∧ (miriSystem H).Safe m ∧
      ∀ o, ¬ (miriSystem H).ReachesOutcome m o :=
  miri_infinite_of_forall_running ((runLoop_forever_iff hsim hinv).2 h)

end InfiniteRuns

theorem forall_running_of_infiniteRun {H : AnnealMiriHooks} {m : AnnealStepState}
    (h : Miri.OperationalSafety.InfiniteRun (miriSystem H) m) :
    ∀ n, ∃ m', runLoopFuel H n m = .running m' := by
  obtain ⟨run, h0, hstep⟩ := h
  have hrun : ∀ n k, runLoopFuel H n (run k) = .running (run (k + n)) := by
    intro n
    induction n with
    | zero => intro k; rfl
    | succ n ih =>
      intro k
      rw [runLoopFuel_succ, (hstep k).1]
      dsimp only
      rw [array_isEmpty_eq_false (hstep k).2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih (k + 1), show k + 1 + n = k + (n + 1) by omega]
  intro n
  exact ⟨run n, by rw [← h0, hrun n 0, Nat.zero_add]⟩

/-- Under a step-closed simulation, `lean-miri` has an infinite run iff Anneal never stops. -/
theorem infiniteRun_iff_anneal_forever {body : CapturedMir} {H : AnnealMiriHooks}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (hsim : StepClosedSim body H Inv RetRel) {s : MachineState} {m : AnnealStepState}
    (hinv : Inv s m) :
    Miri.OperationalSafety.InfiniteRun (miriSystem H) m ↔
      ∀ n, ∃ s', runAnnealBounded body n s = .running s' :=
  ⟨fun h => (runLoop_forever_iff hsim hinv).1 (forall_running_of_infiniteRun h),
    fun h => (miri_infiniteRun_of_anneal_forever hsim hinv h).1⟩

/-! ## 9. Unconditional closed fragment: `InSafeScalarFragment` -/

/-- `lean-miri`'s locals on entry to a body with `n` locals and no arguments:
the return place `_0` is live and uninitialized and every other local is dead,
as in Anneal's `initLocalsAux`. -/
def miriEntryLocals (n : Nat) :
    Array (Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) :=
  ((List.range n).map fun i =>
    if i = 0 then { value := .live (.immediate .uninit), layout := none }
    else { value := .dead, layout := none }).toArray

/-- Layout recorded in the root frame's return place. -/
def entryReturnLayout (body : CapturedMir) : Miri.Interpreter.LocalLayout :=
  match body.localDecls with
  | d :: _ => translateTy d.ty body.layouts
  | [] => translateTy { kind := .tuple [], layoutIdx := 0 } body.layouts

/-- `lean-miri`'s root frame on entry to `body`. -/
def miriEntryFrame (body : CapturedMir) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (entryReturnLayout body) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := miriEntryLocals body.localDecls.length
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri`'s single-threaded state on entry to `body`. -/
def miriEntryState (body : CapturedMir) : AnnealStepState :=
  { stack := ⟨#[miriEntryFrame body]⟩, machine := AnnealMachine.empty }

theorem miriEntryLocals_getElem? (n i : Nat) :
    (miriEntryLocals n)[i]? =
      if i < n then
        some (if i = 0 then { value := .live (.immediate .uninit), layout := none }
          else { value := .dead, layout := none })
      else none := by
  unfold miriEntryLocals
  rw [List.getElem?_toArray, List.getElem?_map]
  by_cases h : i < n
  · have hr : (List.range n)[i]? = some i := by
      rw [List.getElem?_eq_getElem (by simpa using h)]
      simp
    rw [hr]
    simp [h]
  · have hr : (List.range n)[i]? = none := List.getElem?_eq_none (by simpa using h)
    rw [hr]
    simp [h]

theorem miriEntryLocals_size (n : Nat) : (miriEntryLocals n).size = n := by
  simp [miriEntryLocals]

theorem initLocalsAux_succ_nil (k : Nat) (ds : List LocalDecl) (i : Nat) :
    get? (initLocalsAux (k + 1) ds []) i = if i < ds.length then some .dead else none := by
  induction ds generalizing k i with
  | nil => simp [initLocalsAux, get?]
  | cons d ds ih =>
    cases i with
    | zero => simp [initLocalsAux, get?]
    | succ i =>
      show get? (initLocalsAux (k + 1) ds []) i = _
      rw [ih k i]
      by_cases hi : i < ds.length <;> simp [hi]

theorem initLocalsAux_succ_nil_length (k : Nat) (ds : List LocalDecl) :
    (initLocalsAux (k + 1) ds []).length = ds.length := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    show (initLocalsAux (k + 1) ds []).length + 1 = ds.length + 1
    rw [ih k]

theorem entry_locals_get (body : CapturedMir) (i : Nat) :
    get? (initMachineState body []).frame.locals i =
      if i < body.localDecls.length then some (if i = 0 then LocalSlot.uninit else .dead)
      else none := by
  change get? (initLocalsAux 0 body.localDecls []) i = _
  cases hd : body.localDecls with
  | nil => simp [initLocalsAux, get?]
  | cons d ds =>
    cases i with
    | zero => simp [initLocalsAux, get?]
    | succ i =>
      show get? (initLocalsAux (0 + 1) ds []) i = _
      rw [initLocalsAux_succ_nil 0 ds i]
      by_cases hi : i < ds.length <;> simp [hi]

theorem entry_locals_length (body : CapturedMir) :
    (initMachineState body []).frame.locals.length = body.localDecls.length := by
  change (initLocalsAux 0 body.localDecls []).length = _
  cases body.localDecls with
  | nil => rfl
  | cons d ds =>
    show (initLocalsAux (0 + 1) ds []).length + 1 = ds.length + 1
    rw [initLocalsAux_succ_nil_length 0 ds]

/-- The entry states of Anneal (`initMachineState body []`) and `lean-miri`
(`miriEntryState body`) are `StateRel`-related for every body. -/
theorem stateRel_entry (body : CapturedMir) :
    StateRel body (initMachineState body []) (miriEntryState body) := by
  refine StateRel.mk (miriEntryFrame body) rfl rfl ⟨_, rfl⟩ ?_ rfl rfl rfl rfl rfl ?_
  · refine
      { body_eq := rfl
        location_eq := rfl
        af_locals_len := entry_locals_length body
        mf_locals_size := miriEntryLocals_size _
        locals_rel := ?_ }
    intro i decl slot mls hdecl hslot hmls
    have hi : i < body.localDecls.length := by
      rw [get?_eq_getElem?] at hdecl
      exact (List.getElem?_eq_some_iff.1 hdecl).1
    rw [entry_locals_get] at hslot
    change (miriEntryLocals body.localDecls.length)[i]? = some mls at hmls
    rw [miriEntryLocals_getElem?] at hmls
    simp only [hi, ↓reduceIte] at hslot hmls
    by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte] at hslot hmls
      injection hslot with hslot
      injection hmls with hmls
      subst hslot hmls
      exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    · simp only [h0, ↓reduceIte] at hslot hmls
      injection hslot with hslot
      injection hmls with hmls
      subst hslot hmls
      exact .dead none (fun _ h => nomatch h)
  · apply MemoryAllocDisjoint.of_no_indirect
    intro k x hx mp hmp
    change (miriEntryLocals body.localDecls.length)[k]? = some x at hx
    rw [miriEntryLocals_getElem?] at hx
    split at hx
    · split at hx <;> (injection hx with hx; subst hx; cases hmp)
    · cases hx

theorem entry_immediate (body : CapturedMir) (nonAddrTaken : Nat → Prop) :
    NonAddrTakenImmediate body nonAddrTaken (miriEntryState body) := by
  intro tf htf idx _ _ _ mls hmls mp hmp
  have htf' : tf = miriEntryFrame body := by
    injection htf with h; injection h with h; exact h.symm
  subst htf'
  change (miriEntryLocals body.localDecls.length)[idx]? = some mls at hmls
  rw [miriEntryLocals_getElem?] at hmls
  split at hmls
  · split at hmls <;> (injection hmls with hmls; subst hmls; cases hmp)
  · cases hmls

/-- The `LM-1.1` closed invariant: `StateRel`, an in-bounds program counter, and
immediate representation of every non-address-taken local. -/
def ScalarFragmentInv (body : CapturedMir) (nonAddrTaken : Nat → Prop)
    (s : MachineState) (m : AnnealStepState) : Prop :=
  StateRel body s m ∧ ValidFrameLocation body s.frame ∧ NonAddrTakenImmediate body nonAddrTaken m

/-- Return-value relation of the `LM-1` fragments: the operand is an immediate
`ImmediateRel`-related at the type of `_0`. -/
def ImmediateRetRel (body : CapturedMir) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0 imm0, get? body.localDecls 0 = some decl0 ∧ v = .immediate imm0 ∧
    ImmediateRel decl0.ty body.layouts retVal imm0

/-- Lift an `LM-1` `StepRel` (with `Inv` holding at every related post-state)
to `Lockstep` over the `annealMiriHooks` interpreter. -/
theorem StepRel.toLockstep {body : CapturedMir} {Inv : MachineState → AnnealStepState → Prop}
    {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRel body m aRes mRes)
    (hinv : ∀ s' m', aRes = .step s' → mRes = (m', .ok true) → StateRel body s' m' → Inv s' m') :
    Lockstep (annealMiriHooks body) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    have hne : m'.stack.frames ≠ #[] := by
      obtain ⟨tf, hf, _⟩ := id hrel
      rw [hf]; intro h; cases h
    exact .emitStep .silent s' m' (hinv s' m' rfl rfl hrel) hne
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (by
      change (annealControlHooks.returnOperand () m).2 = _; rw [hop])
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) rfl

/-- **Unconditional closed-fragment instance.** For every body in the syntactic
`LM-1.1` scalar fragment (`WellTypedBody`: multi-block `Goto` control flow
including loops, `Return`, `Unreachable`, `StorageLive` / `StorageDead`, and
assignments of constants, copies, unary operators, and wrapping, checked
(`(T, bool)` pair), comparison, bitwise, and shift binary operators),
`ScalarFragmentInv` is step-closed with no per-step hypotheses. -/
theorem scalarFragment_stepClosedSim {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (hbody : WellTypedBody body nonAddrTaken) :
    StepClosedSim body (annealMiriHooks body) (ScalarFragmentInv body nonAddrTaken)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨hstate, hloc, himm⟩ => ?_⟩
  have hstep := step_wellTypedBody_simulation hbody hstate hloc himm
  have hloc' := fun s' (hs : stepMirFn body s = .step s') =>
    ValidFrameLocation.preserved hbody hstate hloc hs
  have himm' := NonAddrTakenImmediate.preserved hbody hstate hloc himm
  refine StepRel.toLockstep hstep fun s' m' ha hm hrel => ⟨hrel, hloc' s' ha, ?_⟩
  change Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
    (m', .ok true) at hm
  have h := himm' (by rw [hm])
  rw [hm] at h
  exact h

/-! ### Generic terminator plumbing -/

/-- At the end of a basic block, Anneal's `stepMirFn` evaluates the terminator. -/
theorem stepMirFn_at_terminator {body : CapturedMir} {s : MachineState}
    (hcal : s.memory.activeCallee = none)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements) :
    stepMirFn body s = evalTerminator s bb.terminator (some body) := by
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]

/-- At the end of a basic block, `lean-miri`'s step is the terminator's outcome
with its `Unit` result mapped to `true`. -/
theorem miri_step_terminator_eq
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    {m' : AnnealStepState} {r : Except Miri.Interpreter.StepError Unit}
    (h : Miri.Interpreter.ControlFlow.evalTerminator
        (annealTerminatorHooks body.localDecls body.layouts) () (translateTerminator bb.terminator) m =
      (m', r)) :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', r.map fun _ => true) := by
  rw [miri_step_at_terminator hframes hbody hloc hbb hstmt_none, h]

/-- A successful `Assert` condition read continues at `target` when the value
matches `expected` (optional overflow checks not ignored), and panics otherwise. -/
theorem evalTerminator_assert_ok
    {P L E M C Op Imm : Type}
    (hooks : Miri.Interpreter.TerminatorHooks P L E M C Op Imm) (choice : C)
    (si : Miri.MIR.SourceInfo) (cond : Miri.MIR.Operand) (expected : Bool)
    (msg : Miri.MIR.AssertKind) (target : Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction)
    (state state' : Miri.Interpreter.StepState P L E M) (b : Bool)
    (hign : hooks.ignoreOptionalOverflowChecks state = false)
    (hread : hooks.readAssertCondition choice cond state = (state', .ok b)) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks choice
        { sourceInfo := si, kind := .Assert cond expected msg target unwind } state =
      if expected == b then Miri.Interpreter.ControlFlow.goToBlock target state'
      else hooks.assertPanic choice msg unwind state' := by
  unfold Miri.Interpreter.ControlFlow.evalTerminator
  simp only [hign, hread, Bool.false_and, Bool.false_or]
  rfl

/-- A failing `Assert` condition read aborts with its error. -/
theorem evalTerminator_assert_error
    {P L E M C Op Imm : Type}
    (hooks : Miri.Interpreter.TerminatorHooks P L E M C Op Imm) (choice : C)
    (si : Miri.MIR.SourceInfo) (cond : Miri.MIR.Operand) (expected : Bool)
    (msg : Miri.MIR.AssertKind) (target : Miri.MIR.BasicBlockId)
    (unwind : Miri.MIR.UnwindAction)
    (state state' : Miri.Interpreter.StepState P L E M) (err : Miri.Interpreter.StepError)
    (hread : hooks.readAssertCondition choice cond state = (state', .error err)) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks choice
        { sourceInfo := si, kind := .Assert cond expected msg target unwind } state =
      (state', .error err) := by
  unfold Miri.Interpreter.ControlFlow.evalTerminator
  simp only [hread]
  rfl

/-! ### `SwitchInt` -/

/-- Outcome characterization of a `SwitchInt` step on a well-typed `bool` or
integer discriminant: both machines report UB, or both continue at
`lookupSwitchTarget bits …` (Anneal emitting `.event bits`) in `StateRel`-related
states whose `lean-miri` frame keeps every immediate local of the pre-frame
immediate. -/
theorem switchInt_step_cases
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {discr : MirAst.Operand} {targets : SwitchTargets} {ty : Ty}
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hdiscr : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame discr ty)
    (hcases : SwitchCasesFit ty targets) :
    (∃ m' msg, stepMirFn body s = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg))) ∨
    (∃ (bits : Nat) (locals' : List LocalSlot)
        (topFrame topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      m.stack.frames = #[topFrame] ∧
      stepMirFn body s = .emitStep (.event bits)
        { s with frame := { blockIdx := lookupSwitchTarget bits targets.branches targets.otherwise,
                            stmtIdx := 0, locals := locals' } } ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        ({ m with stack := ⟨#[{ topFrame' with
            location := .mir ⟨lookupSwitchTarget bits targets.branches targets.otherwise, 0⟩ }]⟩ },
          .ok true) ∧
      StateRel body
        { s with frame := { blockIdx := lookupSwitchTarget bits targets.branches targets.otherwise,
                            stmtIdx := 0, locals := locals' } }
        { m with stack := ⟨#[{ topFrame' with
            location := .mir ⟨lookupSwitchTarget bits targets.branches targets.otherwise, 0⟩ }]⟩ } ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j)) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  have hA := stepMirFn_at_terminator (body := body) hcal hphase hbb hstmt_none hstmt_len
  have hop_sim := evalOperand_scalar_simulation hframes hframe (hdiscr topFrame hframes)
    s.memory.globals none
  rw [(hdiscr topFrame hframes).evalOperand_localDecls_eq] at hop_sim
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .SwitchInt (translateOperand discr) (translateSwitchTargets targets) } := by
    unfold translateTerminator; rw [hterm]; rfl
  have hdisc_eq : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
      (translateOperand discr) m =
      Miri.Interpreter.runRvalue
        (annealEvalOperand body.localDecls body.layouts (translateOperand discr) none >>=
          annealReadImmediate) m := rfl
  generalize ha_op : evalOperand s.frame.locals discr .nil s.memory.globals body.layouts .nil = aOp
    at hop_sim
  generalize hm_op : (annealEvalOperand body.localDecls body.layouts (translateOperand discr) none >>=
    annealReadImmediate) m = mOp at hop_sim
  cases hop_sim with
  | ub m' msg =>
    have hA' : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
      unfold evalTerminator
      rw [hterm]
      dsimp only
      rw [hbor, hcaller, ha_op]
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m = (m', .error (.undefinedBehavior msg)) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_op]
    have hM := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      (m' := m') (r := .error (.undefinedBehavior msg))
      (by rw [hm_term]; exact evalTerminator_switchInt_error _ () _ _ _ m m' _ hdisc)
    exact Or.inl ⟨m', msg, hA.trans hA', hM⟩
  | ok v locals' topFrame' imm hframe' himm himm_loc htf' hdisj_fn =>
    have hprim : ty.kind = .bool ∨ ty.kind = .char ∨
        (∃ it, ty.kind = .int it) ∨ (∃ ut, ty.kind = .uint ut) := by
      rcases hty with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    obtain ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, _⟩ := himm.of_primitive_scalar hprim
    have hdisc : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
        (translateOperand discr) m =
        ({ m with stack := ⟨#[topFrame']⟩ },
          .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩) := by
      rw [hdisc_eq]; unfold Miri.Interpreter.runRvalue; rw [hm_op]
    obtain ⟨hwsz, hwvalid⟩ := boolOrInt_translateTy_size hty body.layouts
    have hwidth : sc.sizeBytes = boolOrIntByteWidth ty :=
      translateSizeBytes_inj hrel.validBytes hwvalid (by rw [← hsz, hwsz])
    have hsz_ty : sc.sizeBytes = match ty.kind with
        | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes := by
      rw [hwidth]
      rcases ty with ⟨tk, tIdx⟩
      rcases hty with h | ⟨k, h⟩ | ⟨k, h⟩ <;> dsimp only at h <;> subst h <;> rfl
    have hbits : ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1 := fun h => (hbool h).2
    have hcmp : ∀ v b, (v, b) ∈ targets.branches →
        (annealTerminatorHooks body.localDecls body.layouts).compareSwitchCase ()
          ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩ v
          { m with stack := ⟨#[topFrame']⟩ } =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok (Nat.beq sc.bits v)) := by
      intro v b hmem
      obtain ⟨hlt, hcase_bool⟩ := hcases v b hmem
      rw [← hwidth] at hlt
      exact compareSwitchCase_simulation hrel body.localDecls body.layouts ty hty hsz_ty hbits
        v hlt hcase_bool _
    have hA' : evalTerminator s bb.terminator (some body) =
        MirStepNode.emitStep (.event sc.bits)
          { s with frame := { blockIdx := lookupSwitchTarget sc.bits targets.branches targets.otherwise,
                              stmtIdx := 0, locals := locals' } } := by
      unfold evalTerminator
      rw [hterm]
      dsimp only
      rw [hbor, hcaller, ha_op]
    have hM := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
      (m' := { m with stack := ⟨#[{ topFrame' with
        location := .mir ⟨lookupSwitchTarget sc.bits targets.branches targets.otherwise, 0⟩ }]⟩ })
      (r := .ok ())
      (by
        rw [hm_term, evalTerminator_switchInt_ok _ () _ _ _ m _ _ sc.bits hdisc hcmp]
        unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
        rw [stack_currentFrame?_singleton _ topFrame' rfl]
        rfl)
    have hrc' : topFrame'.returnContinuation = .stop false := by rw [htf']; exact hretCont
    have hrp' : topFrame'.returnPlace =
        .frameLocal 0 0 none retLay topFrame'.localsIdentity := by rw [htf']; exact hretPlace
    exact Or.inr ⟨sc.bits, locals', topFrame, topFrame', hframes, hA.trans hA', hM,
      StateRel.mk
        { topFrame' with
          location := .mir ⟨lookupSwitchTarget sc.bits targets.branches targets.otherwise, 0⟩ }
        rfl hrc' ⟨retLay, hrp'⟩
        ⟨hframe'.body_eq, rfl, hframe'.af_locals_len, hframe'.mf_locals_size, hframe'.locals_rel⟩
        hcal hstack hbor hprot hcaller (hdisj_fn hd_tf),
      himm_loc⟩

/-- **(a)** `SwitchInt` step simulation (`step_terminator_switchInt_simulation`)
together with frame-immediacy preservation: when `lean-miri` continues with a
singleton stack, every immediate local of the pre-frame stays immediate. -/
theorem step_terminator_switchInt_simulation_imm
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {discr : MirAst.Operand} {targets : SwitchTargets} {ty : Ty}
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hdiscr : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame discr ty)
    (hcases : SwitchCasesFit ty targets) :
    StepObsRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    ∀ topFrame tf', m.stack.frames = #[topFrame] →
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
        .ok true →
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
        #[tf'] →
      ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal tf' j := by
  refine ⟨step_terminator_switchInt_simulation hstate hphase hbb hstmt_none hstmt_len hterm hty
    hdiscr hcases, ?_⟩
  intro topFrame0 tf' hframes0 hok hpost j hj
  rcases switchInt_step_cases hstate hphase hbb hstmt_none hstmt_len hterm hty hdiscr hcases with
    ⟨m', msg, _, hM⟩ | ⟨bits, locals', topFrame, topFrame', hframes, _, hM, _, himm_loc⟩
  · rw [hM] at hok
    cases hok
  · rw [hM] at hpost
    dsimp only at hpost
    rw [hframes] at hframes0
    injection hframes0 with h0
    injection h0 with h0 _
    subst h0
    injection hpost with h1
    injection h1 with h1 _
    subst h1
    exact himm_loc j hj

/-! ### `Assert … unreachable` -/

/-- Joint outcome of reading a well-typed `bool` `Assert` condition: Anneal's
`evalOperand` and `lean-miri`'s `readAssertCondition` both succeed (with the
condition's bit, a `FrameRel`-related post-frame, immediacy preservation, and
`MemoryAllocDisjoint` preservation), or both report UB. -/
theorem readAssertCondition_full
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRel body m.machine s.frame topFrame)
    {cond : MirAst.Operand} {condTy : Ty} (hbool : condTy.kind = .bool)
    (hop : WellTypedScalarOperand body topFrame cond condTy) :
    (∃ (sc : MirAst.ScalarInt) (locals' : List LocalSlot)
        (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      evalOperand s.frame.locals cond .nil s.memory.globals body.layouts .nil =
        .ok (.scalar sc) locals' ∧
      (annealTerminatorHooks body.localDecls body.layouts).readAssertCondition ()
          (translateOperand cond) m =
        ({ m with stack := ⟨#[topFrame']⟩ }, .ok (decide (sc.bits ≠ 0))) ∧
      (sc.bits = 0 ∨ sc.bits = 1) ∧
      FrameRel body m.machine { s.frame with locals := locals' } topFrame' ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      topFrame' = { topFrame with locals := topFrame'.locals } ∧
      (MemoryAllocDisjoint topFrame → MemoryAllocDisjoint topFrame')) ∨
    (evalOperand s.frame.locals cond .nil s.memory.globals body.layouts .nil = .ub ∧
      ∃ m' msg, (annealTerminatorHooks body.localDecls body.layouts).readAssertCondition ()
          (translateOperand cond) m = (m', .error (.undefinedBehavior msg))) := by
  have hop_sim := evalOperand_scalar_simulation hframes hframe hop s.memory.globals none
  rw [hop.evalOperand_localDecls_eq] at hop_sim
  generalize ha_eval : evalOperand s.frame.locals cond .nil s.memory.globals body.layouts .nil =
    aRes at hop_sim
  generalize hm_eval : (annealEvalOperand body.localDecls body.layouts (translateOperand cond) none >>=
    annealReadImmediate) m = mRes at hop_sim
  cases hop_sim with
  | ok val locals' tf' imm hf_rel himm_rel himm_loc htf_eq hdisj =>
    have himm := ImmediateRel.of_primitive_scalar himm_rel (Or.inl hbool)
    rcases himm with ⟨sc, msc, hval_eq, himm_eq, hsc_rel, hsc_sz, hsc_bool, _⟩
    subst hval_eq himm_eq
    left
    refine ⟨sc, locals', tf', rfl, ?_, (hsc_bool hbool).2, hf_rel, himm_loc, htf_eq, hdisj⟩
    dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_assoc_apply]
    rw [EStateM.bind_eq_ok hm_eval]
    rcases hsc_bool hbool with ⟨hsc_sz_eq, hsc_bits⟩
    have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 1 := by
      rw [hsc_rel.size_eq, hsc_sz_eq]
      rfl
    have hmsc_data_eq : msc.data = sc.bits := hsc_rel.data_eq
    rcases msc with ⟨msc_data, msc_size⟩
    subst hmsc_sz
    rcases hsc_bits with h0 | h1
    · rw [h0] at hmsc_data_eq ⊢
      subst hmsc_data_eq
      dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
        Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8,
        Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits,
        Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError,
        Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
      rfl
    · rw [h1] at hmsc_data_eq ⊢
      subst hmsc_data_eq
      dsimp [Miri.Interpreter.Immediate.toScalar, bind, EStateM.bind, pure, EStateM.pure,
        Miri.Memory.Scalar.toBool, Miri.Memory.Scalar.fromScalarInt, Miri.Memory.Scalar.toUInt8,
        Except.bind, Miri.Memory.Scalar.toUInt, Miri.Memory.Scalar.toBits,
        Miri.Memory.ScalarInt.toBits, Miri.Memory.Scalar.toScalarInt, Except.mapError,
        Miri.Memory.Scalar.tryToScalarInt, Miri.ABI.Size.bytes, Miri.ABI.Size.ofBytes]
      rfl
  | ub m' msg =>
    right
    refine ⟨rfl, m', msg, ?_⟩
    dsimp only [annealTerminatorHooks, Miri.Interpreter.TerminatorHooks.readAssertCondition]
    unfold Miri.Interpreter.runRvalue
    rw [EStateM.bind_assoc_apply]
    rw [EStateM.bind_eq_error hm_eval]

/-- Outcome characterization of an `Assert cond expected target unreachable`
step on a well-typed `bool` condition: both machines report UB (operand UB, or a
failed assertion, which unwinds to `unreachable` in Anneal and is `assert panic`
in `lean-miri`), or both continue at `target` in `StateRel`-related states whose
`lean-miri` frame keeps every immediate local of the pre-frame immediate. -/
theorem assert_unreachable_step_cases
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {cond : MirAst.Operand} {expected : Bool} {target : BasicBlockIdx} {condTy : Ty}
    (hterm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hbool : condTy.kind = .bool)
    (hcond : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame cond condTy) :
    (∃ m' msg, stepMirFn body s = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg))) ∨
    (∃ (locals' : List LocalSlot)
        (topFrame topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      m.stack.frames = #[topFrame] ∧
      stepMirFn body s =
        .step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        ({ m with stack := ⟨#[{ topFrame' with location := .mir ⟨target, 0⟩ }]⟩ }, .ok true) ∧
      StateRel body { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
        { m with stack := ⟨#[{ topFrame' with location := .mir ⟨target, 0⟩ }]⟩ } ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j)) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  have hA := stepMirFn_at_terminator (body := body) hcal hphase hbb hstmt_none hstmt_len
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .Assert (translateOperand cond) expected
          (.BoundsCheck (translateOperand cond) (translateOperand cond)) target .Unreachable } := by
    unfold translateTerminator; rw [hterm]; rfl
  rcases readAssertCondition_full hframes hframe hbool (hcond topFrame hframes) with
    ⟨sc, locals', topFrame', h_a, h_m, hsc_bool, hframe', himm_loc, htf', hdisj⟩ |
    ⟨h_a, m', msg, h_m⟩
  · have hM := evalTerminator_assert_ok (annealTerminatorHooks body.localDecls body.layouts) ()
      defaultSourceInfo (translateOperand cond) expected
      (.BoundsCheck (translateOperand cond) (translateOperand cond)) target .Unreachable
      m _ _ rfl h_m
    rw [← hm_term] at hM
    by_cases h_match : (expected == decide (sc.bits ≠ 0)) = true
    · simp only [h_match, ↓reduceIte] at hM
      have hM' := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
        (m' := { m with stack := ⟨#[{ topFrame' with location := .mir ⟨target, 0⟩ }]⟩ })
        (r := .ok ())
        (by
          rw [hM]
          unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
          rw [stack_currentFrame?_singleton _ topFrame' rfl]
          rfl)
      have hA' : evalTerminator s bb.terminator (some body) =
          MirStepNode.step
            { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } } := by
        unfold evalTerminator
        rw [hterm]
        dsimp only
        rw [hbor, hcaller, h_a]
        dsimp only
        split
        · rfl
        · next h_contra =>
          rcases hsc_bool with h0 | h1
          · revert h_match h_contra; simp only [h0]; intros; cases expected <;> contradiction
          · revert h_match h_contra; simp only [h1]; intros; cases expected <;> contradiction
      have hrc' : topFrame'.returnContinuation = .stop false := by rw [htf']; exact hretCont
      have hrp' : topFrame'.returnPlace =
          .frameLocal 0 0 none retLay topFrame'.localsIdentity := by rw [htf']; exact hretPlace
      exact Or.inr ⟨locals', topFrame, topFrame', hframes, hA.trans hA', hM',
        StateRel.mk { topFrame' with location := .mir ⟨target, 0⟩ } rfl hrc' ⟨retLay, hrp'⟩
          ⟨hframe'.body_eq, rfl, hframe'.af_locals_len, hframe'.mf_locals_size, hframe'.locals_rel⟩
          hcal hstack hbor hprot hcaller (hdisj hd_tf),
        himm_loc⟩
    · have h_if : (expected == decide (sc.bits ≠ 0)) = false := by
        revert h_match; cases (expected == decide (sc.bits ≠ 0)) <;> decide
      simp only [h_if, Bool.false_eq_true, ↓reduceIte] at hM
      have hM' := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none
        hM
      have hA' : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
        unfold evalTerminator
        rw [hterm]
        dsimp only
        rw [hbor, hcaller, h_a]
        dsimp only
        split
        · next h_contra =>
          rcases hsc_bool with h0 | h1
          · revert h_if h_contra; simp only [h0]; intros; cases expected <;> contradiction
          · revert h_if h_contra; simp only [h1]; intros; cases expected <;> contradiction
        · rfl
      exact Or.inl ⟨_, "assert panic", hA.trans hA', hM'⟩
  · have hM := evalTerminator_assert_error (annealTerminatorHooks body.localDecls body.layouts) ()
      defaultSourceInfo (translateOperand cond) expected
      (.BoundsCheck (translateOperand cond) (translateOperand cond)) target .Unreachable
      m _ _ h_m
    rw [← hm_term] at hM
    have hM' := miri_step_terminator_eq hframes hframe.body_eq hframe.location_eq hbb hstmt_none hM
    have hA' : evalTerminator s bb.terminator (some body) = MirStepNode.fail .ub := by
      unfold evalTerminator
      rw [hterm]
      dsimp only
      rw [hbor, hcaller, h_a]
    exact Or.inl ⟨m', msg, hA.trans hA', hM'⟩

/-- **(b)** `Assert cond expected target unreachable` step simulation on a
well-typed `bool` condition, together with frame-immediacy preservation. -/
theorem step_terminator_assert_unreachable_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {cond : MirAst.Operand} {expected : Bool} {target : BasicBlockIdx} {condTy : Ty}
    (hterm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hbool : condTy.kind = .bool)
    (hcond : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame cond condTy) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    ∀ topFrame tf', m.stack.frames = #[topFrame] →
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
        .ok true →
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
        #[tf'] →
      ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal tf' j := by
  rcases assert_unreachable_step_cases hstate hphase hbb hstmt_none hstmt_len hterm hbool hcond with
    ⟨m', msg, hA, hM⟩ | ⟨locals', topFrame, topFrame', hframes, hA, hM, hrel, himm_loc⟩
  · refine ⟨?_, ?_⟩
    · rw [hA, hM]
      exact StepRel.ub m' msg
    · intro _ _ _ hok
      rw [hM] at hok
      cases hok
  · refine ⟨?_, ?_⟩
    · rw [hA, hM]
      exact StepRel.step _ _ hrel
    · intro topFrame0 tf' hframes0 _ hpost j hj
      rw [hM] at hpost
      dsimp only at hpost
      rw [hframes] at hframes0
      injection hframes0 with h0
      injection h0 with h0 _
      subst h0
      injection hpost with h1
      injection h1 with h1 _
      subst h1
      exact himm_loc j hj

/-! ### Anneal-side successor locations -/

/-- `MirStepNode.emitStep` determines its successor state. -/
theorem emitStep_state_inj {o₁ o₂ : MirObs} {s₁ s₂ : MachineState}
    (h : MirStepNode.emitStep o₁ s₁ = MirStepNode.emitStep o₂ s₂) : s₁ = s₂ := by
  cases o₁ <;> cases o₂ <;> simp only [MirStepNode.emitStep] at h
  · injection h with h
    injection h
  · cases h
  · cases h
  · injection h with _ h
    have h' := congrFun h PUnit.unit
    exact MirExecState.running.inj h'

theorem fail_ne_emitStep {k : FailureKind} {obs : MirObs} {s' : MachineState} :
    MirStepNode.fail k ≠ MirStepNode.emitStep obs s' := by
  intro h
  cases obs <;> simp only [MirStepNode.emitStep, MirStepNode.fail] at h <;> cases h

theorem unsupported_ne_emitStep {obs : MirObs} {s' : MachineState} :
    MirStepNode.unsupported ≠ MirStepNode.emitStep obs s' :=
  fail_ne_emitStep

theorem retNormal_ne_emitStep {v : Value} {mem : Memory} {obs : MirObs} {s' : MachineState} :
    MirStepNode.retNormal v mem ≠ MirStepNode.emitStep obs s' := by
  intro h
  cases obs <;> simp only [MirStepNode.emitStep, MirStepNode.retNormal] at h <;> cases h

/-- `lookupSwitchTarget` returns the fallback or one of the listed targets. -/
theorem lookupSwitchTarget_cases (bits : Nat) (branches : List (Nat × BasicBlockIdx))
    (otherwise : BasicBlockIdx) :
    lookupSwitchTarget bits branches otherwise = otherwise ∨
      ∃ v, (v, lookupSwitchTarget bits branches otherwise) ∈ branches := by
  induction branches with
  | nil => exact Or.inl rfl
  | cons hd rest ih =>
    obtain ⟨bv, tgt⟩ := hd
    simp only [lookupSwitchTarget]
    split
    · exact Or.inr ⟨bv, List.Mem.head _⟩
    · rcases ih with h | ⟨v, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, List.Mem.tail _ hv⟩

/-- Every intra-frame successor of a `SwitchInt` terminator starts a listed target
block (`lookupSwitchTarget bits …` for the discriminant bits) at statement `0`. -/
theorem evalTerminator_switchInt_location {s s' : MachineState} {term : Terminator}
    {currentBody : Option CapturedMir} {discr : MirAst.Operand} {targets : SwitchTargets}
    {obs : MirObs}
    (hterm : term.kind = .switchInt discr targets)
    (hstep : evalTerminator s term currentBody = .emitStep obs s') :
    ∃ bits, s'.frame.blockIdx = lookupSwitchTarget bits targets.branches targets.otherwise ∧
      s'.frame.stmtIdx = 0 := by
  unfold evalTerminator at hstep
  rw [hterm] at hstep
  dsimp only at hstep
  split at hstep
  · have h := emitStep_state_inj hstep
    subst h
    exact ⟨_, rfl, rfl⟩
  · exact absurd hstep fail_ne_emitStep
  · exact absurd hstep fail_ne_emitStep
  · exact absurd hstep unsupported_ne_emitStep

/-- Every intra-frame successor of an `Assert … target unreachable` terminator
starts block `target` at statement `0`. -/
theorem evalTerminator_assert_unreachable_location {s s' : MachineState} {term : Terminator}
    {currentBody : Option CapturedMir} {cond : MirAst.Operand} {expected : Bool}
    {target : BasicBlockIdx} {obs : MirObs}
    (hterm : term.kind = .assert cond expected target .unreachable)
    (hstep : evalTerminator s term currentBody = .emitStep obs s') :
    s'.frame.blockIdx = target ∧ s'.frame.stmtIdx = 0 := by
  unfold evalTerminator at hstep
  rw [hterm] at hstep
  dsimp only at hstep
  split at hstep
  · split at hstep
    · have h := emitStep_state_inj (o₁ := .silent) hstep
      subst h
      exact ⟨rfl, rfl⟩
    · exact absurd hstep fail_ne_emitStep
  · exact absurd hstep fail_ne_emitStep
  · exact absurd hstep fail_ne_emitStep
  · exact absurd hstep unsupported_ne_emitStep

/-! ### `LM-1.2` and `LM-1.4` statements with frame-immediacy preservation -/

/-- `step_assign_lm1_2_simulation` together with frame-immediacy preservation:
when `lean-miri` continues with a singleton stack, every immediate local of the
pre-frame stays immediate. -/
theorem step_assign_lm1_2_simulation_ext
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM12Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf',
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
            #[tf'] →
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
            .ok true →
          IsImmediateFrameLocal tf' j) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, hd_tf⟩
  suffices StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ j, IsImmediateFrameLocal topFrame j →
      ∀ tf',
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
          #[tf'] →
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
          .ok true →
        IsImmediateFrameLocal tf' j) by
    refine ⟨this.1, fun tf₀ htf₀ j hj tf' htf' hok => ?_⟩
    rw [hframes] at htf₀
    injection htf₀ with h_arr
    injection h_arr with h_eq _
    subst h_eq
    exact this.2 j hj tf' htf' hok
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  cases hwt topFrame hframes with
  | boolCmp dstIdx dstDecl bop lhsOp rhsOp lhsTy rhsTy hkind hdecl_dst himm_dst hbop
      hlhsOp hrhsOp hlhs hrhs hdst =>
    obtain ⟨_, mls_dst0, _, hlt_dst0, _, hmls_opt, hmls_eq0, hloc_dst0⟩ :=
      hframe.lookup_local hdecl_dst
    let topFrame₀ := cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    have hdisj_tf₀_inner : MemoryAllocDisjoint topFrame₀ := by
      apply MemoryAllocDisjoint.mono_layout hd_tf
      intro k
      by_cases hk : k = dstIdx
      · subst hk
        exists (translateTy dstDecl.ty body.layouts)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set]
        simp only [↓reduceIte]
        rw [hmls_opt, hmls_eq0]
        rfl
      · exists (topFrame.locals[k]?).bind (fun x => x.layout)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hk)]
        cases topFrame.locals[k]? <;> rfl
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    have htf₀ : topFrame₀ = { topFrame with locals := topFrame₀.locals } := rfl
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hlhsOp := hlhsOp.mono_immediate hmono₀
    have hrhsOp := hrhsOp.mono_immediate hmono₀
    let knownL := if (translateBinOp bop).leftHomogeneous then some (translateTy dstDecl.ty body.layouts) else none
    have hlhs_sim := evalOperand_scalar_simulation (m := m₀) rfl hframe₀ hlhsOp s.memory.globals knownL
    have hm_eval : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          ((annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
              annealReadImmediate) >>=
            fun left =>
              ((annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
                  (if (translateBinOp bop).rightHomogeneous then some left.layout else none) >>=
                  annealReadImmediate) >>=
                fun right => do
                  let result ← Miri.Interpreter.ScalarOps.binary
                    (annealScalarOpsHooks body.localDecls body.layouts) ()
                    (translateBinOp bop) left right
                  assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
                  annealWriteImmediate result.imm destPlace)) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
        translateRvalue, annealStepHooks]
      apply runRvalue_eq_of_eq
      rw [evalRvalueIntoPlace_binaryOp_def]
      unfold annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
      rw [EStateM.bind_eq_ok hevalPlace_dst, EStateM.bind_assoc_apply]
      dsimp only [knownL, destPlace]
      with_unfolding_all
        simp only [Bind.bind, EStateM.bind]
        cases annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp)
          (if (translateBinOp bop).leftHomogeneous = true then some (translateTy dstDecl.ty body.layouts) else none) m₀ with
        | error _ _ => rfl
        | ok opL st₁ =>
          dsimp only
          cases annealReadImmediate opL st₁ with
          | error _ _ => rfl
          | ok left st₂ =>
            dsimp only
            cases annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp)
              (if (translateBinOp bop).rightHomogeneous = true then some left.layout else none) st₂ <;> rfl
    have hbop_ne : bop ≠ .offset := by
      rintro rfl; rcases hbop with h | h | h | h | h | h | h <;> cases h
    generalize ha_lhs : evalOperand s.frame.locals lhsOp .nil s.memory.globals body.layouts .nil body.localDecls = aLhs at hlhs_sim
    generalize hm_lhs : (annealEvalOperand body.localDecls body.layouts (translateOperand lhsOp) knownL >>=
      annealReadImmediate) m₀ = mLhs at hlhs_sim
    cases hlhs_sim with
    | ub m' msg =>
      have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind]; dsimp only
        unfold evalRvalue; dsimp only
        cases bop <;> first | exact absurd rfl hbop_ne | (dsimp only; rw [hbor, hcaller, ha_lhs])
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          (m', .error (.undefinedBehavior msg)) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_lhs]
      rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
      exact ⟨.ub _ _, fun _ _ _ _ hok => by cases hok⟩
    | ok v₁ locals₁ topFrame₁ imm₁ hframe₁ himm₁ hmono₁ htf₁ hdisj_fn₁ =>
      let m₁ : AnnealStepState := { m with stack := ⟨#[topFrame₁]⟩ }
      let knownR := if (translateBinOp bop).rightHomogeneous then some (translateTy lhsTy body.layouts) else none
      have hrhs_sim := evalOperand_scalar_simulation (m := m₁) rfl hframe₁
        (hrhsOp.mono_immediate hmono₁) s.memory.globals knownR
      dsimp only at hrhs_sim
      generalize ha_rhs : evalOperand locals₁ rhsOp .nil s.memory.globals body.layouts .nil body.localDecls = aRhs at hrhs_sim
      generalize hm_rhs : (annealEvalOperand body.localDecls body.layouts (translateOperand rhsOp) knownR >>=
        annealReadImmediate) m₁ = mRhs at hrhs_sim
      cases hrhs_sim with
      | ub m'' msg =>
        have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; rw [hkind]; dsimp only
          unfold evalRvalue; dsimp only
          cases bop <;> first | exact absurd rfl hbop_ne | (dsimp only; rw [hbor, hcaller, ha_lhs]; dsimp only; rw [ha_rhs])
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
            (m'', .error (.undefinedBehavior msg)) := by
          rw [hm_eval]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hm_lhs]
          dsimp only
          rw [EStateM.bind_eq_error hm_rhs]
        rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
        exact ⟨.ub _ _, fun _ _ _ _ hok => by cases hok⟩
      | ok v₂ locals₂ topFrame₂ imm₂ hframe₂ himm₂ hmono₂ htf₂ hdisj_fn₂ =>
        let m₂ : AnnealStepState := { m with stack := ⟨#[topFrame₂]⟩ }
        obtain ⟨sc₁, sc₂, rfl, rfl, hbin_sim⟩ :=
          scalarOps_binary_boolCmp_simulation (locals₂ := locals₂) (mem := s.memory) (m₂ := m₂)
            hbop hlhsOp.operandTy_eq hlhs hrhs hdst himm₁ himm₂
        have hbind₂ := estate_bind_pure_assoc
          (Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) ()
            (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
            ⟨imm₂, translateTy rhsTy body.layouts⟩)
          (fun result => assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts))
          (fun result => result.imm)
          (fun i => annealWriteImmediate i destPlace)
          m₂
        generalize ha_bin : evalScalarBinOp bop sc₁ sc₂ locals₂ s.memory
          (operandIsSigned body.localDecls lhsOp body.layouts) = aBin at hbin_sim
        generalize hm_bin : (do
          let result ← Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) ()
            (translateBinOp bop) ⟨imm₁, translateTy lhsTy body.layouts⟩
            ⟨imm₂, translateTy rhsTy body.layouts⟩
          assertRvalueLayoutPub result.layout (translateTy dstDecl.ty body.layouts)
          pure result.imm) m₂ = mBin at hbin_sim
        cases hbin_sim with
        | ub msg =>
          have ha_ub : evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
            unfold evalStmt; rw [hkind]; dsimp only
            unfold evalRvalue; dsimp only
            cases bop <;> first | exact absurd rfl hbop_ne | (
              dsimp only
              rw [hbor, hcaller, ha_lhs]
              dsimp only
              rw [ha_rhs]
              dsimp only
              rw [ha_bin])
          have hm_err : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
              (m₂, .error (.undefinedBehavior msg)) := by
            rw [hm_eval]
            unfold Miri.Interpreter.runRvalue
            rw [EStateM.bind_eq_ok hm_lhs]
            dsimp only
            rw [EStateM.bind_eq_ok hm_rhs]
            rw [hbind₂, EStateM.bind_eq_error hm_bin]
          rw [ha_ub, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
          exact ⟨.ub _ _, fun _ _ _ _ hok => by cases hok⟩
        | ok v' imm' himmRel' =>
          have ha_ok : evalStmt s stmt body.localDecls body.layouts =
              match get? locals₂ dstIdx with
              | .some .dead => MirStepNode.fail .ub
              | .some _ =>
                match set? locals₂ dstIdx (.init v') with
                | .some locals₃ => MirStepNode.step (advanceStmt s locals₃ s.memory)
                | .none => MirStepNode.fail .ub
              | .none => MirStepNode.fail .ub := by
            unfold evalStmt; rw [hkind]; dsimp only
            have hrv_ok : evalRvalue s.frame.locals (.binaryOp bop lhsOp rhsOp) s.memory body.localDecls body.layouts =
                .ok v' locals₂ s.memory := by
              unfold evalRvalue; dsimp only
              cases bop <;> first | exact absurd rfl hbop_ne | (
                dsimp only
                rw [hbor, hcaller, ha_lhs]
                dsimp only
                rw [ha_rhs]
                dsimp only
                exact ha_bin)
            rw [hrv_ok]
            dsimp only
            rw [hprot, hbor]
            dsimp only [invalidateConflictingBorrows]
            rw [hmem_same]; rfl
          have hm_write : Miri.Interpreter.Step.evalStatement
              (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
              Miri.Interpreter.runRvalue
                (annealWriteImmediate imm' destPlace)
                m₂ := by
            rw [hm_eval]
            apply runRvalue_eq_of_eq
            rw [EStateM.bind_eq_ok hm_lhs]
            dsimp only
            rw [EStateM.bind_eq_ok hm_rhs]
            rw [hbind₂, EStateM.bind_eq_ok hm_bin]
          have hrc₂ : topFrame₂.returnContinuation = .stop false := by
            rw [htf₂, htf₁, htf₀]; exact hretCont
          have hrp₂ : ∃ rl, topFrame₂.returnPlace = .frameLocal 0 0 none rl topFrame₂.localsIdentity := by
            rw [htf₂, htf₁, htf₀]; exact ⟨retLay, hretPlace⟩
          exact (write_after_rvalue_simulation_ext hrc₂ hrp₂ hcal hstack hbor hprot hcaller
            hframes hframe.body_eq hframe.location_eq
            (fun j hj => hmono₂ j (hmono₁ j (hmono₀ j hj)))
            hbb hstmt hframe₂ (hdisj_fn₂ (hdisj_fn₁ hdisj_tf₀_inner)) hdecl_dst
            (hmono₂ dstIdx (hmono₁ dstIdx (hmono₀ dstIdx himm_dst)))
            himmRel' ha_ok hm_write)
  | intToInt dstIdx dstDecl op srcTy hkind hdecl_dst himm_dst hop hsrc hdst =>
    obtain ⟨_, mls_dst0, _, hlt_dst0, _, hmls_opt, hmls_eq0, hloc_dst0⟩ :=
      hframe.lookup_local hdecl_dst
    let topFrame₀ := cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
    have hdisj_tf₀_inner : MemoryAllocDisjoint topFrame₀ := by
      apply MemoryAllocDisjoint.mono_layout hd_tf
      intro k
      by_cases hk : k = dstIdx
      · subst hk
        exists (translateTy dstDecl.ty body.layouts)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set]
        simp only [↓reduceIte]
        rw [hmls_opt, hmls_eq0]
        rfl
      · exists (topFrame.locals[k]?).bind (fun x => x.layout)
        dsimp [topFrame₀, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hk)]
        cases topFrame.locals[k]? <;> rfl
    let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
    have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_eq0]; exact hloc_dst0.layout_eq
    have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
        .ok ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩ m₀ :=
      annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
    have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
      hframe.cache_local_layout hdecl_dst hlt_dst0
    have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
      fun _ hj => hj.cache_layout hlt_dst0 _
    have htf₀ : topFrame₀ = { topFrame with locals := topFrame₀.locals } := rfl
    let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
    have hopTy := hop.operandTy_eq
    have hop_sim := evalOperand_scalar_simulation_opTy (m := m₀) rfl hframe₀
      (hop.mono_immediate hmono₀) s.memory.globals none
    have hm_eval : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        Miri.Interpreter.runRvalue
          (annealEvalOperand body.localDecls body.layouts (translateOperand op) none >>= fun src =>
            Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16 src .IntToInt
              (encodeTyId dstDecl.ty) destPlace) m₀ := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      rw [hkind]
      dsimp only [translateStmtKind, translatePlace, List.map, List.toArray,
        translateRvalue, translateCastKind, annealStepHooks]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
      rw [EStateM.bind_eq_ok hevalPlace_dst]
      rfl
    generalize ha_op : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls = aOp
      at hop_sim
    generalize hm_op : annealEvalOperand body.localDecls body.layouts (translateOperand op) none m₀ = mOp
      at hop_sim
    have ha_ub : aOp = .ub → evalStmt s stmt body.localDecls body.layouts = MirStepNode.fail .ub := by
      intro hub
      unfold evalStmt; rw [hkind]
      simp [evalRvalue, hbor, hcaller, ha_op, hub]
    cases hop_sim with
    | ub m' msg =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          (m', .error (.undefinedBehavior msg)) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hm_op]
      rw [ha_ub rfl, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
      exact ⟨.ub _ _, fun _ _ _ _ hok => by cases hok⟩
    | uninit m' =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          (m', .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hm_op, cast_intToInt_uninit body.layouts srcTy dstDecl.ty destPlace hsrc hdst rfl m']
      rw [ha_ub rfl, miri_step_at_statement_error _ hframes hframe.body_eq hframe.location_eq hbb hstmt hm_err]
      exact ⟨.ub _ _, fun _ _ _ _ hok => by cases hok⟩
    | ok v locals₁ topFrame₁ imm hframe₁ himmRel hmono htf₁ hdisj_fn =>
      have hprim : srcTy.kind = .bool ∨ srcTy.kind = .char ∨
          (∃ it, srcTy.kind = .int it) ∨ (∃ ut, srcTy.kind = .uint ut) := by
        rcases hsrc with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      obtain ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, _⟩ := himmRel.of_primitive_scalar hprim
      obtain ⟨_, hsz_src⟩ := sizeBytes_eq_of_translateTy hsrc hrel.validBytes hsz
      have hop_a : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals body.localDecls = .ok (.scalar sc) locals₁ := by
        rw [hbor, hcaller]; exact ha_op
      obtain ⟨msc', hrv_ok, _, hcast, hrel'⟩ :=
        evalCast_intToInt_simulation hrel destPlace hop_a hopTy hsrc hdst hsz_src
          (fun h => (hbool h).2) rfl
      have ha_ok : evalStmt s stmt body.localDecls body.layouts =
          match get? locals₁ dstIdx with
          | .some .dead => MirStepNode.fail .ub
          | .some _ =>
            match set? locals₁ dstIdx (.init (.scalar ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
                (2 : Int) ^ (8 * boolOrIntByteWidth dstDecl.ty)).toNat, boolOrIntByteWidth dstDecl.ty⟩)) with
            | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
            | .none => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub := by
        unfold evalStmt; rw [hkind]; dsimp only
        rw [hrv_ok]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same]; rfl
      have hm_write : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc')) destPlace)
            { m with stack := ⟨#[topFrame₁]⟩ } := by
        rw [hm_eval]
        apply runRvalue_eq_of_eq
        rw [EStateM.bind_eq_ok hm_op]
        exact congrFun hcast _
      have hdst' : dstDecl.ty.kind = .bool ∨ (∃ k, dstDecl.ty.kind = .int k) ∨
          (∃ k, dstDecl.ty.kind = .uint k) := Or.inr hdst
      obtain ⟨hwsz_dst, _⟩ := boolOrInt_translateTy_size hdst' body.layouts
      have himmRel' : ImmediateRel dstDecl.ty body.layouts
          (.scalar ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
            (2 : Int) ^ (8 * boolOrIntByteWidth dstDecl.ty)).toNat, boolOrIntByteWidth dstDecl.ty⟩)
          (.scalar (.fromScalarInt msc')) := by
        refine .scalar _ _ hrel' hwsz_dst ?_ ?_
        · intro hb; rcases hdst with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hb <;> cases hb
        · intro hc; rcases hdst with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hc <;> cases hc
      have hrc₁ : topFrame₁.returnContinuation = .stop false := by
        rw [htf₁, htf₀]; exact hretCont
      have hrp₁ : ∃ rl, topFrame₁.returnPlace = .frameLocal 0 0 none rl topFrame₁.localsIdentity := by
        rw [htf₁, htf₀]; exact ⟨retLay, hretPlace⟩
      exact (write_after_rvalue_simulation_ext hrc₁ hrp₁ hcal hstack hbor hprot hcaller
        hframes hframe.body_eq hframe.location_eq (fun j hj => hmono j (hmono₀ j hj))
        hbb hstmt hframe₁ (hdisj_fn hdisj_tf₀_inner) hdecl_dst
        (hmono dstIdx (hmono₀ dstIdx himm_dst)) himmRel' ha_ok
        hm_write)

/-- `MemoryAllocDisjoint` is preserved by memoizing a local's layout via
`cacheFrameLocalLayout`. -/
theorem memoryAllocDisjoint_cache_layout
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hdisj : MemoryAllocDisjoint tf)
    {idx : Nat} (hlt : idx < tf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    MemoryAllocDisjoint (cacheFrameLocalLayout tf idx hlt lay) := by
  apply MemoryAllocDisjoint.mono_layout hdisj
  intro k
  by_cases hk : k = idx
  · subst hk
    exists lay
    dsimp [cacheFrameLocalLayout]
    rw [Array.getElem?_set]
    simp only [↓reduceIte, Array.getElem?_eq_getElem hlt]
    rfl
  · exists (tf.locals[k]?).bind (fun x => x.layout)
    dsimp [cacheFrameLocalLayout]
    rw [Array.getElem?_set_ne _ (Ne.symm hk)]
    cases tf.locals[k]? <;> rfl

/-- Frame-immediacy preservation for `_d = move _s` between immediate locals
(`LM-1.4`): when `lean-miri` continues with a singleton stack, every immediate
local of the pre-frame stays immediate. -/
theorem step_assign_move_preserves_immediate
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {dstDecl srcDecl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hty : dstDecl.ty = srcDecl.ty)
    (hsz : (translateTy srcDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame])
    (himm_src : IsImmediateFrameLocal topFrame srcIdx)
    (himm_dst : IsImmediateFrameLocal topFrame dstIdx) :
    ∀ j, IsImmediateFrameLocal topFrame j →
      ∀ tf',
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
          #[tf'] →
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
          .ok true →
        IsImmediateFrameLocal tf' j := by
  intro j hj tf' htf' hok
  rcases hstate with
    ⟨topFrame', hframes', hretCont, ⟨retLay, hretPlace⟩, hfr, hcal, hstack, hbor, hprot, hcaller,
      hdisj⟩
  have h_eq : topFrame = topFrame' := by
    rw [hframes] at hframes'
    injection hframes' with h_arr
    injection h_arr
  subst h_eq
  obtain ⟨_, _, _, hlt_dst0, _, _, hmls_eq0, hloc_dst0⟩ := hfr.lookup_local hdecl_dst
  let topFrame₀ :=
    cacheFrameLocalLayout topFrame dstIdx hlt_dst0 (translateTy dstDecl.ty body.layouts)
  have hdisj₀ : MemoryAllocDisjoint topFrame₀ := memoryAllocDisjoint_cache_layout hdisj hlt_dst0 _
  let m₀ : AnnealStepState := { m with stack := ⟨#[topFrame₀]⟩ }
  have hcache_dst0 : ∀ l, (topFrame.locals[dstIdx]'hlt_dst0).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_eq0]; exact hloc_dst0.layout_eq
  have hevalPlace_dst : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none topFrame.localsIdentity,
        translateTy dstDecl.ty body.layouts⟩ m₀ :=
    annealEvalPlace_unprojected hframes hlt_dst0 hdecl_dst hcache_dst0
  have hframe₀ : FrameRel body m₀.machine s.frame topFrame₀ :=
    hfr.cache_local_layout hdecl_dst hlt_dst0
  have hmono₀ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₀ j :=
    fun _ hj => hj.cache_layout hlt_dst0 _
  let destPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local 0 dstIdx none topFrame.localsIdentity, translateTy dstDecl.ty body.layouts⟩
  have hmem_same : { s.memory with borrows := .nil, activeProtectors := .nil } = s.memory := by
    revert hbor hprot
    generalize s.memory = mem
    intro hbor hprot
    cases mem
    dsimp only at hbor hprot
    subst hbor hprot
    rfl
  dsimp only at hmem_same
  have hm_eval : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
      Miri.Interpreter.runRvalue
        ((annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) >>=
          fun imm => annealWriteImmediate imm.imm destPlace) m₀ := by
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translatePlace, translateOperand, List.map, List.toArray,
      translateRvalue, annealStepHooks]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]
    rw [EStateM.bind_eq_ok hevalPlace_dst]
    exact EStateM.bind_assoc_apply _ _ _ m₀
  obtain ⟨_, mls_src, hlt_af_src, hlt_src, hslot_src, hmls_src, hmls_src_eq, hloc_src⟩ :=
    hframe₀.lookup_local hdecl_src
  cases hloc_src with
  | dead cl hcl =>
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
        ({ m₀ with stack := ⟨#[cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
            (translateTy srcDecl.ty body.layouts)]⟩ },
          .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_eval]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error (EStateM.bind_eq_error
        (annealEvalOperand_move_dead rfl hlt_src hdecl_src hmls_src_eq (fun l hl => hcl l hl)))]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hok
    cases hok
  | indirect _ mp _ _ _ _ =>
    exact absurd rfl (hmono₀ srcIdx himm_src _ hmls_src mp)
  | immediate _ imm _ hcl hval =>
    have hlt_src' : srcIdx < (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
        (translateTy srcDecl.ty body.layouts)).locals.size := by
      rw [cacheFrameLocalLayout_size]; exact hlt_src
    let topFrame₁ := deinitFrameLocal
      (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src (translateTy srcDecl.ty body.layouts))
      srcIdx hlt_src'
    have hop := annealEvalOperand_move_live
      (known := some (translateTy dstDecl.ty body.layouts))
      (rfl : m₀.stack.frames = #[topFrame₀]) hlt_src hdecl_src hmls_src_eq
      (fun l hl => hcl l hl)
    rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
    · have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m₀ with stack := ⟨#[topFrame₁]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        have hAR : (annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
            (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
            .error (.undefinedBehavior "read of uninitialized local")
              { m₀ with stack := ⟨#[topFrame₁]⟩ } := by
          rw [EStateM.bind_eq_ok hop]
          rfl
        rw [hm_eval]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_error hAR]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hok
      cases hok
    · obtain ⟨hread, _⟩ := annealReadImmediate_of_immediateRel himmRel hsz
        (translateTy srcDecl.ty body.layouts) { m₀ with stack := ⟨#[topFrame₁]⟩ }
      have hm_op : (annealEvalOperand body.localDecls body.layouts (.Move ⟨srcIdx, #[]⟩)
          (some (translateTy dstDecl.ty body.layouts)) >>= annealReadImmediate) m₀ =
          .ok ⟨imm, translateTy srcDecl.ty body.layouts⟩ { m with stack := ⟨#[topFrame₁]⟩ } := by
        rw [EStateM.bind_eq_ok hop, hread]
      have hm_write : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue (annealWriteImmediate imm destPlace)
            { m with stack := ⟨#[topFrame₁]⟩ } := by
        rw [hm_eval]
        apply runRvalue_eq_of_eq
        exact EStateM.bind_eq_ok hm_op
      have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts =
          match get? (s.frame.locals.set srcIdx .uninit) dstIdx with
          | .some .dead => MirStepNode.fail .ub
          | .some _ =>
            match set? (s.frame.locals.set srcIdx .uninit) dstIdx (.init v) with
            | .some locals₂ => MirStepNode.step (advanceStmt s locals₂ s.memory)
            | .none => MirStepNode.fail .ub
          | .none => MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only
        have hval_ok :
            validateLoadedValue body.layouts body.localDecls (.move ⟨srcIdx, .nil⟩) v = true := by
          unfold validateLoadedValue
          have hopTy :
              operandTy body.localDecls body.layouts (.move ⟨srcIdx, .nil⟩) = some srcDecl.ty := by
            simp [operandTy, resolveProjectedTy, hdecl_src]
          rw [hopTy]
          dsimp only
          by_cases hk : srcDecl.ty.kind = .bool
          · obtain ⟨sc, _, rfl, _, _, _, hbool, _⟩ := himmRel.of_primitive_scalar (Or.inl hk)
            rcases (hbool hk).2 with hb | hb <;> simp [hk, hb]
          · cases h : srcDecl.ty.kind <;> simp_all
        have huse : evalRvalue s.frame.locals (.use (.move ⟨srcIdx, .nil⟩)) s.memory
            body.localDecls body.layouts = .ok v (s.frame.locals.set srcIdx .uninit) s.memory := by
          unfold evalRvalue
          dsimp only
          rw [hbor, hcaller]
          have hop_ok : evalOperand s.frame.locals (.move ⟨srcIdx, .nil⟩) .nil
              s.memory.globals body.layouts .nil body.localDecls =
              .ok v (s.frame.locals.set srcIdx .uninit) := by
            simp [evalOperand, hslot_src, set?_eq_some_set hlt_af_src]
          rw [hop_ok]
          dsimp only
          rw [hval_ok]
        rw [huse]
        dsimp only
        rw [hprot, hbor]
        dsimp only [invalidateConflictingBorrows]
        rw [hmem_same]
        rfl
      have hnew : LocalRel m.machine srcDecl body.layouts .uninit
          { (cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
              (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src' with
            value := .live (.immediate .uninit) } := by
        have hlay : ((cacheFrameLocalLayout topFrame₀ srcIdx hlt_src
            (translateTy srcDecl.ty body.layouts)).locals[srcIdx]'hlt_src').layout =
            some (translateTy srcDecl.ty body.layouts) := by
          simp [cacheFrameLocalLayout]
        exact .immediate .uninit .uninit _
          (by rw [hlay]; intro l hl; exact (Option.some.inj hl).symm) (Or.inl ⟨rfl, rfl⟩)
      have hframe₁ : FrameRel body m.machine
          { s.frame with locals := s.frame.locals.set srcIdx .uninit } topFrame₁ :=
        (hframe₀.cache_local_layout hdecl_src hlt_src).update_local hdecl_src .uninit
          (.live (.immediate .uninit)) hnew
      have hdisj₁ : MemoryAllocDisjoint topFrame₁ := by
        apply MemoryAllocDisjoint.mono_immediate (tf := topFrame₀) hdisj₀
        intro k
        by_cases hk : k = srcIdx
        · subst hk
          right
          exact ⟨.uninit, some (translateTy srcDecl.ty body.layouts), by
            simp [topFrame₁, deinitFrameLocal, cacheFrameLocalLayout]⟩
        · left
          simp [topFrame₁, deinitFrameLocal, cacheFrameLocalLayout,
            Array.getElem?_set_ne _ (Ne.symm hk)]
      have hmono₁ : ∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame₁ j :=
        fun j hj => ((hmono₀ j hj).cache_layout hlt_src _).set_immediate hlt_src' .uninit
      have himmRel' : ImmediateRel dstDecl.ty body.layouts v imm := hty ▸ himmRel
      have hext := write_after_rvalue_simulation_ext (tf₀ := topFrame) (topFrame₁ := topFrame₁)
        hretCont ⟨retLay, hretPlace⟩ hcal hstack hbor hprot hcaller
        hframes hfr.body_eq hfr.location_eq hmono₁ hbb hstmt hframe₁ hdisj₁
        hdecl_dst (hmono₁ dstIdx himm_dst) himmRel' ha_ok hm_write
      exact hext.2 j hj tf' htf' hok

/-- `LM-1.4` move simulation (`step_stmt_lm1_4_simulation`) together with
frame-immediacy preservation. -/
theorem step_assign_move_simulation_ext
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {dstDecl srcDecl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hty : dstDecl.ty = srcDecl.ty)
    (hsz : (translateTy srcDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf',
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
            #[tf'] →
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
            .ok true →
          IsImmediateFrameLocal tf' j) :=
  ⟨step_stmt_lm1_4_simulation hstate hphase hbb hstmt (fun tf hframes =>
      .assignMove dstIdx srcIdx dstDecl srcDecl span hdecl_dst hdecl_src hty hsz
        (himm_src tf hframes) (himm_dst tf hframes)),
    fun tf hframes => step_assign_move_preserves_immediate hstate hbb hstmt hdecl_dst hdecl_src
      hty hsz hframes (himm_src tf hframes) (himm_dst tf hframes)⟩

/-! ### Extended statements: `LM-1.2` comparisons and casts, `LM-1.4` moves -/

/-- Syntactic statement well-typedness of the extended scalar fragment: the
`LM-1.1` statements (`WellTypedScalarStmtSyn`), `LM-1.2` comparisons of `bool`
operands and `IntToInt` casts from `bool` or integer operands to integers, and
`LM-1.4` moves between immediate locals of a non-zero-sized type. -/
inductive WellTypedScalarStmtExt (body : CapturedMir) (nonAddrTaken : Nat → Prop) :
    MirAst.Statement → Prop where
  | syn (stmt : Statement) :
      WellTypedScalarStmtSyn body nonAddrTaken stmt →
      WellTypedScalarStmtExt body nonAddrTaken stmt
  | boolCmp (stmt : Statement) (dstIdx : Local) (dstDecl : LocalDecl) (bop : MirAst.BinOp)
      (lhsOp rhsOp : MirAst.Operand) (lhsTy rhsTy : Ty) :
      stmt.kind = .assign ⟨dstIdx, .nil⟩ (.binaryOp bop lhsOp rhsOp) →
      get? body.localDecls dstIdx = some dstDecl →
      nonAddrTaken dstIdx →
      IsCmpBinOp bop →
      WellTypedScalarOperandSyn body nonAddrTaken lhsOp lhsTy →
      WellTypedScalarOperandSyn body nonAddrTaken rhsOp rhsTy →
      lhsTy.kind = .bool → rhsTy.kind = .bool → dstDecl.ty.kind = .bool →
      WellTypedScalarStmtExt body nonAddrTaken stmt
  | intToInt (stmt : Statement) (dstIdx : Local) (dstDecl : LocalDecl)
      (op : MirAst.Operand) (srcTy : Ty) :
      stmt.kind = .assign ⟨dstIdx, .nil⟩ (.cast .intToInt op dstDecl.ty) →
      get? body.localDecls dstIdx = some dstDecl →
      nonAddrTaken dstIdx →
      WellTypedScalarOperandSyn body nonAddrTaken op srcTy →
      (srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k)) →
      ((∃ k, dstDecl.ty.kind = .int k) ∨ (∃ k, dstDecl.ty.kind = .uint k)) →
      WellTypedScalarStmtExt body nonAddrTaken stmt
  | move (stmt : Statement) (dstIdx srcIdx : Local) (dstDecl srcDecl : LocalDecl) :
      stmt.kind = .assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)) →
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcIdx = some srcDecl →
      dstDecl.ty = srcDecl.ty →
      (translateTy srcDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      nonAddrTaken srcIdx →
      nonAddrTaken dstIdx →
      WellTypedScalarStmtExt body nonAddrTaken stmt

/-- Every extended-fragment statement is a `Nop`, `StorageLive`, `StorageDead`, or
an assignment to an unprojected local. -/
theorem WellTypedScalarStmtExt.kind_cases {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {stmt : Statement} (h : WellTypedScalarStmtExt body nonAddrTaken stmt) :
    stmt.kind = .nop ∨ (∃ l, stmt.kind = .storageLive l) ∨ (∃ l, stmt.kind = .storageDead l) ∨
      (∃ dstIdx rv, stmt.kind = .assign ⟨dstIdx, .nil⟩ rv) := by
  cases h with
  | syn hsyn =>
    cases hsyn with
    | nop hk => exact Or.inl hk
    | storageLive loc _ hk _ _ => exact Or.inr (Or.inl ⟨loc, hk⟩)
    | storageDead loc _ hk _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨loc, hk⟩))
    | assign dstIdx _ rv hk _ _ _ => exact Or.inr (Or.inr (Or.inr ⟨dstIdx, rv, hk⟩))
  | boolCmp dstIdx _ _ _ _ _ _ hk => exact Or.inr (Or.inr (Or.inr ⟨dstIdx, _, hk⟩))
  | intToInt dstIdx _ _ _ hk => exact Or.inr (Or.inr (Or.inr ⟨dstIdx, _, hk⟩))
  | move dstIdx _ _ _ hk => exact Or.inr (Or.inr (Or.inr ⟨dstIdx, _, hk⟩))

/-- Statement step simulation for the extended fragment, together with
frame-immediacy preservation. -/
theorem step_stmtExt_simulation_ext
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedScalarStmtExt body nonAddrTaken stmt)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ j, IsImmediateFrameLocal topFrame j →
        ∀ tf',
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
            #[tf'] →
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
            .ok true →
          IsImmediateFrameLocal tf' j) := by
  cases hwt with
  | syn hsyn =>
    exact step_assign_scalar_simulation_ext hstate hphase hbb hstmt
      (fun tf hframes => hsyn.toFrame hframes himm)
  | boolCmp dstIdx dstDecl bop lhsOp rhsOp lhsTy rhsTy hkind hdecl hna hbop hlhs hrhs hl hr hd =>
    exact step_assign_lm1_2_simulation_ext hstate hphase hbb hstmt (fun tf hframes =>
      .boolCmp stmt dstIdx dstDecl bop lhsOp rhsOp lhsTy rhsTy hkind hdecl
        (himm tf hframes dstIdx dstDecl hdecl hna) hbop (hlhs.toFrame hframes himm)
        (hrhs.toFrame hframes himm) hl hr hd)
  | intToInt dstIdx dstDecl op srcTy hkind hdecl hna hop hsrc hdst =>
    exact step_assign_lm1_2_simulation_ext hstate hphase hbb hstmt (fun tf hframes =>
      .intToInt stmt dstIdx dstDecl op srcTy hkind hdecl
        (himm tf hframes dstIdx dstDecl hdecl hna) (hop.toFrame hframes himm) hsrc hdst)
  | move dstIdx srcIdx dstDecl srcDecl hkind hdecl_dst hdecl_src hty hsz hna_src hna_dst =>
    rcases stmt with ⟨kind, span⟩
    dsimp only at hkind
    subst hkind
    exact step_assign_move_simulation_ext hstate hphase hbb hstmt hdecl_dst hdecl_src hty hsz
      (fun tf hframes => himm tf hframes srcIdx srcDecl hdecl_src hna_src)
      (fun tf hframes => himm tf hframes dstIdx dstDecl hdecl_dst hna_dst)

/-! ### Extended unconditional fragment: `LM-1.1` plus `SwitchInt` and `Assert … unreachable` -/

/-- Syntactic terminator well-typedness of the extended scalar fragment: the
`LM-1.1` terminators (`Goto`, `Return`, `Unreachable`), `SwitchInt` on a `bool`
or integer discriminant with in-range case values, and `Assert … unreachable`
on a `bool` condition, with every jump target in bounds. -/
inductive WellTypedTerminatorExt (body : CapturedMir) (nonAddrTaken : Nat → Prop)
    (term : Terminator) : Prop where
  | goto (target : BasicBlockIdx) (targetBb : BasicBlockData) :
      term.kind = .goto target →
      get? body.basicBlocks target = some targetBb →
      WellTypedTerminatorExt body nonAddrTaken term
  | return_ (decl0 : LocalDecl) :
      term.kind = .return_ →
      nonAddrTaken 0 →
      get? body.localDecls 0 = some decl0 →
      (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO →
      WellTypedTerminatorExt body nonAddrTaken term
  | unreachable :
      term.kind = .unreachable →
      WellTypedTerminatorExt body nonAddrTaken term
  | switchInt (discr : MirAst.Operand) (targets : SwitchTargets) (ty : Ty) :
      term.kind = .switchInt discr targets →
      (ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k)) →
      WellTypedScalarOperandSyn body nonAddrTaken discr ty →
      SwitchCasesFit ty targets →
      (∃ bb', get? body.basicBlocks targets.otherwise = some bb') →
      (∀ v b, (v, b) ∈ targets.branches → ∃ bb', get? body.basicBlocks b = some bb') →
      WellTypedTerminatorExt body nonAddrTaken term
  | assertUnreachable (cond : MirAst.Operand) (expected : Bool) (target : BasicBlockIdx)
      (condTy : Ty) (targetBb : BasicBlockData) :
      term.kind = .assert cond expected target .unreachable →
      condTy.kind = .bool →
      WellTypedScalarOperandSyn body nonAddrTaken cond condTy →
      get? body.basicBlocks target = some targetBb →
      WellTypedTerminatorExt body nonAddrTaken term

/-- Syntactic basic-block well-typedness of the extended scalar fragment
(`WellTypedScalarStmtExt` statements, `WellTypedTerminatorExt` terminator). -/
structure WellTypedBasicBlockExt
    (body : CapturedMir) (nonAddrTaken : Nat → Prop) (bb : BasicBlockData) : Prop where
  not_cleanup : bb.isCleanup = false
  stmts_wt : ∀ stmt, stmt ∈ bb.statements → WellTypedScalarStmtExt body nonAddrTaken stmt
  term_wt : WellTypedTerminatorExt body nonAddrTaken bb.terminator

/-- Syntactic whole-body well-typedness of the extended scalar fragment. -/
structure WellTypedBodyExt
    (body : CapturedMir) (nonAddrTaken : Nat → Prop := fun _ => True) : Prop where
  phase_ok : ∀ p, body.phase ≠ .other p
  blocks_wt : ∀ bb, bb ∈ body.basicBlocks → WellTypedBasicBlockExt body nonAddrTaken bb

/-- The `LM-1.1` fragment embeds in the extended fragment. -/
theorem WellTypedBody.toExt {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (h : WellTypedBody body nonAddrTaken) : WellTypedBodyExt body nonAddrTaken := by
  refine ⟨h.phase_ok, fun bb hbb => ?_⟩
  have hwt := h.blocks_wt bb hbb
  refine ⟨hwt.not_cleanup, fun stmt hmem => .syn stmt (hwt.stmts_wt stmt hmem), ?_⟩
  rcases hwt.term_wt with
    ⟨target, targetBb, hgoto, htbb⟩ | ⟨hret, hna0, decl0, hdecl0, hsz0⟩ | hunreach
  · exact .goto target targetBb hgoto htbb
  · exact .return_ decl0 hret hna0 hdecl0 hsz0
  · exact .unreachable hunreach

/-- Unified small-step simulation for the extended fragment (`StepObsRel`, since
`SwitchInt` emits `MirObs.event`). -/
theorem step_wellTypedBodyExt_simulation
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBodyExt body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    StepObsRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hbb_mem : bb ∈ body.basicBlocks := by
    rw [get?_eq_getElem?] at hbb
    exact List.mem_of_getElem? hbb
  have hbb_wt := hbody.blocks_wt bb hbb_mem
  by_cases hlt : s.frame.stmtIdx < bb.statements.length
  · have hstmt : get? bb.statements s.frame.stmtIdx =
        some (bb.statements[s.frame.stmtIdx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    have hstmt_syn := hbb_wt.stmts_wt _ (List.getElem_mem hlt)
    exact (step_stmtExt_simulation_ext hstate hbody.phase_ok hbb hstmt hstmt_syn himm).1.toStepObsRel
  · have hlen_eq : s.frame.stmtIdx = length bb.statements := by
      rw [length_eq_length]; omega
    have hstmt_none : get? bb.statements s.frame.stmtIdx = none := by
      rw [get?_eq_getElem?, List.getElem?_eq_none (by omega)]
    cases hbb_wt.term_wt with
    | goto target _ hgoto _ =>
      exact (step_terminator_goto_return_simulation hstate hbody.phase_ok hbb hstmt_none hlen_eq
        hbb_wt.not_cleanup (Or.inl ⟨target, hgoto⟩)).toStepObsRel
    | return_ decl0 hret hna0 hdecl0 hsz0 =>
      exact (step_terminator_goto_return_simulation hstate hbody.phase_ok hbb hstmt_none hlen_eq
        hbb_wt.not_cleanup (Or.inr (Or.inl ⟨hret, decl0, hdecl0, hsz0,
          fun tf hframes => himm tf hframes 0 decl0 hdecl0 hna0⟩))).toStepObsRel
    | unreachable hunreach =>
      exact (step_terminator_goto_return_simulation hstate hbody.phase_ok hbb hstmt_none hlen_eq
        hbb_wt.not_cleanup (Or.inr (Or.inr hunreach))).toStepObsRel
    | switchInt discr targets ty hsw hty hdiscr hcases _ _ =>
      exact (step_terminator_switchInt_simulation_imm hstate hbody.phase_ok hbb hstmt_none hlen_eq
        hsw hty (fun tf hframes => hdiscr.toFrame hframes himm) hcases).1
    | assertUnreachable cond expected target condTy _ hassert hbool hcond _ =>
      exact (step_terminator_assert_unreachable_simulation hstate hbody.phase_ok hbb hstmt_none
        hlen_eq hassert hbool (fun tf hframes => hcond.toFrame hframes himm)).1.toStepObsRel

/-- `ValidFrameLocation` is preserved across every intra-frame step (silent or
event-emitting) of an extended-fragment body. -/
theorem ValidFrameLocation.preservedExt
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s s' : MachineState} {m : AnnealStepState} {obs : MirObs}
    (hbody : WellTypedBodyExt body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m)
    (hstep : stepMirFn body s = .emitStep obs s') :
    ValidFrameLocation body s'.frame := by
  have hstate' := hstate
  rcases hstate' with ⟨_, _, _, _, _, hcal, hstack, _, _, _, _⟩
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hbb_mem : bb ∈ body.basicBlocks := by
    rw [get?_eq_getElem?] at hbb
    exact List.mem_of_getElem? hbb
  have hbb_wt := hbody.blocks_wt bb hbb_mem
  by_cases hlt : s.frame.stmtIdx < bb.statements.length
  · have hstmt : get? bb.statements s.frame.stmtIdx =
        some (bb.statements[s.frame.stmtIdx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    have hstmt_syn := hbb_wt.stmts_wt _ (List.getElem_mem hlt)
    have hsim := (step_stmtExt_simulation_ext hstate hbody.phase_ok hbb hstmt hstmt_syn himm).1
    cases obs with
    | event t =>
      rw [hstep] at hsim
      cases hsim
    | silent =>
      rw [stepMirFn_eq_of_not_other body s hcal hbody.phase_ok] at hstep
      simp only [hbb, hstmt] at hstep
      obtain ⟨hblk, hidx⟩ := evalStmt_step_location hstmt_syn.kind_cases hstep
      exact ⟨bb, by rw [hblk]; exact hbb, by omega⟩
  · have hlen_eq : s.frame.stmtIdx = length bb.statements := by
      rw [length_eq_length]; omega
    have hstmt_none : get? bb.statements s.frame.stmtIdx = none := by
      rw [get?_eq_getElem?, List.getElem?_eq_none (by omega)]
    rw [stepMirFn_at_terminator hcal hbody.phase_ok hbb hstmt_none hlen_eq] at hstep
    cases hbb_wt.term_wt with
    | goto target targetBb hgoto htbb =>
      unfold evalTerminator at hstep
      rw [hgoto] at hstep
      have h := emitStep_state_inj (o₁ := .silent) hstep
      subst h
      exact ⟨targetBb, htbb, Nat.zero_le _⟩
    | return_ _ hret _ _ _ =>
      unfold evalTerminator at hstep
      rw [hret, hstack] at hstep
      dsimp only at hstep
      revert hstep
      cases get? s.frame.locals 0 with
      | none => exact fun hstep => absurd hstep fail_ne_emitStep
      | some slot =>
        cases slot with
        | dead => exact fun hstep => absurd hstep fail_ne_emitStep
        | uninit => exact fun hstep => absurd hstep fail_ne_emitStep
        | init _ => exact fun hstep => absurd hstep retNormal_ne_emitStep
    | unreachable hunreach =>
      unfold evalTerminator at hstep
      rw [hunreach] at hstep
      exact absurd hstep fail_ne_emitStep
    | switchInt discr targets ty hsw _ _ _ hother hbranches =>
      obtain ⟨bits, hblk, hidx⟩ := evalTerminator_switchInt_location hsw hstep
      have hvalid : ∃ bb', get? body.basicBlocks
          (lookupSwitchTarget bits targets.branches targets.otherwise) = some bb' := by
        rcases lookupSwitchTarget_cases bits targets.branches targets.otherwise with h | ⟨v, hmem⟩
        · rw [h]; exact hother
        · exact hbranches _ _ hmem
      obtain ⟨bb', hbb'⟩ := hvalid
      exact ⟨bb', by rw [hblk]; exact hbb', by rw [hidx]; exact Nat.zero_le _⟩
    | assertUnreachable cond expected target condTy targetBb hassert _ _ htbb =>
      obtain ⟨hblk, hidx⟩ := evalTerminator_assert_unreachable_location hassert hstep
      exact ⟨targetBb, by rw [hblk]; exact htbb, by rw [hidx]; exact Nat.zero_le _⟩

/-- `NonAddrTakenImmediate` is preserved across every `lean-miri` step that
continues (`.ok true`) on an extended-fragment body. -/
theorem NonAddrTakenImmediate.preservedExt
    {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBodyExt body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m)
    (hm_ok : (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
      .ok true) :
    NonAddrTakenImmediate body nonAddrTaken
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1 := by
  intro tf' htf' idx decl hdecl hna
  obtain ⟨bb, hbb, hle⟩ := hloc
  have hbb_mem : bb ∈ body.basicBlocks := by
    rw [get?_eq_getElem?] at hbb
    exact List.mem_of_getElem? hbb
  have hbb_wt := hbody.blocks_wt bb hbb_mem
  by_cases hlt : s.frame.stmtIdx < bb.statements.length
  · have hstmt : get? bb.statements s.frame.stmtIdx =
        some (bb.statements[s.frame.stmtIdx]'hlt) := by
      rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    have hstmt_syn := hbb_wt.stmts_wt _ (List.getElem_mem hlt)
    have hext := (step_stmtExt_simulation_ext hstate hbody.phase_ok hbb hstmt hstmt_syn himm).2
    rcases hstate with ⟨topFrame, hframes, _, _, _, _, _, _, _, _⟩
    exact hext topFrame hframes idx (himm topFrame hframes idx decl hdecl hna) tf' htf' hm_ok
  · have hlen_eq : s.frame.stmtIdx = length bb.statements := by
      rw [length_eq_length]; omega
    have hstmt_none : get? bb.statements s.frame.stmtIdx = none := by
      rw [get?_eq_getElem?, List.getElem?_eq_none (by omega)]
    cases hbb_wt.term_wt with
    | goto target _ hgoto _ =>
      rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _⟩
      have himm_orig := himm topFrame hframes idx decl hdecl hna
      have hm_step := miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb
        hstmt_none
      unfold translateTerminator
        Miri.Interpreter.ControlFlow.evalTerminator
        Miri.Interpreter.ControlFlow.goToBlock
        Miri.Interpreter.ControlFlow.setLocation at hm_step
      rw [hgoto, stack_currentFrame?_singleton m.stack topFrame hframes, hframes] at hm_step
      dsimp only [translateTerminatorKind, Except.map, Id.run] at hm_step
      rw [hm_step] at htf'
      dsimp only at htf'
      injection htf' with h_arr
      injection h_arr with h_eq _
      subst h_eq
      exact himm_orig
    | return_ decl0 hret hna0 hdecl0 hsz0 =>
      have hsim := step_terminator_goto_return_simulation hstate hbody.phase_ok hbb hstmt_none
        hlen_eq hbb_wt.not_cleanup
        (Or.inr (Or.inl ⟨hret, decl0, hdecl0, hsz0,
          fun tf hframes => himm tf hframes 0 decl0 hdecl0 hna0⟩))
      rcases hstate with ⟨_, _, _, _, _, hcal, hstack, _, _, _⟩
      generalize ha_eq : stepMirFn body s = aRes at hsim
      generalize Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        mRes at hsim htf' hm_ok
      cases hsim with
      | ub _ _ => cases hm_ok
      | retRoot _ _ _ _ _ _ _ _ hm' =>
        subst hm'
        dsimp only at htf'
        cases htf'
      | step s' _ _ =>
        rw [stepMirFn_eq_of_not_other body s hcal hbody.phase_ok] at ha_eq
        have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
          simp [hlen_eq]
        simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte] at ha_eq
        unfold evalTerminator at ha_eq
        rw [hret, hstack] at ha_eq
        dsimp only at ha_eq
        revert ha_eq
        cases get? s.frame.locals 0 with
        | none => exact fun ha_eq => absurd ha_eq MirStepNode_fail_ne_step
        | some slot =>
          cases slot with
          | dead => exact fun ha_eq => absurd ha_eq MirStepNode_fail_ne_step
          | uninit => exact fun ha_eq => absurd ha_eq MirStepNode_fail_ne_step
          | init _ => exact fun ha_eq => absurd ha_eq MirStepNode_retNormal_ne_step
    | unreachable hunreach =>
      rcases hstate with ⟨topFrame, hframes, _, _, hframe, _, _, _, _, _⟩
      have hm_step := miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb
        hstmt_none
      unfold translateTerminator Miri.Interpreter.ControlFlow.evalTerminator at hm_step
      rw [hunreach] at hm_step
      dsimp only [translateTerminatorKind, Except.map, Id.run] at hm_step
      rw [hm_step] at hm_ok
      cases hm_ok
    | switchInt discr targets ty hsw hty hdiscr hcases _ _ =>
      have hpres := (step_terminator_switchInt_simulation_imm hstate hbody.phase_ok hbb hstmt_none
        hlen_eq hsw hty (fun tf hframes => hdiscr.toFrame hframes himm) hcases).2
      rcases hstate with ⟨topFrame, hframes, _, _, _, _, _, _, _, _⟩
      exact hpres topFrame tf' hframes hm_ok htf' idx (himm topFrame hframes idx decl hdecl hna)
    | assertUnreachable cond expected target condTy _ hassert hbool hcond _ =>
      have hpres := (step_terminator_assert_unreachable_simulation hstate hbody.phase_ok hbb
        hstmt_none hlen_eq hassert hbool (fun tf hframes => hcond.toFrame hframes himm)).2
      rcases hstate with ⟨topFrame, hframes, _, _, _, _, _, _, _, _⟩
      exact hpres topFrame tf' hframes hm_ok htf' idx (himm topFrame hframes idx decl hdecl hna)

/-! ### Closed-simulation glue for the extended fragment

These declarations use the `StepClosedSim` engine of `Safety.lean`
(`Lockstep`, `StepClosedSim`, `annealMiriHooks`, `ScalarFragmentInv`,
`ImmediateRetRel`, `stateRel_entry`, `entry_immediate`,
`treeSafe_iff_miriSafe`), so they belong after those definitions. -/

/-- Lift a `StepObsRel` to `Lockstep` over the `annealMiriHooks` interpreter,
given `Inv` at every related post-state reached by an Anneal `emitStep`. -/
theorem StepObsRel.toLockstepExt {body : CapturedMir}
    {Inv : MachineState → AnnealStepState → Prop}
    {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRel body m aRes mRes)
    (hinv : ∀ obs s' m', aRes = .emitStep obs s' → mRes = (m', .ok true) →
      StateRel body s' m' → Inv s' m') :
    Lockstep (annealMiriHooks body) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | emitStep obs s' m' hrel =>
    have hne : m'.stack.frames ≠ #[] := by
      obtain ⟨tf, hf, _⟩ := id hrel
      rw [hf]; intro h; cases h
    exact .emitStep obs s' m' (hinv obs s' m' rfl rfl hrel) hne
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (by
      change (annealControlHooks.returnOperand () m).2 = _; rw [hop])
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg =>
    exact .fault .ub m' (.undefinedBehavior msg)
      (by first | rfl | exact ⟨fun _ => rfl, fun _ => rfl⟩)

/-- **Extended unconditional closed-fragment instance.** For every body in
`WellTypedBodyExt` (`LM-1.1` plus `SwitchInt` on `bool`/integer discriminants
and `Assert … unreachable` on `bool` conditions), `ScalarFragmentInv` is
step-closed with no per-step hypotheses. -/
theorem scalarFragmentExt_stepClosedSim {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (hbody : WellTypedBodyExt body nonAddrTaken) :
    StepClosedSim body (annealMiriHooks body) (ScalarFragmentInv body nonAddrTaken)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨hstate, hloc, himm⟩ => ?_⟩
  have hstep := step_wellTypedBodyExt_simulation hbody hstate hloc himm
  have himm' := NonAddrTakenImmediate.preservedExt hbody hstate hloc himm
  refine StepObsRel.toLockstepExt hstep fun obs s' m' ha hm hrel =>
    ⟨hrel, ValidFrameLocation.preservedExt hbody hstate hloc himm ha, ?_⟩
  change Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
    (m', .ok true) at hm
  have h := himm' (by rw [hm])
  rw [hm] at h
  exact h

/-- The entry states satisfy the closed invariant for every nonempty body. -/
theorem scalarFragmentExt_entry {body : CapturedMir} (hne : body.basicBlocks ≠ []) :
    ScalarFragmentInv body (fun _ => True) (initMachineState body []) (miriEntryState body) := by
  refine ⟨stateRel_entry body, ?_, entry_immediate body _⟩
  cases hb : body.basicBlocks with
  | nil => exact absurd hb hne
  | cons bb bbs => exact ⟨bb, by rw [hb]; rfl, Nat.zero_le _⟩

/-- Integration check: whole-program `TreeSafe ↔ System.Safe` for the extended
fragment. -/
theorem scalarFragmentExt_treeSafe_iff_miriSafe {body : CapturedMir}
    (hbody : WellTypedBodyExt body) (hne : body.basicBlocks ≠ []) :
    TreeSafe (mirCallTree body []) ↔
      (miriSystem (annealMiriHooks body)).Safe (miriEntryState body) :=
  treeSafe_iff_miriSafe (scalarFragmentExt_stepClosedSim hbody) (scalarFragmentExt_entry hne)

/-- `InSafeScalarFragment body`: the syntactic, unconditional scalar fragment
`WellTypedBodyExt` (`LM-1.1` statements and terminators, plus `SwitchInt` on
`bool` / integer discriminants and `Assert … unreachable` on `bool`
conditions) with every local immediate, over a nonempty body. -/
structure InSafeScalarFragment (body : CapturedMir) : Prop where
  wellTyped : WellTypedBodyExt body
  blocks_ne : body.basicBlocks ≠ []

/-- Every fault of a body in the extended fragment is undefined behavior: the
fragment has no unsupported construct and no fuel bound. -/
theorem scalarFragmentExt_ubOnly {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (hbody : WellTypedBodyExt body nonAddrTaken) :
    UBOnlyFaults body (ScalarFragmentInv body nonAddrTaken) := by
  intro s m ⟨hstate, hloc, himm⟩ k hk
  have h := step_wellTypedBodyExt_simulation hbody hstate hloc himm
  rw [hk] at h
  generalize Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
    mRes at h
  generalize ha : MirStepNode.fail k = aRes at h
  cases h with
  | emitStep obs s' m' _ => cases obs <;> cases ha
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub m' msg =>
    injection ha with ha
    injection ha with ha
    injection ha with ha

/-- The entry states satisfy the closed invariant. -/
theorem scalarFragment_entry {body : CapturedMir} (hfrag : InSafeScalarFragment body) :
    ScalarFragmentInv body (fun _ => True) (initMachineState body []) (miriEntryState body) := by
  refine ⟨stateRel_entry body, ?_, entry_immediate body _⟩
  cases hb : body.basicBlocks with
  | nil => exact absurd hb hfrag.blocks_ne
  | cons bb bbs => exact ⟨bb, by rw [hb]; rfl, Nat.zero_le _⟩

section ScalarFragment

variable {body : CapturedMir} (hfrag : InSafeScalarFragment body)
include hfrag

/-- `TreeSafe (mirCallTree body []) ↔ System.Safe` for the unconditional fragment. -/
theorem scalarFragment_treeSafe_iff_miriSafe :
    TreeSafe (mirCallTree body []) ↔
      (miriSystem (annealMiriHooks body)).Safe (miriEntryState body) :=
  treeSafe_iff_miriSafe (scalarFragmentExt_stepClosedSim hfrag.wellTyped) (scalarFragment_entry hfrag)

/-- Bidirectional finite-step UB reachability for the unconditional fragment. -/
theorem scalarFragment_reachesUB_iff :
    MirReachesUB (mirCallTree body []) ↔
      ∃ e, (miriSystem (annealMiriHooks body)).ReachesOutcome (miriEntryState body)
        (.undefinedBehavior e) :=
  reachesUB_iff_miriReachesUB (scalarFragmentExt_stepClosedSim hfrag.wellTyped)
    (scalarFragment_entry hfrag)

/-- Partial-correctness equivalence for the unconditional fragment. -/
theorem scalarFragment_partialCorrect_iff (postA : Value → Prop)
    (postM : Miri.Interpreter.Operand AnnealProv → Prop)
    (hpost : ∀ retVal v, ImmediateRetRel body retVal v → (postA retVal ↔ postM v)) :
    (miriSystem (annealMiriHooks body)).PartialCorrect (miriEntryState body) postM ↔
      ∀ tr retVal mem, ReachesRet (mirCallTree body []) tr (.normal (retVal, mem)) →
        postA retVal :=
  partialCorrect_iff_annealPostcondition (scalarFragmentExt_stepClosedSim hfrag.wellTyped)
    (scalarFragment_entry hfrag) postA postM hpost

/-- Multi-step `RunLoop` simulation for the unconditional fragment, for every fuel. -/
theorem scalarFragment_runLoop_simulation (fuel : Nat) :
    RunLoopRel (ScalarFragmentInv body (fun _ => True)) (ImmediateRetRel body)
      (runAnnealBounded body fuel (initMachineState body []))
      (runLoopFuel (annealMiriHooks body) fuel (miriEntryState body)) :=
  runLoop_universal_simulation (scalarFragmentExt_stepClosedSim hfrag.wellTyped) fuel
    (scalarFragment_entry hfrag)

/-- Divergence correspondence for the unconditional fragment. -/
theorem scalarFragment_infiniteRun_iff :
    Miri.OperationalSafety.InfiniteRun (miriSystem (annealMiriHooks body)) (miriEntryState body) ↔
      ∀ n, ∃ s', runAnnealBounded body n (initMachineState body []) = .running s' :=
  infiniteRun_iff_anneal_forever (scalarFragmentExt_stepClosedSim hfrag.wellTyped)
    (scalarFragment_entry hfrag)

/-- In the unconditional fragment every reachable `lean-miri` outcome is a
normal return or undefined behavior: no unsupported or blocked outcome is
reachable. -/
theorem scalarFragment_outcomes :
    ∀ o, (miriSystem (annealMiriHooks body)).ReachesOutcome (miriEntryState body) o →
      o.isReturn ∨ ∃ e, o = .undefinedBehavior e :=
  miri_outcomes_of_ubOnly (scalarFragmentExt_stepClosedSim hfrag.wellTyped)
    (scalarFragmentExt_ubOnly hfrag.wellTyped) (scalarFragment_entry hfrag)

/-- In the unconditional fragment every finitely reachable Anneal fault is
undefined behavior. -/
theorem scalarFragment_faults_ub {k : FailureKind}
    (hk : MirReachesFault (mirCallTree body []) k) : k = .ub :=
  anneal_faults_ub_of_ubOnly (scalarFragmentExt_stepClosedSim hfrag.wellTyped)
    (scalarFragmentExt_ubOnly hfrag.wellTyped) (scalarFragment_entry hfrag) hk

/-- Class-wise fault reachability for the unconditional fragment. -/
theorem scalarFragment_reachesFault_iff (k : FailureKind) :
    MirReachesFault (mirCallTree body []) k ↔
      ∃ o, (miriSystem (annealMiriHooks body)).ReachesOutcome (miriEntryState body) o ∧
        outcomeFaultClass o = some (annealFaultClass k) :=
  reachesFault_iff_miriReachesClass (scalarFragmentExt_stepClosedSim hfrag.wellTyped)
    (scalarFragment_entry hfrag) k

end ScalarFragment

/-! ## 10. Bridges from the `LM-1` … `LM-4.2` step relations -/

section Bridges

variable {core : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool}

/-- An interpreter whose root-frame return reads `_0` through `annealControlHooks`
(the `LM-1`, `LM-2`, `LM-3`, and `LM-4.2` interpreters). -/
def rootHooks (core : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool) :
    AnnealMiriHooks :=
  ⟨core, annealControlHooks.returnOperand⟩

theorem frames_ne_of_eq_singleton {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : m.stack.frames = #[tf]) : m.stack.frames ≠ #[] := by
  rw [h]; intro h'; cases h'

theorem retRoot_operand {m : AnnealStepState} {imm0 : Miri.Interpreter.Immediate AnnealProv}
    (hop : annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0))) :
    ((rootHooks core).returnOperand () m).2 = .ok (.immediate imm0) := by
  change (annealControlHooks.returnOperand () m).2 = _
  rw [hop]

theorem ub_faultAgrees (msg : String) :
    FaultAgrees .ub (.undefinedBehavior msg) := rfl

/-- `LM-1.2` `StepObsRel` (`SwitchInt` branch observations) as `Lockstep`. -/
theorem StepObsRel.toLockstep {body : CapturedMir} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop} (h : StepObsRel body m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRel body s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep obs s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.2` `StepRelLM2_2` (struct / tuple projections) as `Lockstep`. -/
theorem StepRelLM2_2.toLockstep {body : CapturedMir} {env : StructTypeEnv}
    {stEnv' : LM2_2StaticEnv} {b' : Nat} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (h : StepRelLM2_2 body env stEnv' b' m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM2_2 body env stEnv' b' s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv RetRel m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.3` `StepRelLM2_3` (multi-variant enums, `Downcast`, `SwitchInt`) as `Lockstep`. -/
theorem StepRelLM2_3.toLockstep {body : CapturedMir} {env : EnumTypeEnv} {b' : Nat}
    {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelLM2_3 body env b' m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM2_3 body env b' s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep obs s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.4` `StepRelLM2_4` (unions) as `Lockstep`. -/
theorem StepRelLM2_4.toLockstep {body : CapturedMir} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (h : StepRelLM2_4 body m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM2_4 body s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv RetRel m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-3.1` / `LM-4.2` `StepRelLM3_1` (raw pointers, intrinsics) as `Lockstep`. -/
theorem StepRelLM3_1.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelLM3_1 body m allocMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_1 body s' m' allocMap → Inv s' m') :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- Return relation of `LM-3.2`: an immediate `ImmediateRelLM3_2`-related at `_0`'s type. -/
def RefRetRel (body : CapturedMir) (allocMap : List AllocMapEntry) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0 imm0, get? body.localDecls 0 = some decl0 ∧ v = .immediate imm0 ∧
    ImmediateRelLM3_2 allocMap decl0.ty body.layouts retVal imm0

/-- `LM-3.2` `StepRelLM3_2` (safe references, Tree Borrows hierarchy) as `Lockstep`. -/
theorem StepRelLM3_2.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelLM3_2 body m allocMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_2 body s' m' allocMap → Inv s' m') :
    Lockstep (rootHooks core) Inv (RefRetRel body allocMap) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- The `LM-4.1` multi-frame interpreter (`annealControlHooksLM4_1` reads `_0`). -/
def multiFrameHooks (rootBody : CapturedMir)
    (core : Unit → AnnealStepState → Miri.Interpreter.StepResult AnnealStepState Bool) :
    AnnealMiriHooks :=
  ⟨core, (annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand⟩

/-- Return relation of `LM-4.1`: an immediate or memory-backed `_0`. -/
def MultiFrameRetRel (rootBody : CapturedMir) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0, get? rootBody.localDecls 0 = some decl0 ∧
    ((∃ imm0, v = .immediate imm0 ∧ ImmediateRel decl0.ty rootBody.layouts retVal imm0) ∨
      (∃ mach mp0, v = .indirect mp0 ∧ MemPlaceRel mach decl0.ty rootBody.layouts (some retVal) mp0))

/-- `LM-4.1` `StepRelMultiFrame` (calls, returns, `GlobalState.endCall`) as `Lockstep`. -/
theorem StepRelMultiFrame.toLockstep {rootBody : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelMultiFrame rootBody m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → MultiFrameStateRel rootBody s' m' → Inv s' m') :
    Lockstep (multiFrameHooks rootBody core) Inv (MultiFrameRetRel rootBody) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) hrel.frames_ne_empty
  | retRoot decl0 retVal retOp mem' m' hdecl hop hrel hm' =>
    subst hm'
    refine .retRoot retVal mem' _ retOp rfl (by
      change ((annealControlHooksLM4_1 rootBody.localDecls rootBody.layouts).returnOperand () m).2 = _
      rw [hop]) ⟨decl0, hdecl, ?_⟩
    rcases hrel with ⟨imm0, h1, h2⟩ | ⟨mp0, h1, h2⟩
    · exact Or.inl ⟨imm0, h1, h2⟩
    · exact Or.inr ⟨m.machine, mp0, h1, h2⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- Generic multi-step lifting: an invariant whose every pair takes a
`Lockstep`-related step back into the invariant is a step-closed simulation,
so every relation above lifts to `runLoop_universal_simulation`,
`treeSafe_iff_miriSafe`, `reachesUB_iff_miriReachesUB`, and
`partialCorrect_iff_annealPostcondition` as soon as its per-step theorem is
shown on a step-closed fragment. -/
theorem stepClosedSim_of_lockstep {body : CapturedMir} {H : AnnealMiriHooks}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    (h : ∀ s m, Inv s m → Lockstep H Inv RetRel m (stepMirFn body s) (H.coreStep () m)) :
    StepClosedSim body H Inv RetRel :=
  ⟨h⟩

/-- `LM-2.3` lifting (`StateRelLM2_3`, any stack-allocation budget). -/
theorem stepClosedSim_of_stepRelLM2_3 {body : CapturedMir} {env : EnumTypeEnv}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m b, StateRelLM2_3 body env b s m → Frag s m → ∃ b',
      StepRelLM2_3 body env b' m (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM2_3 body env b' s' m' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => (∃ b, StateRelLM2_3 body env b s m) ∧ Frag s m)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨⟨b, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨b', hstep, hpres⟩ := h s m b hrel hfrag
  exact StepRelLM2_3.toLockstep hstep fun s' m' hm hrel' => ⟨⟨b', hrel'⟩, hpres s' m' hm hrel'⟩

/-- `LM-3.1` / `LM-4.2` lifting (`StateRelLM3_1`, any allocation map). -/
theorem stepClosedSim_of_stepRelLM3_1 {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m a, StateRelLM3_1 body s m a → Frag s m → ∃ a',
      StepRelLM3_1 body m a' (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM3_1 body s' m' a' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => (∃ a, StateRelLM3_1 body s m a) ∧ Frag s m)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨⟨a, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨a', hstep, hpres⟩ := h s m a hrel hfrag
  exact StepRelLM3_1.toLockstep hstep fun s' m' hm hrel' => ⟨⟨a', hrel'⟩, hpres s' m' hm hrel'⟩

/-- `LM-4.1` lifting (`MultiFrameStateRel`). -/
theorem stepClosedSim_of_stepRelMultiFrame {rootBody : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m, MultiFrameStateRel rootBody s m → Frag s m →
      StepRelMultiFrame rootBody m (stepMirFn rootBody s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → MultiFrameStateRel rootBody s' m' → Frag s' m') :
    StepClosedSim rootBody (multiFrameHooks rootBody core)
      (fun s m => MultiFrameStateRel rootBody s m ∧ Frag s m) (MultiFrameRetRel rootBody) := by
  refine ⟨fun s m ⟨hrel, hfrag⟩ => ?_⟩
  obtain ⟨hstep, hpres⟩ := h s m hrel hfrag
  exact StepRelMultiFrame.toLockstep hstep fun s' m' hm hrel' => ⟨hrel', hpres s' m' hm hrel'⟩

/-- Weaken the invariant and the return relation of a `Lockstep` step. -/
theorem Lockstep.mono {H : AnnealMiriHooks} {Inv Inv' : MachineState → AnnealStepState → Prop}
    {R R' : Value → Miri.Interpreter.Operand AnnealProv → Prop} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : Lockstep H Inv R m aRes mRes) (hinv : ∀ s m, Inv s m → Inv' s m)
    (hret : ∀ r v, R r v → R' r v) : Lockstep H Inv' R' m aRes mRes := by
  cases h with
  | emitStep obs s' m' hi hne => exact .emitStep obs s' m' (hinv s' m' hi) hne
  | retRoot retVal mem' m' v hemp hop hr => exact .retRoot retVal mem' m' v hemp hop (hret _ _ hr)
  | fault k m' e hag => exact .fault k m' e hag

/-- `LM-1` `StepRel` as `Lockstep` over any `rootHooks` interpreter. -/
theorem StepRel.toLockstepRoot {body : CapturedMir} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop} (h : StepRel body m aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRel body s' m' → Inv s' m') :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- Return relation of `LM-2.2` tuple / struct returns: an immediate
`ImmediateStructRel`-related at `_0`'s type, or a memory place holding the
`StructMemPlaceRel`-related value (including padding) in some machine. -/
def StructRetRel (body : CapturedMir) (fields : List StructFieldDesc)
    (paths : List (List ProjectionElem)) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0, get? body.localDecls 0 = some decl0 ∧
    ((∃ imm0, v = .immediate imm0 ∧
        ImmediateStructRel decl0.ty body.layouts fields paths retVal imm0) ∨
      (∃ mach mp0, v = .indirect mp0 ∧
        StructMemPlaceRel mach decl0.ty body.layouts fields paths retVal mp0))

/-- `LM-2.2` `StepRelStructReturnLM2_2` (root `Return` of a tuple / struct
`_0`, immediate or padded memory) as `Lockstep`. -/
theorem StepRelStructReturnLM2_2.toLockstep {body : CapturedMir}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelStructReturnLM2_2 body fields paths m aRes mRes) :
    Lockstep (rootHooks core) Inv (StructRetRel body fields paths) m aRes mRes := by
  cases h with
  | retRootImm decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, hdecl, Or.inl ⟨imm0, rfl, himm⟩⟩
  | retRootMem decl0 retVal mp0 mem' m' hdecl hop hmem hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.indirect mp0) rfl (by
      change (annealControlHooks.returnOperand () m).2 = _; rw [hop])
      ⟨decl0, hdecl, Or.inr ⟨_, mp0, rfl, hmem⟩⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- A root-return `StepRel` step (`step_terminator_return_lm2_2_simulation` and
the other scalar-return lemmas) as `Lockstep`, for any invariant: a return has
no post-state to relate. -/
theorem StepRel.toLockstepOfRet {body : CapturedMir} {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop} (h : StepRel body m aRes mRes)
    (hret : ∃ retVal mem, aRes = .retNormal retVal mem) :
    Lockstep (rootHooks core) Inv (ImmediateRetRel body) m aRes mRes := by
  cases h with
  | step s' m' _ =>
    obtain ⟨_, _, h⟩ := hret
    cases h
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg =>
    obtain ⟨_, _, h⟩ := hret
    cases h

/-- `LM-2.2` lifting: non-return steps through `StepRelLM2_2` (any static
environment and allocation budget), root returns of a tuple / struct `_0`
through `StepRelStructReturnLM2_2`, and root returns of a scalar `_0` through
`StepRel` (`step_terminator_return_lm2_2_simulation`). -/
theorem stepClosedSim_of_stepRelLM2_2 {body : CapturedMir} {env : StructTypeEnv}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m stEnv b, StateRelLM2_2 body env stEnv b s m → Frag s m →
      (∃ stEnv' b', StepRelLM2_2 body env stEnv' b' m (stepMirFn body s) (core () m) ∧
        ∀ s' m', core () m = (m', .ok true) → StateRelLM2_2 body env stEnv' b' s' m' →
          Frag s' m') ∨
      StepRelStructReturnLM2_2 body fields paths m (stepMirFn body s) (core () m) ∨
      ((∃ retVal mem, stepMirFn body s = .retNormal retVal mem) ∧
        StepRel body m (stepMirFn body s) (core () m))) :
    StepClosedSim body (rootHooks core)
      (fun s m => (∃ stEnv b, StateRelLM2_2 body env stEnv b s m) ∧ Frag s m)
      (fun r v => ImmediateRetRel body r v ∨ StructRetRel body fields paths r v) := by
  refine ⟨fun s m ⟨⟨stEnv, b, hrel⟩, hfrag⟩ => ?_⟩
  rcases h s m stEnv b hrel hfrag with ⟨stEnv', b', hstep, hpres⟩ | hret | ⟨hisret, hret⟩
  · exact StepRelLM2_2.toLockstep hstep fun s' m' hm hrel' =>
      ⟨⟨stEnv', b', hrel'⟩, hpres s' m' hm hrel'⟩
  · exact Lockstep.mono (StepRelStructReturnLM2_2.toLockstep
      (Inv := fun s m => (∃ stEnv b, StateRelLM2_2 body env stEnv b s m) ∧ Frag s m) hret)
      (fun _ _ h => h) (fun _ _ h => Or.inr h)
  · exact Lockstep.mono (StepRel.toLockstepOfRet
      (Inv := fun s m => (∃ stEnv b, StateRelLM2_2 body env stEnv b s m) ∧ Frag s m) hret hisret)
      (fun _ _ h => h) (fun _ _ h => Or.inl h)

/-- Return relation of `LM-2.3` enum returns: a memory place holding the
`EnumMemRel`-related active variant and fields in some machine. -/
def EnumRetRel (body : CapturedMir) (env : EnumTypeEnv) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0 tagBytes variants v_act fieldVals mach mp0,
    get? body.localDecls 0 = some decl0 ∧ env decl0.ty = some (tagBytes, variants) ∧
    retVal = .aggregate v_act fieldVals ∧ v = .indirect mp0 ∧
    EnumMemRel mach decl0.ty body.layouts tagBytes variants v_act fieldVals mp0

/-- `LM-2.3` `StepRelEnumReturnLM2_3` (root `Return` of a multi-variant enum
`_0`) as `Lockstep`. -/
theorem StepRelEnumReturnLM2_3.toLockstep {body : CapturedMir} {env : EnumTypeEnv}
    {m : AnnealStepState} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelEnumReturnLM2_3 body env m aRes mRes) :
    Lockstep (rootHooks core) Inv (EnumRetRel body env) m aRes mRes := by
  cases h with
  | retRootEnum decl0 tagBytes variants v_act fieldVals mp0 mem' m' hdecl henv hop hmem hm' =>
    subst hm'
    exact .retRoot _ mem' _ (.indirect mp0) rfl (by
      change (annealControlHooks.returnOperand () m).2 = _; rw [hop])
      ⟨decl0, tagBytes, variants, v_act, fieldVals, _, mp0, hdecl, henv, rfl, rfl, hmem⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.3` lifting with enum-valued root returns: steps (including scalar
returns) through `StepRelLM2_3`, root returns of an enum `_0` through
`StepRelEnumReturnLM2_3`. -/
theorem stepClosedSim_of_stepRelLM2_3_enumReturn {body : CapturedMir} {env : EnumTypeEnv}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m b, StateRelLM2_3 body env b s m → Frag s m →
      (∃ b', StepRelLM2_3 body env b' m (stepMirFn body s) (core () m) ∧
        ∀ s' m', core () m = (m', .ok true) → StateRelLM2_3 body env b' s' m' → Frag s' m') ∨
      StepRelEnumReturnLM2_3 body env m (stepMirFn body s) (core () m)) :
    StepClosedSim body (rootHooks core)
      (fun s m => (∃ b, StateRelLM2_3 body env b s m) ∧ Frag s m)
      (fun r v => ImmediateRetRel body r v ∨ EnumRetRel body env r v) := by
  refine ⟨fun s m ⟨⟨b, hrel⟩, hfrag⟩ => ?_⟩
  rcases h s m b hrel hfrag with ⟨b', hstep, hpres⟩ | hret
  · exact Lockstep.mono
      (StepRelLM2_3.toLockstep (Inv := fun s m => (∃ b, StateRelLM2_3 body env b s m) ∧ Frag s m)
        hstep fun s' m' hm hrel' => ⟨⟨b', hrel'⟩, hpres s' m' hm hrel'⟩)
      (fun _ _ h => h) (fun _ _ h => Or.inl h)
  · exact Lockstep.mono
      (StepRelEnumReturnLM2_3.toLockstep
        (Inv := fun s m => (∃ b, StateRelLM2_3 body env b s m) ∧ Frag s m) hret)
      (fun _ _ h => h) (fun _ _ h => Or.inr h)

/-- At a terminator, `annealStepHooksLM2_4` (which overrides only
`StepHooks.assign`) runs `annealTerminatorHooksLM2_2`, whose control hooks are
`annealControlHooks`. -/
theorem miri_step_at_terminator_lm2_4
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {bb : BasicBlockData}
    (hframes : m.stack.frames = #[topFrame])
    (hbody : topFrame.body = translateBody body)
    (hloc : topFrame.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none) :
    Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
      let res := Miri.Interpreter.ControlFlow.evalTerminator
        (annealTerminatorHooksLM2_2 body.localDecls body.layouts) ()
        (translateTerminator bb.terminator) m
      (res.1, res.2.map fun _ => true) := by
  unfold Miri.Interpreter.Step.step
  rw [stack_currentFrame?_singleton m.stack topFrame hframes]
  dsimp only
  rw [hloc, hbody]
  dsimp only
  rw [translateBody_basicBlocks_getElem?, hbb]
  dsimp only [Option.map]
  rw [translateBasicBlockData_statements_getElem?, hstmt_none]
  rfl

/-- **`LM-2.4` root return** (`StateRelLM2_4`, `annealStepHooksLM2_4`): the root
`Return` of a sized immediate `_0` steps both machines in lockstep (`StepRel`)
even while initialized, memory-backed union locals remain live in the frame:
a union local is always `.live (.indirect _)`, so an immediate `_0` is related
by the base `LocalRel`. -/
theorem step_terminator_return_lm2_4_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (hsz0 : (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (himm0 : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator_lm2_4 hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, huloc0⟩ := hframe.lookup_local hdecl0
  have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
  have himm0' := himm0 topFrame hframes mls0 hmls0
  have hloc0 : LocalRel m.machine decl0 body.layouts slot0 mls0 := by
    cases huloc0 with
    | base _ _ h => exact h
    | union _ _ _ _ _ mp _ _ _ _ _ _ => exact False.elim (himm0' mp rfl)
    | unionOverlay _ _ _ _ _ _ _ mp _ _ _ _ _ _ => exact False.elim (himm0' mp rfl)
  have hctrl_eq :
      (annealTerminatorHooksLM2_2 body.localDecls body.layouts).toControlHooks =
        annealControlHooks := rfl
  unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
  rw [hret, hstack, hctrl_eq, hslot0]
  dsimp only [translateTerminatorKind, Id.run, Pure.pure]
  cases hloc0 with
  | dead _ _ =>
    rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
    exact StepRel.ub _ _
  | indirect _ mp _ _ _ _ =>
    exact False.elim (himm0' mp rfl)
  | immediate _ imm _ _ hval =>
    rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
    · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
      exact StepRel.ub _ _
    · cases himmRel with
      | unit hzero => exact False.elim (hsz0 hzero)
      | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
        have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
        rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup hretCont hop0
          (annealControlHooks_popFrame_singleton hframes)
          (annealControlHooks_copyReturn_empty _ hretPlace)
          (annealControlHooks_cleanupFrame_eq false topFrame _)]
        exact StepRel.retRoot decl0 _ _ s.memory _ hdecl0 hop0
          (.scalar sc msc hsc hsz_sc hbool_sc hchar_sc) rfl
      | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
        have hop0 := annealControlHooks_returnOperand_scalarPair hframes hget0
        rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup hretCont hop0
          (annealControlHooks_popFrame_singleton hframes)
          (annealControlHooks_copyReturn_empty _ hretPlace)
          (annealControlHooks_cleanupFrame_eq false topFrame _)]
        exact StepRel.retRoot decl0 _ _ s.memory _ hdecl0 hop0
          (.scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair) rfl

/-- `LM-2.4` lifting (`StateRelLM2_4`): union steps through `StepRelLM2_4`,
other steps and scalar root returns through the base `StepRel` (whose
post-states embed by `StateRel.toLM2_4`); root returns under `StateRelLM2_4`
with live union locals are supplied by `step_terminator_return_lm2_4_simulation`. -/
theorem stepClosedSim_of_stepRelLM2_4 {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m, StateRelLM2_4 body s m → Frag s m →
      (StepRelLM2_4 body m (stepMirFn body s) (core () m) ∨
        StepRel body m (stepMirFn body s) (core () m)) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM2_4 body s' m' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => StateRelLM2_4 body s m ∧ Frag s m)
      (ImmediateRetRel body) := by
  refine ⟨fun s m ⟨hrel, hfrag⟩ => ?_⟩
  obtain ⟨hstep | hstep, hpres⟩ := h s m hrel hfrag
  · exact StepRelLM2_4.toLockstep hstep fun s' m' hm hrel' => ⟨hrel', hpres s' m' hm hrel'⟩
  · exact StepRel.toLockstepRoot hstep fun s' m' hm hrel' =>
      ⟨hrel'.toLM2_4, hpres s' m' hm hrel'.toLM2_4⟩

/-- Return relation for union-valued `_0` (`LM-2.4`): `lean-miri` returns an
indirect `MemPlace` `mp0` related to Anneal's returned union value `retVal`
by `UnionLocalRel` (covering single-active-field unions `UnionLocalRel.union`,
Stage-1 `D13a` raw-byte-overlay unions `UnionLocalRel.unionOverlay`, and
`MemPlaceRel`-backed indirect values). -/
def UnionRetRel (body : CapturedMir) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0 mach mp0,
    get? body.localDecls 0 = some decl0 ∧
    v = .indirect mp0 ∧
    UnionLocalRel mach decl0 body.layouts (.init retVal) ⟨.live (.indirect mp0), none⟩

/-- One-step root-return correspondence under `StateRelLM2_4` covering both
immediate returns (`retRootImm`) and memory-backed union returns
(`retRootUnion`, including `UnionLocalRel.union` and Stage-1
`UnionLocalRel.unionOverlay`), as well as dead or uninitialized `_0` undefined
behavior (`ub`). -/
inductive StepRelUnionReturnLM2_4
    (body : CapturedMir)
    (m : AnnealStepState) :
    MirStepNode →
    Miri.Interpreter.StepResult AnnealStepState Bool →
    Prop where
  | retRootImm (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateRel decl0.ty body.layouts retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelUnionReturnLM2_4 body m
        (MirStepNode.retNormal retVal mem') (m', .ok true)
  | retRootUnion (decl0 : LocalDecl) (retVal : Value)
      (mp0 : Miri.Interpreter.MemPlace AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.indirect mp0)) →
      UnionLocalRel m'.machine decl0 body.layouts (.init retVal) ⟨.live (.indirect mp0), none⟩ →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelUnionReturnLM2_4 body m
        (MirStepNode.retNormal retVal mem') (m', .ok true)
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelUnionReturnLM2_4 body m
        (MirStepNode.fail .ub) (m', .error (.undefinedBehavior msg))

/-- **`LM-2.4` union and immediate root return** (`StateRelLM2_4`,
`annealStepHooksLM2_4`): root-frame `Return` steps both machines in lockstep
(`StepRelUnionReturnLM2_4`) when `_0` is a union (`UnionLocalRel.union` or
Stage-1 `UnionLocalRel.unionOverlay`), a sized immediate, or dead /
uninitialized immediate, provided `_0` is not an uninitialized indirect local. -/
theorem step_terminator_return_union_lm2_4_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (hsz0 : (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (hnot_uninit_ind :
      ¬ (get? s.frame.locals 0 = some .uninit ∧
          ∃ topFrame mp0 c0,
            m.stack.frames = #[topFrame] ∧
            topFrame.locals[0]? = some ⟨.live (.indirect mp0), c0⟩)) :
    StepRelUnionReturnLM2_4 body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hbor, hprot, hcaller, _⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator_lm2_4 hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, huloc0⟩ := hframe.lookup_local hdecl0
  have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
  have hctrl_eq :
      (annealTerminatorHooksLM2_2 body.localDecls body.layouts).toControlHooks =
        annealControlHooks := rfl
  unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
  rw [hret, hstack, hctrl_eq, hslot0]
  dsimp only [translateTerminatorKind, Id.run, Pure.pure]
  cases huloc0 with
  | base _ _ hloc0 =>
    cases hloc0 with
    | dead _ _ =>
      rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
        hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
      exact .ub _ _
    | immediate _ imm0 _ _ hval =>
      rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
      · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
        exact .ub _ _
      · cases himmRel with
        | unit hzero => exact False.elim (hsz0 hzero)
        | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
          have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
          rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup hretCont hop0
            (annealControlHooks_popFrame_singleton hframes)
            (annealControlHooks_copyReturn_empty _ hretPlace)
            (annealControlHooks_cleanupFrame_eq false topFrame _)]
          exact .retRootImm decl0 _ _ s.memory _ hdecl0 hop0
            (.scalar sc msc hsc hsz_sc hbool_sc hchar_sc) rfl
        | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
          have hop0 := annealControlHooks_returnOperand_scalarPair hframes hget0
          rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup hretCont hop0
            (annealControlHooks_popFrame_singleton hframes)
            (annealControlHooks_copyReturn_empty _ hretPlace)
            (annealControlHooks_cleanupFrame_eq false topFrame _)]
          exact .retRootImm decl0 _ _ s.memory _ hdecl0 hop0
            (.scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair) rfl
    | indirect _ mp0 c0 _ hne_dead hmem =>
      cases slot0 with
      | dead => exact False.elim (hne_dead rfl)
      | uninit =>
        exact False.elim (hnot_uninit_ind ⟨hslot0, topFrame, mp0, c0, hframes, hmls0⟩)
      | init retVal =>
        have hop0 := annealControlHooks_returnOperand_indirect hframes hget0
        rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup hretCont hop0
          (annealControlHooks_popFrame_singleton hframes)
          (annealControlHooks_copyReturn_empty _ hretPlace)
          (annealControlHooks_cleanupFrame_eq false topFrame _)]
        exact .retRootUnion decl0 retVal mp0 s.memory _ hdecl0 hop0
          (.base _ _ (.indirect (.init retVal) mp0 none (fun _ h => nomatch h)
            (fun h => nomatch h) hmem)) rfl
  | union S n f f0Ty sc mp0 _ _ hwt hfields hf hmem =>
    have hop0 := annealControlHooks_returnOperand_indirect hframes hget0
    rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup hretCont hop0
      (annealControlHooks_popFrame_singleton hframes)
      (annealControlHooks_copyReturn_empty _ hretPlace)
      (annealControlHooks_cleanupFrame_eq false topFrame _)]
    exact .retRootUnion decl0 _ mp0 s.memory _ hdecl0 hop0
      (.union S n f f0Ty sc mp0 none (fun _ h => nomatch h) hwt hfields hf hmem) rfl
  | unionOverlay S n j f0Ty sc sc_low mergedBytes mp0 _ _ hwt hfields hspec hmem =>
    have hop0 := annealControlHooks_returnOperand_indirect hframes hget0
    rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
      hframe.location_eq hbb hcleanup hretCont hop0
      (annealControlHooks_popFrame_singleton hframes)
      (annealControlHooks_copyReturn_empty _ hretPlace)
      (annealControlHooks_cleanupFrame_eq false topFrame _)]
    exact .retRootUnion decl0 _ mp0 s.memory _ hdecl0 hop0
      (.unionOverlay S n j f0Ty sc sc_low mergedBytes mp0 none (fun _ h => nomatch h)
        hwt hfields hspec hmem) rfl

/-- Specialization of `step_terminator_return_union_lm2_4_simulation` when `_0`
has a `WellTypedUnionTy` layout (automatically non-ZST). -/
theorem step_terminator_return_wellTypedUnion_lm2_4_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : LocalDecl} {S : Nat}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (hwt0 : WellTypedUnionTy body.layouts decl0.ty S)
    (hnot_uninit_ind :
      ¬ (get? s.frame.locals 0 = some .uninit ∧
          ∃ topFrame mp0 c0,
            m.stack.frames = #[topFrame] ∧
            topFrame.locals[0]? = some ⟨.live (.indirect mp0), c0⟩)) :
    StepRelUnionReturnLM2_4 body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) := by
  refine step_terminator_return_union_lm2_4_simulation hstate hphase hbb hstmt_none hstmt_len
    hcleanup hret hdecl0 ?_ hnot_uninit_ind
  rw [hwt0.size_eq]
  rcases hwt0.size_valid with rfl | rfl | rfl | rfl | rfl <;> decide

/-- `StepRelUnionReturnLM2_4` as `Lockstep` for `ImmediateRetRel ∨ UnionRetRel`. -/
theorem StepRelUnionReturnLM2_4.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelUnionReturnLM2_4 body m aRes mRes) :
    Lockstep (rootHooks core) Inv
      (fun r v => ImmediateRetRel body r v ∨ UnionRetRel body r v) m aRes mRes := by
  cases h with
  | retRootImm decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      (Or.inl ⟨decl0, imm0, hdecl, rfl, himm⟩)
  | retRootUnion decl0 retVal mp0 mem' m' hdecl hop huloc hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.indirect mp0) rfl (by
      change (annealControlHooks.returnOperand () m).2 = _; rw [hop])
      (Or.inr ⟨decl0, m.machine, mp0, hdecl, rfl, huloc⟩)
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-2.4` lifting with union-valued root returns: intra-frame steps through
`StepRelLM2_4` or `StepRel`, and root returns (both immediate and union-valued)
through `StepRelUnionReturnLM2_4`. -/
theorem stepClosedSim_of_stepRelLM2_4_unionReturn {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m, StateRelLM2_4 body s m → Frag s m →
      (((StepRelLM2_4 body m (stepMirFn body s) (core () m) ∨
          StepRel body m (stepMirFn body s) (core () m)) ∧
        ∀ s' m', core () m = (m', .ok true) → StateRelLM2_4 body s' m' → Frag s' m') ∨
       StepRelUnionReturnLM2_4 body m (stepMirFn body s) (core () m))) :
    StepClosedSim body (rootHooks core)
      (fun s m => StateRelLM2_4 body s m ∧ Frag s m)
      (fun r v => ImmediateRetRel body r v ∨ UnionRetRel body r v) := by
  refine ⟨fun s m ⟨hrel, hfrag⟩ => ?_⟩
  rcases h s m hrel hfrag with ⟨hstep | hstep, hpres⟩ | hret
  · exact Lockstep.mono
      (StepRelLM2_4.toLockstep hstep fun s' m' hm hrel' => ⟨hrel', hpres s' m' hm hrel'⟩)
      (fun _ _ h => h) (fun _ _ h => Or.inl h)
  · exact Lockstep.mono
      (StepRel.toLockstepRoot hstep fun s' m' hm hrel' =>
        ⟨hrel'.toLM2_4, hpres s' m' hm hrel'.toLM2_4⟩)
      (fun _ _ h => h) (fun _ _ h => Or.inl h)
  · exact StepRelUnionReturnLM2_4.toLockstep hret

/-- `LM-3.2` lifting (`StateRelLM3_2`, any allocation map). -/
theorem stepClosedSim_of_stepRelLM3_2 {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m a, StateRelLM3_2 body s m a → Frag s m → ∃ a',
      StepRelLM3_2 body m a' (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM3_2 body s' m' a' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => (∃ a, StateRelLM3_2 body s m a) ∧ Frag s m)
      (fun r v => ∃ a, RefRetRel body a r v) := by
  refine ⟨fun s m ⟨⟨a, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨a', hstep, hpres⟩ := h s m a hrel hfrag
  exact Lockstep.mono
    (StepRelLM3_2.toLockstep (Inv := fun s m => (∃ a, StateRelLM3_2 body s m a) ∧ Frag s m)
      hstep fun s' m' hm hrel' => ⟨⟨a', hrel'⟩, hpres s' m' hm hrel'⟩)
    (fun _ _ h => h) (fun _ _ h => ⟨a', h⟩)

/-- `LM-3.2` / `LM-3.3` `StepRelLM3_2Tree` (parent / child reborrow trees) as
`Lockstep`. -/
theorem StepRelLM3_2Tree.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepRelLM3_2Tree body m treeMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_2Tree body s' m' treeMap → Inv s' m') :
    Lockstep (rootHooks core) Inv
      (RefRetRel body (treeMap.map ReborrowMapEntry.toAllocMapEntry)) m aRes mRes := by
  cases h with
  | step s' m' _ hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel.erased_rel
    exact .emitStep .silent s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot _ decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub _ m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-3.2` / `LM-3.3` lifting (`StateRelLM3_2Tree`, any reborrow tree). -/
theorem stepClosedSim_of_stepRelLM3_2Tree {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m t, StateRelLM3_2Tree body s m t → Frag s m → ∃ t',
      StepRelLM3_2Tree body m t' (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM3_2Tree body s' m' t' → Frag s' m') :
    StepClosedSim body (rootHooks core)
      (fun s m => (∃ t, StateRelLM3_2Tree body s m t) ∧ Frag s m)
      (fun r v => ∃ t : List ReborrowMapEntry,
        RefRetRel body (t.map ReborrowMapEntry.toAllocMapEntry) r v) := by
  refine ⟨fun s m ⟨⟨t, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨t', hstep, hpres⟩ := h s m t hrel hfrag
  exact Lockstep.mono
    (StepRelLM3_2Tree.toLockstep
      (Inv := fun s m => (∃ t, StateRelLM3_2Tree body s m t) ∧ Frag s m)
      hstep fun s' m' hm hrel' => ⟨⟨t', hrel'⟩, hpres s' m' hm hrel'⟩)
    (fun _ _ h => h) (fun _ _ h => ⟨t', h⟩)

/-- Return relation of `LM-3.1` / `LM-4.2`: an immediate `ImmediateRelLM3_1`-related
at `_0`'s type, including tracked raw pointers (`ImmediateRelLM3_1.rawPtr`). -/
def PtrRetRel (body : CapturedMir) (allocMap : List AllocMapEntry) (retVal : Value)
    (v : Miri.Interpreter.Operand AnnealProv) : Prop :=
  ∃ decl0 imm0, get? body.localDecls 0 = some decl0 ∧ v = .immediate imm0 ∧
    ImmediateRelLM3_1 allocMap decl0.ty body.layouts retVal imm0

/-- `LM-3.1` / `LM-4.2` `StepObsRelLM3_1` (raw-pointer root returns,
`step_terminator_return_rawPtr_lm3_1_simulation`, and `SwitchInt` observations;
the unified `step_mir_lm3_1_state_simulation`) as `Lockstep`. -/
theorem StepObsRelLM3_1.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepObsRelLM3_1 body m allocMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_1 body s' m' allocMap → Inv s' m') :
    Lockstep (rootHooks core) Inv (PtrRetRel body allocMap) m aRes mRes := by
  cases h with
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep obs s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-3.1` / `LM-4.2` lifting through `StepObsRelLM3_1` (any allocation map),
covering raw-pointer root returns and `SwitchInt`. -/
theorem stepClosedSim_of_stepObsRelLM3_1 {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m a, StateRelLM3_1 body s m a → Frag s m → ∃ a',
      StepObsRelLM3_1 body m a' (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM3_1 body s' m' a' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => (∃ a, StateRelLM3_1 body s m a) ∧ Frag s m)
      (fun r v => ∃ a, PtrRetRel body a r v) := by
  refine ⟨fun s m ⟨⟨a, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨a', hstep, hpres⟩ := h s m a hrel hfrag
  exact Lockstep.mono
    (StepObsRelLM3_1.toLockstep (Inv := fun s m => (∃ a, StateRelLM3_1 body s m a) ∧ Frag s m)
      hstep fun s' m' hm hrel' => ⟨⟨a', hrel'⟩, hpres s' m' hm hrel'⟩)
    (fun _ _ h => h) (fun _ _ h => ⟨a', h⟩)

/-- `LM-3.2` `StepObsRelLM3_2` (safe-reference root returns and `SwitchInt`
observations; the unified `step_mir_lm3_2_state_simulation`) as `Lockstep`. -/
theorem StepObsRelLM3_2.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepObsRelLM3_2 body m allocMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_2 body s' m' allocMap → Inv s' m') :
    Lockstep (rootHooks core) Inv (RefRetRel body allocMap) m aRes mRes := by
  cases h with
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel
    exact .emitStep obs s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-3.2` lifting through `StepObsRelLM3_2` (any allocation map), covering
safe-reference root returns and `SwitchInt`. -/
theorem stepClosedSim_of_stepObsRelLM3_2 {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m a, StateRelLM3_2 body s m a → Frag s m → ∃ a',
      StepObsRelLM3_2 body m a' (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM3_2 body s' m' a' → Frag s' m') :
    StepClosedSim body (rootHooks core) (fun s m => (∃ a, StateRelLM3_2 body s m a) ∧ Frag s m)
      (fun r v => ∃ a, RefRetRel body a r v) := by
  refine ⟨fun s m ⟨⟨a, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨a', hstep, hpres⟩ := h s m a hrel hfrag
  exact Lockstep.mono
    (StepObsRelLM3_2.toLockstep (Inv := fun s m => (∃ a, StateRelLM3_2 body s m a) ∧ Frag s m)
      hstep fun s' m' hm hrel' => ⟨⟨a', hrel'⟩, hpres s' m' hm hrel'⟩)
    (fun _ _ h => h) (fun _ _ h => ⟨a', h⟩)

/-- `LM-3.2` / `LM-3.3` `StepObsRelLM3_2Tree` (safe-reference root returns and
`SwitchInt` observations across parent/child reborrow trees; the unified
`step_mir_lm3_2_tree_state_simulation`) as `Lockstep`. -/
theorem StepObsRelLM3_2Tree.toLockstep {body : CapturedMir} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry} {aRes : MirStepNode}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {Inv : MachineState → AnnealStepState → Prop}
    (h : StepObsRelLM3_2Tree body m treeMap aRes mRes)
    (hinv : ∀ s' m', mRes = (m', .ok true) → StateRelLM3_2Tree body s' m' treeMap → Inv s' m') :
    Lockstep (rootHooks core) Inv
      (RefRetRel body (treeMap.map ReborrowMapEntry.toAllocMapEntry)) m aRes mRes := by
  cases h with
  | emitStep obs s' m' hrel =>
    obtain ⟨tf, hf, _⟩ := id hrel.erased_rel
    exact .emitStep obs s' m' (hinv s' m' rfl hrel) (frames_ne_of_eq_singleton hf)
  | retRoot decl0 retVal imm0 mem' m' hdecl hop himm hm' =>
    subst hm'
    exact .retRoot retVal mem' _ (.immediate imm0) rfl (retRoot_operand hop)
      ⟨decl0, imm0, hdecl, rfl, himm⟩
  | ub m' msg => exact .fault .ub m' (.undefinedBehavior msg) (ub_faultAgrees msg)

/-- `LM-3.2` / `LM-3.3` lifting through `StepObsRelLM3_2Tree` (any reborrow
tree), covering safe-reference root returns and `SwitchInt`. -/
theorem stepClosedSim_of_stepObsRelLM3_2Tree {body : CapturedMir}
    {Frag : MachineState → AnnealStepState → Prop}
    (h : ∀ s m t, StateRelLM3_2Tree body s m t → Frag s m → ∃ t',
      StepObsRelLM3_2Tree body m t' (stepMirFn body s) (core () m) ∧
      ∀ s' m', core () m = (m', .ok true) → StateRelLM3_2Tree body s' m' t' → Frag s' m') :
    StepClosedSim body (rootHooks core)
      (fun s m => (∃ t, StateRelLM3_2Tree body s m t) ∧ Frag s m)
      (fun r v => ∃ t : List ReborrowMapEntry,
        RefRetRel body (t.map ReborrowMapEntry.toAllocMapEntry) r v) := by
  refine ⟨fun s m ⟨⟨t, hrel⟩, hfrag⟩ => ?_⟩
  obtain ⟨t', hstep, hpres⟩ := h s m t hrel hfrag
  exact Lockstep.mono
    (StepObsRelLM3_2Tree.toLockstep
      (Inv := fun s m => (∃ t, StateRelLM3_2Tree body s m t) ∧ Frag s m)
      hstep fun s' m' hm hrel' => ⟨⟨t', hrel'⟩, hpres s' m' hm hrel'⟩)
    (fun _ _ h => h) (fun _ _ h => ⟨t', h⟩)

/-- Every `UnwindingStateRel` intermediate state has a non-empty `lean-miri`
call stack (`Array.push` onto the caller prefix). -/
theorem UnwindingStateRel.frames_ne_empty
    {rootBody : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : UnwindingStateRel rootBody s m) :
    m.stack.frames ≠ #[] := by
  rcases h with ⟨_, _, _, _, rfl, _⟩
  intro hemp
  have hsz := congrArg Array.size hemp
  simp at hsz

/-- Lift a `k`-step `MiriUnwindSteps` trace that catches at a cleanup block
(`m'.stack.frames ≠ #[]`, e.g. `MultiFrameStateRel.frames_ne_empty`) into a
whole-program `MiriPath` under any `AnnealMiriHooks` `H` whose `coreStep` agrees
with `annealStepHooksForState` at the initial and intermediate unwinding states. -/
theorem MiriUnwindSteps.toMiriPath_ok
    {rootBody : CapturedMir} {H : AnnealMiriHooks} {k : Nat}
    {s : MachineState} {m m' : AnnealStepState}
    (h : MiriUnwindSteps rootBody k s m (m', .ok true))
    (hne : m'.stack.frames ≠ #[])
    (hhooks : ∀ sᵢ mᵢ,
      ((sᵢ = s ∧ mᵢ = m) ∨ UnwindingStateRel rootBody sᵢ mᵢ) →
      H.coreStep () mᵢ =
        Miri.Interpreter.Step.step (annealStepHooksForState rootBody sᵢ) () mᵢ) :
    MiriPath H m m' := by
  generalize hres : (m', (Except.ok true : Except Miri.Interpreter.StepError Bool)) = res at h
  induction h with
  | single s₀ m₀ m₁ out hstep =>
    injection hres with hm hout
    subst m' out
    have hcore : H.coreStep () m₀ = (m₁, .ok true) := by
      rw [hhooks s₀ m₀ (Or.inl ⟨rfl, rfl⟩)]; exact hstep
    exact .step hcore hne (.refl m₁)
  | cons s₀ s₁ m₀ m₁ _ _ hstep hunw _ ih =>
    have hcore : H.coreStep () m₀ = (m₁, .ok true) := by
      rw [hhooks s₀ m₀ (Or.inl ⟨rfl, rfl⟩)]; exact hstep
    have hrest : MiriPath H m₁ m' :=
      ih (fun sᵢ mᵢ hor => by
        rcases hor with ⟨hs_eq, hm_eq⟩ | hu
        · rw [hs_eq, hm_eq]; exact hhooks s₁ m₁ (Or.inr hunw)
        · exact hhooks sᵢ mᵢ (Or.inr hu)) hres
    exact .step hcore (UnwindingStateRel.frames_ne_empty hunw) hrest

/-- Lift a `k`-step `MiriUnwindSteps` trace ending in `StepError` `e` (such as
unwinding into `.unreachable` UB or unwinding past the root frame) into a
`MiriPath` prefix plus whole-program `ReachesOutcome (classifyError e)` and
`¬ Safe` in `miriSystem H`. -/
theorem MiriUnwindSteps.toMiriOutcome_error
    {rootBody : CapturedMir} {H : AnnealMiriHooks} {k : Nat}
    {s : MachineState} {m m' : AnnealStepState} {e : Miri.Interpreter.StepError}
    (h : MiriUnwindSteps rootBody k s m (m', .error e))
    (hhooks : ∀ sᵢ mᵢ,
      ((sᵢ = s ∧ mᵢ = m) ∨ UnwindingStateRel rootBody sᵢ mᵢ) →
      H.coreStep () mᵢ =
        Miri.Interpreter.Step.step (annealStepHooksForState rootBody sᵢ) () mᵢ) :
    ∃ mₙ, MiriPath H m mₙ ∧ H.coreStep () mₙ = (m', .error e) ∧
      (miriSystem H).ReachesOutcome m (classifyError e) ∧ ¬ (miriSystem H).Safe m := by
  suffices haux : ∃ mₙ, MiriPath H m mₙ ∧ H.coreStep () mₙ = (m', .error e) by
    obtain ⟨mₙ, hpath, herr⟩ := haux
    have hout := miri_outcome_of_path_error hpath herr
    exact ⟨mₙ, hpath, herr, hout.1, hout.2⟩
  generalize hres : (m', (Except.error e : Except Miri.Interpreter.StepError Bool)) = res at h
  induction h with
  | single s₀ m₀ m₁ out hstep =>
    injection hres with hm hout
    subst m' out
    refine ⟨m₀, .refl m₀, ?_⟩
    rw [hhooks s₀ m₀ (Or.inl ⟨rfl, rfl⟩)]
    exact hstep
  | cons s₀ s₁ m₀ m₁ _ _ hstep hunw _ ih =>
    have hcore : H.coreStep () m₀ = (m₁, .ok true) := by
      rw [hhooks s₀ m₀ (Or.inl ⟨rfl, rfl⟩)]; exact hstep
    obtain ⟨mₙ, hpath, herr⟩ := ih (fun sᵢ mᵢ hor => by
      rcases hor with ⟨hs_eq, hm_eq⟩ | hu
      · rw [hs_eq, hm_eq]; exact hhooks s₁ m₁ (Or.inr hunw)
      · exact hhooks sᵢ mᵢ (Or.inr hu)) hres
    exact ⟨mₙ, .step hcore (UnwindingStateRel.frames_ne_empty hunw) hpath, herr⟩

/-! ### Entry states of the `LM-2` … `LM-4.1` relations

The entry pair `(initMachineState body [], miriEntryState body)` is related by
every relation of the campaign, so each lifting above applies from program
entry. -/

theorem stateRelLM2_2_entry (body : CapturedMir) :
    StateRelLM2_2 body emptyStructTypeEnv {} 0 (initMachineState body []) (miriEntryState body) :=
  (stateRel_entry body).toLM2_2

/-- Every enum environment with valid layouts relates the entry states:
on entry every local other than `_0` is dead and `_0` is an uninitialized
immediate. -/
theorem stateRelLM2_3_entry (body : CapturedMir) {env : EnumTypeEnv}
    (henv_valid : ∀ ty tb vs, env ty = some (tb, vs) → ValidEnumLayout ty body.layouts tb vs) :
    StateRelLM2_3 body env 0 (initMachineState body []) (miriEntryState body) := by
  refine (stateRel_entry body).toLM2_3 henv_valid ?_ (Or.inl rfl)
  intro idx decl slot mls hdecl _ hslot tf htf hmls
  have htf' : tf = miriEntryFrame body := by
    injection htf with h; injection h with h; exact h.symm
  subst htf'
  have hi : idx < body.localDecls.length := by
    rw [get?_eq_getElem?] at hdecl
    exact (List.getElem?_eq_some_iff.1 hdecl).1
  rw [entry_locals_get] at hslot
  change (miriEntryLocals body.localDecls.length)[idx]? = some mls at hmls
  rw [miriEntryLocals_getElem?] at hmls
  simp only [hi, ↓reduceIte] at hslot hmls
  by_cases h0 : idx = 0
  · simp only [h0, ↓reduceIte] at hslot hmls
    injection hslot with hslot
    injection hmls with hmls
    subst hslot hmls
    exact Or.inr ⟨rfl, rfl⟩
  · simp only [h0, ↓reduceIte] at hslot
    injection hslot with hslot
    exact Or.inl hslot.symm

/-- `stateRelLM2_3_entry` for every allocation budget below the `AllocId` bound. -/
theorem stateRelLM2_3_entry_of_budget (body : CapturedMir) {env : EnumTypeEnv}
    (henv_valid : ∀ ty tb vs, env ty = some (tb, vs) → ValidEnumLayout ty body.layouts tb vs)
    {b : Nat} (hb : b = 0 ∨ 1 + b < 2 ^ 32) :
    StateRelLM2_3 body env b (initMachineState body []) (miriEntryState body) := by
  rcases stateRelLM2_3_entry body henv_valid with
    ⟨tf, hf, hrc, hrp, hfr, _, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  refine .mk tf hf hrc hrp hfr ?_ hcal hst hbor hprot hcaller hdisj
  rcases hb with rfl | hb
  · exact Or.inl rfl
  · exact Or.inr (AllocIdWatermark.empty b hb)

/-- Every struct environment, static environment without initialized locals,
and allocation budget below the `AllocId` bound relates the entry states: on
entry every local other than `_0` is dead, `_0` is an uninitialized immediate,
and no local is memory-backed. -/
theorem stateRelLM2_2_entry_env (body : CapturedMir) (env : StructTypeEnv)
    (immLocals : List Local) {b : Nat} (hb : b = 0 ∨ 1 + b < 2 ^ 32) :
    StateRelLM2_2 body env { initLocals := [], immLocals := immLocals } b
      (initMachineState body []) (miriEntryState body) := by
  rcases stateRel_entry body with ⟨tf, hf, hrc, hrp, hfr, hcal, hst, hbor, hprot, hcaller, hdisj⟩
  have htf : tf = miriEntryFrame body := by
    injection hf with h; injection h with h; exact h.symm
  subst htf
  refine .mk (miriEntryFrame body) hf hrc hrp
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size, ?_⟩
    (fun _ hmem => nomatch hmem) ?_ ?_ hcal hst hbor hprot hcaller hdisj
  · intro i decl slot mls hdecl hslot hmls
    cases henv : env decl.ty with
    | none => exact .base slot mls henv (hfr.locals_rel i decl slot mls hdecl hslot hmls)
    | some fp =>
      obtain ⟨fields, paths⟩ := fp
      have hi : i < body.localDecls.length := by
        rw [get?_eq_getElem?] at hdecl
        exact (List.getElem?_eq_some_iff.1 hdecl).1
      rw [entry_locals_get] at hslot
      change (miriEntryLocals body.localDecls.length)[i]? = some mls at hmls
      rw [miriEntryLocals_getElem?] at hmls
      simp only [hi, ↓reduceIte] at hslot hmls
      by_cases h0 : i = 0
      · simp only [h0, ↓reduceIte] at hslot hmls
        injection hslot with hslot
        injection hmls with hmls
        subst hslot hmls
        exact .structUninitImm fields paths none henv (fun _ h => nomatch h)
      · simp only [h0, ↓reduceIte] at hslot hmls
        injection hslot with hslot
        injection hmls with hmls
        subst hslot hmls
        exact .structDead fields paths none henv (fun _ h => nomatch h)
  · intro idx _ mp lay hmls
    change (miriEntryLocals body.localDecls.length)[idx]? = some _ at hmls
    rw [miriEntryLocals_getElem?] at hmls
    split at hmls
    · split at hmls <;> simp at hmls
    · cases hmls
  · rcases hb with rfl | hb
    · exact Or.inl rfl
    · exact Or.inr (AllocIdWatermark.empty b hb)

theorem stateRelLM2_4_entry (body : CapturedMir) :
    StateRelLM2_4 body (initMachineState body []) (miriEntryState body) :=
  (stateRel_entry body).toLM2_4

theorem stateRelLM3_1_entry (body : CapturedMir) :
    StateRelLM3_1 body (initMachineState body []) (miriEntryState body) [] :=
  (stateRel_entry body).toLM3_1

theorem stateRelLM3_2_entry (body : CapturedMir) :
    StateRelLM3_2 body (initMachineState body []) (miriEntryState body) [] :=
  (stateRelLM3_1_entry body).toLM3_2

theorem stateRelLM3_2Tree_entry (body : CapturedMir) :
    StateRelLM3_2Tree body (initMachineState body []) (miriEntryState body) [] :=
  (stateRelLM3_2_entry body).toTree

theorem treeBorrowsStateRel_entry (body : CapturedMir) :
    TreeBorrowsStateRel body (initMachineState body []) (miriEntryState body) :=
  (stateRel_entry body).toTreeBorrowsStateRel

theorem multiFrameStateRel_entry (body : CapturedMir) :
    MultiFrameStateRel body (initMachineState body []) (miriEntryState body) :=
  (StateRel.iff_multiFrameStateRel_depth1 rfl rfl rfl rfl rfl (show 0 < 1 from Nat.one_pos)).1
    (stateRel_entry body)

/-- Trace lifting: a `Lockstep`-related `emitStep` advances both machines
(`AnnealPath` and `MiriPath` one step) into the invariant. -/
theorem Lockstep.emitStep_lift {body : CapturedMir} {H : AnnealMiriHooks}
    {Inv : MachineState → AnnealStepState → Prop}
    {RetRel : Value → Miri.Interpreter.Operand AnnealProv → Prop}
    {s s' : MachineState} {m : AnnealStepState} {obs : MirObs}
    (h : Lockstep H Inv RetRel m (stepMirFn body s) (H.coreStep () m))
    (hs : stepMirFn body s = .emitStep obs s') :
    ∃ m', H.coreStep () m = (m', .ok true) ∧ m'.stack.frames ≠ #[] ∧ Inv s' m' := by
  generalize hc : H.coreStep () m = mRes at h
  rw [hs] at h
  generalize ha : MirStepNode.emitStep obs s' = aRes at h
  cases h with
  | emitStep obs' s'' m' hinv hne =>
    have : s'' = s' := by
      cases obs <;> cases obs' <;> simp only [MirStepNode.emitStep] at ha <;>
        first | (injection ha with ha; injection ha with ha; exact ha.symm) | cases ha |
          (injection ha with h₁ h₂; cases h₁; have := congrFun h₂ PUnit.unit;
            injection this with this; exact this.symm)
    subst this
    exact ⟨m', rfl, hne, hinv⟩
  | retRoot => cases obs <;> cases ha
  | fault => cases obs <;> cases ha

end Bridges

end LeanMiriSpec.Correspondence.Safety
