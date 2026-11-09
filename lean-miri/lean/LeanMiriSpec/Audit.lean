/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri
import LeanMiriSpec.Correspondence.Translate
import LeanMiriSpec.Correspondence.Relation
import LeanMiriSpec.Correspondence.Simulation
import LeanMiriSpec.Correspondence.SimLM1_2
import LeanMiriSpec.Correspondence.Witness
import LeanMiriSpec.Correspondence.WitLM1_2
import LeanMiriSpec.Correspondence.SimLM1_3
import LeanMiriSpec.Correspondence.WitLM1_3
import LeanMiriSpec.Correspondence.AllocLM1_4
import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.WitLM1_4
import LeanMiriSpec.Correspondence.AllocLM2_1
import LeanMiriSpec.Correspondence.SimLM2_1
import LeanMiriSpec.Correspondence.WitLM2_1
import LeanMiriSpec.Correspondence.PtrLM3_1
import LeanMiriSpec.Correspondence.SimLM3_1
import LeanMiriSpec.Correspondence.WitLM3_1
import LeanMiriSpec.Correspondence.RefLM3_2
import LeanMiriSpec.Correspondence.SimLM3_2
import LeanMiriSpec.Correspondence.WitLM3_2
import LeanMiriSpec.Correspondence.TreeBorrowsRel
import LeanMiriSpec.Correspondence.SimLM3_3
import LeanMiriSpec.Correspondence.WitLM3_3

/-!
# Axiom Audit (`LeanMiriSpec.Audit`)

`#assert_standard_axioms` fails the build unless each listed declaration
depends only on Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`); in particular on zero `sorryAx` and zero
`Lean.ofReduceBool` (which `native_decide` would introduce).

`#assert_all_leanmirispec_and_miri_standard_axioms` additionally walks every
declaration across all `LeanMiriSpec.*` and `Miri.*` modules in `Lean.Environment`
and verifies that none depends on any non-standard axiom.

The `example`s at the end pin the exact statements of the headline results, so
a later edit that weakens a hypothesis or conclusion fails this file even if the
weakened theorem keeps its name:

* `step_wellTypedBody_bisim`: the bidirectional step / normal-return /
  undefined-behavior correspondence, stated on `stepMirFn` and
  `Miri.Interpreter.Step.step` directly;
* `Witness.bisim_applies`: a concrete body and initial states satisfy every
  premise, so the correspondence is not vacuous (`Witness.divByZero_ub_agrees`
  and `Witness.div_returns_agree` additionally run both machines on it);
* `annealStepHooks_storageDead_returnPlace`: the hooks keep `lean-miri`'s source
  behavior for `StorageDead(_0)` rather than imitating Anneal;
* `annealEvalOperand_move_live`: on `Move`, the hooks deinitialize the
  moved-from local, implementing the runtime-MIR `Operand::Move` semantics that
  Anneal implements and that the pinned Miri interpreter leaves unimplemented;
* `LM-1.2`: the value-level `bool`/comparison/`Cmp`/`IntToInt`/`SwitchInt`
  results, the step theorems `step_stmt_lm1_2_simulation` (`StepRel`) and
  `step_terminator_lm1_2_simulation` (`StepObsRel`), and the `WitLM1_2`
  witnesses that their premises hold for concrete bodies on which both machines
  agree;
* the `LM-1.4` theorems: `StorageLive`/`StorageDead`/`PlaceMention`, destructive
  moves (`evalOperand_move_simulation`), their composition
  (`step_stmt_lm1_4_simulation`), and the representation coalescing theorem
  `forceAllocation_preserves_StateRel`, together with the `WitLM1_4` witnesses
  showing that these premises can be met, that `forceAllocation` really
  promotes an immediate local to memory, and that storage statements then free
  that memory in lockstep.
-/

namespace LeanMiriSpec.Audit

open Lean Elab Command

/-- Fail unless every listed declaration depends only on Lean's standard axioms
(`propext`, `Quot.sound`, `Classical.choice`). -/
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    logInfo m!"{n} depends on axioms: {axs.toList}"

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  translateTy
  translatePlace
  translateOperand
  translatePointerCoercion
  translateCastKind
  translateRvalue
  translateStmt
  translateTerminator
  translateBody
  AnnealMachine
  AnnealMachine.lookupBaseAddr
  annealCastHooks
  annealStepHooks
  ScalarRel
  ImmediateRel
  MemPlaceRel
  MemPlaceRel.relOffset_bytes_eq
  LocalRel
  FrameRel
  StateRel
  RvalueResultRel
  StepRel
  StepRel.step_iff
  StepRel.retNormal_iff
  StepRel.retNormal_rel
  StepRel.ub_iff
  StepRel.toStepObsRel
  StepObsRel
  StepObsRel.emitStep_iff
  StepObsRel.retNormal_iff
  StepObsRel.retNormal_rel
  StepObsRel.ub_iff
  evalBinOp_arithmetic_simulation
  evalBinOp_bitwise_simulation
  evalBinOp_shift_simulation
  evalUnOp_neg_not_simulation
  step_assign_scalar_simulation
  step_terminator_goto_return_simulation
  evalUnOp_bool_not_simulation
  evalScalarBinOp_rel_eq
  integerOps_binary_rel_eq
  evalBinOp_rel_simulation
  evalBinOp_cmp_simulation
  scalarOps_cmp_simulation
  evalCast_intToInt_simulation
  cast_intToInt_uninit
  compareSwitchCase_simulation
  evalTerminator_switchInt_ok
  evalTerminator_switchInt_error
  step_terminator_switchInt_simulation
  evalOperand_scalar_simulation_opTy
  scalarOps_binary_boolCmp_simulation
  step_assign_lm1_2_simulation
  step_stmt_lm1_2_simulation
  step_terminator_lm1_2_simulation
  Witness.lm12Switch_step_applies
  Witness.lm12Switch_case_agrees
  Witness.lm12Switch_otherwise_agrees
  Witness.lm12BoolCmp_step_applies
  Witness.lm12BoolCmp_returns_agree
  Witness.lm12Cast_step_applies
  Witness.lm12Cast_returns_agree
  Witness.lm12Cast_shapes_agree
  WellTypedBody
  step_wellTypedBody_simulation
  step_wellTypedBody_bisim
  annealLocalStorageHooks
  annealStepHooks_storageLive_eq
  annealStepHooks_storageDead_eq
  annealStepHooks_storageDead_returnPlace
  annealStepHooks_deinit_ne_ok
  annealStepHooks_retag_ne_ok
  ValidFrameLocation.preserved
  NonAddrTakenImmediate.preserved
  runAnnealBounded_emitStep
  run_wellTypedBody_simulation
  run_wellTypedBody_bisim
  Witness.stateRel_init
  Witness.wellTypedBody
  Witness.bisim_applies
  Witness.divByZero_ub_agrees
  Witness.div_returns_agree
  Witness.run_bisim_divBody
  Witness.stateRel_signedDiv
  Witness.wellTyped_signedDiv
  Witness.run_bisim_signedDiv
  Witness.signedDiv_intMinNegOne_ub_agrees
  Witness.signedDiv_returns_agree
  Witness.stateRel_addWithOverflow
  Witness.wellTyped_addWithOverflow
  Witness.run_bisim_addWithOverflow
  Witness.addWithOverflow_overflows_agrees
  Witness.addWithOverflow_noOverflow_agrees
  Witness.indirect_localRel_uninit_witness
  Witness.indirect_localRel_scalar_witness
  Witness.stateRel_unreachable
  Witness.wellTyped_unreachable
  Witness.run_bisim_unreachable
  Witness.unreachable_ub_agrees
  Witness.stateRel_charCopy
  Witness.wellTyped_charCopy
  Witness.charCopy_returns_agree
  Witness.stateRel_shiftUnchecked
  Witness.wellTyped_shiftUnchecked
  Witness.shiftUnchecked_witness_agrees
  Witness.stateRel_addUncheckedNop
  Witness.wellTyped_addUncheckedNop
  Witness.addUncheckedNop_witness_agrees
  Witness.annealCast_intToInt_fidelity
  Witness.annealSwitchInt_fidelity
  Witness.stateRel_unaryBitwise
  Witness.wellTyped_unaryBitwise
  Witness.unaryBitwise_returns_agree
  annealZeroedStorage
  annealStackBaseAddr
  annealPlaceHooks
  MemoryAllocDisjoint
  StateRel.memoryAllocDisjoint
  freshStackAlloc_spec
  freshStackAlloc_writeScalar_readScalar
  IsLiveFrameLocal
  WellTypedLM1_4Stmt
  deallocLocalMemory
  LocalAllocLive
  annealLocalStorageHooks_deallocateLocal_eq
  LocalRel.allocLive
  MemPlaceRel.of_filter_live
  LocalRel.of_dealloc
  FrameRel.update_local_dealloc
  annealStepHooks_storageLive_any_eq
  annealStepHooks_storageDead_any_eq
  step_storageLive_simulation
  step_storageDead_simulation
  evalStatement_placeMention_eq
  step_placeMention_simulation
  annealEvalOperand_move_live
  annealEvalOperand_move_dead
  evalOperand_move_simulation
  reserveAllocId_ok_live
  placeLayoutOfLocal_eq
  annealPlaceHooks_allocateStack_inv
  annealPlaceHooks_writeMemoryNoValidate_fresh_inv
  annealStackBaseAddr_isAligned
  MemPlaceRel.of_live_base
  LocalRel.of_live_base
  FrameRel.of_live_base
  stackAllocMachine_live_base
  stackAlloc_memPlaceRel
  stackAlloc_stateRel
  forceAllocation_preserves_StateRel
  step_stmt_lm1_4_simulation
  Witness.lm14Scalar42
  Witness.lm14_scalarRel42
  Witness.lm14MoveBody
  Witness.lm14MoveAnneal
  Witness.lm14MovedAnneal
  Witness.lm14MoveMiriFrame
  Witness.lm14MoveMiri
  Witness.lm14_stateRel
  Witness.lm14_phase
  Witness.lm14_move_wellTyped
  Witness.lm14_move_stepRel
  Witness.lm14_move_anneal_step
  Witness.lm14_move_steps
  Witness.lm14_placeMention_wellTyped
  Witness.lm14_placeMention_stepRel
  Witness.lm14_placeMention_steps
  Witness.lm14_forceAllocation_witness
  Witness.lm14LiveAnneal
  Witness.lm14DeadAnneal
  Witness.lm14_storageLive_indirect_steps
  Witness.lm14_storageDead_indirect_steps
  ArraySliceRel
  ArraySliceRel.nil
  ArraySliceRel.readScalar_get
  ArraySliceRel.writeScalar_snoc
  ArraySliceRel.writeScalar_set
  writeScalarRepeatedly_spec
  WellTypedArrayTy
  LiveAllocsNodup
  StepPreservesNodup
  StepPreservesImmediate
  StepPreservesImmediate.mono
  arrayConstructDest?
  LiveAllocsNodup.stackAllocMachine
  CanReserveAllocId
  annealEnsureAllocated_indirect
  stepPreservesNodup_of_write_local
  arraySliceMetaTyId
  annealPointerResolver
  annealPointerArithmetic
  annealLiveAllocationLookup
  projectionMemoryOffset_inbounds_of_memPlaceRel
  annealReadImmediate_whole_array_unsupported
  ArrayConstructDestReady
  inplaceMachine
  evalProjection_index_simulation
  evalProjection_constantIndex_simulation
  evalRvalue_len_array_simulation
  evalRvalue_repeat_simulation
  evalRvalue_aggregate_array_simulation
  WellTypedArrayElemProj
  WellTypedArrayElemAssign
  step_assign_array_element_simulation
  WellTypedLM2_1ArrayStmt
  step_stmt_lm2_1_array_simulation
  step_storageLive_establishes_immediate
  step_scalar_preserves_nodup
  step_lm1_4_preserves_nodup_and_immediate
  LiveAllocsNodup.deallocLocalMemory
  annealLocalIndex_usize_spec
  encodeTyId_ne_arraySliceMetaTyId
  translateProjectionElem_ne_unwrapArraySliceMeta
  projectUnwrapArraySliceMeta_of_array_memPlaceRel
  projectSubslice_array_unsupported
  MemoryHighWater
  MemoryHighWater.empty
  MemoryHighWater.canReserveAllocId
  MemoryHighWater.stackAllocMachine
  StepPreservesHighWater
  StepPreservesHighWater.mono_budget
  WellTypedLM2_1ScalarOperand
  movedScalarLocal?
  WellTypedLM2_1Stmt
  step_stmt_lm2_1_simulation
  Witness.lm21Body
  Witness.lm21ArrAlloc
  Witness.lm21ArrElems
  Witness.lm21_wf_u16Arr3
  Witness.lm21_wf_u16Arr2
  Witness.lm21_wf_u16Arr0
  Witness.lm21_arraySliceRel
  Witness.lm21_memPlaceRel
  Witness.lm21_init_stateRel
  Witness.lm21_arr_stateRel
  Witness.lm21_aggregate_array_steps
  Witness.lm21_repeat_array_steps
  Witness.lm21_repeat_zero_steps
  Witness.lm21_len_array_steps
  Witness.lm21_len_uninit_ub
  Witness.lm21_evalProjection_index_witness
  Witness.lm21_evalProjection_constantIndex_witness
  Witness.lm21_index_read_steps
  Witness.lm21_index_write_steps
  Witness.lm21_constantIndex_fromStart_steps
  Witness.lm21_constantIndex_fromEnd_read_steps
  Witness.lm21_constantIndex_fromEnd_write_steps
  Witness.lm21_index_oob_ub
  Witness.lm21_index_write_oob_ub
  Witness.lm21_index_uninit_ub
  Witness.lm21_constantIndex_oob_ub
  Witness.lm21_chain_steps
  Witness.lm21_whole_array_read_unsupported
  Witness.lm21_partial_subslice_unsupported
  Witness.lm21_whole_subslice_unsupported
  Witness.lm21_indirect_index_read_steps
  Witness.lm21_indirect_index_uninit_ub
  Witness.lm21MixedBody
  Witness.lm21_mixed_reassign_chain_steps
  Witness.lm21MultiMoveBody
  Witness.lm21_multi_init_stateRel
  Witness.lm21_multi_alloc_move_chain_steps
  Witness.lm21_aggregate_move_then_copy_ub
  projectConstantIndex_malformed_invariant
  arrayElemReadOperand
  annealEvalOperand_projected_array_simulation
  annealEvalPlace_projected_array_simulation
  Witness.lm21CopyZeroBody
  Witness.lm21ZeroArrAlloc
  Witness.lm21ZeroArrMemPlace
  Witness.lm21_zeroArr_uninit_memPlaceRel
  Witness.lm21_zeroArr_stateRel
  Witness.lm21_intra_and_inter_array_copyElem_steps
  Witness.lm21_copyElem_src_oob_ub
  Witness.lm21_uninit_indirect_zero_array_read_ub
  Witness.lm21_uninit_indirect_zero_array_write_ub
  Witness.lm21_malformed_constantIndex_invariant
  annealEvalOperand_malformed_constantIndex_invalidProgram
  annealEvalPlace_malformed_constantIndex_invalidProgram
  step_assign_malformed_constantIndex_invalidProgram
  runMiriBounded_step_of_stateRel
  runBounded_of_stepRel_retRoot
  Witness.lm21MalformedConstBody
  Witness.lm21_mal_arr_stateRel
  Witness.lm21_malformed_constantIndex_step_invalidProgram
  Witness.lm21_wf_i32Arr3
  Witness.lm21_wf_boolArr2
  Witness.lm21_wf_charArr2
  Witness.lm21FullFnBody
  Witness.lm21_fullFn_init_stateRel
  Witness.lm21_signed_bool_char_runBounded_return
  AllocMapEntry
  lookupAllocMapByTag
  lookupAllocMapByLocal
  AllocMapRel
  PtrRel
  annealResolvePtr
  annealLookupAlloc
  checkAndDerefPtr_withoutProvenance_err
  checkAndDerefPtr_deadAlloc_err
  checkAndDerefPtr_live_inbounds_ok
  checkAndDerefPtr_live_oob_err
  ptrOffsetInbounds_zero_ok
  ptrOffsetInbounds_withoutProvenance_err
  ptrOffsetInbounds_deadAlloc_err
  ptrOffsetInbounds_live_inbounds_ok
  ptrOffsetInbounds_live_oob_err
  ptrOffsetInbounds_live_iff
  size_isAligned_eight_of_aligned
  size_isAligned_eight_of_misaligned
  LocalRelLM3_1
  FrameRelLM3_1
  StateRelLM3_1
  StepRelLM3_1
  FrameRel.toLM3_1
  StateRel.toLM3_1
  StateRelLM3_1.toStateRel
  StepRel.toLM3_1
  FrameRelLM3_1.update_local
  annealForceAllocation
  ImmediateRelLM3_1
  castTypeInfoOfEncodedTyIdLM3_1
  annealCastHooksLM3_1
  evalDerefReadScalarMiri
  evalDerefWriteScalarMiri
  rawPtrPerm
  AllocIdSupplyReady
  AllocIdSupplyReady.empty
  IsPrimScalarTy.layout_ok
  forceAllocation_promote_eq
  evalRvalueIntoPlace_rawPtr_ok
  evalRvalueIntoPlace_rawPtr_force_error
  annealForceAllocation_dead_eq
  StateRel.cache_layout
  rawPtrBorrowEntry
  rawPtrAllocMapEntry
  step_rawPtr_addrOf_simulation
  evalProjection_deref_read_ok
  evalProjection_deref_write_ok
  evalProjection_deref_deadAlloc_ub
  evalProjection_deref_oob_ub
  evalProjection_deref_misaligned_ub
  evalProjection_deref_simulation
  evalBinOp_offset_inbounds_simulation
  evalRvalue_expose_withExposed_roundtrip
  evalCast_ptrToPtr_simulation
  WellTypedLM3_1Stmt
  step_stmt_lm3_1_simulation
  step_storageDead_lm3_1_simulation
  step_storageLive_lm3_1_simulation
  step_rawPtr_addrOf_lm3_1_simulation
  evalRvalue_rawPtr_addrOf_simulation
  step_deref_read_simulation
  step_deref_write_simulation
  step_deref_oob_miri_ub
  step_deref_misaligned_miri_ub
  step_cast_ptrToPtr_simulation
  step_binOp_offset_simulation
  step_binOp_offset_oob_dangling_miri_ub
  WellTypedLM3_1StateStmt
  step_stmt_lm3_1_state_simulation
  Witness.wit_lm3_1_rawPtr_step
  Witness.wit_lm3_1_addrOf_write_read_deref
  Witness.wit_lm3_1_binOp_offset_inbounds_and_oob
  Witness.wit_lm3_1_anneal_offset_deref_divergence
  Witness.wit_lm3_1_anneal_storage_revive_divergence
  Witness.wit_lm3_1_anneal_deref_type_pun_divergence
  step_deref_oob_divergence
  lookupBorrow_map_toBorrowEntry_parentTag
  derefWriteTreeUB_map_toBorrowEntry_eq_false
  hasTreeReadUB_map_toBorrowEntry_eq_false
  perm_ne_disabled_of_tag_eq_of_nodup
  derefReadTreeUB_map_toBorrowEntry_eq_false
  Witness.wit_lm3_1_use_after_storageDead_ub
  Witness.wit_lm3_1_addrOf_deref_storageDead_real_steps
  Witness.wit_lm3_1_use_after_storageDead_real_steps
  Witness.wit_lm3_1_ptrToPtr_and_offset_real_steps
  Witness.wit_lm3_1_deref_oob_and_misaligned_real_steps
  isThinRawPtrPointee
  annealValidateScalarForTyId
  castTypeInfoOfEncodedTyId_encodeRawPtrTyId
  castTypeInfoOfEncodedTyId_nonThin_err
  derefReadNextAllocMap
  step_deref_read_simulation_explicit
  derefWriteNextAllocMap
  step_deref_write_simulation_explicit
  step_rawPtr_addrOf_preserves_supply
  step_rawPtr_addrOf_indirect_lm3_1_simulation
  step_rawPtr_addrOf_indirect_preserves
  step_nop_lm3_1_simulation
  step_scalar_use_lm3_1_simulation
  step_direct_write_promoted_lm3_1_simulation
  step_deref_misaligned_divergence
  step_deref_invalid_bool_divergence
  ptrOffsetInbounds_neg_one_live_ok
  step_binOp_offset_stride_divergence
  step_binOp_offset_neg_isize_divergence
  Witness.wit_lm3_1_two_promotions_reborrow_and_direct_write_real_steps
  Witness.wit_lm3_1_invalid_bool_cast_deref_real_steps
  Witness.wit_lm3_1_offset_stride_and_neg_isize_real_steps
  step_placeMention_local_lm3_1_simulation
  step_placeMention_deref_lm3_1_simulation
  evalCast_ptrToPtr_annealCastHooks_simulation
  lookupDerefPointeeLayout_ref_eq_none
  annealValidateScalarForTyId_never_false
  annealValidateScalarForTyId_nonNullPtr_null_false
  step_deref_invalid_char_divergence
  step_deref_write_invalid_bool_divergence
  step_placeMention_deref_uninit_divergence
  annealForceAllocation_memory_eq
  memPlace_toRef_withoutProvenance
  step_rawPtr_deref_null_divergence
  step_rawPtr_deref_nonzero_offset_divergence
  step_cast_expose_provenance_ptr_unsupported
  step_cast_with_exposed_provenance_divergence
  step_terminator_goto_return_lm3_1_simulation
  Witness.step_placeMention_preserves
  Witness.wit_lm3_1_end_to_end_return_real_steps
  Witness.wit_lm3_1_rawPtr_deref_null_and_offset_real_steps
  Witness.wit_lm3_1_anneal_forged_provenance_real_steps
  Witness.wit_lm3_1_invalid_char_write_bool_and_placeMention_real_steps
  IsImmediateFrameLocal.deinit_local
  WellTypedScalarOperand.of_deinitFrameLocal
  StateRelLM3_1.deinit_immediate_local
  step_rawPtr_use_lm3_1_simulation
  step_cast_ptrToPtr_move_simulation
  step_binOp_offset_move_simulation
  step_cast_expose_provenance_scalar_simulation
  lookupDerefPointeeLayout_decl_eq_encoded
  step_cast_ptrToPtr_scalar_divergence
  step_binOp_offset_scalar_zero_divergence
  step_binOp_offset_scalar_nonzero_divergence
  step_rawPtr_deref_perm_divergence
  step_rawPtr_deref_zero_offset_correspondence
  Witness.wit_lm3_1_rawPtr_use_move_and_expose_scalar_real_steps
  Witness.wit_lm3_1_null_ptrToPtr_and_offset_divergences_real_steps
  Witness.wit_lm3_1_rawPtr_deref_zero_and_perm_divergence_real_steps
  annealExecutionScalarLeaves
  annealDerefValidity
  annealDerefValidity_nonThin_or_ref_err
  step_rawPtr_cmp_scalar_lm3_1_simulation
  step_binOp_offset_zero_any_stride_lm3_1_simulation
  step_unaryOp_ptrMetadata_thin_rawPtr_ub_simulation
  step_unaryOp_ptrMetadata_thin_rawPtr_divergence
  step_rawPtr_cmp_ptr_divergence
  step_cast_ptrToPtr_move_scalar_divergence
  step_binOp_offset_move_scalar_zero_divergence
  StepObsRelLM3_1
  StepRelLM3_1.toStepObsRelLM3_1
  StepObsRelLM3_1.emitStep_iff
  StepObsRelLM3_1.retNormal_iff
  StepObsRelLM3_1.retNormal_rel
  StepObsRelLM3_1.ub_iff
  step_terminator_return_rawPtr_lm3_1_simulation
  step_terminator_switchInt_lm3_1_simulation
  step_terminator_assert_lm3_1_simulation
  Witness.wit_lm3_1_branch_offset_zero_and_return_rawPtr_real_steps
  Witness.wit_lm3_1_rawPtr_cmp_and_ptrMetadata_real_steps
  step_rawPtr_cmp_ub_lm3_1_simulation
  step_rawPtr_cmp_scalar_ptr_divergence
  step_binOp_offset_move_scalar_nonzero_divergence
  WellTypedLM3_1StateTerminator
  step_terminator_lm3_1_state_simulation
  step_mir_lm3_1_state_simulation
  Witness.wit_lm3_1_cmp_symm_move_ub_and_unified_step_real_steps
  step_safeRef_deref_read_invalid_scalar_divergence
  evalRvalue_reborrow_safeRef_tree_simulation
  step_safeRef_deref_read_tree_simulation
  step_safeRef_deref_write_tree_simulation
  treeMap_ancestorOrSelf_not_disabled
  hasTreeReadUB_treeMap_eq_false
  derefReadTreeUB_treeMap_eq_false
  derefWriteTreeUB_treeMap_eq_false
  step_terminator_goto_return_tree_simulation
  Witness.wit_lm3_2_ref_never_and_enum_discriminant_validity
  Witness.wit_lm3_2_invalid_bool_deref_read_divergence_real_steps
  Witness.wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps

/-- Exhaustively verify that every declaration across every imported
`LeanMiriSpec.*` and `Miri.*` module in the environment — as well as every
declaration elaborated in the current `Audit.lean` module (`env.constants.map₂`) —
depends only on Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`). -/
elab "#assert_all_leanmirispec_and_miri_standard_axioms" : command => do
  let env ← getEnv
  let mut specChecked : Nat := 0
  let mut miriChecked : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    let isSpec := (`LeanMiriSpec).isPrefixOf modName
    let isMiri := (`Miri).isPrefixOf modName
    if isSpec || isMiri then
      let modData := env.header.moduleData[i]!
      for c in modData.constNames do
        let axs ← liftCoreM <| Lean.collectAxioms c
        for a in axs do
          unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
            throwError "{c} (in {modName}) depends on the non-standard axiom {a}"
        if isSpec then
          specChecked := specChecked + 1
        if isMiri then
          miriChecked := miriChecked + 1
  for (c, _) in env.constants.map₂.toList do
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} (in LeanMiriSpec.Audit) depends on the non-standard axiom {a}"
    specChecked := specChecked + 1
  if specChecked == 0 then
    throwError "LeanMiriSpec.Audit: found 0 LeanMiriSpec.* declarations in environment"
  if miriChecked == 0 then
    throwError "LeanMiriSpec.Audit: found 0 Miri.* declarations in environment"
  logInfo m!"LeanMiriSpec.Audit: exhaustively verified standard axioms for {specChecked} LeanMiriSpec.* declarations and {miriChecked} Miri.* declarations"

/-! ## Statement pins -/

section StatementPins

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

example {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    ((∃ s', stepMirFn body s = .step s' ∧
        StateRel body s' (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1) ↔
      ((Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true ∧
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames ≠ #[])) ∧
    ((∃ retVal mem', stepMirFn body s = .retNormal retVal mem') ↔
      ((Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 = .ok true ∧
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames = #[])) ∧
    (stepMirFn body s = .fail .ub ↔
      ∃ msg, (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).2 =
        .error (.undefinedBehavior msg)) ∧
    ((∃ s', stepMirFn body s = .step s') ∨
      (∃ retVal mem', stepMirFn body s = .retNormal retVal mem') ∨
      stepMirFn body s = .fail .ub) :=
  step_wellTypedBody_bisim hbody hstate hloc himm

example (divisor : Nat) (hd : divisor < 256) :
    WellTypedBody (Witness.divBody divisor) ∧
    StateRel (Witness.divBody divisor) (Witness.annealInit divisor) (Witness.miriInit divisor) ∧
    ValidFrameLocation (Witness.divBody divisor) (Witness.annealInit divisor).frame ∧
    NonAddrTakenImmediate (Witness.divBody divisor) (fun _ => True) (Witness.miriInit divisor) :=
  ⟨Witness.wellTypedBody divisor hd, Witness.stateRel_init divisor, ⟨_, rfl, Nat.zero_le _⟩,
    NonAddrTakenImmediate.of_live_nil _ (Witness.stateRel_init divisor) rfl⟩

example {localDecls : List MirAst.LocalDecl} {layouts : Layout.LayoutTable} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[topFrame]) :
    (annealStepHooks localDecls layouts).storageDead () 0 m =
      (m, .error (.stack .cannotMakeReturnPlaceDead)) :=
  annealStepHooks_storageDead_returnPlace hframes

example {body : CapturedMir} {nonAddrTaken : Nat → Prop}
    (fuel : Nat) {s : MachineState} {m : AnnealStepState}
    (hbody : WellTypedBody body nonAddrTaken)
    (hstate : StateRel body s m)
    (hloc : ValidFrameLocation body s.frame)
    (himm : NonAddrTakenImmediate body nonAddrTaken m) :
    ((∃ s', runAnnealBounded body fuel s = .running s') ↔
      (∃ m', runMiriBounded body fuel m = .running m')) ∧
    (∀ s' m',
      runAnnealBounded body fuel s = .running s' →
      runMiriBounded body fuel m = .running m' →
      StateRel body s' m') ∧
    ((∃ retVal mem', runAnnealBounded body fuel s = .returned retVal mem') ↔
      (∃ m' retImm, runMiriBounded body fuel m = .returned m' (.ok (.immediate retImm)))) ∧
    (∀ retVal mem' m' retImm,
      runAnnealBounded body fuel s = .returned retVal mem' →
      runMiriBounded body fuel m = .returned m' (.ok (.immediate retImm)) →
      ∃ decl0, get? body.localDecls 0 = some decl0 ∧
        ImmediateRel decl0.ty body.layouts retVal retImm) ∧
    (runAnnealBounded body fuel s = .faulted .ub ↔
      ∃ m' msg, runMiriBounded body fuel m = .error m' (.undefinedBehavior msg)) ∧
    ((∃ s', runAnnealBounded body fuel s = .running s') ∨
      (∃ retVal mem', runAnnealBounded body fuel s = .returned retVal mem') ∨
      runAnnealBounded body fuel s = .faulted .ub) :=
  run_wellTypedBody_bisim fuel hbody hstate hloc himm

example (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable)
    (place : MirAst.Place) (span : String) (m m' : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks localDecls layouts) ()
      (translateStmt ⟨.deinit place, span⟩) m ≠ (m', .ok ()) :=
  annealStepHooks_deinit_ne_ok localDecls layouts place span m m'

example (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable)
    (rk : MirAst.RetagKind) (place : MirAst.Place) (span : String) (m m' : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks localDecls layouts) ()
      (translateStmt ⟨.retag rk place, span⟩) m ≠ (m', .ok ()) :=
  annealStepHooks_retag_ne_ok localDecls layouts rk place span m m'

example (divisorBits : Nat) (hd : divisorBits < 256) :
    WellTypedBody (Witness.signedDivBody divisorBits) ∧
    StateRel (Witness.signedDivBody divisorBits)
      (Witness.annealSignedDivInit divisorBits)
      (Witness.miriSignedDivInit divisorBits) :=
  ⟨Witness.wellTyped_signedDiv divisorBits hd, Witness.stateRel_signedDiv divisorBits⟩

example (rhs : Nat) (hrhs : rhs < 65536) :
    WellTypedBody (Witness.addWithOverflowBody rhs) ∧
    StateRel (Witness.addWithOverflowBody rhs)
      (Witness.annealAddOvfInit rhs)
      (Witness.miriAddOvfInit rhs) :=
  ⟨Witness.wellTyped_addWithOverflow rhs hrhs, Witness.stateRel_addWithOverflow rhs⟩

example {mp : Miri.Interpreter.MemPlace AnnealProv}
    {baseAddr : UInt64} {relOffset : Miri.ABI.Size}
    (hno_ovf : baseAddr.toNat + relOffset.bytes.toNat < 2 ^ 64)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes)) :
    relOffset.bytes.toNat = mp.ptr.offset.bytes.toNat - baseAddr.toNat :=
  MemPlaceRel.relOffset_bytes_eq hno_ovf hptr

example :
    LocalRel (Witness.witnessMachineOf Witness.witnessUninitAlloc) Witness.u8Decl
      emptyLayoutTable .uninit ⟨.live (.indirect Witness.witnessMemPlace), none⟩ ∧
    LocalRel (Witness.witnessMachineOf Witness.witnessInitAlloc42) Witness.u8Decl
      emptyLayoutTable (.init (.scalar ⟨42, 1⟩))
      ⟨.live (.indirect Witness.witnessMemPlace), none⟩ :=
  ⟨Witness.indirect_localRel_uninit_witness, Witness.indirect_localRel_scalar_witness⟩

example :
    WellTypedBody Witness.unreachableBody ∧
    StateRel Witness.unreachableBody Witness.annealUnreachableInit Witness.miriUnreachableInit ∧
    (Witness.annealOutcomeIsUB
        (runAnnealBounded Witness.unreachableBody 4 Witness.annealUnreachableInit) = true ∧
      Witness.miriOutcomeIsUB
        (runMiriBounded Witness.unreachableBody 4 Witness.miriUnreachableInit) = true) :=
  ⟨Witness.wellTyped_unreachable, Witness.stateRel_unreachable, Witness.unreachable_ub_agrees⟩

example :
    WellTypedBody Witness.charCopyBody ∧
    StateRel Witness.charCopyBody Witness.annealCharInit Witness.miriCharInit ∧
    (Witness.annealOutcomeScalarBits 4
        (runAnnealBounded Witness.charCopyBody 5 Witness.annealCharInit) = some 0x03BB ∧
      Witness.miriOutcomeScalarBits 4
        (runMiriBounded Witness.charCopyBody 5 Witness.miriCharInit) = some 0x03BB) :=
  ⟨Witness.wellTyped_charCopy, Witness.stateRel_charCopy, Witness.charCopy_returns_agree⟩

example {body : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRel body m aRes mRes) :
    ((∃ obs s', aRes = .emitStep obs s' ∧ StateRel body s' mRes.1) ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames ≠ #[])) ∧
    ((∃ retVal mem', aRes = .retNormal retVal mem') ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames = #[])) ∧
    ((aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg))) :=
  ⟨h.emitStep_iff, h.retNormal_iff, h.ub_iff⟩

example (body : CapturedMir) (fuel : Nat) (s s' : MachineState) (obs : MirObs)
    (hstep : stepMirFn body s = .emitStep obs s') :
    runAnnealBounded body (fuel + 1) s = runAnnealBounded body fuel s' :=
  runAnnealBounded_emitStep body fuel s s' obs hstep

example (shiftBits : Nat) (hs : shiftBits < 65536) :
    WellTypedBody (Witness.shiftUncheckedBody shiftBits) ∧
    StateRel (Witness.shiftUncheckedBody shiftBits)
      (Witness.annealShiftUncheckedInit shiftBits)
      (Witness.miriShiftUncheckedInit shiftBits) :=
  ⟨Witness.wellTyped_shiftUnchecked shiftBits hs, Witness.stateRel_shiftUnchecked shiftBits⟩

example (rhs : Nat) (hrhs : rhs < 256) :
    WellTypedBody (Witness.addUncheckedNopBody rhs) ∧
    StateRel (Witness.addUncheckedNopBody rhs)
      (Witness.annealAddUncheckedNopInit rhs)
      (Witness.miriAddUncheckedNopInit rhs) :=
  ⟨Witness.wellTyped_addUncheckedNop rhs hrhs, Witness.stateRel_addUncheckedNop rhs⟩

example :
    WellTypedBody Witness.unaryBitwiseBody ∧
    StateRel Witness.unaryBitwiseBody Witness.annealUnaryBitwiseInit Witness.miriUnaryBitwiseInit ∧
    (Witness.annealOutcomeScalarBits 1
        (runAnnealBounded Witness.unaryBitwiseBody 6 Witness.annealUnaryBitwiseInit) = some 0x2A ∧
      Witness.miriOutcomeScalarBits 1
        (runMiriBounded Witness.unaryBitwiseBody 6 Witness.miriUnaryBitwiseInit) = some 0x2A) :=
  ⟨Witness.wellTyped_unaryBitwise, Witness.stateRel_unaryBitwise, Witness.unaryBitwise_returns_agree⟩

/-! ### `LM-1.2` -/

example
    {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (locals : List LocalSlot)
    (mem : Memory)
    (localDecls : List MirAst.LocalDecl)
    (layouts : Layout.LayoutTable)
    (ty : Ty)
    (hty : ty.kind = .bool)
    (hsz : sc.sizeBytes = 1)
    (hbits : sc.bits = 0 ∨ sc.bits = 1) :
    ∃ sc' msc',
      evalUnaryNot sc (some ty) locals mem = .ok (.scalar sc') locals mem ∧
      Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks localDecls layouts) () .Not
        ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy ty layouts⟩ ∧
      ScalarRel sc' msc' ∧
      sc'.sizeBytes = 1 ∧ (sc'.bits = 0 ∨ sc'.bits = 1) :=
  evalUnOp_bool_not_simulation hrel locals mem localDecls layouts ty hty hsz hbits

example
    (op : MirAst.BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {sc₁ sc₂ : MirAst.ScalarInt}
    {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁)
    (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot)
    (mem : Memory)
    (localDecls : List MirAst.LocalDecl)
    (layouts : Layout.LayoutTable)
    (ty : Ty)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes)
    (hsz_ty : sc₁.sizeBytes = match ty.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc₁.sizeBytes)
    (hbits₁ : ty.kind = .bool → sc₁.bits = 0 ∨ sc₁.bits = 1)
    (hbits₂ : ty.kind = .bool → sc₂.bits = 0 ∨ sc₂.bits = 1)
    (mop : Miri.MIR.BinOp)
    (hmop : translateBinOp op = some mop) :
    ∃ b : Bool,
      evalScalarBinOp op sc₁ sc₂ locals mem (tyIsSigned ty) =
        .ok (.scalar (boolToScalar b)) locals mem ∧
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) () mop
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty layouts⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty layouts⟩ =
        .ok ⟨.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofBool b)),
          translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable⟩ :=
  evalBinOp_rel_simulation op hop hrel₁ hrel₂ locals mem localDecls layouts ty hty hsz hsz_ty hbits₁ hbits₂ mop hmop

example
    {sc₁ sc₂ : MirAst.ScalarInt}
    {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁)
    (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot)
    (mem : Memory)
    (isSigned : Bool)
    (kind : Miri.MIR.IntegerKind)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes)
    (hsigned : kind.signed = isSigned) :
    ∃ o : Ordering,
      evalScalarBinOp .cmp sc₁ sc₂ locals mem isSigned =
        .ok (.scalar ⟨orderingI8Bits o, 1⟩) locals mem ∧
      Miri.Interpreter.IntegerOps.binary .Cmp
        ⟨msc₁, ⟨translateSizeBytes sc₁.sizeBytes, kind⟩⟩
        ⟨msc₂, ⟨translateSizeBytes sc₂.sizeBytes, kind⟩⟩ =
        .ok (.ordering o) :=
  evalBinOp_cmp_simulation hrel₁ hrel₂ locals mem isSigned kind hsz hsigned

example
    {sc₁ sc₂ : MirAst.ScalarInt}
    {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (hrel₁ : ScalarRel sc₁ msc₁)
    (hrel₂ : ScalarRel sc₂ msc₂)
    (locals : List LocalSlot)
    (mem : Memory)
    (localDecls : List MirAst.LocalDecl)
    (layouts : Layout.LayoutTable)
    {ty : Ty}
    {kind : Miri.MIR.IntegerKind}
    (hty : IsIntegralTy ty kind)
    (hsz_ty : (translateTy ty layouts).layout.size = translateSizeBytes sc₁.sizeBytes)
    (hsz : sc₁.sizeBytes = sc₂.sizeBytes) :
    ∃ (o : Ordering) (msc'' : Miri.Memory.ScalarInt),
      o = compare (decodeBitsInt kind.signed sc₁.sizeBytes sc₁.bits)
        (decodeBitsInt kind.signed sc₁.sizeBytes sc₂.bits) ∧
      evalScalarBinOp .cmp sc₁ sc₂ locals mem (tyIsSigned ty) =
        .ok (.scalar ⟨orderingI8Bits o, 1⟩) locals mem ∧
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) () .Cmp
        ⟨.scalar (.fromScalarInt msc₁), translateTy ty layouts⟩
        ⟨.scalar (.fromScalarInt msc₂), translateTy ty layouts⟩ =
        .ok ⟨.scalar (.fromScalarInt msc''),
          translateTy { kind := .int .i8, layoutIdx := 0 } emptyLayoutTable⟩ ∧
      ScalarRel ⟨orderingI8Bits o, 1⟩ msc'' :=
  scalarOps_cmp_simulation hrel₁ hrel₂ locals mem localDecls layouts hty hsz_ty hsz

example
    {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    {locals locals' : List LocalSlot}
    {mem : Memory}
    {localDecls : List MirAst.LocalDecl}
    {layouts : Layout.LayoutTable}
    {op : MirAst.Operand}
    {srcTy dstTy : Ty}
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals =
      .ok (.scalar sc) locals')
    (hopTy : operandTy localDecls layouts op = some srcTy)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hdst : (∃ k, dstTy.kind = .int k) ∨ (∃ k, dstTy.kind = .uint k))
    (hsz_src : sc.sizeBytes = match srcTy.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits_src : srcTy.kind = .bool → sc.bits = 0 ∨ sc.bits = 1)
    (h_dest : dest.layout = translateTy dstTy layouts) :
    ∃ msc',
      evalRvalue locals (.cast .intToInt op dstTy) mem localDecls layouts =
        .ok (.scalar ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
          (2 : Int) ^ (8 * boolOrIntByteWidth dstTy)).toNat, boolOrIntByteWidth dstTy⟩) locals' mem ∧
      Miri.Interpreter.Cast.castFromIntLike (annealCastHooks layouts) ()
        (.fromScalarInt msc) (translateTy srcTy layouts) (translateTy dstTy layouts) =
        .ok ⟨.scalar (.fromScalarInt msc'), translateTy dstTy layouts⟩ ∧
      Miri.Interpreter.Cast.cast (annealCastHooks layouts) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcTy layouts⟩ .IntToInt
        (encodeTyId dstTy) dest =
        annealWriteImmediate (.scalar (.fromScalarInt msc')) dest ∧
      ScalarRel ⟨(decodeBitsInt (tyIsSigned srcTy) sc.sizeBytes sc.bits %
          (2 : Int) ^ (8 * boolOrIntByteWidth dstTy)).toNat, boolOrIntByteWidth dstTy⟩ msc' :=
  evalCast_intToInt_simulation hrel dest hop hopTy hsrc hdst hsz_src hbits_src h_dest

example
    (layouts : Layout.LayoutTable)
    (srcTy dstTy : Ty)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (hsrc : srcTy.kind = .bool ∨ (∃ k, srcTy.kind = .int k) ∨ (∃ k, srcTy.kind = .uint k))
    (hdst : (∃ k, dstTy.kind = .int k) ∨ (∃ k, dstTy.kind = .uint k))
    (h_dest : dest.layout = translateTy dstTy layouts)
    (st : AnnealStepState) :
    Miri.Interpreter.Cast.cast (annealCastHooks layouts) () 16
      ⟨.immediate .uninit, translateTy srcTy layouts⟩ .IntToInt (encodeTyId dstTy) dest st =
      .error (.undefinedBehavior "read of uninitialized local") st :=
  cast_intToInt_uninit layouts srcTy dstTy dest hsrc hdst h_dest st

example
    {sc : MirAst.ScalarInt}
    {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (localDecls : List MirAst.LocalDecl)
    (layouts : Layout.LayoutTable)
    (ty : Ty)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hsz_ty : sc.sizeBytes = match ty.kind with | .bool => 1 | .int k => k.byteWidth 64 | .uint k => k.byteWidth 64 | _ => sc.sizeBytes)
    (hbits : ty.kind = .bool → sc.bits = 0 ∨ sc.bits = 1)
    (caseVal : Nat)
    (hcase_lt : caseVal < scalarModulus sc.sizeBytes)
    (hcase_bool : ty.kind = .bool → caseVal = 0 ∨ caseVal = 1)
    (state : AnnealStepState) :
    (annealTerminatorHooks localDecls layouts).compareSwitchCase ()
      ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ caseVal state =
      (state, .ok (Nat.beq sc.bits caseVal)) :=
  compareSwitchCase_simulation hrel localDecls layouts ty hty hsz_ty hbits caseVal hcase_lt hcase_bool state

example
    {P L E M C Op Imm : Type}
    (hooks : Miri.Interpreter.TerminatorHooks P L E M C Op Imm)
    (choice : C)
    (si : Miri.MIR.SourceInfo)
    (discr : Miri.MIR.Operand)
    (targets : SwitchTargets)
    (state state' : Miri.Interpreter.StepState P L E M)
    (value : Imm)
    (bits : Nat)
    (hdisc : hooks.evalDiscriminant choice discr state = (state', .ok value))
    (hcmp : ∀ v b, (v, b) ∈ targets.branches →
      hooks.compareSwitchCase choice value v state' = (state', .ok (Nat.beq bits v))) :
    Miri.Interpreter.ControlFlow.evalTerminator hooks choice
        { sourceInfo := si, kind := .SwitchInt discr (translateSwitchTargets targets) } state =
      Miri.Interpreter.ControlFlow.goToBlock
        (lookupSwitchTarget bits targets.branches targets.otherwise) state' :=
  evalTerminator_switchInt_ok hooks choice si discr targets state state' value bits hdisc hcmp

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {discr : MirAst.Operand}
    {targets : SwitchTargets}
    {ty : Ty}
    (hterm : bb.terminator.kind = .switchInt discr targets)
    (hty : ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k))
    (hdiscr : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame discr ty)
    (hcases : SwitchCasesFit ty targets) :
    StepObsRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_switchInt_simulation hstate hphase hbb hstmt_none hstmt_len hterm hty hdiscr hcases

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM12Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_assign_lm1_2_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarStmt body topFrame stmt ∨ WellTypedLM12Stmt body topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm1_2_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm :
      ((∃ target, bb.terminator.kind = .goto target) ∨
        (bb.terminator.kind = .return_ ∧
          ∃ decl0,
            get? body.localDecls 0 = some decl0 ∧
            (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
            ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) ∨
        bb.terminator.kind = .unreachable) ∨
      (∃ discr targets ty,
        bb.terminator.kind = .switchInt discr targets ∧
        (ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k)) ∧
        (∀ topFrame, m.stack.frames = #[topFrame] →
          WellTypedScalarOperand body topFrame discr ty) ∧
        SwitchCasesFit ty targets)) :
    StepObsRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_lm1_2_simulation hstate hphase hbb hstmt_none hstmt_len hcleanup hterm

open Witness in
example
    (d : Nat)
    (hd : d < 256) :
    StepObsRel (lm12SwitchBody d) (lm12MiriInit (lm12SwitchBody d) u8Ty)
      (stepMirFn (lm12SwitchBody d) (initMachineState (lm12SwitchBody d) []))
      (Miri.Interpreter.Step.step
        (annealStepHooks (lm12SwitchBody d).localDecls (lm12SwitchBody d).layouts) ()
        (lm12MiriInit (lm12SwitchBody d) u8Ty)) :=
  lm12Switch_step_applies d hd

open Witness in
example
     :
    annealOutcomeScalarBits 1
        (runAnnealBounded (lm12SwitchBody 7) 4 (initMachineState (lm12SwitchBody 7) [])) =
      some 20 ∧
    miriOutcomeScalarBits 1
        (runMiriBounded (lm12SwitchBody 7) 4 (lm12MiriInit (lm12SwitchBody 7) u8Ty)) =
      some 20 :=
  lm12Switch_case_agrees

open Witness in
example
     :
    annealOutcomeScalarBits 1
        (runAnnealBounded (lm12SwitchBody 9) 4 (initMachineState (lm12SwitchBody 9) [])) =
      some 30 ∧
    miriOutcomeScalarBits 1
        (runMiriBounded (lm12SwitchBody 9) 4 (lm12MiriInit (lm12SwitchBody 9) u8Ty)) =
      some 30 :=
  lm12Switch_otherwise_agrees

open Witness in
example
     :
    StepRel lm12BoolCmpBody (lm12MiriInit lm12BoolCmpBody boolTy)
      (stepMirFn lm12BoolCmpBody (initMachineState lm12BoolCmpBody []))
      (Miri.Interpreter.Step.step
        (annealStepHooks lm12BoolCmpBody.localDecls lm12BoolCmpBody.layouts) ()
        (lm12MiriInit lm12BoolCmpBody boolTy)) :=
  lm12BoolCmp_step_applies

open Witness in
example
     :
    annealOutcomeScalarBits 1
        (runAnnealBounded lm12BoolCmpBody 3 (initMachineState lm12BoolCmpBody [])) = some 1 ∧
    miriOutcomeScalarBits 1
        (runMiriBounded lm12BoolCmpBody 3 (lm12MiriInit lm12BoolCmpBody boolTy)) = some 1 :=
  lm12BoolCmp_returns_agree

open Witness in
example
     :
    StepRel lm12CastBody (lm12MiriInit lm12CastBody lm12I16Ty)
      (stepMirFn lm12CastBody (initMachineState lm12CastBody []))
      (Miri.Interpreter.Step.step
        (annealStepHooks lm12CastBody.localDecls lm12CastBody.layouts) ()
        (lm12MiriInit lm12CastBody lm12I16Ty)) :=
  lm12Cast_step_applies

open Witness in
example
     :
    annealOutcomeScalarBits 2
        (runAnnealBounded lm12CastBody 3 (initMachineState lm12CastBody [])) = some 0xFFFF ∧
    miriOutcomeScalarBits 2
        (runMiriBounded lm12CastBody 3 (lm12MiriInit lm12CastBody lm12I16Ty)) = some 0xFFFF :=
  lm12Cast_returns_agree

open Witness in
example
     :
    (annealOutcomeScalarBits 1
        (runAnnealBounded (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) 3
          (initMachineState (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) [])) = some 0x34 ∧
      miriOutcomeScalarBits 1
        (runMiriBounded (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) 3
          (lm12MiriInit (lm12CastBodyOf (constU16 0x1234) u8Decl u8Layout) u8Ty)) = some 0x34) ∧
    (annealOutcomeScalarBits 2
        (runAnnealBounded (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) 3
          (initMachineState (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) [])) =
        some 0x00FF ∧
      miriOutcomeScalarBits 2
        (runMiriBounded (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) 3
          (lm12MiriInit (lm12CastBodyOf (constU8 0xFF) u16Decl lm12I16Layout) u16Ty)) =
        some 0x00FF) ∧
    (annealOutcomeScalarBits 4
        (runAnnealBounded (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout) 3
          (initMachineState (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout) [])) =
        some 1 ∧
      miriOutcomeScalarBits 4
        (runMiriBounded (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout) 3
          (lm12MiriInit (lm12CastBodyOf (lm12ConstBool true) lm12I32Decl lm12I32Layout)
            lm12I32Ty)) =
        some 1) :=
  lm12Cast_shapes_agree

/-! ### `LM-1.4` statement pins -/

example {body : CapturedMir} {topFrame : Miri.Interpreter.Frame AnnealProv
      Miri.Interpreter.LocalLayout Unit}
    {loc : MirAst.Local} {decl : MirAst.LocalDecl} {span : String}
    (hdecl : get? body.localDecls loc = some decl) :
    WellTypedLM1_4Stmt body topFrame ⟨.storageLive loc, span⟩ :=
  .storageLive loc decl span hdecl

example {body : CapturedMir} {topFrame : Miri.Interpreter.Frame AnnealProv
      Miri.Interpreter.LocalLayout Unit}
    {loc : MirAst.Local} {decl : MirAst.LocalDecl} {span : String}
    (hdecl : get? body.localDecls loc = some decl) (hne : loc ≠ 0) :
    WellTypedLM1_4Stmt body topFrame ⟨.storageDead loc, span⟩ :=
  .storageDead loc decl span hdecl hne

example {body : CapturedMir} {topFrame : Miri.Interpreter.Frame AnnealProv
      Miri.Interpreter.LocalLayout Unit}
    {loc : MirAst.Local} {decl : MirAst.LocalDecl} {span : String}
    (hdecl : get? body.localDecls loc = some decl) (hlive : IsLiveFrameLocal topFrame loc) :
    WellTypedLM1_4Stmt body topFrame ⟨.placeMention ⟨loc, .nil⟩, span⟩ :=
  .placeMention loc decl span hdecl hlive

example {body : CapturedMir} {topFrame : Miri.Interpreter.Frame AnnealProv
      Miri.Interpreter.LocalLayout Unit}
    {dstIdx srcIdx : MirAst.Local} {dstDecl srcDecl : MirAst.LocalDecl} {span : String}
    (hdst : get? body.localDecls dstIdx = some dstDecl)
    (hsrc : get? body.localDecls srcIdx = some srcDecl)
    (hty : dstDecl.ty = srcDecl.ty)
    (hsz : (translateTy srcDecl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (himm_src : IsImmediateFrameLocal topFrame srcIdx)
    (himm_dst : IsImmediateFrameLocal topFrame dstIdx) :
    WellTypedLM1_4Stmt body topFrame
      ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩ :=
  .assignMove dstIdx srcIdx dstDecl srcDecl span hdst hsrc hty hsz himm_src himm_dst

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {loc : MirAst.Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.storageLive loc, span⟩) :
    StepRel body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_storageLive_simulation hstate hphase hbb hstmt hwt

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {loc : MirAst.Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.storageDead loc, span⟩) :
    StepRel body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_storageDead_simulation hstate hphase hbb hstmt hwt

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {loc : MirAst.Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention ⟨loc, .nil⟩, span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame ⟨.placeMention ⟨loc, .nil⟩, span⟩) :
    StepRel body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_placeMention_simulation hstate hphase hbb hstmt hwt

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {dstIdx srcIdx : MirAst.Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM1_4Stmt body topFrame
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) :
    StepRel body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalOperand_move_simulation hstate hphase hbb hstmt hwt

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m) (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM1_4Stmt body topFrame stmt) :
    StepRel body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm1_4_simulation hstate hphase hbb hstmt hwt

example {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {place : Miri.Interpreter.RuntimePlace AnnealProv}
    {mplace : Miri.Interpreter.MPlaceTy AnnealProv}
    (hstate : StateRel body s m)
    (hforce : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) ()
      place m = .ok mplace m') :
    StateRel body s m' ∧
    ∀ frameIndex localId identity,
      place.ref = .local frameIndex localId none identity →
      ∃ tf' lay, m'.stack.frames = #[tf'] ∧
        tf'.locals[localId]? = some ⟨.live (.indirect mplace.mplace), lay⟩ :=
  forceAllocation_preserves_StateRel hstate hforce

example {body : CapturedMir} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Nat} {decl : MirAst.LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[topFrame])
    (hlt : idx < topFrame.locals.size)
    (hdecl : get? body.localDecls idx = some decl)
    (hmls : topFrame.locals[idx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy decl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts (.Move ⟨idx, #[]⟩) known m =
      .ok ⟨opVal, translateTy decl.ty body.layouts⟩
        { m with
          stack := ⟨#[deinitFrameLocal
            (cacheFrameLocalLayout topFrame idx hlt (translateTy decl.ty body.layouts)) idx
            (by rw [cacheFrameLocalLayout_size]; exact hlt)]⟩ } :=
  annealEvalOperand_move_live hframes hlt hdecl hmls hcache

/-! ### `LM-1.4` witness pins -/

example :
    StateRel Witness.lm14MoveBody (Witness.lm14MoveAnneal 3) (Witness.lm14MoveMiri 3) ∧
    StepRel Witness.lm14MoveBody (Witness.lm14MoveMiri 3)
      (stepMirFn Witness.lm14MoveBody (Witness.lm14MoveAnneal 3))
      (Miri.Interpreter.Step.step
        (annealStepHooks Witness.lm14MoveBody.localDecls Witness.lm14MoveBody.layouts) ()
        (Witness.lm14MoveMiri 3)) :=
  ⟨Witness.lm14_stateRel 3, Witness.lm14_move_stepRel⟩

example :
    stepMirFn Witness.lm14MoveBody (Witness.lm14MoveAnneal 3) =
      .step Witness.lm14MovedAnneal ∧
    ∃ m', Miri.Interpreter.Step.step
        (annealStepHooks Witness.lm14MoveBody.localDecls Witness.lm14MoveBody.layouts) ()
        (Witness.lm14MoveMiri 3) = (m', .ok true) ∧
      StateRel Witness.lm14MoveBody Witness.lm14MovedAnneal m' :=
  ⟨Witness.lm14_move_anneal_step, Witness.lm14_move_steps⟩

example :
    stepMirFn Witness.lm14MoveBody (Witness.lm14MoveAnneal 2) =
      .step (Witness.lm14MoveAnneal 3) ∧
    ∃ m', Miri.Interpreter.Step.step
        (annealStepHooks Witness.lm14MoveBody.localDecls Witness.lm14MoveBody.layouts) ()
        (Witness.lm14MoveMiri 2) = (m', .ok true) ∧
      StateRel Witness.lm14MoveBody (Witness.lm14MoveAnneal 3) m' :=
  Witness.lm14_placeMention_steps

example :
    (Witness.lm14MoveMiriFrame 3).locals[1]? =
      some ⟨.live (.immediate (.scalar (.fromScalarInt Witness.lm14Scalar42))), none⟩ ∧
    ∃ (mplace : Miri.Interpreter.MPlaceTy AnnealProv) (m' : AnnealStepState),
      Miri.Interpreter.forceAllocation
          (annealPlaceHooks Witness.lm14MoveBody.localDecls Witness.lm14MoveBody.layouts) ()
          ⟨.local 0 1 none (Witness.lm14MoveMiriFrame 3).localsIdentity,
            translateTy Witness.u8Ty⟩
          (Witness.lm14MoveMiri 3) = .ok mplace m' ∧
      (∃ tf' lay', m'.stack.frames = #[tf'] ∧
        tf'.locals[1]? = some ⟨.live (.indirect mplace.mplace), lay'⟩) ∧
      StateRel Witness.lm14MoveBody (Witness.lm14MoveAnneal 3) m' :=
  ⟨rfl, Witness.lm14_forceAllocation_witness 3⟩

example :
    ∃ (m : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (lay : Option Miri.Interpreter.LocalLayout),
      m.stack.frames = #[tf] ∧ tf.locals[1]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StateRel Witness.lm14MoveBody (Witness.lm14MoveAnneal 0) m ∧
      stepMirFn Witness.lm14MoveBody (Witness.lm14MoveAnneal 0) =
        .step Witness.lm14LiveAnneal ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm14MoveBody.localDecls Witness.lm14MoveBody.layouts) () m =
          (m', .ok true) ∧
        StateRel Witness.lm14MoveBody Witness.lm14LiveAnneal m' :=
  Witness.lm14_storageLive_indirect_steps

example :
    ∃ (m : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv)
      (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (lay : Option Miri.Interpreter.LocalLayout),
      m.stack.frames = #[tf] ∧ tf.locals[1]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StateRel Witness.lm14MoveBody (Witness.lm14MoveAnneal 4) m ∧
      stepMirFn Witness.lm14MoveBody (Witness.lm14MoveAnneal 4) =
        .step Witness.lm14DeadAnneal ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm14MoveBody.localDecls Witness.lm14MoveBody.layouts) () m =
          (m', .ok true) ∧
        StateRel Witness.lm14MoveBody Witness.lm14DeadAnneal m' :=
  Witness.lm14_storageDead_indirect_steps

/-! ### `LM-2.1` (`ArraySliceRel`, `SimLM2_1`, `WitLM2_1`) statement pins -/

example
    {elemKind : MirAst.RigidTy} {count : Nat} {layouts : Layout.LayoutTable}
    {elems : List Value} {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind count layouts elems relOffset alloc)
    {idx : Nat} {elemVal : Value}
    (hget : get? elems idx = some elemVal) :
    let elemTy : MirAst.Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy layouts).layout
    let elemOff :=
      Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (idx * elemLay.size.bytes.toNat))
    ∃ sc msc,
      elemVal = .scalar sc ∧
      ImmediateRel elemTy layouts elemVal (.scalar (.fromScalarInt msc)) ∧
      alloc.readScalar
        annealTargetDataLayout
        (Miri.Memory.allocRange elemOff elemLay.size)
        false = .ok (.fromScalarInt msc) :=
  hslice.readScalar_get hget

example
    {elemKind : MirAst.RigidTy} {count : Nat} {layouts : Layout.LayoutTable}
    {elems : List Value} {relOffset : Miri.ABI.Size}
    {alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind count layouts elems relOffset alloc)
    {idx : Nat} (hlt : idx < count)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange
          (Miri.ABI.Size.ofBytes
            (relOffset.bytes +
              UInt64.ofNat
                (idx *
                  (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
          msc.size)
        (.fromScalarInt msc) alloc = .ok () alloc' ∧
      alloc'.byteSize = alloc.byteSize ∧
      alloc'.align = alloc.align ∧
      alloc'.initializationMask = alloc.initializationMask ∧
      ArraySliceRel elemKind count layouts (elems.set idx (.scalar sc)) relOffset alloc' :=
  hslice.writeScalar_set hlt hrel hsz hbool hchar

example
    {mach : AnnealMachine} {ty : MirAst.Ty} {layouts : Layout.LayoutTable} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {offset : Miri.ABI.Size}
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach ty layouts optVal mp)
    (hoff_le : offset.bytes.toNat ≤ (translateTy ty layouts).layout.size.bytes.toNat)
    (hoff_i64 : offset.bytes.toNat < 2 ^ 63) :
    Miri.Interpreter.projectionMemoryOffset
      annealPointerArithmetic
      (annealPointerResolver mach)
      (annealLiveAllocationLookup mach)
      mp offset .inbounds .none =
      .ok
        { mp with
          ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + offset.bytes) }
          metadata := .none } :=
  projectionMemoryOffset_inbounds_of_memPlaceRel hnodup hmp hoff_le hoff_i64

example
    {m : AnnealStepState} {layouts : Layout.LayoutTable}
    {arrTy : MirAst.Ty} {elemKind : MirAst.RigidTy} {count : Nat} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup m.machine)
    (hmp : MemPlaceRel m.machine arrTy layouts optVal mp) :
    annealReadImmediate ⟨.indirect mp, translateTy arrTy layouts⟩ m =
      .error (.unsupported "whole-array immediate read not supported") m :=
  annealReadImmediate_whole_array_unsupported hwf hnodup hmp

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {idxLocal : MirAst.Local} {arrTy : MirAst.Ty} {idxDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hmp : MemPlaceRel m.machine arrTy body.layouts (some (.aggregate 0 elems)) mp)
    (hidx_decl : get? body.localDecls idxLocal = some idxDecl)
    (hidx_ty : idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 }) :
    let cx := annealProjectionCx topFrame body.layouts m.machine
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect mp, translateTy arrTy body.layouts⟩
    let elemTy : MirAst.Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy body.layouts).layout
    ((get? s.frame.locals idxLocal = some .dead ∨ get? s.frame.locals idxLocal = some .uninit) →
      readProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] = .ub ∧
      (∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] v = .ub) ∧
      ∃ msg,
        (annealProjectList cx base [.Index idxLocal]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) ∧
    (∀ idxSc : MirAst.ScalarInt,
      get? s.frame.locals idxLocal = some (.init (.scalar idxSc)) →
      idxSc.bits < count →
      ∃ elemVal sc msc,
        get? elems idxSc.bits = some elemVal ∧
        elemVal = .scalar sc ∧
        readProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] =
          ProjReadResult.ok elemVal ∧
        annealProjectList cx base [.Index idxLocal] =
          Except.ok
            ⟨.indirect
              { mp with
                ptr :=
                  { mp.ptr with
                    offset :=
                      Miri.ABI.Size.ofBytes
                        (mp.ptr.offset.bytes +
                          UInt64.ofNat (idxSc.bits * elemLay.size.bytes.toNat)) }
                metadata := .none },
              translateTy elemTy body.layouts⟩ ∧
        ImmediateRel elemTy body.layouts elemVal (.scalar (.fromScalarInt msc)) ∧
        annealReadImmediate
          ⟨.indirect
            { mp with
              ptr :=
                { mp.ptr with
                  offset :=
                    Miri.ABI.Size.ofBytes
                      (mp.ptr.offset.bytes +
                        UInt64.ofNat (idxSc.bits * elemLay.size.bytes.toNat)) }
              metadata := .none },
            translateTy elemTy body.layouts⟩
          m = EStateM.Result.ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩ m) ∧
    (∀ idxSc : MirAst.ScalarInt,
      get? s.frame.locals idxLocal = some (.init (.scalar idxSc)) →
      count ≤ idxSc.bits →
      readProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] = .ub ∧
      (∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [.index idxLocal] v = .ub) ∧
      ∃ msg,
        (annealProjectList cx base [.Index idxLocal]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) :=
  evalProjection_index_simulation hrel hframes hnodup hwf hmp hidx_decl hidx_ty

example
    {body : CapturedMir} {locals : List LocalSlot} {m : AnnealStepState}
    (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (hnodup : LiveAllocsNodup m.machine)
    {arrTy : MirAst.Ty}
    {elemKind : MirAst.RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy body.layouts arrTy elemKind count)
    (hmp : MemPlaceRel m.machine arrTy body.layouts (some (.aggregate 0 elems)) mp)
    (offset minLength : Nat) (fromEnd : Bool)
    (hoff_bound : offset < 2 ^ 64)
    (hmin_bound : minLength < 2 ^ 64)
    (hwf_const :
      (fromEnd = false → offset < minLength) ∧
      (fromEnd = true → 0 < offset ∧ offset ≤ minLength)) :
    let cx := annealProjectionCx topFrame body.layouts m.machine
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect mp, translateTy arrTy body.layouts⟩
    let elemTy : MirAst.Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy body.layouts).layout
    let idx := if fromEnd then count - offset else offset
    (minLength ≤ count →
      ∃ elemVal sc msc,
        get? elems idx = some elemVal ∧
        elemVal = .scalar sc ∧
        readProjectedValue locals (.aggregate 0 elems)
          [.constantIndex offset minLength fromEnd] = ProjReadResult.ok elemVal ∧
        annealProjectList cx base [.ConstantIndex offset minLength fromEnd] =
          Except.ok
            ⟨.indirect
              { mp with
                ptr :=
                  { mp.ptr with
                    offset :=
                      Miri.ABI.Size.ofBytes
                        (mp.ptr.offset.bytes +
                          UInt64.ofNat (idx * elemLay.size.bytes.toNat)) }
                metadata := .none },
              translateTy elemTy body.layouts⟩ ∧
        ImmediateRel elemTy body.layouts elemVal (.scalar (.fromScalarInt msc)) ∧
        annealReadImmediate
          ⟨.indirect
            { mp with
              ptr :=
                { mp.ptr with
                  offset :=
                    Miri.ABI.Size.ofBytes
                      (mp.ptr.offset.bytes +
                        UInt64.ofNat (idx * elemLay.size.bytes.toNat)) }
              metadata := .none },
            translateTy elemTy body.layouts⟩
          m = EStateM.Result.ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩ m) ∧
    (count < minLength →
      readProjectedValue locals (.aggregate 0 elems)
        [.constantIndex offset minLength fromEnd] = .ub ∧
      (∀ v,
        writeProjectedValue locals (.aggregate 0 elems)
          [.constantIndex offset minLength fromEnd] v = .ub) ∧
      ∃ msg,
        (annealProjectList cx base [.ConstantIndex offset minLength fromEnd]).mapError
          annealLiftProjectionError = .error (.undefinedBehavior msg)) :=
  evalProjection_constantIndex_simulation topFrame hnodup hwf hmp
    offset minLength fromEnd hoff_bound hmin_bound hwf_const

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {dstIdx arrIdx : MirAst.Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.len ⟨arrIdx, .nil⟩), span⟩)
    {arrDecl dstDecl : MirAst.LocalDecl} {elemKind : MirAst.RigidTy} {count : Nat}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_ty : dstDecl.ty = { kind := .uint .usize, layoutIdx := 0 })
    (hdst_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (harr_slot :
      get? s.frame.locals arrIdx = some .dead ∨
      (get? s.frame.locals arrIdx = some .uninit ∧
        (0 < count ∨
          ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame arrIdx)) ∨
      ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun _ => True)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_len_array_simulation hstate hnodup hphase hbb hstmt
    hdecl_arr hwf hdecl_dst hdst_ty hdst_imm harr_slot

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {bb : MirAst.BasicBlockData} {dstIdx : MirAst.Local} {dstDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {op : MirAst.Operand} {span : String}
    (hrel : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hdst_ready : ∀ topFrame, m.stack.frames = #[topFrame] →
      ArrayConstructDestReady s m topFrame dstIdx)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM2_1ScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 }) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 1
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_repeat_simulation hrel hnodup hbb hstmt hdecl_dst hwf hdst_ready hop hprim

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {bb : MirAst.BasicBlockData} {dstIdx : MirAst.Local} {dstDecl : MirAst.LocalDecl}
    {elemTy : MirAst.Ty} {elemKind : MirAst.RigidTy} {count : Nat}
    {ops : List MirAst.Operand} {span : String}
    (hrel : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hlen_ops : ops.length = count)
    (hdst_ready : ∀ topFrame, m.stack.frames = #[topFrame] →
      ArrayConstructDestReady s m topFrame dstIdx)
    (hops : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ op ∈ ops, WellTypedLM2_1ScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 }) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
        body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => j ≠ dstIdx)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 1
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_aggregate_array_simulation hrel hnodup hbb hstmt hdecl_dst hwf hlen_ops hdst_ready
    hops hprim

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedArrayElemAssign body s topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun _ => True)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_assign_array_element_simulation hstate hnodup hphase hbb hstmt hwt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM2_1ArrayStmt body s m topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => arrayConstructDest? stmt ≠ some j)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m (if (arrayConstructDest? stmt).isSome then 1 else 0)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm2_1_array_simulation hstate hnodup hphase hbb hstmt hwt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    {bb : MirAst.BasicBlockData} {loc : MirAst.Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    {tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (htf' :
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) ()
          m).1.stack.frames = #[tf']) :
    IsImmediateFrameLocal tf' loc :=
  step_storageLive_establishes_immediate hstate hbb hstmt hdecl htf'

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    {bb : MirAst.BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedScalarStmt body topFrame stmt) :
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_scalar_preserves_nodup hstate hnodup hbb hstmt hwt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    {bb : MirAst.BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM1_4Stmt body topFrame stmt) :
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun _ => True)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_lm1_4_preserves_nodup_and_immediate hstate hnodup hbb hstmt hwt

example
    {body : CapturedMir} {af : StackFrame} {mach : AnnealMachine}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRel body mach af topFrame)
    (hnodup : LiveAllocsNodup mach)
    {idxLocal : MirAst.Local} {idxDecl : MirAst.LocalDecl}
    (hidx_decl : get? body.localDecls idxLocal = some idxDecl)
    (hidx_ty : idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 }) :
    ((get? af.locals idxLocal = some .dead ∨ get? af.locals idxLocal = some .uninit) →
      ∃ msg,
        annealLocalIndex topFrame mach idxLocal = .error (.machineError (.undefinedBehavior msg))) ∧
    (∀ idxSc : MirAst.ScalarInt,
      get? af.locals idxLocal = some (.init (.scalar idxSc)) →
      idxSc.bits < 2 ^ 64 ∧
      annealLocalIndex topFrame mach idxLocal = .ok (UInt64.ofNat idxSc.bits)) :=
  annealLocalIndex_usize_spec hfr hnodup hidx_decl hidx_ty

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedLM2_1Stmt body s m topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesImmediate m (fun j => arrayConstructDest? stmt ≠ some j)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m (if (arrayConstructDest? stmt).isSome then 1 else 0)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm2_1_simulation hstate hnodup hphase hbb hstmt hwt

example (pe : MirAst.ProjectionElem) :
    translateProjectionElem pe ≠ .UnwrapUnsafeBinder arraySliceMetaTyId :=
  translateProjectionElem_ne_unwrapArraySliceMeta pe

example
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {layouts : Layout.LayoutTable} {arrTy : MirAst.Ty} {elemKind : MirAst.RigidTy} {count : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (fromIdx toIdx : Nat) (fromEnd : Bool)
    (hin :
      (fromEnd = false ∧ fromIdx ≤ toIdx ∧ toIdx ≤ count) ∨
      (fromEnd = true ∧ fromIdx + toIdx ≤ count)) :
    annealProjectList (annealProjectionCx frame layouts mach)
      ⟨.indirect mp, translateTy arrTy layouts⟩ [.Subslice fromIdx toIdx fromEnd] =
      .error (.obligation "array subslice in annealProjectionCx") :=
  projectSubslice_array_unsupported frame hwf fromIdx toIdx fromEnd hin

example {mem : AnnealMemory} (hw : MemoryHighWater mem) : CanReserveAllocId mem :=
  MemoryHighWater.canReserveAllocId hw

example (m : AnnealStepState) (allocBudget : Nat)
    (r : Miri.Interpreter.StepResult AnnealStepState Bool) :
    StepPreservesHighWater m allocBudget r ↔
      (r.2 = .ok true →
        MemoryHighWater m.machine.memory →
        m.machine.memory.nextAllocId.toNat + allocBudget < 2 ^ 64 →
        MemoryHighWater r.1.machine.memory ∧
        r.1.machine.memory.nextAllocId.toNat ≤ m.machine.memory.nextAllocId.toNat + allocBudget) :=
  Iff.rfl

example (r : Miri.Interpreter.StepResult AnnealStepState Bool) :
    StepPreservesNodup r ↔ (r.2 = .ok true → LiveAllocsNodup r.1.machine) :=
  Iff.rfl

example (m : AnnealStepState) (keep : Nat → Prop)
    (r : Miri.Interpreter.StepResult AnnealStepState Bool) :
    StepPreservesImmediate m keep r ↔
      (r.2 = .ok true →
        ∀ tf tf', m.stack.frames = #[tf] → r.1.stack.frames = #[tf'] →
          ∀ j, keep j → IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) :=
  Iff.rfl

example (dst : MirAst.Local) (elemTy : MirAst.Ty) (ops : List MirAst.Operand)
    (op : MirAst.Operand) (count : Nat) (span : String) :
    arrayConstructDest? ⟨.assign ⟨dst, .nil⟩ (.aggregate (.array elemTy) ops), span⟩ = some dst ∧
      arrayConstructDest? ⟨.assign ⟨dst, .nil⟩ (.repeat op count), span⟩ = some dst :=
  ⟨rfl, rfl⟩

example {st : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {id : Miri.Interpreter.LocalsIdentity} {lay : Miri.Interpreter.LocalLayout}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hframes : st.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : (tf.locals[dstIdx]'hlt).value = .live (.indirect mp)) :
    annealEnsureAllocated ⟨.local 0 dstIdx none id, lay⟩ st = .ok mp st :=
  annealEnsureAllocated_indirect hframes hlt hind

example
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    {layouts : Layout.LayoutTable} {arrTy : MirAst.Ty} {elemKind : MirAst.RigidTy} {count : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (offset minLength : Nat) (fromEnd : Bool)
    (hmal :
      2 ^ 64 ≤ offset ∨
      2 ^ 64 ≤ minLength ∨
      (minLength ≤ count ∧
        ((fromEnd = false ∧ minLength ≤ offset) ∨
         (fromEnd = true ∧ (offset = 0 ∨ minLength < offset))))) :
    ∃ msg,
      annealProjectList (annealProjectionCx frame layouts mach)
        ⟨.indirect mp, translateTy arrTy layouts⟩ [.ConstantIndex offset minLength fromEnd] =
        .error (.invariant msg) :=
  projectConstantIndex_malformed_invariant frame hwf offset minLength fromEnd hmal

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : MirAst.Local} {arrDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat}
    {proj : MirAst.ProjectionElem} (isMove : Bool)
    (known : Option Miri.Interpreter.LocalLayout)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hproj : WellTypedArrayElemProj body s topFrame proj)
    (harr_slot :
      get? s.frame.locals arrIdx = some .dead ∨
      get? s.frame.locals arrIdx = some .uninit ∨
      ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) :
    let op := arrayElemReadOperand isMove arrIdx proj
    let elemTy : MirAst.Ty := { kind := elemKind, layoutIdx := 0 }
    (evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub ∧
      ∃ m' msg,
        (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
          annealReadImmediate) m = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc topFrame',
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
        .ok (.scalar sc) s.frame.locals ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy elemTy body.layouts⟩
          { m with stack := ⟨#[topFrame']⟩ } ∧
      StateRel body s { m with stack := ⟨#[topFrame']⟩ } ∧
      FrameRel body m.machine s.frame topFrame' ∧
      MemoryAllocDisjoint topFrame' ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      topFrame' = { topFrame with locals := topFrame'.locals } ∧
      (∀ k, k ≠ arrIdx → topFrame'.locals[k]? = topFrame.locals[k]?) ∧
      (∀ v, topFrame.locals[arrIdx]? =
          some ⟨v, some (translateTy arrDecl.ty body.layouts)⟩ →
        topFrame'.locals[arrIdx]? =
          some ⟨v, some (translateTy arrDecl.ty body.layouts)⟩) ∧
      ImmediateRel elemTy body.layouts (.scalar sc) (.scalar (.fromScalarInt msc))) :=
  annealEvalOperand_projected_array_simulation hstate hframes hnodup isMove known
    hdecl_arr hwf hproj harr_slot

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : MirAst.Local} {arrDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat}
    {proj : MirAst.ProjectionElem}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hproj : WellTypedArrayElemProj body s topFrame proj)
    (harr_slot :
      get? s.frame.locals arrIdx = some .dead ∨
      get? s.frame.locals arrIdx = some .uninit ∨
      ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems))) :
    let elemTy : MirAst.Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := translateTy elemTy body.layouts
    ((get? s.frame.locals arrIdx = some .dead ∨
        get? s.frame.locals arrIdx = some .uninit ∨
        ∃ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
          ∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [proj] v = .ub) ∧
      ∃ m' msg,
        annealEvalPlace body.localDecls body.layouts (translatePlace ⟨arrIdx, [proj]⟩) m =
          .error (.undefinedBehavior msg) m') ∨
    (∃ elems mp idx topFrame',
      idx < count ∧
      get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
      (∀ v, writeProjectedValue s.frame.locals (.aggregate 0 elems) [proj] v =
        .ok (.aggregate 0 (elems.set idx v))) ∧
      annealEvalPlace body.localDecls body.layouts (translatePlace ⟨arrIdx, [proj]⟩) m =
        .ok
          ⟨.memory
            { mp with
              ptr :=
                { mp.ptr with
                  offset :=
                    Miri.ABI.Size.ofBytes
                      (mp.ptr.offset.bytes +
                        UInt64.ofNat (idx * elemLay.layout.size.bytes.toNat)) }
              metadata := .none },
            elemLay⟩
          { m with stack := ⟨#[topFrame']⟩ } ∧
      topFrame'.locals[arrIdx]? =
        some ⟨.live (.indirect mp), some (translateTy arrDecl.ty body.layouts)⟩ ∧
      MemPlaceRel m.machine arrDecl.ty body.layouts (some (.aggregate 0 elems)) mp ∧
      FrameRel body m.machine s.frame topFrame' ∧
      MemoryAllocDisjoint topFrame' ∧
      (∀ j, IsImmediateFrameLocal topFrame j → IsImmediateFrameLocal topFrame' j) ∧
      topFrame' = { topFrame with locals := topFrame'.locals }) :=
  annealEvalPlace_projected_array_simulation hstate hframes hnodup hdecl_arr hwf hproj harr_slot

example
    {body : CapturedMir} {s : MachineState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (dstArr srcArr : MirAst.Local) (dstDecl srcDecl : MirAst.LocalDecl)
    (elemKind : MirAst.RigidTy) (dstCount srcCount : Nat)
    (dstProj srcProj : MirAst.ProjectionElem) (isMove : Bool) (span : String)
    (hdst : get? body.localDecls dstArr = some dstDecl)
    (hwf_dst : WellTypedArrayTy body.layouts dstDecl.ty elemKind dstCount)
    (hsrc : get? body.localDecls srcArr = some srcDecl)
    (hwf_src : WellTypedArrayTy body.layouts srcDecl.ty elemKind srcCount)
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hproj_dst : WellTypedArrayElemProj body s topFrame dstProj)
    (hproj_src : WellTypedArrayElemProj body s topFrame srcProj)
    (hslot_dst :
      get? s.frame.locals dstArr = some .dead ∨
      get? s.frame.locals dstArr = some .uninit ∨
      ∃ elems, get? s.frame.locals dstArr = some (.init (.aggregate 0 elems)))
    (hslot_src :
      get? s.frame.locals srcArr = some .dead ∨
      get? s.frame.locals srcArr = some .uninit ∨
      ∃ elems, get? s.frame.locals srcArr = some (.init (.aggregate 0 elems))) :
    WellTypedArrayElemAssign body s topFrame
      ⟨.assign ⟨dstArr, [dstProj]⟩ (.use (arrayElemReadOperand isMove srcArr srcProj)), span⟩ :=
  .copyElem dstArr srcArr dstDecl srcDecl elemKind dstCount srcCount dstProj srcProj isMove span
    hdst hwf_dst hsrc hwf_src hprim hproj_dst hproj_src hslot_dst hslot_src

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : MirAst.Local} {arrDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {elems : List Value}
    (isMove : Bool)
    (known : Option Miri.Interpreter.LocalLayout)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hinit_elems : get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)))
    (offset minLength : Nat) (fromEnd : Bool)
    (hmal :
      2 ^ 64 ≤ offset ∨
      2 ^ 64 ≤ minLength ∨
      (minLength ≤ count ∧
        ((fromEnd = false ∧ minLength ≤ offset) ∨
         (fromEnd = true ∧ (offset = 0 ∨ minLength < offset))))) :
    ∃ m' msg,
      annealEvalOperand body.localDecls body.layouts
        (translateOperand
          (arrayElemReadOperand isMove arrIdx (.constantIndex offset minLength fromEnd)))
        known m = .error (.invalidProgram msg) m' ∧
      Miri.Interpreter.RunLoop.reportsUB (.invalidProgram msg) = false :=
  annealEvalOperand_malformed_constantIndex_invalidProgram
    hstate hframes hnodup isMove known hdecl_arr hwf hinit_elems offset minLength fromEnd hmal

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : MirAst.Local} {arrDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {elems : List Value}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hinit_elems : get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)))
    (offset minLength : Nat) (fromEnd : Bool)
    (hmal :
      2 ^ 64 ≤ offset ∨
      2 ^ 64 ≤ minLength ∨
      (minLength ≤ count ∧
        ((fromEnd = false ∧ minLength ≤ offset) ∨
         (fromEnd = true ∧ (offset = 0 ∨ minLength < offset))))) :
    ∃ m' msg,
      annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨arrIdx, [.constantIndex offset minLength fromEnd]⟩) m =
        .error (.invalidProgram msg) m' ∧
      Miri.Interpreter.RunLoop.reportsUB (.invalidProgram msg) = false :=
  annealEvalPlace_malformed_constantIndex_invalidProgram
    hstate hframes hnodup hdecl_arr hwf hinit_elems offset minLength fromEnd hmal

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hnodup : LiveAllocsNodup m.machine)
    {bb : MirAst.BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    {arrIdx : MirAst.Local} {arrDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {elems : List Value}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hinit_elems : get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)))
    (offset minLength : Nat) (fromEnd : Bool)
    (hmal :
      2 ^ 64 ≤ offset ∨
      2 ^ 64 ≤ minLength ∨
      (minLength ≤ count ∧
        ((fromEnd = false ∧ minLength ≤ offset) ∨
         (fromEnd = true ∧ (offset = 0 ∨ minLength < offset)))))
    (hshape :
      (∃ dstIdx dstDecl isMove span,
        get? body.localDecls dstIdx = some dstDecl ∧
        stmt =
          ⟨.assign ⟨dstIdx, .nil⟩
            (.use (arrayElemReadOperand isMove arrIdx (.constantIndex offset minLength fromEnd))),
           span⟩) ∨
      (∃ srcOp span,
        stmt =
          ⟨.assign ⟨arrIdx, [.constantIndex offset minLength fromEnd]⟩ (.use srcOp), span⟩)) :
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.invalidProgram msg)) ∧
      Miri.Interpreter.RunLoop.reportsUB (.invalidProgram msg) = false :=
  step_assign_malformed_constantIndex_invalidProgram
    hstate hnodup hbb hstmt hdecl_arr hwf hinit_elems offset minLength fromEnd hmal hshape

example
    {body : CapturedMir} {s' : MachineState} {m m' : AnnealStepState}
    (fuel : Nat)
    (hstep : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true))
    (hrel : StateRel body s' m') :
    runMiriBounded body (fuel + 1) m = runMiriBounded body fuel m' :=
  runMiriBounded_step_of_stateRel fuel hstep hrel

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {retVal : Value} {mem' : Memory}
    (fuel : Nat)
    (ha : stepMirFn body s = .ret (.normal (retVal, mem')))
    (hrel : StepRel body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m)) :
    runAnnealBounded body (fuel + 1) s = .returned retVal mem' ∧
    ∃ decl0 m' retImm,
      get? body.localDecls 0 = some decl0 ∧
      ImmediateRel decl0.ty body.layouts retVal retImm ∧
      m'.stack.frames = #[] ∧
      runMiriBounded body (fuel + 1) m = .returned m' (.ok (.immediate retImm)) :=
  runBounded_of_stepRel_retRoot fuel ha hrel

/-! ### `LM-2.1` witness pins -/

example :
    ArraySliceRel (.uint .u16) 3 emptyLayoutTable Witness.lm21ArrElems
      Witness.witnessRelOffset Witness.lm21ArrAlloc ∧
    MemPlaceRel (Witness.witnessMachineOf Witness.lm21ArrAlloc) Witness.lm21U16Arr3Ty
      emptyLayoutTable (some (.aggregate 0 Witness.lm21ArrElems))
      Witness.witnessMemPlace :=
  ⟨Witness.lm21_arraySliceRel, Witness.lm21_memPlaceRel⟩

example :
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 1
            locals := [.uninit, .init (.aggregate 0 Witness.lm21ArrElems), .uninit, .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body (Witness.lm21InitAnneal 0) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) ()
          (Witness.lm21InitMiri 0) = (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_aggregate_array_steps

example :
    let repElems : List Value := [.scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩]
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 2
            locals := [.uninit, .init (.aggregate 0 repElems), .uninit, .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body (Witness.lm21InitAnneal 1) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) ()
          (Witness.lm21InitMiri 1) = (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_repeat_array_steps

example :
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 3
            locals := [.uninit, .uninit, .uninit, .init (.aggregate 0 [])] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body (Witness.lm21InitAnneal 2) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) ()
          (Witness.lm21InitMiri 2) = (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_repeat_zero_steps

example :
    let s' := Witness.lm21ArrAnneal 4 (.init (.scalar ⟨3, 8⟩))
    stepMirFn Witness.lm21Body (Witness.lm21ArrAnneal 3 .uninit) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) ()
          (Witness.lm21ArrMiri 3 .uninit) = (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_len_array_steps

example :
    stepMirFn Witness.lm21Body (Witness.lm21InitAnneal 3) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) ()
          (Witness.lm21InitMiri 3) = (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_len_uninit_ub

example :
    ∃ elemVal sc msc,
      get? Witness.lm21ArrElems 1 = some elemVal ∧
      elemVal = .scalar ⟨0x0304, 2⟩ ∧
      sc = ⟨0x0304, 2⟩ ∧
      annealProjectList
        (annealProjectionCx
          (Witness.lm21ArrMiriFrame 4 (.scalar (.fromScalarInt Witness.lm21Usize1)))
          Witness.lm21Body.layouts
          (Witness.witnessMachineOf Witness.lm21ArrAlloc))
        ⟨.indirect Witness.witnessMemPlace,
          translateTy Witness.lm21U16Arr3Ty Witness.lm21Body.layouts⟩
        [.Index 2] =
        .ok ⟨.indirect
              { Witness.witnessMemPlace with
                ptr := { Witness.witnessMemPlace.ptr with offset := Miri.ABI.Size.ofBytes 0x1006 }
                metadata := .none },
            translateTy Witness.lm21U16Ty Witness.lm21Body.layouts⟩ ∧
      ImmediateRel Witness.lm21U16Ty Witness.lm21Body.layouts (.scalar sc)
        (.scalar (.fromScalarInt msc)) :=
  Witness.lm21_evalProjection_index_witness

example :
    ∃ msc,
      annealProjectList
        (annealProjectionCx (Witness.lm21ArrMiriFrame 7 .uninit) Witness.lm21Body.layouts
          (Witness.witnessMachineOf Witness.lm21ArrAlloc))
        ⟨.indirect Witness.witnessMemPlace,
          translateTy Witness.lm21U16Arr3Ty Witness.lm21Body.layouts⟩
        [.ConstantIndex 2 3 true] =
        .ok ⟨.indirect
              { Witness.witnessMemPlace with
                ptr := { Witness.witnessMemPlace.ptr with offset := Miri.ABI.Size.ofBytes 0x1006 }
                metadata := .none },
            translateTy Witness.lm21U16Ty Witness.lm21Body.layouts⟩ ∧
      ImmediateRel Witness.lm21U16Ty Witness.lm21Body.layouts (.scalar ⟨0x0304, 2⟩)
        (.scalar (.fromScalarInt msc)) :=
  Witness.lm21_evalProjection_constantIndex_witness

example :
    let s₀ := Witness.lm21ArrAnneal 4 (.init (.scalar ⟨1, 8⟩))
    let m₀ := Witness.lm21ArrMiri 4 (.scalar (.fromScalarInt Witness.lm21Usize1))
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 5
            locals :=
              [.init (.scalar ⟨0x0304, 2⟩), .init (.aggregate 0 Witness.lm21ArrElems),
               .init (.scalar ⟨1, 8⟩), .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_index_read_steps

example :
    let s₀ := Witness.lm21ArrAnneal 5 (.init (.scalar ⟨1, 8⟩))
    let m₀ := Witness.lm21ArrMiri 5 (.scalar (.fromScalarInt Witness.lm21Usize1))
    let updatedElems : List Value :=
      [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x090A, 2⟩, .scalar ⟨0x0506, 2⟩]
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 6
            locals :=
              [.uninit, .init (.aggregate 0 updatedElems),
               .init (.scalar ⟨1, 8⟩), .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_index_write_steps

example :
    let s₀ := Witness.lm21ArrAnneal 6 .uninit
    let m₀ := Witness.lm21ArrMiri 6 .uninit
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 7
            locals :=
              [.init (.scalar ⟨0x0506, 2⟩), .init (.aggregate 0 Witness.lm21ArrElems),
               .uninit, .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_constantIndex_fromStart_steps

example :
    let s₀ := Witness.lm21ArrAnneal 7 .uninit
    let m₀ := Witness.lm21ArrMiri 7 .uninit
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 8
            locals :=
              [.init (.scalar ⟨0x0304, 2⟩), .init (.aggregate 0 Witness.lm21ArrElems),
               .uninit, .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_constantIndex_fromEnd_read_steps

example :
    let s₀ := Witness.lm21ArrAnneal 8 .uninit
    let m₀ := Witness.lm21ArrMiri 8 .uninit
    let updatedElems : List Value :=
      [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩, .scalar ⟨0x0B0C, 2⟩]
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 9
            locals := [.uninit, .init (.aggregate 0 updatedElems), .uninit, .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_constantIndex_fromEnd_write_steps

example :
    let s₀ := Witness.lm21ArrAnneal 4 (.init (.scalar ⟨3, 8⟩))
    let m₀ := Witness.lm21ArrMiri 4 (.scalar (.fromScalarInt Witness.lm21Usize3))
    stepMirFn Witness.lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_index_oob_ub

example :
    let s₀ := Witness.lm21ArrAnneal 5 (.init (.scalar ⟨3, 8⟩))
    let m₀ := Witness.lm21ArrMiri 5 (.scalar (.fromScalarInt Witness.lm21Usize3))
    stepMirFn Witness.lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_index_write_oob_ub

example :
    let s₀ := Witness.lm21ArrAnneal 4 .uninit
    let m₀ := Witness.lm21ArrMiri 4 .uninit
    stepMirFn Witness.lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_index_uninit_ub

example :
    let s₀ := Witness.lm21ArrAnneal 9 .uninit
    let m₀ := Witness.lm21ArrMiri 9 .uninit
    stepMirFn Witness.lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_constantIndex_oob_ub

example :
    let hooks := annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts
    let elems₂ : List Value := [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩, .scalar ⟨0x0B0C, 2⟩]
    let elems₃ : List Value := [.scalar ⟨0x0D0E, 2⟩, .scalar ⟨0x0304, 2⟩, .scalar ⟨0x0B0C, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState Witness.lm21Body []).memory }
    let s₁ := mkState 11 [.uninit, .init (.aggregate 0 Witness.lm21ArrElems), .uninit, .uninit]
    let s₂ := mkState 12 [.uninit, .init (.aggregate 0 elems₂), .uninit, .uninit]
    let s₃ := mkState 13 [.uninit, .init (.aggregate 0 elems₃), .uninit, .uninit]
    let s₄ := mkState 14 [.init (.scalar ⟨0x0B0C, 2⟩), .init (.aggregate 0 elems₃), .uninit, .uninit]
    let s₅ := mkState 15
      [.init (.scalar ⟨0x0B0C, 2⟩), .init (.aggregate 0 elems₃), .init (.scalar ⟨3, 8⟩), .uninit]
    stepMirFn Witness.lm21Body (Witness.lm21InitAnneal 10) = .step s₁ ∧
      stepMirFn Witness.lm21Body s₁ = .step s₂ ∧
      stepMirFn Witness.lm21Body s₂ = .step s₃ ∧
      stepMirFn Witness.lm21Body s₃ = .step s₄ ∧
      stepMirFn Witness.lm21Body s₄ = .step s₅ ∧
      ∃ m₁ m₂ m₃ m₄ m₅,
        Miri.Interpreter.Step.step hooks () (Witness.lm21InitMiri 10) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        StateRel Witness.lm21Body s₅ m₅ ∧
        LiveAllocsNodup m₅.machine :=
  Witness.lm21_chain_steps

example :
    annealReadImmediate
      ⟨.indirect Witness.witnessMemPlace,
        translateTy Witness.lm21U16Arr3Ty Witness.lm21Body.layouts⟩
      (Witness.lm21ArrMiri 3 .uninit) =
      .error (.unsupported "whole-array immediate read not supported")
        (Witness.lm21ArrMiri 3 .uninit) :=
  Witness.lm21_whole_array_read_unsupported

example :
    (annealProjectList
      (annealProjectionCx (Witness.lm21ArrMiriFrame 3 .uninit) Witness.lm21Body.layouts
        (Witness.witnessMachineOf Witness.lm21ArrAlloc))
      ⟨.indirect Witness.witnessMemPlace,
        translateTy Witness.lm21U16Arr3Ty Witness.lm21Body.layouts⟩
      [.Subslice 1 3 false]).mapError annealLiftProjectionError =
      .error (.unsupported "array subslice in annealProjectionCx") :=
  Witness.lm21_partial_subslice_unsupported

example :
    (∀ v, writeProjectedValue (Witness.lm21ArrAnneal 3 .uninit).frame.locals
      (.aggregate 0 Witness.lm21ArrElems) [.subslice 0 3 false] v = .unsupported) ∧
    (∀ v, writeProjectedValue (Witness.lm21ArrAnneal 3 .uninit).frame.locals
      (.aggregate 0 Witness.lm21ArrElems) [.subslice 0 0 true] v = .unsupported) ∧
    (annealProjectList
      (annealProjectionCx (Witness.lm21ArrMiriFrame 3 .uninit) Witness.lm21Body.layouts
        (Witness.witnessMachineOf Witness.lm21ArrAlloc))
      ⟨.indirect Witness.witnessMemPlace,
        translateTy Witness.lm21U16Arr3Ty Witness.lm21Body.layouts⟩
      [.Subslice 0 3 false]).mapError annealLiftProjectionError =
      .error (.unsupported "array subslice in annealProjectionCx") ∧
    (annealProjectList
      (annealProjectionCx (Witness.lm21ArrMiriFrame 3 .uninit) Witness.lm21Body.layouts
        (Witness.witnessMachineOf Witness.lm21ArrAlloc))
      ⟨.indirect Witness.witnessMemPlace,
        translateTy Witness.lm21U16Arr3Ty Witness.lm21Body.layouts⟩
      [.Subslice 0 0 true]).mapError annealLiftProjectionError =
      .error (.unsupported "array subslice in annealProjectionCx") :=
  Witness.lm21_whole_subslice_unsupported

example :
    let s₀ := Witness.lm21ArrAnneal 4 (.init (.scalar ⟨1, 8⟩))
    let m₀ := Witness.lm21IndIdxMiri 4 Witness.lm21IdxInitAlloc1
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 5
            locals :=
              [.init (.scalar ⟨0x0304, 2⟩), .init (.aggregate 0 Witness.lm21ArrElems),
               .init (.scalar ⟨1, 8⟩), .uninit] }
        memory := (initMachineState Witness.lm21Body []).memory }
    stepMirFn Witness.lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel Witness.lm21Body s' m' :=
  Witness.lm21_indirect_index_read_steps

example :
    let s₀ := Witness.lm21ArrAnneal 4 .uninit
    let m₀ := Witness.lm21IndIdxMiri 4 Witness.lm21IdxUninitAlloc
    stepMirFn Witness.lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21Body.localDecls Witness.lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_indirect_index_uninit_ub

example :
    let hooks := annealStepHooks Witness.lm21MixedBody.localDecls Witness.lm21MixedBody.layouts
    let repElems : List Value := [.scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩]
    let newElems : List Value := [.scalar ⟨0x090A, 2⟩, .scalar ⟨0x0B0C, 2⟩, .scalar ⟨0x0D0E, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState Witness.lm21MixedBody []).memory }
    let s₁ := mkState 1 [.uninit, .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .init (.aggregate 0 Witness.lm21ArrElems), .uninit]
    let s₃ := mkState 3 [.uninit, .init (.aggregate 0 repElems), .uninit]
    let s₄ := mkState 4 [.uninit, .init (.aggregate 0 newElems), .uninit]
    let s₅ := mkState 5 [.uninit, .init (.aggregate 0 newElems), .init (.scalar ⟨2, 8⟩)]
    let s₆ := mkState 6
      [.init (.scalar ⟨0x0D0E, 2⟩), .init (.aggregate 0 newElems), .init (.scalar ⟨2, 8⟩)]
    let s₇ := mkState 7 [.init (.scalar ⟨0x0D0E, 2⟩), .dead, .init (.scalar ⟨2, 8⟩)]
    stepMirFn Witness.lm21MixedBody Witness.lm21MixedInitAnneal = .step s₁ ∧
      stepMirFn Witness.lm21MixedBody s₁ = .step s₂ ∧
      stepMirFn Witness.lm21MixedBody s₂ = .step s₃ ∧
      stepMirFn Witness.lm21MixedBody s₃ = .step s₄ ∧
      stepMirFn Witness.lm21MixedBody s₄ = .step s₅ ∧
      stepMirFn Witness.lm21MixedBody s₅ = .step s₆ ∧
      stepMirFn Witness.lm21MixedBody s₆ = .step s₇ ∧
      ∃ m₁ m₂ m₃ m₄ m₅ m₆ m₇,
        Miri.Interpreter.Step.step hooks () Witness.lm21MixedInitMiri = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok true) ∧
        StateRel Witness.lm21MixedBody s₇ m₇ ∧
        LiveAllocsNodup m₇.machine :=
  Witness.lm21_mixed_reassign_chain_steps

example :
    let hooks :=
      annealStepHooks Witness.lm21MultiMoveBody.localDecls Witness.lm21MultiMoveBody.layouts
    let arr1_init : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x7788, 2⟩]
    let arr2_init : List Value := [.scalar ⟨0x3344, 2⟩, .scalar ⟨0x3344, 2⟩]
    let arr1_upd  : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x5566, 2⟩, .scalar ⟨0x7788, 2⟩]
    let arr1_real : List Value := [.scalar ⟨0x3344, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x3344, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState Witness.lm21MultiMoveBody []).memory }
    let s₁ := mkState 1 [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .init (.scalar ⟨0x3344, 2⟩), .uninit]
    let s₃ := mkState 3 [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .init (.scalar ⟨0x3344, 2⟩), .init (.scalar ⟨0x5566, 2⟩)]
    let s₄ := mkState 4 [.uninit, .uninit, .uninit, .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨0x1122, 2⟩), .init (.scalar ⟨0x3344, 2⟩), .init (.scalar ⟨0x5566, 2⟩)]
    let s₅ := mkState 5 [.uninit, .init (.aggregate 0 arr1_init), .uninit, .init (.scalar ⟨1, 8⟩), .uninit, .init (.scalar ⟨0x3344, 2⟩), .init (.scalar ⟨0x5566, 2⟩)]
    let s₆ := mkState 6 [.uninit, .init (.aggregate 0 arr1_init), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .init (.scalar ⟨0x5566, 2⟩)]
    let s₇ := mkState 7 [.uninit, .init (.aggregate 0 arr1_upd), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₈ := mkState 8 [.uninit, .dead, .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₉ := mkState 9 [.uninit, .uninit, .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₁₀ := mkState 10 [.init (.scalar ⟨0x3344, 2⟩), .uninit, .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₁₁ := mkState 11 [.uninit, .init (.aggregate 0 arr1_real), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₁₂ := mkState 12 [.init (.scalar ⟨0x3344, 2⟩), .init (.aggregate 0 arr1_real), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    stepMirFn Witness.lm21MultiMoveBody (Witness.lm21MultiInitAnneal 0) = .step s₁ ∧
      stepMirFn Witness.lm21MultiMoveBody s₁ = .step s₂ ∧
      stepMirFn Witness.lm21MultiMoveBody s₂ = .step s₃ ∧
      stepMirFn Witness.lm21MultiMoveBody s₃ = .step s₄ ∧
      stepMirFn Witness.lm21MultiMoveBody s₄ = .step s₅ ∧
      stepMirFn Witness.lm21MultiMoveBody s₅ = .step s₆ ∧
      stepMirFn Witness.lm21MultiMoveBody s₆ = .step s₇ ∧
      stepMirFn Witness.lm21MultiMoveBody s₇ = .step s₈ ∧
      stepMirFn Witness.lm21MultiMoveBody s₈ = .step s₉ ∧
      stepMirFn Witness.lm21MultiMoveBody s₉ = .step s₁₀ ∧
      stepMirFn Witness.lm21MultiMoveBody s₁₀ = .step s₁₁ ∧
      stepMirFn Witness.lm21MultiMoveBody s₁₁ = .step s₁₂ ∧
      ∃ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂,
        Miri.Interpreter.Step.step hooks () (Witness.lm21MultiInitMiri 0) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₇ = (m₈, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₈ = (m₉, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₉ = (m₁₀, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁₀ = (m₁₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁₁ = (m₁₂, .ok true) ∧
        StateRel Witness.lm21MultiMoveBody s₁₂ m₁₂ ∧
        LiveAllocsNodup m₁₂.machine ∧
        MemoryHighWater m₁₂.machine.memory ∧
        m₁₂.machine.memory.nextAllocId.toNat ≤ 4 :=
  Witness.lm21_multi_alloc_move_chain_steps

example :
    let hooks :=
      annealStepHooks Witness.lm21MultiMoveBody.localDecls Witness.lm21MultiMoveBody.layouts
    let s₁ : MachineState :=
      { frame :=
          { blockIdx := 1
            stmtIdx := 1
            locals := [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .uninit, .uninit] }
        memory := (initMachineState Witness.lm21MultiMoveBody []).memory }
    stepMirFn Witness.lm21MultiMoveBody (Witness.lm21MultiInitAnneal 1) = .step s₁ ∧
      stepMirFn Witness.lm21MultiMoveBody s₁ = .fail .ub ∧
      ∃ m₁ m₂ msg,
        Miri.Interpreter.Step.step hooks () (Witness.lm21MultiInitMiri 1) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg)) :=
  Witness.lm21_aggregate_move_then_copy_ub

example :
    let hooks :=
      annealStepHooks Witness.lm21CopyZeroBody.localDecls Witness.lm21CopyZeroBody.layouts
    let arr1_0 : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x5566, 2⟩]
    let arr2_0 : List Value := [.scalar ⟨0x7788, 2⟩, .scalar ⟨0x7788, 2⟩]
    let arr1_1 : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x1122, 2⟩]
    let arr2_1 : List Value := [.scalar ⟨0x7788, 2⟩, .scalar ⟨0x1122, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState Witness.lm21CopyZeroBody []).memory }
    let s₁ := mkState 1 [.uninit, .init (.aggregate 0 arr1_0), .uninit, .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .init (.aggregate 0 arr1_0), .init (.aggregate 0 arr2_0), .uninit, .uninit]
    let s₃ := mkState 3 [.uninit, .init (.aggregate 0 arr1_0), .init (.aggregate 0 arr2_0), .init (.scalar ⟨1, 8⟩), .uninit]
    let s₄ := mkState 4 [.uninit, .init (.aggregate 0 arr1_1), .init (.aggregate 0 arr2_0), .init (.scalar ⟨1, 8⟩), .uninit]
    let s₅ := mkState 5 [.uninit, .init (.aggregate 0 arr1_1), .init (.aggregate 0 arr2_1), .init (.scalar ⟨1, 8⟩), .uninit]
    let s₆ := mkState 6 [.init (.scalar ⟨0x1122, 2⟩), .init (.aggregate 0 arr1_1), .init (.aggregate 0 arr2_1), .init (.scalar ⟨1, 8⟩), .uninit]
    stepMirFn Witness.lm21CopyZeroBody (Witness.lm21CopyZeroInitAnneal 0) = .step s₁ ∧
      stepMirFn Witness.lm21CopyZeroBody s₁ = .step s₂ ∧
      stepMirFn Witness.lm21CopyZeroBody s₂ = .step s₃ ∧
      stepMirFn Witness.lm21CopyZeroBody s₃ = .step s₄ ∧
      stepMirFn Witness.lm21CopyZeroBody s₄ = .step s₅ ∧
      stepMirFn Witness.lm21CopyZeroBody s₅ = .step s₆ ∧
      ∃ m₁ m₂ m₃ m₄ m₅ m₆,
        Miri.Interpreter.Step.step hooks () (Witness.lm21CopyZeroInitMiri 0) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
        StateRel Witness.lm21CopyZeroBody s₆ m₆ ∧
        LiveAllocsNodup m₆.machine ∧
        MemoryHighWater m₆.machine.memory :=
  Witness.lm21_intra_and_inter_array_copyElem_steps

example :
    let hooks :=
      annealStepHooks Witness.lm21CopyZeroBody.localDecls Witness.lm21CopyZeroBody.layouts
    let arr1_0 : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x5566, 2⟩]
    let arr2_0 : List Value := [.scalar ⟨0x7788, 2⟩, .scalar ⟨0x7788, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := k, locals := locals }
        memory := (initMachineState Witness.lm21CopyZeroBody []).memory }
    let s₁ := mkState 1 [.uninit, .init (.aggregate 0 arr1_0), .uninit, .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .init (.aggregate 0 arr1_0), .init (.aggregate 0 arr2_0), .uninit, .uninit]
    stepMirFn Witness.lm21CopyZeroBody (Witness.lm21CopyZeroInitAnneal 1) = .step s₁ ∧
      stepMirFn Witness.lm21CopyZeroBody s₁ = .step s₂ ∧
      stepMirFn Witness.lm21CopyZeroBody s₂ = .fail .ub ∧
      ∃ m₁ m₂ m₃ msg,
        Miri.Interpreter.Step.step hooks () (Witness.lm21CopyZeroInitMiri 1) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg)) :=
  Witness.lm21_copyElem_src_oob_ub

example :
    annealCheckIndirectInitialized (Witness.witnessMachineOf Witness.lm21ZeroArrAlloc)
        Witness.lm21ZeroArrMemPlace
        (translateTy Witness.lm21U16Arr0Ty emptyLayoutTable).layout.size = .ok () ∧
      stepMirFn Witness.lm21CopyZeroBody (Witness.lm21ZeroArrAnneal 0) = .fail .ub ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21CopyZeroBody.localDecls Witness.lm21CopyZeroBody.layouts) ()
          (Witness.lm21ZeroArrMiri 0) = (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_uninit_indirect_zero_array_read_ub

example :
    annealCheckIndirectInitialized (Witness.witnessMachineOf Witness.lm21ZeroArrAlloc)
        Witness.lm21ZeroArrMemPlace
        (translateTy Witness.lm21U16Arr0Ty emptyLayoutTable).layout.size = .ok () ∧
      stepMirFn Witness.lm21CopyZeroBody (Witness.lm21ZeroArrAnneal 1) = .fail .ub ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm21CopyZeroBody.localDecls Witness.lm21CopyZeroBody.layouts) ()
          (Witness.lm21ZeroArrMiri 1) = (m', .error (.undefinedBehavior msg)) :=
  Witness.lm21_uninit_indirect_zero_array_write_ub

example :
    let cx := annealProjectionCx (Witness.lm21ArrMiriFrame 7 .uninit) Witness.lm21Body.layouts
      (Witness.witnessMachineOf Witness.lm21ArrAlloc)
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect Witness.witnessMemPlace, translateTy Witness.lm21U16Arr3Ty Witness.lm21Body.layouts⟩
    (∃ msg, annealProjectList cx base [.ConstantIndex (2 ^ 64) 3 false] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 0 (2 ^ 64) false] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 3 3 false] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 0 3 true] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 4 3 true] =
      .error (.invariant msg)) :=
  Witness.lm21_malformed_constantIndex_invariant

example :
    let hooks :=
      annealStepHooks Witness.lm21MalformedConstBody.localDecls
        Witness.lm21MalformedConstBody.layouts
    (∃ m' msg,
      Miri.Interpreter.Step.step hooks () (Witness.lm21MalArrMiri 0) =
        (m', .error (.invalidProgram msg)) ∧
      runMiriBounded Witness.lm21MalformedConstBody 1 (Witness.lm21MalArrMiri 0) =
        .error m' (.invalidProgram msg) ∧
      Miri.Interpreter.RunLoop.reportsUB (.invalidProgram msg) = false) ∧
    (∃ m' msg,
      Miri.Interpreter.Step.step hooks () (Witness.lm21MalArrMiri 1) =
        (m', .error (.invalidProgram msg)) ∧
      runMiriBounded Witness.lm21MalformedConstBody 1 (Witness.lm21MalArrMiri 1) =
        .error m' (.invalidProgram msg) ∧
      Miri.Interpreter.RunLoop.reportsUB (.invalidProgram msg) = false) :=
  Witness.lm21_malformed_constantIndex_step_invalidProgram

example :
    WellTypedArrayTy emptyLayoutTable Witness.lm21I32Arr3Ty (.int .i32) 3 ∧
    WellTypedArrayTy emptyLayoutTable Witness.lm21BoolArr2Ty .bool 2 ∧
    WellTypedArrayTy emptyLayoutTable Witness.lm21CharArr2Ty .char 2 :=
  ⟨Witness.lm21_wf_i32Arr3, Witness.lm21_wf_boolArr2, Witness.lm21_wf_charArr2⟩

example :
    ∃ mem' m',
      m'.stack.frames = #[] ∧
      runAnnealBounded Witness.lm21FullFnBody 21
        (initMachineState Witness.lm21FullFnBody []) =
        .returned (.scalar ⟨22, 4⟩) mem' ∧
      runMiriBounded Witness.lm21FullFnBody 21 Witness.lm21FullFnInitMiri =
        .returned m'
          (.ok (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 22))))) ∧
      ImmediateRel Witness.lm21I32Ty emptyLayoutTable (.scalar ⟨22, 4⟩)
        (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 22))) :=
  Witness.lm21_signed_bool_char_runBounded_return

/-! ### `LM-3.1` statement and witness pins -/

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) : StateRelLM3_1 body s m [] :=
  StateRel.toLM3_1 h

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRelLM3_1 body s m []) : StateRel body s m :=
  StateRelLM3_1.toStateRel h

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr mutability pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    StepRelLM3_1 body m
      [rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩]
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_addrOf_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne
    himm hsupply

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hmap : AllocMapRel body s m allocMap)
    (ptrLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (pointeeTy : Ty)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hsz8 : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8)
    (halign8 : (translateTy pointeeTy body.layouts).layout.align.abi = Miri.ABI.Align.EIGHT) :
    (∀ (e : AllocMapEntry) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind),
      e ∈ allocMap →
      e.tag = ptrVal.tag →
      e.perm ≠ .disabled →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ →
      get? s.frame.locals e.localIdx = some (.init (.scalar sc)) →
      m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
        some (e.allocId, localAlloc) →
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8 →
      localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) false =
        .ok (.fromScalarInt msc) →
      evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
        .ok (.scalar sc) s.frame.locals ∧
      evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .ok (.fromScalarInt msc)) ∧
    (∀ (e : AllocMapEntry) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
       (oldSlot : LocalSlot) (locals' : List LocalSlot)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind)
       (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      e ∈ allocMap →
      e.tag = ptrVal.tag →
      e.perm = .active →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ →
      get? s.frame.locals e.localIdx = some oldSlot →
      oldSlot ≠ .dead →
      set? s.frame.locals e.localIdx (.init (.scalar sc)) = some locals' →
      m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
        some (e.allocId, localAlloc) →
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8 →
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
        (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' →
      writePlaceValue s.frame.locals s.memory.borrows ⟨ptrLoc, .cons .deref .nil⟩ (.scalar sc) =
        .ok locals' ∧
      evalDerefWriteScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi
        (.fromScalarInt msc) = .ok alloc') ∧
    (∀ (entry : BorrowEntry) (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag),
      lookupBorrow s.memory.borrows ptrVal.tag = some entry →
      entry.perm ≠ .disabled →
      get? s.frame.locals entry.targetLocal = some .dead →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete allocId borTag⟩ →
      allocId.value.toNat < 2 ^ 32 →
      ptrVal.offsetBytes < 2 ^ 32 →
      m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = none →
      evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub ∧
      ∃ msg, evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .error (.undefinedBehavior msg)) ∧
    (∀ (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind),
      lookupBorrow s.memory.borrows ptrVal.tag = none →
      lookupGlobalAlloc s.memory.globals ptrVal.allocId = none →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete allocId borTag⟩ →
      allocId.value.toNat < 2 ^ 32 →
      ptrVal.offsetBytes < 2 ^ 32 →
      m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc) →
      localAlloc.allocation.byteSize.bytes.toNat < ptrVal.offsetBytes + 8 →
      evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub ∧
      ∃ msg, evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .error (.undefinedBehavior msg)) ∧
    (∀ (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind),
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete allocId borTag⟩ →
      allocId.value.toNat < 2 ^ 32 →
      ptrVal.offsetBytes < 2 ^ 32 →
      m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc) →
      ptrVal.offsetBytes + 8 ≤ localAlloc.allocation.byteSize.bytes.toNat →
      ptrVal.offsetBytes % 8 ≠ 0 →
      ∃ msg, evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .error (.undefinedBehavior msg)) :=
  evalProjection_deref_simulation hmap ptrLoc ptrVal mptr pointeeTy hptr_slot hsz8 halign8

example {s : MachineState} {mach : AnnealMachine}
    {allocMap : List AllocMapEntry}
    (ptrLoc offLoc : Local)
    (ptrVal : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv)
    (deltaBytes : Nat) (offsetSc : MirAst.ScalarInt)
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hptr_rel : PtrRel allocMap ptrVal mptr)
    (hprov : mptr.provenance = .concrete allocId borTag)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hoff_in : ptrVal.offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat)
    (hdelta : deltaBytes < 2 ^ 32)
    (hsc_bits : offsetSc.bits = deltaBytes)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hoff_slot : get? s.frame.locals offLoc = some (.init (.scalar offsetSc))) :
    ((∃ ptr',
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr.offset, some mptr.provenance⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) = .ok ptr') ↔
      ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) ∧
    (ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat →
      ptrVal.offsetBytes + deltaBytes < 2 ^ 32 →
      let mptr' : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes
          (annealStackBaseAddr allocId + UInt64.ofNat (ptrVal.offsetBytes + deltaBytes)),
          .concrete allocId borTag⟩
      evalRvalue s.frame.locals
        (.binaryOp .offset (.copy ⟨ptrLoc, .nil⟩) (.copy ⟨offLoc, .nil⟩))
        s.memory [] emptyLayoutTable =
        .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + deltaBytes } 8)
          s.frame.locals s.memory ∧
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr.offset, some mptr.provenance⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .ok ⟨mptr'.offset, some mptr'.provenance⟩ ∧
      PtrRel allocMap
        { ptrVal with offsetBytes := ptrVal.offsetBytes + deltaBytes }
        mptr') ∧
    (localAlloc.allocation.byteSize.bytes.toNat < ptrVal.offsetBytes + deltaBytes →
      0 < deltaBytes →
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr.offset, some mptr.provenance⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .error (.access (.pointerOutOfBounds allocId localAlloc.allocation.byteSize
          (Int.ofNat ptrVal.offsetBytes) (Int.ofNat deltaBytes) .inboundsPointerArithmetic)) ∧
      (⟨mptr.offset, some mptr.provenance⟩ : Miri.Memory.Pointer (Option AnnealProv)).wrappingSignedOffset
        (Int64.ofInt (deltaBytes : Int)) annealPointerArithmetic =
        .ok ⟨Miri.ABI.Size.ofBytes
          ((annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes) + UInt64.ofNat deltaBytes),
          some (Miri.Memory.Provenance.concrete allocId borTag)⟩) :=
  evalBinOp_offset_inbounds_simulation ptrLoc offLoc ptrVal mptr deltaBytes offsetSc
    allocId borTag localAlloc hptr_rel hprov hbase hlive hoff_in hdelta hsc_bits hptr_slot hoff_slot

example {allocMap : List AllocMapEntry}
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable)
    (m : AnnealStepState)
    (srcLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (srcMut dstMut : Mutability) (srcPointee dstPointee : RigidTy)
    (srcTy dstTy : Ty)
    (hsrcTy : srcTy.kind = .rawPtr srcMut srcPointee)
    (hdstTy : dstTy.kind = .rawPtr dstMut dstPointee)
    (hsrc_slot : get? locals srcLoc = some (.init (.ptr ptrVal 8)))
    (hptr_rel : PtrRel allocMap ptrVal mptr) :
    evalRvalue locals (.cast .ptrToPtr (.copy ⟨srcLoc, .nil⟩) dstTy) mem localDecls layouts =
      .ok (.ptr ptrVal 8) locals mem ∧
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooksLM3_1 layouts)
      ()
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy srcTy layouts⟩
      (translateTy dstTy layouts)
      m =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy dstTy layouts⟩ m ∧
    ImmediateRelLM3_1 allocMap dstTy layouts
      (.ptr ptrVal 8)
      (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) :=
  evalCast_ptrToPtr_simulation locals mem localDecls layouts m srcLoc ptrVal mptr
    srcMut dstMut srcPointee dstPointee srcTy dstTy hsrcTy hdstTy hsrc_slot hptr_rel

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_1Stmt body m stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    ∃ allocMap : List AllocMapEntry,
      StepRelLM3_1 body m allocMap
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm3_1_simulation hstate hphase hbb hstmt hwt hsupply

example :
    ∃ (s' : MachineState) (m' : AnnealStepState),
      stepMirFn Witness.lm31AddrOfBody Witness.lm31AddrOfAnnealPre = .step s' ∧
      Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm31AddrOfBody.localDecls Witness.lm31AddrOfBody.layouts) ()
          Witness.lm31AddrOfMiriPre = (m', .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s' m'
        [rawPtrAllocMapEntry Witness.lm31AddrOfBody.localDecls Witness.lm31AddrOfBody.layouts
          .mut 1 1 Witness.lm31AllocId1] :=
  Witness.wit_lm3_1_rawPtr_step

example :
    Witness.annealOutcomeScalarBits 8
      (runAnnealBounded Witness.lm31AddrOfBody 9 (initMachineState Witness.lm31AddrOfBody [])) = some 99 ∧
    (∃ (s' : MachineState) (m' : AnnealStepState),
      stepMirFn Witness.lm31AddrOfBody Witness.lm31AddrOfAnnealPre = .step s' ∧
      Miri.Interpreter.Step.step
          (annealStepHooks Witness.lm31AddrOfBody.localDecls Witness.lm31AddrOfBody.layouts) ()
          Witness.lm31AddrOfMiriPre = (m', .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s' m'
        [rawPtrAllocMapEntry Witness.lm31AddrOfBody.localDecls Witness.lm31AddrOfBody.layouts
          .mut 1 1 Witness.lm31AllocId1]) ∧
    (∃ (alloc42 alloc99 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      let mptr : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1),
          .concrete Witness.lm31AllocId1 Miri.Memory.BorTag.one⟩
      evalDerefWriteScalarMiri (Witness.mkSingleAllocMachine Witness.lm31AllocId1 alloc42) mptr
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT
        (.fromScalarInt Witness.lm31Scalar99) = .ok alloc99 ∧
      evalDerefReadScalarMiri (Witness.mkSingleAllocMachine Witness.lm31AllocId1 alloc99) mptr
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT =
        .ok (.fromScalarInt Witness.lm31Scalar99)) :=
  Witness.wit_lm3_1_addrOf_write_read_deref

example :
    ∃ (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      let mach : AnnealMachine := Witness.mkSingleAllocMachine Witness.lm31AllocId1 alloc
      let mptr0 : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + UInt64.ofNat 0),
          .concrete Witness.lm31AllocId1 Miri.Memory.BorTag.one⟩
      let mptr8 : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + UInt64.ofNat 8),
          .concrete Witness.lm31AllocId1 Miri.Memory.BorTag.one⟩
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr0.offset, some mptr0.provenance⟩
        8
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .ok ⟨mptr8.offset, some mptr8.provenance⟩ ∧
      (∃ err, Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr0.offset, some mptr0.provenance⟩
        9
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .error err) ∧
      (∃ msg, evalDerefReadScalarMiri mach mptr8
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT =
        .error (.undefinedBehavior msg)) :=
  Witness.wit_lm3_1_binOp_offset_inbounds_and_oob

example :
    Witness.annealOutcomeIsUB
      (runAnnealBounded Witness.lm31DanglingBody 6 (initMachineState Witness.lm31DanglingBody [])) = true ∧
    (let sDead : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 5
            locals := [.uninit, .dead, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
        memory :=
          { (initMachineState Witness.lm31DanglingBody []).memory with
            borrows :=
              [{ tag := 1
                 targetLocal := 1
                 targetProjection := .nil
                 perm := .frozen }]
            nextTag := 2 } }
     let mDead : AnnealStepState :=
      { stack := ⟨#[Witness.lm31AddrOfMiriFramePre]⟩
        machine :=
          { memory := Miri.Memory.MemoryState.empty
            addresses := { AnnealMachine.empty.addresses with
              baseAddr := #[⟨Witness.lm31AllocId1, annealStackBaseAddr Witness.lm31AllocId1⟩] } } }
     let mptr : Miri.Memory.Pointer AnnealProv :=
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + UInt64.ofNat 0),
        .concrete Witness.lm31AllocId1 Miri.Memory.BorTag.one⟩
     evalOperand sDead.frame.locals (.copy ⟨2, .cons .deref .nil⟩)
       sDead.memory.borrows sDead.memory.globals Witness.lm31DanglingBody.layouts
       sDead.memory.callerLocals = .ub ∧
     ∃ msg, evalDerefReadScalarMiri mDead.machine mptr
       (translateTy Witness.u64Ty Witness.lm31DanglingBody.layouts).layout.size
       (translateTy Witness.u64Ty Witness.lm31DanglingBody.layouts).layout.align.abi =
       .error (.undefinedBehavior msg)) :=
  Witness.wit_lm3_1_use_after_storageDead_ub

example :
    Witness.annealOutcomeScalarBits 8
      (runAnnealBounded Witness.lm31OffsetDerefBody 10
        (initMachineState Witness.lm31OffsetDerefBody [])) = some 42 ∧
    ∃ alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      alloc.byteSize = Miri.ABI.Size.ofBytes 8 ∧
      ∃ err, Miri.Memory.checkAndDerefPtr annealPointerArithmetic
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + UInt64.ofNat 8),
          some (.concrete Witness.lm31AllocId1 Miri.Memory.BorTag.one)⟩
        ((8 : Nat) : Int) .memoryAccess
        (annealResolvePtr (Witness.mkSingleAllocMachine Witness.lm31AllocId1 alloc))
        (annealLookupAlloc (Witness.mkSingleAllocMachine Witness.lm31AllocId1 alloc)) =
        .error err :=
  Witness.wit_lm3_1_anneal_offset_deref_divergence

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_storageDead_lm3_1_simulation hstate hphase hbb hstmt hdecl hne0

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hnot_mapped : ∀ e ∈ allocMap, e.localIdx ≠ loc) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_storageLive_lm3_1_simulation hstate hphase hbb hstmt hdecl hnot_mapped

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr mutability pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    StepRelLM3_1 body m
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_addrOf_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty
    hne himm hsupply

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal, get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl → decl.ty.kind = dstDecl.ty.kind)) :
    ∃ allocMap',
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_read_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_prim
    himm hlive_ptr

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {ptrDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_write_simulation hstate hphase hbb hstmt hdecl_ptr hptr_ty hval_prim hval_kind hop
    himm_ptr hlive_ptr

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hoob : localAlloc.allocation.byteSize.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat) :
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_deref_oob_miri_ub hstate hopKind hbb hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty himm_ptr
    hslot_p he htag hfind_la hoob

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (hmis : (Miri.ABI.Size.ofBytes
        (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok false) :
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_deref_misaligned_miri_ub hstate hopKind hbb hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty
    himm_ptr hslot_p he htag hfind_la hinbounds hmis

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : MirAst.LocalDecl}
    {srcMut dstMut castMut : Mutability} {srcPointee dstPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hno_int : ∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_cast_ptrToPtr_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src hsrc_ty hdst_ty
    hcast_ty hsrc_thin hdst_thin himm hno_int

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {ptrMut dstMut : Mutability} {pointeeKind : RigidTy}
    {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hinbounds : ∀ ptrVal sc e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) s.frame.locals →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      sc.bits = 0 ∨
        (get? s.frame.locals e.localIdx ≠ some .dead ∧
          ptrVal.offsetBytes + sc.bits ≤
            (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_binOp_offset_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpt
    hrhs_ty hop_rhs himm hno_int hinbounds

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl tgtDecl : MirAst.LocalDecl}
    {ptrMut : Mutability} {pointeeKind : RigidTy} {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {sc : MirAst.ScalarInt} {e : AllocMapEntry}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he_mem : e ∈ allocMap)
    (he_tag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (hpos : 0 < sc.bits)
    (hbits_lt : sc.bits < 2 ^ 32)
    (hbad : get? s.frame.locals e.localIdx = some .dead ∨
      (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat <
        ptrVal.offsetBytes + sc.bits) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8)))
          s.memory) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_binOp_offset_oob_dangling_miri_ub hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hpt
    hrhs_ty hop_rhs himm hptr_slot hrhs_eval hdst_live he_mem he_tag hdecl_tgt hpos hbits_lt hbad

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_1StateStmt body s m allocMap stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm3_1_state_simulation hstate hphase hbb hstmt hwt hsupply

example :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (allocMap₂ allocMap₃ : List AllocMapEntry),
      let hooks := annealStepHooks Witness.lm31AddrOfBody.localDecls Witness.lm31AddrOfBody.layouts
      stepMirFn Witness.lm31AddrOfBody Witness.lm31AddrOfAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () Witness.lm31AddrOfMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s₁ m₁
        [rawPtrAllocMapEntry Witness.lm31AddrOfBody.localDecls Witness.lm31AddrOfBody.layouts
          .mut 1 1 Witness.lm31AllocId1] ∧
      stepMirFn Witness.lm31AddrOfBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s₂ m₂ allocMap₂ ∧
      stepMirFn Witness.lm31AddrOfBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s₃ m₃ allocMap₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      (∀ tf₃, m₃.stack.frames = #[tf₃] →
        (tf₃.locals[0]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99))))) ∧
      stepMirFn Witness.lm31AddrOfBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s₄ m₄ allocMap₃ ∧
      stepMirFn Witness.lm31AddrOfBody s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s₅ m₅ allocMap₃ ∧
      m₅.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId1) = none :=
  Witness.wit_lm3_1_addrOf_deref_storageDead_real_steps

example :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks Witness.lm31DanglingBody.localDecls
        Witness.lm31DanglingBody.layouts
      let entry := rawPtrAllocMapEntry Witness.lm31DanglingBody.localDecls
        Witness.lm31DanglingBody.layouts .not 1 1 Witness.lm31AllocId1
      stepMirFn Witness.lm31DanglingBody Witness.lm31DanglingAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () Witness.lm31DanglingMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 Witness.lm31DanglingBody s₁ m₁ [entry] ∧
      stepMirFn Witness.lm31DanglingBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 Witness.lm31DanglingBody s₂ m₂ [entry] ∧
      m₂.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId1) = none ∧
      stepMirFn Witness.lm31DanglingBody s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm3_1_use_after_storageDead_real_steps

example :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks Witness.lm31PtrCastOffsetBody.localDecls
        Witness.lm31PtrCastOffsetBody.layouts
      let entry := rawPtrAllocMapEntry Witness.lm31PtrCastOffsetBody.localDecls
        Witness.lm31PtrCastOffsetBody.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn Witness.lm31PtrCastOffsetBody
        (Witness.mkSixLocalAnnealPre Witness.lm31PtrCastOffsetBody) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (Witness.mkSixLocalMiriPre Witness.lm31PtrCastOffsetBody Witness.u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 Witness.lm31PtrCastOffsetBody s₁ m₁ [entry] ∧
      stepMirFn Witness.lm31PtrCastOffsetBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 Witness.lm31PtrCastOffsetBody s₂ m₂ [entry] ∧
      stepMirFn Witness.lm31PtrCastOffsetBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 Witness.lm31PtrCastOffsetBody s₃ m₃ [entry] ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn Witness.lm31PtrCastOffsetBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm3_1_ptrToPtr_and_offset_real_steps

example :
    (∃ (s₄ s₅ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := Witness.lm31DerefOobRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      stepMirFn b s₄ = .step s₅ ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) ∧
    (∃ (s₄ s₅ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := Witness.lm31DerefMisalignedRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₄ = .step s₅ ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) :=
  Witness.wit_lm3_1_deref_oob_and_misaligned_real_steps

example :
    Witness.annealOutcomeScalarBits 8
      (runAnnealBounded Witness.lm31ReviveBody 10 (initMachineState Witness.lm31ReviveBody [])) =
      some 7 ∧
    Miri.Memory.checkAndDerefPtr annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + UInt64.ofNat 0),
        some (.concrete Witness.lm31AllocId1 Miri.Memory.BorTag.one)⟩
      ((8 : Nat) : Int) .memoryAccess
      (annealResolvePtr { AnnealMachine.empty with
        addresses := { AnnealMachine.empty.addresses with
          baseAddr := #[⟨Witness.lm31AllocId1, annealStackBaseAddr Witness.lm31AllocId1⟩] } })
      (annealLookupAlloc { AnnealMachine.empty with
        addresses := { AnnealMachine.empty.addresses with
          baseAddr := #[⟨Witness.lm31AllocId1, annealStackBaseAddr Witness.lm31AllocId1⟩] } }) =
      .error (.allocationLookup (.deadAllocation Witness.lm31AllocId1)) :=
  Witness.wit_lm3_1_anneal_storage_revive_divergence

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr mutability pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    StepRelLM3_1 body m
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_rawPtr_addrOf_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty
    htgt_ty hne himm hsupply

example :
    Witness.annealOutcomeScalarBits 8
      (runAnnealBounded Witness.lm31TypePunBody 10
        (initMachineState Witness.lm31TypePunBody [])) = some 4294967301 :=
  Witness.wit_lm3_1_anneal_deref_type_pun_divergence

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hoob : localAlloc.allocation.byteSize.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)
    (hperm : e.perm ≠ .disabled)
    {sc : MirAst.ScalarInt}
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_deref_oob_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty
    himm_ptr hslot_p he htag hfind_la hoob hperm htarget hdst_live

example (pointee : RigidTy) (hthin : isThinRawPtrPointee pointee = true) :
    ∃ inner, castTypeInfoOfEncodedTyId (encodeRawPtrTyId pointee) = .ok (.rawPointer inner) :=
  castTypeInfoOfEncodedTyId_encodeRawPtrTyId pointee hthin

example (pointee : RigidTy) (hnot : isThinRawPtrPointee pointee = false) :
    ∃ msg, castTypeInfoOfEncodedTyId (encodeRawPtrTyId pointee) =
      .error (.unsupported msg) :=
  castTypeInfoOfEncodedTyId_nonThin_err pointee hnot

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal, get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl → decl.ty.kind = dstDecl.ty.kind)) :
    StepRelLM3_1 body m (derefReadNextAllocMap s.frame.locals allocMap ptrIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_read_simulation_explicit hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr hptr_ty
    hdst_prim himm hlive_ptr

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {ptrDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    StepRelLM3_1 body m (derefWriteNextAllocMap s.frame.locals allocMap ptrIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_write_simulation_explicit hstate hphase hbb hstmt hdecl_ptr hptr_ty hval_prim
    hval_kind hop himm_ptr hlive_ptr

example {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr mutability pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hroom : m.machine.memory.nextAllocId.toNat + 1 < 2 ^ 32)
    (hsrc : m.machine.memory.sourceAllocIdWorldActive = true →
      m.machine.memory.sourceAllocIdNext + 1 ≠ 0)
    (hm_step : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true)) :
    (AllocIdSupplyReady m'.machine.memory ∧
      m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId + 1 ∧
      m'.machine.memory.sourceAllocIdWorldActive = m.machine.memory.sourceAllocIdWorldActive) ∧
    (∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, k ≠ targetIdx → IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k) :=
  step_rawPtr_addrOf_preserves_supply hstate hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne
    himm hsupply hroom hsrc hm_step

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr mutability pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = targetIdx) :
    StepRelLM3_1 body m
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        e₀.allocId :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_addrOf_indirect_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty
    htgt_ty hne himm_dst he₀ he₀_loc

example {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hne : dstIdx ≠ targetIdx)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = targetIdx)
    (hm_step : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true)) :
    m'.machine = m.machine ∧
    (∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k) :=
  step_rawPtr_addrOf_indirect_preserves hstate hbb hstmt hdecl_dst hdecl_tgt hne himm_dst he₀
    he₀_loc hm_step

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.nop, span⟩) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_nop_lm3_1_simulation hstate hphase hbb hstmt

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : MirAst.LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_scalar_use_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdst_prim hval_kind hop
    himm_dst

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : MirAst.LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (hmem_dst : ∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_direct_write_promoted_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdst_prim hval_kind
    hop hmem_dst

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (hmis : (Miri.ABI.Size.ofBytes
        (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok false)
    (hperm : e.perm ≠ .disabled)
    {sc : MirAst.ScalarInt}
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_deref_misaligned_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty
    himm_ptr hslot_p he htag hfind_la hinbounds hmis hperm htarget hdst_live

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl tgtDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_bool : dstDecl.ty.kind = .bool)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_byte : tgtDecl.ty.kind = .uint .u8 ∨ tgtDecl.ty.kind = .int .i8)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinvalid : 2 ≤ sc.bits)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) :=
  step_deref_invalid_bool_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hdst_bool hptr_ty
    himm_ptr hslot_p hoff0 he htag hperm hdecl_tgt htgt_byte htarget hinvalid hdst_live

example {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hlo_off : 1 ≤ offsetBytes)
    (hhi_off : offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (-1 : Int64)
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .ok ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat (offsetBytes - 1)),
        some (.concrete allocId borTag)⟩ :=
  ptrOffsetInbounds_neg_one_live_ok allocId borTag offsetBytes localAlloc hid hoff hbase hlive
    hlo_off hhi_off

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl tgtDecl : MirAst.LocalDecl}
    {ptrMut dstMut : Mutability} {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut (.uint .u64))
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut (.uint .u64))
    (hrhs_ty : rhsTy.kind = .uint .usize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar ⟨1, 8⟩) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he_mem : e ∈ allocMap)
    (he_tag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_ty : tgtDecl.ty.kind = .uint .u64)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx (.init (.ptr { ptrVal with offsetBytes := 1 } 8)))
          s.memory) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + 8),
              .concrete e.allocId borTag⟩)))) :=
  step_binOp_offset_stride_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty
    hrhs_ty hop_rhs himm hptr_slot hoff0 hrhs_eval hdst_live he_mem he_tag hdecl_tgt htgt_ty
    htgt_live

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl tgtDecl : MirAst.LocalDecl}
    {ptrMut dstMut : Mutability} {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut (.uint .u8))
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut (.uint .u8))
    (hrhs_ty : rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar ⟨2 ^ 64 - 1, 8⟩) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he_mem : e ∈ allocMap)
    (he_tag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead)
    (hlo_off : 1 ≤ ptrVal.offsetBytes)
    (hhi_off : ptrVal.offsetBytes ≤
      (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + (2 ^ 64 - 1) } 8)))
          s.memory) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes - 1)),
              .concrete e.allocId borTag⟩)))) :=
  step_binOp_offset_neg_isize_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty
    hdst_ty hrhs_ty hop_rhs himm hptr_slot hrhs_eval hdst_live he_mem he_tag hdecl_tgt htgt_live
    hlo_off hhi_off

example :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState),
      let b := Witness.lm31TwoPromotionsBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 Witness.lm31AllocId2
      let e₃ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 3 Witness.lm31AllocId1
      let map₄ := updateAllocMapOnWrite [e₃, e₂, e₁] 1 none
      stepMirFn b Witness.lm31TwoPromotionsAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () Witness.lm31TwoPromotionsMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      m₁.machine.memory.nextAllocId = 2 ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₂, e₁] ∧
      m₂.machine.memory.nextAllocId = 3 ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [e₃, e₂, e₁] ∧
      m₃.machine.memory.nextAllocId = 3 ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ map₄ ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ (derefReadNextAllocMap s₄.frame.locals map₄ 4) ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      (∀ tf₅, m₅.stack.frames = #[tf₅] →
        (tf₅.locals[0]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99))))) :=
  Witness.wit_lm3_1_two_promotions_reborrow_and_direct_write_real_steps

example :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := Witness.lm31InvalidBoolDerefBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1
      stepMirFn b Witness.lm31InvalidBoolAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () Witness.lm31InvalidBoolMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨2, 1⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "reading invalid value")) :=
  Witness.wit_lm3_1_invalid_bool_cast_deref_real_steps

example :
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := Witness.lm31StrideOffsetRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (Witness.mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (Witness.mkSixLocalMiriPre b Witness.u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + 8),
              .concrete Witness.lm31AllocId1 borTag⟩))))) ∧
    (∃ (s₃ s₄ : MachineState) (m₃ m₄ : AnnealStepState)
      (tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := Witness.lm31NegIsizeOffsetRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₃ m₃
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₃ = .step s₄ ∧
      get? s₄.frame.locals 5 =
        some (.init (.ptr { allocId := 1, offsetBytes := 2 + (2 ^ 64 - 1) } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      m₄.stack.frames = #[tf₄] ∧
      (tf₄.locals[5]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + 1),
              .concrete Witness.lm31AllocId1 borTag⟩))))) :=
  Witness.wit_lm3_1_offset_stride_and_neg_isize_real_steps

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention ⟨loc, .nil⟩, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hlive : get? s.frame.locals loc ≠ some .dead) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_placeMention_local_lm3_1_simulation hstate hphase hbb hstmt hdecl hlive

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {ptrDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hnot_uninit : get? s.frame.locals ptrIdx ≠ some .uninit) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_placeMention_deref_lm3_1_simulation hstate hphase hbb hstmt hdecl_ptr
    hptr_ty hpk_prim himm_ptr hnot_uninit

example
    {allocMap : List AllocMapEntry}
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable)
    (m : AnnealStepState)
    (srcLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (srcMut dstMut : Mutability) (srcPointee dstPointee : RigidTy)
    (srcTy dstTy : Ty)
    (hsrcTy : srcTy.kind = .rawPtr srcMut srcPointee)
    (hdstTy : dstTy.kind = .rawPtr dstMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (hsrc_slot : get? locals srcLoc = some (.init (.ptr ptrVal 8)))
    (hptr_rel : PtrRel allocMap ptrVal mptr) :
    evalRvalue locals (.cast .ptrToPtr (.copy ⟨srcLoc, .nil⟩) dstTy) mem localDecls layouts =
      .ok (.ptr ptrVal 8) locals mem ∧
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooks layouts)
      ()
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy srcTy layouts⟩
      (translateTy dstTy layouts)
      m =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy dstTy layouts⟩ m ∧
    ImmediateRelLM3_1 allocMap dstTy layouts
      (.ptr ptrVal 8)
      (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) :=
  evalCast_ptrToPtr_annealCastHooks_simulation locals mem localDecls layouts m srcLoc ptrVal
    mptr srcMut dstMut srcPointee dstPointee srcTy dstTy hsrcTy hdstTy hsrc_thin hdst_thin
    hsrc_slot hptr_rel

example
    {localDecls : List MirAst.LocalDecl} {layouts : Layout.LayoutTable}
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (ptrLay : Miri.Interpreter.LocalLayout) :
    lookupDerefPointeeLayout localDecls layouts refIdx ptrLay = none :=
  lookupDerefPointeeLayout_ref_eq_none hdecl hty ptrLay

example (sc : Miri.Memory.Scalar AnnealProv) :
    annealValidateScalarForTyId 50 sc = false :=
  annealValidateScalarForTyId_never_false sc

example (tyId : Miri.MIR.TyId) (hty : tyId = 41 ∨ tyId = 42) :
    annealValidateScalarForTyId tyId
      (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0)) = false :=
  annealValidateScalarForTyId_nonNullPtr_null_false tyId hty

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl tgtDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_char : dstDecl.ty.kind = .char)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_word : tgtDecl.ty.kind = .uint .u32 ∨ tgtDecl.ty.kind = .int .i32)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinvalid : isValidCharCode sc.bits = false)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) :=
  step_deref_invalid_char_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hdst_char hptr_ty himm_ptr hslot_p hoff0 he htag hperm hdecl_tgt htgt_word
    htarget hinvalid hdst_live

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {c : ConstOperand} {b : Nat} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩)
    {ptrDecl tgtDecl : MirAst.LocalDecl}
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr .mut .bool)
    (hc_val : c.val = .scalar (.int ⟨b, 1⟩))
    (hc_ty : c.ty.kind = .bool)
    (hb_lo : 2 ≤ b) (hb_hi : b < 256)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_1 : tgtDecl.ty.kind = .bool ∨ tgtDecl.ty.kind = .uint .u8 ∨ tgtDecl.ty.kind = .int .i8)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals e.localIdx = some (.init (.scalar ⟨b, 1⟩))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "writing invalid value")) :=
  step_deref_write_invalid_bool_divergence hstate hphase hbb hstmt hdecl_ptr hptr_ty
    hc_val hc_ty hb_lo hb_hi himm_ptr hslot_p hoff0 he htag hperm hdecl_tgt htgt_1 htgt_live

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {ptrDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (huninit : get? s.frame.locals ptrIdx = some .uninit) :
    stepMirFn body s = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "read of uninitialized local")) :=
  step_placeMention_deref_uninit_divergence hstate hphase hbb hstmt hdecl_ptr
    hptr_ty hpk_prim himm_ptr huninit

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {sc : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc))) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' msc_ref,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc_ref ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_ref)))) :=
  step_rawPtr_deref_null_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              .concrete e.allocId borTag⟩)))) :=
  step_rawPtr_deref_nonzero_offset_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p he htag hperm

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty}
    {dstDecl srcDecl : MirAst.LocalDecl} {srcMut : Mutability} {srcPointee : RigidTy}
    {ptrVal : ProvenancePtr} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_ty : dstDecl.ty.kind = .uint .usize)
    (hcast_ty : castTy.kind = .uint .usize)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8))) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported "exposeProvenance in cast")) :=
  step_cast_expose_provenance_ptr_unsupported hstate hphase hbb hstmt hdecl_dst hdecl_src
    hsrc_ty hsrc_thin hdst_ty hcast_ty himm_src hdst_live hslot_s

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty}
    {dstDecl : MirAst.LocalDecl} {dstMut castMut : Mutability} {dstPointee : RigidTy}
    {bits : Nat} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .pointerWithExposedProvenance (.constant c) castTy), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (hc_ty : c.ty.kind = .uint .usize)
    (hc_val : c.val = .scalar (.int ⟨bits, 8⟩))
    (hbits_lt : bits < 2 ^ 64)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := bits / 65536, offsetBytes := bits % 65536 } 8))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported "pointerFromExposedAddress in cast")) :=
  step_cast_with_exposed_provenance_divergence hstate hphase hbb hstmt hdecl_dst
    hdst_ty hcast_ty hdst_thin hc_ty hc_val hbits_lt hdst_live

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm :
      (∃ target, bb.terminator.kind = .goto target) ∨
      (bb.terminator.kind = .return_ ∧
        ∃ decl0,
          get? body.localDecls 0 = some decl0 ∧
          (∀ mutability pk, decl0.ty.kind ≠ .rawPtr mutability pk) ∧
          (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
          ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) ∨
      bb.terminator.kind = .unreachable) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_goto_return_lm3_1_simulation hstate hphase hbb hstmt_none
    hstmt_len hcleanup hterm

example :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (allocMap₂ allocMap₃ : List AllocMapEntry),
      let hooks := annealStepHooks Witness.lm31AddrOfBody.localDecls Witness.lm31AddrOfBody.layouts
      stepMirFn Witness.lm31AddrOfBody Witness.lm31AddrOfAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () Witness.lm31AddrOfMiriPre = (m₁, .ok true) ∧
      stepMirFn Witness.lm31AddrOfBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s₂ m₂ allocMap₂ ∧
      stepMirFn Witness.lm31AddrOfBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn Witness.lm31AddrOfBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      stepMirFn Witness.lm31AddrOfBody s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 Witness.lm31AddrOfBody s₅ m₅ allocMap₃ ∧
      m₅.machine.memory.live.find? (fun x => x.1 == Witness.lm31AllocId1) = none ∧
      stepMirFn Witness.lm31AddrOfBody s₅ = .retNormal (.scalar ⟨99, 8⟩) s₅.memory ∧
      Miri.Interpreter.Step.step hooks () m₅ = ({ m₅ with stack := ⟨#[]⟩ }, .ok true) ∧
      Miri.Interpreter.Step.step hooks () { m₅ with stack := ⟨#[]⟩ } =
        ({ m₅ with stack := ⟨#[]⟩ }, .ok false) ∧
      annealControlHooks.returnOperand () m₅ =
        (m₅, .ok (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar99)))) :=
  Witness.wit_lm3_1_end_to_end_return_real_steps

example :
    (∃ (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := Witness.lm31RawPtrDerefNullBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty
        Witness.rawPtrConstU64Ty Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar0U64))))) ∧
    (∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
      (tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := Witness.lm31RawPtrDerefOffsetBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₃ m₃
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1] ∧
      s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      stepMirFn b (Witness.mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (Witness.mkSixLocalMiriPre b Witness.u64Ty) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      m₄.stack.frames = #[tf₄] ∧
      (tf₄.locals[5]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1 + 1),
              .concrete Witness.lm31AllocId1 borTag⟩))))) :=
  Witness.wit_lm3_1_rawPtr_deref_null_and_offset_real_steps

example :
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := Witness.lm31ForgedProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (Witness.mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (Witness.mkSixLocalMiriPre b Witness.u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.unsupported "pointerFromExposedAddress in cast")) ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩))) ∧
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := Witness.lm31ExposeProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (Witness.mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (Witness.mkSixLocalMiriPre b Witness.u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.scalar ⟨65536, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.unsupported "exposeProvenance in cast"))) :=
  Witness.wit_lm3_1_anneal_forged_provenance_real_steps

example :
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := Witness.lm31InvalidCharDerefBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0xD800, 4⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.charTyLM31
        Witness.u32TyLM31 Witness.lm31ScalarSurrogateU32
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨0xD800, 4⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "reading invalid value"))) ∧
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := Witness.lm31WriteInvalidBoolBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 1⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u8TyLM31
        Witness.u8TyLM31 Witness.lm31Scalar0U8
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1] ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨2, 1⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "writing invalid value"))) ∧
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := Witness.lm31PlaceMentionDerefBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty
        Witness.rawPtrConstU64Ty Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "read of uninitialized local"))) :=
  Witness.wit_lm3_1_invalid_char_write_bool_and_placeMention_real_steps

example
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx : Nat} (hlt : srcIdx < tf.locals.size)
    {k : Nat} (hk : IsImmediateFrameLocal tf k) :
    IsImmediateFrameLocal (deinitFrameLocal tf srcIdx hlt) k :=
  IsImmediateFrameLocal.deinit_local hlt hk

example
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (srcIdx : Nat) (hlt : srcIdx < tf.locals.size) :
    WellTypedScalarOperand body (deinitFrameLocal tf srcIdx hlt) op ty :=
  WellTypedScalarOperand.of_deinitFrameLocal hop srcIdx hlt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {srcIdx : Local} {srcDecl : MirAst.LocalDecl}
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {slot_s : LocalSlot}
    (hslot_s : get? s.frame.locals srcIdx = some slot_s)
    (hne_dead : slot_s ≠ .dead)
    (himm_src : IsImmediateFrameLocal tf srcIdx)
    (hlt_s : srcIdx < tf.locals.size) :
    StateRelLM3_1 body
      { s with frame := { s.frame with locals := s.frame.locals.set srcIdx .uninit } }
      { m with stack := ⟨#[deinitFrameLocal tf srcIdx hlt_s]⟩ }
      allocMap :=
  StateRelLM3_1.deinit_immediate_local hstate hframes hdecl_src hslot_s hne_dead himm_src hlt_s

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : MirAst.LocalDecl} {srcMut dstMut : Mutability} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_use_lm3_1_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_src
    hsrc_ty hdst_ty himm

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : MirAst.LocalDecl}
    {srcMut dstMut castMut : Mutability} {srcPointee dstPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hno_int : ∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_cast_ptrToPtr_move_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src
    hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hno_int

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {ptrMut dstMut : Mutability} {pointeeKind : RigidTy}
    {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hinbounds : ∀ ptrVal sc e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      evalOperand (s.frame.locals.set ptrIdx .uninit) rhsOp s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals =
        .ok (.scalar sc) (s.frame.locals.set ptrIdx .uninit) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      sc.bits = 0 ∨
        (get? s.frame.locals e.localIdx ≠ some .dead ∧
          ptrVal.offsetBytes + sc.bits ≤
            (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_binOp_offset_move_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hno_int hinbounds

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {castTy : Ty} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .pointerExposeProvenance (opKind ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : MirAst.LocalDecl} {srcMut : Mutability} {srcPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_ty : dstDecl.ty.kind = .uint .usize)
    (hcast_ty : castTy.kind = .uint .usize)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hno_ptr : ∀ ptrVal, get? s.frame.locals srcIdx ≠ some (.init (.ptr ptrVal 8))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_cast_expose_provenance_scalar_simulation hstate hphase hopKind hbb hstmt
    hdecl_dst hdecl_src hsrc_ty hsrc_thin hdst_ty hcast_ty himm hno_ptr

example
    (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable)
    (localId : Local) (decl : MirAst.LocalDecl)
    (hdecl : get? localDecls localId = some decl) :
    lookupDerefPointeeLayout localDecls layouts localId (translateTy decl.ty layouts) =
      lookupDerefPointeeLayout .nil layouts localId (translateTy decl.ty layouts) :=
  lookupDerefPointeeLayout_decl_eq_encoded localDecls layouts localId decl hdecl

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty}
    {dstDecl srcDecl : MirAst.LocalDecl}
    {srcMut dstMut castMut : Mutability} {srcPointee dstPointee : RigidTy}
    {sc : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.scalar sc))) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' msc,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) :=
  step_cast_ptrToPtr_scalar_divergence hstate hphase hbb hstmt hdecl_dst hdecl_src
    hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hdst_live hslot_s

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand}
    {dstDecl ptrDecl : MirAst.LocalDecl} {ptrMut dstMut : Mutability}
    {pointeeKind : RigidTy} {rhsTy : Ty} {sc sc_rhs : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc_rhs) s.frame.locals)
    (hrhs_zero : sc_rhs.bits = 0) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' msc_out,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc_out ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_out)))) :=
  step_binOp_offset_scalar_zero_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hdst_live hslot_p hrhs_eval hrhs_zero

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand}
    {dstDecl ptrDecl : MirAst.LocalDecl} {ptrMut : Mutability}
    {pointeeKind : RigidTy} {rhsTy : Ty} {sc sc_rhs : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc_rhs) s.frame.locals)
    (hrhs_pos : 0 < sc_rhs.bits)
    (hrhs_lt : sc_rhs.bits < 2 ^ 32) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "pointer Offset out of bounds")) :=
  step_binOp_offset_scalar_nonzero_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hpt hrhs_ty hop_rhs himm_ptr hslot_p hrhs_eval hrhs_pos hrhs_lt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .disabled ∨ (e.perm = .frozen ∧ rawMut = .mut)) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              .concrete e.allocId borTag⟩)))) :=
  step_rawPtr_deref_perm_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p he htag hperm

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hzero_perm : ∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ rawMut = .mut)) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? s.frame.locals dstIdx ≠ some .dead →
      (∃ s', stepMirFn body s = .step s' ∧
        get? s'.frame.locals dstIdx =
          some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
      ∃ m' tf' borTag,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧
        (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                .concrete e.allocId borTag⟩))))) :=
  step_rawPtr_deref_zero_offset_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hpk_prim himm hno_int hzero_perm

example :
    (∃ (s₁ s₂ s₃ s₄ s₅ : MachineState)
      (m₁ m₂ m₃ m₄ m₅ m₆ : AnnealStepState) (msg : String),
      let b := Witness.lm31RawPtrUseMoveBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1
      stepMirFn b (Witness.mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (Witness.mkSixLocalMiriPre b Witness.u64Ty) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      get? s₃.frame.locals 2 = some .uninit ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ [entry] ∧
      get? s₅.frame.locals 3 = some .uninit ∧
      get? s₅.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      stepMirFn b s₅ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .error (.undefinedBehavior msg))) ∧
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let bc := Witness.lm31ExposeScalarCopyBody
      let bm := Witness.lm31ExposeScalarMoveBody
      let hc := annealStepHooks bc.localDecls bc.layouts
      let hm := annealStepHooks bm.localDecls bm.layouts
      stepMirFn bc (Witness.mkFourLocalScalarAnnealPre bc ⟨0, 8⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hc ()
        (Witness.mkFourLocalScalarMiriPre bc Witness.u64Ty Witness.rawPtrConstU64Ty
          Witness.lm31Scalar0U64) = (m₁, .ok true) ∧
      StateRelLM3_1 bc s₁ m₁ [] ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      stepMirFn bm (Witness.mkFourLocalScalarAnnealPre bm ⟨42, 8⟩) = .step s₂ ∧
      Miri.Interpreter.Step.step hm ()
        (Witness.mkFourLocalScalarMiriPre bm Witness.u64Ty Witness.rawPtrConstU64Ty
          Witness.lm31Scalar42) = (m₂, .ok true) ∧
      StateRelLM3_1 bm s₂ m₂ [] ∧
      get? s₂.frame.locals 1 = some .uninit ∧
      get? s₂.frame.locals 2 = some (.init (.scalar ⟨42, 8⟩))) :=
  Witness.wit_lm3_1_rawPtr_use_move_and_expose_scalar_real_steps

example :
    (∃ (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := Witness.lm31NullPtrToPtrBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.rawPtrConstU64Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar0U64))))) ∧
    (∃ (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := Witness.lm31NullOffsetZeroBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.rawPtrConstU8Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar0U64))))) ∧
    (∃ (m₁ : AnnealStepState),
      let b := Witness.lm31NullOffsetOneBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.rawPtrConstU8Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₀ =
        (m₁, .error (.undefinedBehavior "pointer Offset out of bounds"))) :=
  Witness.wit_lm3_1_null_ptrToPtr_and_offset_divergences_real_steps

example :
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := Witness.lm31RawPtrDerefZeroBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.u64Ty Witness.lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 Witness.lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1),
              .concrete Witness.lm31AllocId1 borTag⟩))))) ∧
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := Witness.lm31RawPtrDerefFrozenMutBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.u64Ty Witness.lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 Witness.lm31AllocId1] ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr Witness.lm31AllocId1),
              .concrete Witness.lm31AllocId1 borTag⟩))))) :=
  Witness.wit_lm3_1_rawPtr_deref_zero_and_perm_divergence_real_steps

example
    (layouts : Layout.LayoutTable)
    (value : Miri.Interpreter.RvalueImmTy AnnealProv)
    (hnone : rawPtrPointeeEncodedTyId? value.layout.ty = none)
    (st : AnnealStepState) :
    annealDerefValidity layouts value st =
      .error (.unsupported
        s!"derefValidity not supported for non-thin or safe-reference TyId {value.layout.ty}")
        st :=
  annealDerefValidity_nonThin_or_ref_err layouts value hnone st

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {opKind₁ opKind₂ : Place → MirAst.Operand}
    (hopKind₁ : opKind₁ = MirAst.Operand.copy ∨ opKind₁ = MirAst.Operand.move)
    (hopKind₂ : opKind₂ = MirAst.Operand.copy ∨ opKind₂ = MirAst.Operand.move)
    {bop : MirAst.BinOp} (hbop : IsCmpBinOp bop)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp bop (opKind₁ ⟨lhsIdx, .nil⟩) (opKind₂ ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : MirAst.LocalDecl}
    {lhsMut rhsMut : Mutability} {lhsPointee rhsPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hlhs_ty : lhsDecl.ty.kind = .rawPtr lhsMut lhsPointee)
    (hrhs_ty : rhsDecl.ty.kind = .rawPtr rhsMut rhsPointee)
    (hdst_ty : dstDecl.ty.kind = .bool)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧
      IsImmediateFrameLocal topFrame lhsIdx ∧
      IsImmediateFrameLocal topFrame rhsIdx)
    (hno_ptr_lhs : ∀ ptrVal, get? s.frame.locals lhsIdx ≠ some (.init (.ptr ptrVal 8)))
    (hno_ptr_rhs : ∀ ptrVal, get? s.frame.locals rhsIdx ≠ some (.init (.ptr ptrVal 8))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_cmp_scalar_lm3_1_simulation hstate hphase hopKind₁ hopKind₂ hbop hbb hstmt
    hdecl_dst hdecl_lhs hdecl_rhs hlhs_ty hrhs_ty hdst_ty himm hno_ptr_lhs hno_ptr_rhs

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (opKind ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {ptrMut dstMut : Mutability} {pointeeKind : RigidTy}
    {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hexact : derefPointeeKindHasExactLayout pointeeKind = true)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hzero : ∀ locals_mid sc locals',
      ((opKind = MirAst.Operand.copy ∧ locals_mid = s.frame.locals) ∨
       (opKind = MirAst.Operand.move ∧ locals_mid = s.frame.locals.set ptrIdx .uninit)) →
      evalOperand locals_mid rhsOp s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) locals' →
      sc.bits = 0) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_binOp_offset_zero_any_stride_lm3_1_simulation hstate hphase hopKind hbb hstmt
    hdecl_dst hdecl_ptr hptr_ty hdst_ty hexact hrhs_ty hop_rhs himm hno_int hzero

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .ptrMetadata (opKind ⟨ptrIdx, .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hdead_or_uninit :
      get? s.frame.locals ptrIdx = some .dead ∨ get? s.frame.locals ptrIdx = some .uninit) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_unaryOp_ptrMetadata_thin_rawPtr_ub_simulation hstate hphase hopKind hbb hstmt
    hdecl_dst hdecl_ptr hptr_ty himm_ptr hdead_or_uninit

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.unaryOp .ptrMetadata (opKind ⟨ptrIdx, .nil⟩)), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hexact : derefPointeeKindHasExactLayout pointeeKind = true)
    (hdst_ty : dstDecl.ty.kind = .tuple .nil)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hptr_init :
      get? s.frame.locals ptrIdx ≠ some .dead ∧ get? s.frame.locals ptrIdx ≠ some .uninit) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate .uninit)) :=
  step_unaryOp_ptrMetadata_thin_rawPtr_divergence hstate hphase hopKind hbb hstmt
    hdecl_dst hdecl_ptr hptr_ty hexact hdst_ty himm hdst_live hptr_init

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {opKind₁ opKind₂ : Place → MirAst.Operand}
    (hopKind₁ : opKind₁ = MirAst.Operand.copy ∨ opKind₁ = MirAst.Operand.move)
    (hopKind₂ : opKind₂ = MirAst.Operand.copy ∨ opKind₂ = MirAst.Operand.move)
    {bop : MirAst.BinOp} (hbop : IsCmpBinOp bop)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp bop (opKind₁ ⟨lhsIdx, .nil⟩) (opKind₂ ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : MirAst.LocalDecl}
    {lhsMut rhsMut : Mutability} {lhsPointee rhsPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hlhs_ty : lhsDecl.ty.kind = .rawPtr lhsMut lhsPointee)
    (hrhs_ty : rhsDecl.ty.kind = .rawPtr rhsMut rhsPointee)
    (hdst_ty : dstDecl.ty.kind = .bool)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧
      IsImmediateFrameLocal topFrame lhsIdx ∧
      IsImmediateFrameLocal topFrame rhsIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    {ptrVal₁ : ProvenancePtr}
    (hlhs_ptr : get? s.frame.locals lhsIdx = some (.init (.ptr ptrVal₁ 8)))
    (hrhs_init :
      get? s.frame.locals rhsIdx ≠ some .dead ∧ get? s.frame.locals rhsIdx ≠ some .uninit)
    (hmove_disj : opKind₁ = MirAst.Operand.move → lhsIdx ≠ rhsIdx) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' b,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool b))))) :=
  step_rawPtr_cmp_ptr_divergence hstate hphase hopKind₁ hopKind₂ hbop hbb hstmt
    hdecl_dst hdecl_lhs hdecl_rhs hlhs_ty hrhs_ty hdst_ty himm hdst_live hlhs_ptr hrhs_init
    hmove_disj

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty}
    {dstDecl srcDecl : MirAst.LocalDecl}
    {srcMut dstMut castMut : Mutability} {srcPointee dstPointee : RigidTy}
    {sc : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.scalar sc))) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' msc,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) :=
  step_cast_ptrToPtr_move_scalar_divergence hstate hphase hbb hstmt hdecl_dst hdecl_src
    hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hdst_live hslot_s

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {ptrMut dstMut : Mutability} {pointeeKind : RigidTy}
    {rhsTy : Ty} {sc_p sc_r : MirAst.ScalarInt} {locals_r : List LocalSlot}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hexact : derefPointeeKindHasExactLayout pointeeKind = true)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc_p)))
    (ha_rhs : evalOperand (s.frame.locals.set ptrIdx .uninit) rhsOp
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
      .ok (.scalar sc_r) locals_r)
    (hbits0 : sc_r.bits = 0) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' msc_out,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc_p msc_out ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_out)))) :=
  step_binOp_offset_move_scalar_zero_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hexact hrhs_ty hop_rhs himm hdst_live hslot_p ha_rhs hbits0

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (hty0 : decl0.ty.kind = .rawPtr mutability pointeeKind)
    (himm0 : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) :
    StepObsRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_return_rawPtr_lm3_1_simulation hstate hphase hbb hstmt_none hstmt_len
    hcleanup hret hdecl0 hty0 himm0

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
    StepObsRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_switchInt_lm3_1_simulation hstate hphase hbb hstmt_none hstmt_len
    hterm hty hdiscr hcases

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {cond : MirAst.Operand} {condTy : Ty} {expected : Bool} {target : BasicBlockIdx}
    (hterm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hbool : condTy.kind = .bool)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame cond condTy) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_assert_lm3_1_simulation hstate hphase hbb hstmt_none hstmt_len
    hterm hbool hop

example :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState)
      (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (allocMap₂ : List AllocMapEntry)
      (mptr : Miri.Memory.Pointer AnnealProv),
      let b := Witness.lm31BranchOffsetReturnPtrBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b Witness.lm31BranchOffsetReturnPtrAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () Witness.lm31BranchOffsetReturnPtrMiriPre =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      get? s₃.frame.locals 2 = some .uninit ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      s₄.frame.blockIdx = 1 ∧
      stepMirFn b s₄ = .emitStep (.event 1) s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      s₅.frame.blockIdx = 2 ∧
      StateRelLM3_1 b s₅ m₅ allocMap₂ ∧
      stepMirFn b s₅ =
        .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₅.memory ∧
      Miri.Interpreter.Step.step hooks () m₅ = ({ m₅ with stack := ⟨#[]⟩ }, .ok true) ∧
      annealControlHooks.returnOperand () m₅ =
        (m₅, .ok (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))) ∧
      PtrRel allocMap₂ { allocId := 1, offsetBytes := 0 } mptr :=
  Witness.wit_lm3_1_branch_offset_zero_and_return_rawPtr_real_steps

example :
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState),
      let b := Witness.lm31RawPtrCmpScalarBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.rawPtrConstU64Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨1, 1⟩))) ∧
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (eqRes : Bool),
      let b := Witness.lm31RawPtrCmpPtrBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.u64Ty
        Witness.lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool eqRes)))))) ∧
    (∃ (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := Witness.lm31MoveNullPtrToPtrBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.rawPtrConstU64Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar0U64))))) ∧
    (∃ (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := Witness.lm31MoveNullOffsetZeroBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.rawPtrConstU64Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt Witness.lm31Scalar0U64))))) ∧
    (∃ (m_ub m_ok : AnnealStepState) (msg : String)
      (tf_ok : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let bu := Witness.lm31PtrMetadataUninitBody
      let bt := Witness.lm31PtrMetadataThinBody
      let su := Witness.mkFourLocalScalarAnnealPre bu ⟨0, 8⟩
      let mu := Witness.mkFourLocalScalarMiriPre bu Witness.u64Ty Witness.rawPtrConstU64Ty
        Witness.lm31Scalar0U64
      let st := Witness.mkFourLocalScalarAnnealPre bt ⟨0, 8⟩
      let mt := Witness.mkFourLocalScalarMiriPre bt Witness.u64Ty Witness.rawPtrConstU64Ty
        Witness.lm31Scalar0U64
      stepMirFn bu su = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks bu.localDecls bu.layouts) () mu =
        (m_ub, .error (.undefinedBehavior msg)) ∧
      stepMirFn bt st = .unsupported ∧
      Miri.Interpreter.Step.step (annealStepHooks bt.localDecls bt.layouts) () mt =
        (m_ok, .ok true) ∧
      m_ok.stack.frames = #[tf_ok] ∧
      (tf_ok.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate .uninit))) :=
  Witness.wit_lm3_1_rawPtr_cmp_and_ptrMetadata_real_steps

example
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_1 body m allocMap aRes mRes) :
    StepObsRelLM3_1 body m allocMap aRes mRes :=
  h.toStepObsRelLM3_1

example
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_1 body m allocMap aRes mRes) :
    ((∃ obs s', aRes = .emitStep obs s' ∧ StateRelLM3_1 body s' mRes.1 allocMap) ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames ≠ #[])) ∧
    ((∃ retVal mem', aRes = .retNormal retVal mem') ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames = #[])) ∧
    ((aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg))) :=
  ⟨h.emitStep_iff, h.retNormal_iff, h.ub_iff⟩

example
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {retVal : Value} {mem' : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_1 body m allocMap (.retNormal retVal mem') mRes) :
    ∃ decl0 imm0,
      get? body.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_1 allocMap decl0.ty body.layouts retVal imm0 ∧
      mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) :=
  h.retNormal_rel

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {opKind₁ opKind₂ : Place → MirAst.Operand}
    (hopKind₁ : opKind₁ = MirAst.Operand.copy ∨ opKind₁ = MirAst.Operand.move)
    (hopKind₂ : opKind₂ = MirAst.Operand.copy ∨ opKind₂ = MirAst.Operand.move)
    {bop : MirAst.BinOp}
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp bop (opKind₁ ⟨lhsIdx, .nil⟩) (opKind₂ ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : MirAst.LocalDecl}
    {lhsMut rhsMut : Mutability} {lhsPointee rhsPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hlhs_ty : lhsDecl.ty.kind = .rawPtr lhsMut lhsPointee)
    (hrhs_ty : rhsDecl.ty.kind = .rawPtr rhsMut rhsPointee)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame lhsIdx ∧
      IsImmediateFrameLocal topFrame rhsIdx)
    (hub :
      get? s.frame.locals lhsIdx = some .dead ∨
      get? s.frame.locals lhsIdx = some .uninit ∨
      get? s.frame.locals rhsIdx = some .dead ∨
      get? s.frame.locals rhsIdx = some .uninit ∨
      (opKind₁ = MirAst.Operand.move ∧ lhsIdx = rhsIdx)) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_cmp_ub_lm3_1_simulation hstate hphase hopKind₁ hopKind₂ hbb hstmt
    hdecl_dst hdecl_lhs hdecl_rhs hlhs_ty hrhs_ty himm hub

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {opKind₁ opKind₂ : Place → MirAst.Operand}
    (hopKind₁ : opKind₁ = MirAst.Operand.copy ∨ opKind₁ = MirAst.Operand.move)
    (hopKind₂ : opKind₂ = MirAst.Operand.copy ∨ opKind₂ = MirAst.Operand.move)
    {bop : MirAst.BinOp} (hbop : IsCmpBinOp bop)
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp bop (opKind₁ ⟨lhsIdx, .nil⟩) (opKind₂ ⟨rhsIdx, .nil⟩)), span⟩)
    {dstDecl lhsDecl rhsDecl : MirAst.LocalDecl}
    {lhsMut rhsMut : Mutability} {lhsPointee rhsPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_lhs : get? body.localDecls lhsIdx = some lhsDecl)
    (hdecl_rhs : get? body.localDecls rhsIdx = some rhsDecl)
    (hlhs_ty : lhsDecl.ty.kind = .rawPtr lhsMut lhsPointee)
    (hrhs_ty : rhsDecl.ty.kind = .rawPtr rhsMut rhsPointee)
    (hdst_ty : dstDecl.ty.kind = .bool)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧
      IsImmediateFrameLocal topFrame lhsIdx ∧
      IsImmediateFrameLocal topFrame rhsIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    {sc₁ : MirAst.ScalarInt} {ptrVal₂ : ProvenancePtr}
    (hlhs_sc : get? s.frame.locals lhsIdx = some (.init (.scalar sc₁)))
    (hrhs_ptr : get? s.frame.locals rhsIdx = some (.init (.ptr ptrVal₂ 8))) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' b,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool b))))) :=
  step_rawPtr_cmp_scalar_ptr_divergence hstate hphase hopKind₁ hopKind₂ hbop hbb hstmt
    hdecl_dst hdecl_lhs hdecl_rhs hlhs_ty hrhs_ty hdst_ty himm hdst_live hlhs_sc hrhs_ptr

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : MirAst.LocalDecl} {ptrMut : Mutability} {pointeeKind : RigidTy}
    {rhsTy : Ty} {sc_p sc_r : MirAst.ScalarInt} {locals_r : List LocalSlot}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc_p)))
    (ha_rhs : evalOperand (s.frame.locals.set ptrIdx .uninit) rhsOp
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
      .ok (.scalar sc_r) locals_r)
    (hrhs_pos : 0 < sc_r.bits)
    (hrhs_lt : sc_r.bits < 2 ^ 32) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "pointer Offset out of bounds")) :=
  step_binOp_offset_move_scalar_nonzero_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hpt hrhs_ty hop_rhs himm_ptr hslot_p ha_rhs hrhs_pos hrhs_lt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hwt : WellTypedLM3_1StateTerminator body m bb) :
    StepObsRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_lm3_1_state_simulation hstate hphase hbb hstmt_none hstmt_len hwt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hloc :
      (∃ stmt, get? bb.statements s.frame.stmtIdx = some stmt ∧
        WellTypedLM3_1StateStmt body s m allocMap stmt) ∨
      (get? bb.statements s.frame.stmtIdx = none ∧
        s.frame.stmtIdx = length bb.statements ∧
        WellTypedLM3_1StateTerminator body m bb))
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    ∃ allocMap' : List AllocMapEntry,
      StepObsRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_mir_lm3_1_state_simulation hstate hphase hbb hloc hsupply

example :
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (eqRes : Bool),
      let b := Witness.lm31RawPtrCmpScalarPtrBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.boolTyLM31 Witness.rawPtrConstU64Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool eqRes)))))) ∧
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := Witness.lm31RawPtrCmpMoveUbBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.u64Ty
        Witness.lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg))) ∧
    (∃ (m₁ : AnnealStepState),
      let b := Witness.lm31MoveNullOffsetNonzeroBody
      let s₀ := Witness.mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := Witness.mkFourLocalScalarMiriPre b Witness.u64Ty Witness.rawPtrConstU8Ty
        Witness.lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .unsupported ∧
      Miri.Interpreter.Step.step hooks () m₀ =
        (m₁, .error (.undefinedBehavior "pointer Offset out of bounds"))) :=
  Witness.wit_lm3_1_cmp_symm_move_ub_and_unified_step_real_steps






/-! ### `LM-3.2` statement pins -/

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    ∀ l ∈ mls.layout, l = translateTy decl.ty layouts :=
  LocalRelLM3_2.cachedLayout_eq h

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (e : AllocMapEntry) {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_2 mach (e :: allocMap) decl layouts slot mls :=
  LocalRelLM3_2.mono_cons e h

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (halloc : ∀ e, (f e).allocId = e.allocId)
    {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_2 mach (allocMap.map f) decl layouts slot mls :=
  LocalRelLM3_2.map_preserve f htag halloc h

open Trusted.Rustc.V2026_06_01.Layout in
example {mach mach' : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_2 mach' allocMap decl layouts slot mls :=
  LocalRelLM3_2.of_live_base hlive hbase h

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {lay : Option Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot ⟨.live (.indirect mp), lay⟩) :
    LocalRelLM3_1 mach allocMap decl layouts slot ⟨.live (.indirect mp), lay⟩ :=
  LocalRelLM3_2.indirect_base h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine}
    {allocMap : List AllocMapEntry} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_1 body mach allocMap af mf) :
    FrameRelLM3_2 body mach allocMap af mf :=
  FrameRelLM3_1.toLM3_2 h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (h : StateRelLM3_1 body s m allocMap) :
    StateRelLM3_2 body s m allocMap :=
  StateRelLM3_1.toLM3_2 h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_1 body m allocMap aRes mRes) :
    StepRelLM3_2 body m allocMap aRes mRes :=
  StepRelLM3_1.toLM3_2 h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine}
    {allocMap : List AllocMapEntry} {af : StackFrame}
    {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_2 body mach allocMap af mf)
    (hnoref : ∀ i decl, get? body.localDecls i = some decl →
      ∀ mutability pointeeKind, decl.ty.kind ≠ .ref mutability pointeeKind) :
    FrameRelLM3_1 body mach allocMap af mf :=
  FrameRelLM3_2.toLM3_1 h hnoref

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (h : StateRelLM3_2 body s m allocMap)
    (hnoref : ∀ i decl, get? body.localDecls i = some decl →
      ∀ mutability pointeeKind, decl.ty.kind ≠ .ref mutability pointeeKind) :
    StateRelLM3_1 body s m allocMap :=
  StateRelLM3_2.toLM3_1 h hnoref

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf)
    {idx : Nat} {decl : MirAst.LocalDecl}
    (hdecl : get? body.localDecls idx = some decl) :
    ∃ (slot : LocalSlot) (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (_ : idx < af.locals.length) (hlt_mf : idx < mf.locals.size),
      get? af.locals idx = some slot ∧
      mf.locals[idx]? = some mls ∧
      mf.locals[idx]'hlt_mf = mls ∧
      LocalRelLM3_2 mach allocMap decl body.layouts slot mls :=
  FrameRelLM3_2.lookup_local hfr hdecl

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf)
    {idx : Nat} {decl : MirAst.LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < mf.locals.size) :
    FrameRelLM3_2 body mach allocMap af
      (cacheFrameLocalLayout mf idx hlt (translateTy decl.ty body.layouts)) :=
  FrameRelLM3_2.cache_local_layout hfr hdecl hlt

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (e : AllocMapEntry)
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach (e :: allocMap) af mf :=
  FrameRelLM3_2.mono_cons e hfr

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach mach' : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach' allocMap af mf :=
  FrameRelLM3_2.of_live_base hlive hbase h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM3_2 body mach allocMap af mf)
    {idx : Nat} {decl : MirAst.LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRelLM3_2 mach allocMap decl body.layouts newSlot
      { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM3_2 body mach allocMap
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } :=
  FrameRelLM3_2.update_local hrel hdecl newSlot newVal hnew

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf)
    {j : Nat} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hj : mf.locals[j]? = some ⟨.live (.indirect mp), lay⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList :=
  FrameRelLM3_2.indirect_allocId hfr hj

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach allocMap
      { af with stmtIdx := Nat.add af.stmtIdx 1 }
      { mf with location := .mir ⟨af.blockIdx, af.stmtIdx + 1⟩ } :=
  FrameRelLM3_2.advance h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    FrameRelLM3_2 body m.machine allocMap s.frame tf :=
  StateRelLM3_2.frame_rel_singleton hstate hframes

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} {decl : MirAst.LocalDecl} (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < tf.locals.size) :
    StateRelLM3_2 body s
      { m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt
          (translateTy decl.ty body.layouts)]⟩ }
      allocMap :=
  StateRelLM3_2.cache_layout hstate hframes hdecl hlt

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Local} {slot : LocalSlot}
    (hslot : get? s.frame.locals idx = some slot)
    (hne_dead : slot ≠ .dead)
    (himm : IsImmediateFrameLocal tf idx) :
    ∀ e ∈ allocMap, e.localIdx ≠ idx :=
  StateRelLM3_2.immediate_not_in_allocMap hstate hframes hslot hne_dead himm

open Trusted.Rustc.V2026_06_01.Layout in
example (id : Miri.Memory.AllocId) (offsetBytes : Nat)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32) :
    (annealStackBaseAddr id + UInt64.ofNat offsetBytes == 0) = false :=
  annealStackBaseAddr_add_ne_zero id offsetBytes hid hoff

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == id) = some (id, localAlloc))
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63)
    (hinbounds : offsetBytes + pointeeLay.layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (haligned : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes))
      pointeeLay.layout.align.abi = .ok none) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .ok ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
        some (.concrete id borTag)⟩, .none, none⟩ :=
  annealSafeRefDerefCheck_live_ok id borTag offsetBytes pointeeLay localAlloc hid hoff hbase hlive hsz hpos hfit hinbounds haligned

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hdead : mach.memory.live.find? (fun entry => entry.1 == id) = none)
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .error (.undefinedBehavior "dereferencing a dangling reference") :=
  annealSafeRefDerefCheck_dead_err id borTag offsetBytes pointeeLay hid hoff hbase hdead hsz hpos hfit

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == id) = some (id, localAlloc))
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63)
    (hoob : localAlloc.allocation.byteSize.bytes.toNat <
      offsetBytes + pointeeLay.layout.size.bytes.toNat) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .error (.undefinedBehavior "dereferencing a dangling reference") :=
  annealSafeRefDerefCheck_oob_err id borTag offsetBytes pointeeLay localAlloc hid hoff hbase hlive hsz hpos hfit hoob

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat) (pointeeLay : Miri.Interpreter.LocalLayout)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == id) = some (id, localAlloc))
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63)
    (hinbounds : offsetBytes + pointeeLay.layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes))
      pointeeLay.layout.align.abi = .ok (some mis)) :
    annealSafeRefDerefCheck mach
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            .concrete id borTag⟩))
        pointeeLay =
      .error (.undefinedBehavior "dereferencing an unaligned reference") :=
  annealSafeRefDerefCheck_misaligned_err id borTag offsetBytes pointeeLay localAlloc hid hoff hbase hlive hsz hpos hfit hinbounds hmis

open Trusted.Rustc.V2026_06_01.Layout in
example (mach : AnnealMachine) (pointeeLay : Miri.Interpreter.LocalLayout)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8) (h0 : sc.bits = 0) :
    annealSafeRefDerefCheck mach (.scalar (Miri.Memory.Scalar.fromScalarInt msc)) pointeeLay =
      .error (.undefinedBehavior "dereferencing a null reference") :=
  annealSafeRefDerefCheck_int_null_err mach pointeeLay hrel hsz8 h0

open Trusted.Rustc.V2026_06_01.Layout in
example (mach : AnnealMachine) (pointeeLay : Miri.Interpreter.LocalLayout)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8) (hne : sc.bits ≠ 0)
    (hsz : Miri.Memory.sizeAsI64 pointeeLay.layout.size =
      .ok (pointeeLay.layout.size.bytes.toNat : Int))
    (hpos : 0 < pointeeLay.layout.size.bytes.toNat)
    (hfit : (pointeeLay.layout.size.bytes.toNat : Int) < 2 ^ 63) :
    annealSafeRefDerefCheck mach (.scalar (Miri.Memory.Scalar.fromScalarInt msc)) pointeeLay =
      .error (.undefinedBehavior "dereferencing a dangling reference") :=
  annealSafeRefDerefCheck_int_dangling_err mach pointeeLay hrel hsz8 hne hsz hpos hfit

open Trusted.Rustc.V2026_06_01.Layout in
example {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    {imm : Miri.Interpreter.Immediate AnnealProv}
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate imm))
    (lay : Miri.Interpreter.LocalLayout) :
    annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ m =
      .ok (.immediate imm) m :=
  annealValidityPlaceOperand_local hframes hlt hval lay

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty) {ty : Ty}
    (st : AnnealStepState) :
    (ty.kind = .bool →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .boolean st) ∧
    (ty.kind = .char →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .character st) ∧
    (∀ it, ty.kind = .int it →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (∀ ut, ty.kind = .uint ut →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .integer st) ∧
    (ty.kind = .never →
      annealValidityClassify layouts c (translateTy ty layouts).ty st = .ok .never st) :=
  annealValidityClassify_prim layouts c st

open Trusted.Rustc.V2026_06_01.Layout in
example {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz1 : sc.sizeBytes = 1) :
    (∃ b, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b) ↔
      (sc.bits = 0 ∨ sc.bits = 1) :=
  fromScalarInt_toBool_ok_iff hrel hsz1

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    {sc : Miri.Memory.Scalar AnnealProv}
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate (.scalar sc)))
    (lay : Miri.Interpreter.LocalLayout) (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.local 0 idx none tf.localsIdentity, lay⟩ ev m =
      .ok ⟨.scalar sc, lay⟩ m :=
  annealValidityHooks_readImmediate_local layouts c hframes hlt hval lay ev

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty) {ty : Ty}
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt} (hrel : ScalarRel sc msc)
    (hsz : (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))))
    (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c
        ⟨.local 0 idx none tf.localsIdentity, translateTy ty layouts⟩ ev m =
      .ok ⟨.scalar (.fromScalarInt msc), translateTy ty layouts⟩ m ∧
    (ty.kind = .bool →
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .boolean m ∧
      ((∃ b, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBool = .ok b) ↔
        AnnealScalarValid ty sc)) ∧
    (ty.kind = .char →
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .character m) ∧
    ((∃ it, ty.kind = .int it) ∨ (∃ ut, ty.kind = .uint ut) →
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .integer m ∧
      AnnealScalarValid ty sc) ∧
    (ty.kind = .never →
      annealValidityClassify layouts c (translateTy ty layouts).ty m = .ok .never m) :=
  validityVisitor_scalar_bool_simulation layouts c hrel hsz hframes hlt hval ev

open Trusted.Rustc.V2026_06_01.Layout in
example {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b :=
  mem_eq_of_map_nodup

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} {allocMap : List AllocMapEntry}
    (halloc : AllocMapRel body s m allocMap)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr) {e : AllocMapEntry} (he : e ∈ allocMap)
    (htag : e.tag = p.tag) :
    ∃ borTag, mptr =
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes),
        .concrete e.allocId borTag⟩ ∧ p.offsetBytes < 2 ^ 32 :=
  PtrRel.allocId_of_entry halloc hptr he htag

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty)
    (m : AnnealStepState) (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (size : Miri.ABI.Size) :
    (annealValidityHooks layouts).checkPointerAccess c ptr size m =
      .ok (annealValidityAccessCheck m.machine ptr size) m :=
  annealValidityHooks_checkPointerAccess_eq layouts c m ptr size

open Trusted.Rustc.V2026_06_01.Layout in
example (mach : AnnealMachine)
    (id : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag) (offsetBytes : Nat)
    (size : Miri.ABI.Size)
    (hid : id.value.toNat < 2 ^ 32) (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr id = some (annealStackBaseAddr id))
    (hsz : Miri.Memory.sizeAsI64 size = .ok (size.bytes.toNat : Int))
    (hpos : 0 < size.bytes.toNat) (hfit : (size.bytes.toNat : Int) < 2 ^ 63) :
    (∀ localAlloc, mach.memory.live.find? (fun entry => entry.1 == id) =
        some (id, localAlloc) →
      offsetBytes + size.bytes.toNat ≤ localAlloc.allocation.byteSize.bytes.toNat →
      annealValidityAccessCheck mach
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            some (.concrete id borTag)⟩ size = .ok ()) ∧
    (∀ localAlloc, mach.memory.live.find? (fun entry => entry.1 == id) =
        some (id, localAlloc) →
      localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + size.bytes.toNat →
      ∃ err, annealValidityAccessCheck mach
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            some (.concrete id borTag)⟩ size = .error err) ∧
    (mach.memory.live.find? (fun entry => entry.1 == id) = none →
      ∃ err, annealValidityAccessCheck mach
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id + UInt64.ofNat offsetBytes),
            some (.concrete id borTag)⟩ size = .error err) :=
  annealValidityAccessCheck_stack mach id borTag offsetBytes size hid hoff hbase hsz hpos hfit

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr) (hoff0 : p.offsetBytes = 0)
    {e : AllocMapEntry} (he : e ∈ allocMap) (htag : e.tag = p.tag)
    {targetDecl : MirAst.LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut targetDecl.ty.kind) :
    (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead →
      annealValidityPointeeLayout body.layouts refTy =
        some (translateTy targetDecl.ty body.layouts) ∧
      (annealValidityHooks body.layouts).checkPointerAccess refTy mptr.withOptionalProvenance
          (translateTy targetDecl.ty body.layouts).layout.size m = .ok (.ok ()) m ∧
      (annealValidityHooks body.layouts).checkPointerAlignResult refTy
          mptr.withOptionalProvenance
          (translateTy targetDecl.ty body.layouts).layout.align.abi m = .ok (.ok ()) m ∧
      annealSafeRefDerefCheck m.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (translateTy targetDecl.ty body.layouts) =
        .ok ⟨mptr.withOptionalProvenance, .none, none⟩) ∧
    (get? s.frame.locals e.localIdx = some .dead →
      (∃ err, (annealValidityHooks body.layouts).checkPointerAccess refTy
          mptr.withOptionalProvenance
          (translateTy targetDecl.ty body.layouts).layout.size m = .ok (.error err) m) ∧
      annealSafeRefDerefCheck m.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (translateTy targetDecl.ty body.layouts) =
        .error (.undefinedBehavior "dereferencing a dangling reference") ∧
      ∀ refIdx, get? s.frame.locals refIdx = some (.init (.ptr p 8)) →
        evalOperand s.frame.locals (.copy ⟨refIdx, .cons .deref .nil⟩) s.memory.borrows
          s.memory.globals body.layouts s.memory.callerLocals = .ub) :=
  validityVisitor_ref_dereferenceable_simulation hstate hptr hoff0 he htag hdecl_t hrefTy

open Trusted.Rustc.V2026_06_01.Layout in
example (s : MachineState) (localDecls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (targetIdx : Local) (slot : LocalSlot)
    (hslot : get? s.frame.locals targetIdx = some slot)
    (hlive : slot ≠ .dead) :
    let perm : TreeBorrowPerm := refBorrowPerm localDecls layouts bk targetIdx
    let entry : BorrowEntry :=
      { tag := s.memory.nextTag
        targetLocal := targetIdx
        targetProjection := .nil
        perm := perm }
    evalRvalue s.frame.locals (.ref bk ⟨targetIdx, .nil⟩) s.memory localDecls layouts =
      .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)
        s.frame.locals
        { s.memory with
          borrows := .cons entry s.memory.borrows
          nextTag := s.memory.nextTag + 1 } :=
  evalRvalue_ref_live_eq s localDecls layouts bk targetIdx slot hslot hlive

open Trusted.Rustc.V2026_06_01.Layout in
example (s : MachineState) (localDecls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (bk : BorrowKind) (targetIdx : Local)
    (hdead : get? s.frame.locals targetIdx = some .dead) :
    evalRvalue s.frame.locals (.ref bk ⟨targetIdx, .nil⟩) s.memory localDecls layouts =
      .ub :=
  evalRvalue_ref_dead_eq s localDecls layouts bk targetIdx hdead

open Trusted.Rustc.V2026_06_01.Layout in
example {ld : List MirAst.LocalDecl} {ly : LayoutTable} {region : Miri.MIR.Region}
    {borrow : Miri.MIR.BorrowKind}
    {dst src : Miri.MIR.Place} {m m₁ m₂ m₃ : AnnealStepState}
    {dest srcPlace : Miri.Interpreter.RuntimePlace AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hdst : annealEvalPlace ld ly dst m = .ok dest m₁)
    (hsrc : annealEvalPlace ld ly src m₁ = .ok srcPlace m₂)
    (hforce : annealForceAllocation ld ly srcPlace m₂ = .ok mp m₃)
    (href : mp.toRef annealTargetDataLayout = .ok imm) :
    Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks ld ly) ()
        (.Ref region borrow src) dst m =
      annealWriteImmediate imm dest m₃ :=
  evalRvalueIntoPlace_ref_ok hdst hsrc hforce href

open Trusted.Rustc.V2026_06_01.Layout in
example {ld : List MirAst.LocalDecl} {ly : LayoutTable} {region : Miri.MIR.Region}
    {borrow : Miri.MIR.BorrowKind}
    {dst src : Miri.MIR.Place} {m m₁ m₂ m₃ : AnnealStepState}
    {dest srcPlace : Miri.Interpreter.RuntimePlace AnnealProv}
    {err : Miri.Interpreter.StepError}
    (hdst : annealEvalPlace ld ly dst m = .ok dest m₁)
    (hsrc : annealEvalPlace ld ly src m₁ = .ok srcPlace m₂)
    (hforce : annealForceAllocation ld ly srcPlace m₂ = .error err m₃) :
    Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks ld ly) ()
        (.Ref region borrow src) dst m =
      .error err m₃ :=
  evalRvalueIntoPlace_ref_force_error hdst hsrc hforce

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {bk : BorrowKind} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl} {refMut : Mutability} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .ref refMut pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    StepRelLM3_2 body m
      (refAllocMapEntry body.localDecls body.layouts bk targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_ref_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm hsupply

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine}
    {allocMap : List AllocMapEntry} {decl : MirAst.LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hty : decl.ty.kind = .rawPtr mutability pointeeKind)
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalRelLM3_1 mach allocMap decl layouts slot mls :=
  LocalRelLM3_2.toLM3_1_of_rawPtr hty h

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {refDecl : MirAst.LocalDecl} {layouts : LayoutTable}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    {slot_p : LocalSlot}
    {mls_p : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hloc : LocalRelLM3_2 mach allocMap refDecl layouts slot_p mls_p)
    (hnot_ind : ∀ mp, mls_p.value ≠ .live (.indirect mp)) :
    (slot_p = .dead ∧ mls_p.value = .dead) ∨
    (slot_p = .uninit ∧ mls_p.value = .live (.immediate .uninit)) ∨
    (∃ sc msc, slot_p = .init (.scalar sc) ∧ sc.sizeBytes = 8 ∧ ScalarRel sc msc ∧
      mls_p.value = .live (.immediate (.scalar (.fromScalarInt msc)))) ∨
    (∃ ptrVal mptr, slot_p = .init (.ptr ptrVal 8) ∧ PtrRel allocMap ptrVal mptr ∧
      mls_p.value = .live (.immediate (.scalar
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))) :=
  LocalRelLM3_2.ref_immediate_cases hty hloc hnot_ind

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hzero_perm : ∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared)) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? s.frame.locals dstIdx ≠ some .dead →
      (∃ s', stepMirFn body s = .step s' ∧
        get? s'.frame.locals dstIdx =
          some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
      ∃ m' tf' borTag,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧ m'.machine = m.machine ∧
        (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                .concrete e.allocId borTag⟩))))) :=
  evalRvalue_reborrow_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hno_int hzero_perm

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hzero_perm : ∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared))
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    {targetDecl : MirAst.LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩)))) ∧
      (∃ err, annealValidityAccessCheck m'.machine
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId), some (.concrete e.allocId borTag)⟩
        (translateTy targetDecl.ty body.layouts).layout.size = .error err) ∧
      annealSafeRefDerefCheck m'.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩))
          (translateTy targetDecl.ty body.layouts) =
        .error (.undefinedBehavior "dereferencing a dangling reference") :=
  evalRvalue_reborrow_dangling_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hno_int hzero_perm hslot_p he htag hdead_t hdst_live hdecl_t

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .disabled ∨ (e.perm = .frozen ∧ bk ≠ .shared)) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              .concrete e.allocId borTag⟩)))) :=
  evalRvalue_reborrow_perm_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p he htag hperm

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    StateRel lm32RefBody lm32RefAnnealPre lm32RefMiriPre :=
  Witness.lm32Ref_stateRel_pre

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∀ topFrame, lm32RefMiriPre.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame 2 ∧ IsImmediateFrameLocal topFrame 1 :=
  Witness.lm32Ref_immediate_pre

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s' : MachineState) (m' : AnnealStepState),
      stepMirFn lm32RefBody lm32RefAnnealPre = .step s' ∧
      Miri.Interpreter.Step.step
          (annealStepHooks lm32RefBody.localDecls lm32RefBody.layouts) ()
          lm32RefMiriPre = (m', .ok true) ∧
      StateRelLM3_2 lm32RefBody s' m'
        [refAllocMapEntry lm32RefBody.localDecls lm32RefBody.layouts .shared 1 1
          lm31AllocId1] :=
  Witness.wit_lm3_2_ref_step

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    lm32Validate boolTyLM32 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 1))) =
      .ok () (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 1)))) ∧
    (∃ msg, lm32Validate boolTyLM32 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))))) ∧
    lm32Validate charTyLM32 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0x41))) =
      .ok () (lm32ValidityState
        (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0x41)))) ∧
    (∃ msg, lm32Validate charTyLM32
        (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0xD800))) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 0xD800))))) ∧
    (∃ msg, lm32Validate neverTyLM32 .uninit =
      .error (.undefinedBehavior msg) (lm32ValidityState .uninit)) ∧
    (∃ msg, lm32Validate refU64Ty
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
            .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩)) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
            .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩)))) ∧
    (∃ msg, lm32Validate refU64Ty (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0))) =
      .error (.undefinedBehavior msg)
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0))))) :=
  Witness.wit_lm3_2_validity_visitor_runs

open Trusted.Rustc.V2026_06_01.Layout in
example {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz4 : sc.sizeBytes = 4) :
    (∃ c, (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toChar = .ok c) ↔
      isValidCharCode sc.bits = true :=
  fromScalarInt_toChar_ok_iff hrel hsz4

open Trusted.Rustc.V2026_06_01.Layout in
example {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hdead : (tf.locals[idx]'hlt).value = .dead)
    (lay : Miri.Interpreter.LocalLayout) :
    annealValidityPlaceOperand ⟨.local 0 idx none tf.localsIdentity, lay⟩ m =
      .error (.undefinedBehavior "validation of a dead local") m :=
  annealValidityPlaceOperand_dead_local hframes hlt hdead lay

open Trusted.Rustc.V2026_06_01.Layout in
example {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    annealValidityPlaceOperand ⟨.memory mp, lay⟩ m =
      .ok (.indirect mp) m :=
  annealValidityPlaceOperand_memory hframes mp lay

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate .uninit))
    (lay : Miri.Interpreter.LocalLayout) (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.local 0 idx none tf.localsIdentity, lay⟩ ev m =
      .error (.undefinedBehavior "read of uninitialized local") m :=
  annealValidityHooks_readImmediate_uninit_local layouts c hframes hlt hval lay ev

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size)
    (hdead : (tf.locals[idx]'hlt).value = .dead)
    (lay : Miri.Interpreter.LocalLayout) (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.local 0 idx none tf.localsIdentity, lay⟩ ev m =
      .error (.undefinedBehavior "validation of a dead local") m :=
  annealValidityHooks_readImmediate_dead_local layouts c hframes hlt hdead lay ev

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout)
    (hfields : lay.layout.fields = .Primitive)
    (ev : Miri.Memory.ExpectedValue) :
    (annealValidityHooks layouts).readImmediate c ⟨.memory mp, lay⟩ ev m =
      annealReadMemoryPlace mp lay m :=
  annealValidityHooks_readImmediate_memory layouts c hframes mp lay hfields ev

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable)
    {A : Type} (action : Miri.Interpreter.ValidityVisitor.M AnnealStepState A) :
    (annealValidityHooks layouts).withGhostValidation action = action :=
  annealValidityHooks_withGhostValidation_eq layouts action

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty) (tyId : Miri.MIR.TyId) :
    (annealValidityHooks layouts).typeName c tyId = pure "" :=
  annealValidityHooks_typeName_eq layouts c tyId

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) (c : Ty) (fuel : Nat)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState) :
    let initSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := ⟨"", #[]⟩
        flags := ⟨false, false⟩
        ctfeMode := none
        refTracking := none
        dataBytes := none }
    (∀ session' m',
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks layouts) c fuel initSession place m =
        .ok session' m' →
      session'.dataBytes = none →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) c fuel place
          false false m =
        .ok () m') ∧
    (∀ err m',
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks layouts) c fuel initSession place m =
        .error err m' →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) c fuel place
          false false m =
        .error err m') :=
  validatePlace_annealValidityHooks_nonrecursive_eq layouts c fuel place m

open Trusted.Rustc.V2026_06_01.Layout in
example (h : Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState Ty Unit Unit Unit Unit)
    (c : Ty) (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session AnnealProv)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState)
    (hreset : session.flags.resetProvenanceAndPadding = false) :
    (h.classify c place.layout.ty m = .ok .never m →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
        .error (.undefinedBehavior s!"validation{session.path.render}: {"never value"}") m) ∧
    (∀ kind, (kind = .boolean ∨ kind = .character ∨ kind = .integer) →
      h.classify c place.layout.ty m = .ok kind m →
      ∀ err,
        h.readImmediate c place
            (match kind with | .boolean => .boolean | .character => .character | _ => .integer) m =
          .error err m →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error err m) ∧
    (h.classify c place.layout.ty m = .ok .integer m →
      ∀ sc, h.readImmediate c place .integer m = .ok ⟨.scalar sc, place.layout⟩ m →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
        .ok session m) ∧
    (h.classify c place.layout.ty m = .ok .boolean m →
      ∀ sc, h.readImmediate c place .boolean m = .ok ⟨.scalar sc, place.layout⟩ m →
      (∀ b, sc.toBool = .ok b →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .ok session m) ∧
      (∀ err, sc.toBool = .error err →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error (.undefinedBehavior s!"validation{session.path.render}: {repr err}") m)) ∧
    (h.classify c place.layout.ty m = .ok .character m →
      ∀ sc, h.readImmediate c place .character m = .ok ⟨.scalar sc, place.layout⟩ m →
      (∀ ch, sc.toChar = .ok ch →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .ok session m) ∧
      (∀ err, sc.toChar = .error err →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error (.undefinedBehavior s!"validation{session.path.render}: {repr err}") m)) :=
  visit_primitive_cases h c fuel session place m hreset

open Trusted.Rustc.V2026_06_01.Layout in
example (h : Miri.Interpreter.ValidityVisitor.Hooks AnnealProv AnnealStepState Ty Unit Unit Unit Unit)
    (c : Ty) (fuel : Nat) (session : Miri.Interpreter.ValidityVisitor.Session AnnealProv)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState)
    (mutBool : Bool)
    (hcl : h.classify c place.layout.ty m = .ok (.reference mutBool) m)
    (hreset : session.flags.resetProvenanceAndPadding = false)
    (hmd : session.flags.mayDangle = false)
    (hctfe : session.ctfeMode = none) :
    (∀ err, h.readImmediate c place .reference m = .error err m →
      Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
        .error err m) ∧
    (∀ ptrImm ptPlace,
      h.readImmediate c place .reference m = .ok ptrImm m →
      h.ptrToPlace c ptrImm m = .ok ptPlace m →
      ptPlace.layout.layout.isSized = true →
      h.sizeAndAlign c ptPlace m =
        .ok (some (ptPlace.layout.layout.size, ptPlace.layout.layout.align.abi)) m →
      (∀ accErr,
        h.checkPointerAccess c ptPlace.mplace.ptr ptPlace.layout.layout.size m =
          .ok (.error accErr) m →
        Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
          .error (Miri.Interpreter.ValidityVisitor.classifyPointerAccessError
            session.path (.reference mutBool) accErr) m) ∧
      (∀ sc,
        h.checkPointerAccess c ptPlace.mplace.ptr ptPlace.layout.layout.size m =
          .ok (.ok ()) m →
        Miri.Memory.Scalar.fromMaybePointer h.target.base ptPlace.mplace.ptr = .ok sc →
        (h.scalarMayBeNull c sc m = .ok true m →
          Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
            .error (.undefinedBehavior
              s!"validation{session.path.render}: {"null or maybe-null safe pointer"}") m) ∧
        (h.scalarMayBeNull c sc m = .ok false m →
          (h.opsemInhabited c ptPlace.layout.ty m = .ok false m →
            Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
              .error (.undefinedBehavior
                s!"validation{session.path.render}: {"safe pointer to uninhabited type"}") m) ∧
          (h.opsemInhabited c ptPlace.layout.ty m = .ok true m →
            (∀ mis,
              h.checkPointerAlignResult c ptPlace.mplace.ptr
                  ptPlace.layout.layout.align.abi m = .ok (.error mis) m →
              Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
                .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
                  session.path (.reference mutBool) mis) m) ∧
            (h.checkPointerAlignResult c ptPlace.mplace.ptr
                ptPlace.layout.layout.align.abi m = .ok (.ok ()) m →
              Miri.Interpreter.ValidityVisitor.visit h c (fuel + 1) session place m =
                .ok { session with
                  refTracking := session.refTracking.map fun tracker =>
                    tracker.track ⟨ptPlace.mplace, ptPlace.layout⟩
                      (fun _ => session.path.push .deref) } m))))) :=
  visit_reference_cases h c fuel session place m mutBool hcl hreset hmd hctfe

open Trusted.Rustc.V2026_06_01.Layout in
example (layouts : LayoutTable) {ty : Ty} (fuel : Nat)
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) {idx : Nat} (hlt : idx < tf.locals.size) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 idx none tf.localsIdentity, translateTy ty layouts⟩
    (ty.kind = .never →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
        place false false m =
        .error (.undefinedBehavior "validation: never value") m) ∧
    (IsPrimScalarTy ty →
      (tf.locals[idx]'hlt).value = .dead →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
        place false false m =
        .error (.undefinedBehavior "validation of a dead local") m) ∧
    (IsPrimScalarTy ty →
      (tf.locals[idx]'hlt).value = .live (.immediate .uninit) →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
        place false false m =
        .error (.undefinedBehavior "read of uninitialized local") m) ∧
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      IsPrimScalarTy ty →
      ScalarRel sc msc →
      (translateTy ty layouts).layout.size = translateSizeBytes sc.sizeBytes →
      (tf.locals[idx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))) →
      (Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty (fuel + 1)
          place false false m = .ok () m ↔ AnnealScalarValid ty sc) ∧
      ((∃ msg, Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks layouts) ty
          (fuel + 1) place false false m = .error (.undefinedBehavior msg) m) ↔
        ¬ AnnealScalarValid ty sc)) :=
  validatePlace_prim_scalar_simulation layouts fuel hframes hlt

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {targetTy : Ty} (hprim : IsPrimScalarTy targetTy)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut targetTy.kind)
    (fuel : Nat) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    ((tf.locals[refIdx]'hlt).value = .dead →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
        (fuel + 1) place false false m =
        .error (.undefinedBehavior "validation of a dead local") m) ∧
    ((tf.locals[refIdx]'hlt).value = .live (.immediate .uninit) →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
        (fuel + 1) place false false m =
        .error (.undefinedBehavior "read of uninitialized local") m) ∧
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      ScalarRel sc msc → sc.sizeBytes = 8 →
      (tf.locals[refIdx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))) →
      (sc.bits = 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior "validation: encountered a null reference") m) ∧
      (sc.bits ≠ 0 →
        ∃ msg, Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m = .error (.undefinedBehavior msg) m)) ∧
    (∀ {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry},
      PtrRel allocMap p mptr → e ∈ allocMap → e.tag = p.tag →
      (∃ d, get? body.localDecls e.localIdx = some d ∧ d.ty = targetTy) →
      (tf.locals[refIdx]'hlt).value =
        .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))) →
      (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead → p.offsetBytes = 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m = .ok () m) ∧
      (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead → 0 < p.offsetBytes →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior
            "validation: encountered a dangling reference (going beyond the bounds of its allocation)") m) ∧
      (get? s.frame.locals e.localIdx = some .dead →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior
            "validation: encountered a dangling reference (use-after-free)") m)) :=
  validatePlace_ref_nonrecursive_simulation hstate hframes hlt hprim hrefTy fuel

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (hptr : PtrRel allocMap p mptr) (hoff0 : p.offsetBytes = 0)
    {e : AllocMapEntry} (he : e ∈ allocMap) (htag : e.tag = p.tag)
    {targetDecl : MirAst.LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    (hprim : IsPrimScalarTy targetDecl.ty)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut targetDecl.ty.kind)
    (hval : (tf.locals[refIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    {slot : LocalSlot} (hslot : get? s.frame.locals e.localIdx = some slot)
    (hne_dead : slot ≠ .dead) (fuel : Nat) :
    let rootPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    let rootSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := ⟨"", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := some .empty, dataBytes := none }
    let ptKey : Miri.Interpreter.ValidityVisitor.Key AnnealProv :=
      ⟨⟨mptr.withOptionalProvenance, .none, none⟩, translateTy targetDecl.ty body.layouts⟩
    let childPath : Miri.Memory.ValidationPath := ⟨"", #[.deref]⟩
    let tracked : Miri.Memory.Validity.RefTracking
        (Miri.Interpreter.ValidityVisitor.Key AnnealProv) Miri.Memory.ValidationPath :=
      ⟨#[ptKey], #[(ptKey, childPath)]⟩
    let childSession : Miri.Interpreter.ValidityVisitor.Session AnnealProv :=
      { path := childPath, flags := ⟨false, true⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    let childPlace : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.memory ptKey.mplace, ptKey.layout⟩
    Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts) refTy (fuel + 1)
        rootSession rootPlace m =
      .ok { rootSession with refTracking := some tracked } m ∧
    tracked.next = some ((ptKey, childPath), ⟨#[ptKey], #[]⟩) ∧
    (slot = .uninit →
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts) refTy (fuel + 1)
        childSession childPlace m =
        .error (.undefinedBehavior "read of uninitialized memory") m) ∧
    (∀ sc, slot = .init (.scalar sc) →
      AnnealScalarValid targetDecl.ty sc ∧
      Miri.Interpreter.ValidityVisitor.visit (annealValidityHooks body.layouts) refTy (fuel + 1)
        childSession childPlace m = .ok childSession m) :=
  visit_ref_recursive_pointee_simulation hstate hframes hlt hptr hoff0 he htag hdecl_t hprim hrefTy hval hslot hne_dead fuel

open Trusted.Rustc.V2026_06_01.Layout in
example {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (ptrLay : Miri.Interpreter.LocalLayout) :
    lookupDerefPointeeLayout ld ly refIdx ptrLay = none :=
  lookupDerefPointeeLayout_safeRef_eq hdecl hty ptrLay

open Trusted.Rustc.V2026_06_01.Layout in
example {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 }) :
    lookupRefDerefPointeeLayout ld ly refIdx =
      some (translateTy { kind := pointeeKind, layoutIdx := 0 } ly) :=
  lookupRefDerefPointeeLayout_safeRef_eq hdecl hty hpk

open Trusted.Rustc.V2026_06_01.Layout in
example {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    annealDerefOperandToMemPlace ld ly refIdx (.immediate .uninit) ptrLay st =
      .error (.undefinedBehavior "read of uninitialized local") st :=
  annealDerefOperandToMemPlace_safeRef_uninit hdecl hty hpk ptrLay st

open Trusted.Rustc.V2026_06_01.Layout in
example {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    (sc.bits = 0 →
      annealDerefOperandToMemPlace ld ly refIdx (.immediate (.scalar (.fromScalarInt msc)))
        ptrLay st =
        .error (.undefinedBehavior "dereferencing a null reference") st) ∧
    (sc.bits ≠ 0 →
      annealDerefOperandToMemPlace ld ly refIdx (.immediate (.scalar (.fromScalarInt msc)))
        ptrLay st =
        .error (.undefinedBehavior "dereferencing a dangling reference") st) :=
  annealDerefOperandToMemPlace_safeRef_scalarInt hdecl hty hpk hrel hsz8 ptrLay st

open Trusted.Rustc.V2026_06_01.Layout in
example {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (mptr : Miri.Memory.Pointer AnnealProv)
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    annealDerefOperandToMemPlace ld ly refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      match annealSafeRefDerefCheck st.machine
          (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (translateTy { kind := pointeeKind, layoutIdx := 0 } ly) with
      | .ok mplace => .ok (mplace, translateTy { kind := pointeeKind, layoutIdx := 0 } ly) st
      | .error err => .error err st :=
  annealDerefOperandToMemPlace_safeRef_pointer_eq hdecl hty hpk mptr ptrLay st

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {bk : BorrowKind} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : MirAst.LocalDecl} {refMut : Mutability} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .ref refMut pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = targetIdx) :
    StepRelLM3_2 body m
      (refAllocMapEntry body.localDecls body.layouts bk targetIdx s.memory.nextTag
        e₀.allocId :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_ref_indirect_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm_dst he₀ he₀_loc

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {sc : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc))) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' msc,
      ScalarRel sc msc ∧ sc.sizeBytes = 8 ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) :=
  evalRvalue_reborrow_rawPtr_int_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry}
    (hptrRel : PtrRel allocMap ptrVal mptr)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead)
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .error (.undefinedBehavior "dereferencing a dangling reference") st :=
  annealDerefOperandToMemPlace_safeRef_ptr_dead hstate hdecl hty hpk hptrRel he htag hdead_t ptrLay hmach

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry} {borTag : Miri.Memory.BorTag}
    (hprov_eq : mptr.provenance = .concrete e.allocId borTag)
    (hmptr_off : mptr.offset =
      Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
    (he : e ∈ allocMap)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind)
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .ok (⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
            some (.concrete e.allocId borTag)⟩, .none, none⟩,
        translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts) st :=
  annealDerefOperandToMemPlace_safeRef_ptr_live hstate hdecl hty hpk hprov_eq hmptr_off he hoff0 hlive_t htgt_kind ptrLay hmach

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_zero_perm : ∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? s.frame.locals e.localIdx ≠ some .dead ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind)) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? s.frame.locals dstIdx ≠ some .dead →
      (∃ s', stepMirFn body s = .step s' ∧
        get? s'.frame.locals dstIdx =
          some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
      ∃ m' tf' borTag,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧ m'.machine = m.machine ∧
        (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                .concrete e.allocId borTag⟩))))) :=
  evalRvalue_reborrow_safeRef_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {refMut : Mutability} {pointeeKind : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared))
    (hdead_t : get? s.frame.locals e.localIdx = some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) :=
  evalRvalue_reborrow_safeRef_dangling_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ref href_ty hpk_prim himm_ref hdst_live hslot_r he htag hperm hdead_t

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {id : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {newMem : AnnealMemory}
    (hfind : mach.memory.live.find? (fun x => x.1 == id) = some (id, localAlloc))
    (hset : mach.memory.setLiveAllocation id alloc' = .ok newMem)
    {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls)
    (hne : ∀ mp, mls.value = .live (.indirect mp) →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    LocalRelLM3_2 { mach with memory := newMem } allocMap decl layouts slot mls :=
  LocalRelLM3_2.of_setLiveAllocation_ne hfind hset h hne

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (halloc : ∀ e, (f e).allocId = e.allocId)
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_2 body mach allocMap af mf) :
    FrameRelLM3_2 body mach (allocMap.map f) af mf :=
  FrameRelLM3_2.map_preserve f htag halloc hfr

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (hloc_idx : ∀ e, (f e).localIdx = e.localIdx)
    (halloc_id : ∀ e, (f e).allocId = e.allocId)
    {dstIdx : Local} {dstDecl : MirAst.LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {hlt_d : dstIdx < tf.locals.size}
    {oldImm newImm : Miri.Interpreter.Immediate AnnealProv}
    (hd_imm : (tf.locals[dstIdx]'hlt_d).value = .live (.immediate oldImm))
    {newSlot : LocalSlot}
    (hnew : LocalRelLM3_2 m.machine (allocMap.map f) dstDecl body.layouts newSlot
      { tf.locals[dstIdx]'hlt_d with value := .live (.immediate newImm) })
    {mem' : Memory}
    (hmem_cal : mem'.activeCallee = none)
    (hmem_stack : mem'.callStack = .nil)
    (hmem_prot : mem'.activeProtectors = .nil)
    (hmem_caller : mem'.callerLocals = .nil)
    (hmem_bor : mem'.borrows = (allocMap.map f).map AllocMapEntry.toBorrowEntry)
    (hmem_next : mem'.nextTag = s.memory.nextTag) :
    StateRelLM3_2 body
      (advanceStmt s (s.frame.locals.set dstIdx newSlot) mem')
      { m with stack := ⟨#[{ { tf with
          locals := tf.locals.set dstIdx
            { tf.locals[dstIdx]'hlt_d with value := .live (.immediate newImm) } hlt_d } with
          location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩ }
      (allocMap.map f) :=
  StateRelLM3_2.advance_write_immediate_perm_map hstate hframes f htag hloc_idx halloc_id hdecl_dst hnot_dst hd_imm hnew hmem_cal hmem_stack hmem_prot hmem_caller hmem_bor hmem_next

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {srcIdx : Local} {srcDecl : MirAst.LocalDecl}
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {slot_s : LocalSlot}
    (hslot_s : get? s.frame.locals srcIdx = some slot_s)
    (hne_dead : slot_s ≠ .dead)
    (himm_src : IsImmediateFrameLocal tf srcIdx)
    (hlt_s : srcIdx < tf.locals.size) :
    StateRelLM3_2 body
      { s with frame := { s.frame with locals := s.frame.locals.set srcIdx .uninit } }
      { m with stack := ⟨#[deinitFrameLocal tf srcIdx hlt_s]⟩ }
      allocMap :=
  StateRelLM3_2.deinit_immediate_local hstate hframes hdecl_src hslot_s hne_dead himm_src hlt_s

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : MirAst.LocalDecl} {srcMut dstMut : Mutability}
    {srcPointee dstPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_use_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_src hsrc_ty hdst_ty himm

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal, get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl →
            decl.ty.kind = dstDecl.ty.kind)) :
    StepRelLM3_2 body m (derefReadNextAllocMap s.frame.locals allocMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_read_simulation_explicit hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal, get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl →
            decl.ty.kind = dstDecl.ty.kind)) :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_read_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (f : AllocMapEntry → AllocMapEntry)
    (hf_tag : ∀ x, (f x).tag = x.tag)
    (hf_loc : ∀ x, (f x).localIdx = x.localIdx)
    (hf_aid : ∀ x, (f x).allocId = x.allocId)
    {e : AllocMapEntry} (he : e ∈ allocMap)
    {tgtDecl : MirAst.LocalDecl} (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_prim : IsPrimScalarTy tgtDecl.ty)
    {slot_t : LocalSlot} (hslot_t : get? s.frame.locals e.localIdx = some slot_t)
    (ht_ne_dead : slot_t ≠ .dead)
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hkind_la : localAlloc.kind = .stack)
    (halign_la : localAlloc.allocation.align =
      (translateTy tgtDecl.ty body.layouts).layout.align.abi)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel_sc : ScalarRel sc msc)
    (hsz_tgt : (translateTy tgtDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hbool_tgt : tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar_tgt : tgtDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (halign_alloc' : alloc'.align = localAlloc.allocation.align)
    (hshape_alloc' : StackScalarAllocShape (translateSizeBytes sc.sizeBytes) alloc')
    (hinit_alloc' : alloc'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()))
    (hread_alloc' : alloc'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
      .ok (.fromScalarInt msc)) :
    StateRelLM3_2 body
      (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
        { s.memory with
          borrows := (allocMap.map f).map AllocMapEntry.toBorrowEntry })
      { stack := ⟨#[{ tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩
        machine := { m.machine with
          memory := { m.machine.memory with
            live := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
              (e.allocId, ⟨localAlloc.kind, alloc'⟩) } } }
      (allocMap.map f) :=
  StateRelLM3_2.advance_write_deref_scalar hstate hframes f hf_tag hf_loc hf_aid he hdecl_tgt htgt_prim hslot_t ht_ne_dead hfind_la hkind_la halign_la hrel_sc hsz_tgt hbool_tgt hchar_tgt halign_alloc' hshape_alloc' hinit_alloc' hread_alloc'

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ m' msg,
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc tf',
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) s.frame.locals ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_2 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      ImmediateRel ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) ∧
      tf'.localsIdentity = tf.localsIdentity ∧
      (∀ (k : Nat), (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) :=
  evalOperand_scalar_lm3_2_simulation hstate hframes hop hprim known

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    StepRelLM3_2 body m (derefWriteNextAllocMap s.frame.locals allocMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_write_simulation_explicit hstate hphase hbb hstmt hdecl_ref href_ty hval_prim hval_kind hop himm_ref hlive_ref

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_write_simulation hstate hphase hbb hstmt hdecl_ref href_ty hval_prim hval_kind hop himm_ref hlive_ref

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value :=
  LocalRelLM3_2.allocLive h

open Trusted.Rustc.V2026_06_01.Layout in
example {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : MirAst.LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    (h : LocalRelLM3_2 mach allocMap decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    LocalRelLM3_2 { mach with memory := deallocLocalMemory mach.memory v }
      allocMap decl layouts slot mls :=
  LocalRelLM3_2.of_dealloc h hdisj

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_storageDead_lm3_2_simulation hstate hphase hbb hstmt hdecl hne0

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hnot_mapped : ∀ e ∈ allocMap, e.localIdx ≠ loc) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_storageLive_lm3_2_simulation hstate hphase hbb hstmt hdecl hnot_mapped

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example {st : AnnealStepState} {idx : Nat}
    (hchk : checkImmediateInTopFrame st idx = true) :
    ∀ topFrame, st.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame idx :=
  Witness.isImmediate_of_checkImmediateInTopFrame hchk

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let hooks := annealStepHooks lm32RefBody.localDecls lm32RefBody.layouts
      let entry := refAllocMapEntry lm32RefBody.localDecls lm32RefBody.layouts .shared 1 1
        lm31AllocId1
      stepMirFn lm32RefBody lm32RefAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32RefMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₁ m₁ [entry] ∧
      stepMirFn lm32RefBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₂ m₂ [entry] ∧
      get? s₂.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩)) ∧
      (m₂.stack.frames[0]?.bind (fun tf => (tf.locals[0]?).map Miri.Interpreter.LocalState.value)) =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar42)))) ∧
      stepMirFn lm32RefBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₃ m₃ [entry] ∧
      stepMirFn lm32RefBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 lm32RefBody s₄ m₄ [entry] ∧
      m₄.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none :=
  Witness.wit_lm3_2_ref_deref_read_storageDead_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    StateRel lm32MutRefChainBody lm32MutRefChainAnnealPre lm32MutRefChainMiriPre :=
  Witness.lm32MutRefChain_stateRel_pre

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (tf₅ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let hooks := annealStepHooks lm32MutRefChainBody.localDecls lm32MutRefChainBody.layouts
      let entry := refAllocMapEntry lm32MutRefChainBody.localDecls lm32MutRefChainBody.layouts
        (.mut false) 1 1 lm31AllocId1
      stepMirFn lm32MutRefChainBody lm32MutRefChainAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32MutRefChainMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₁ m₁ [entry] ∧
      stepMirFn lm32MutRefChainBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₂ m₂ [entry] ∧
      get? s₂.frame.locals 2 = some .uninit ∧
      stepMirFn lm32MutRefChainBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₃ m₃ [{ entry with perm := .active }] ∧
      stepMirFn lm32MutRefChainBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 lm32MutRefChainBody s₄ m₄ [{ entry with perm := .active }] ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      (m₄.stack.frames[0]?.bind (fun tf => (tf.locals[0]?).map Miri.Interpreter.LocalState.value)) =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99)))) ∧
      stepMirFn lm32MutRefChainBody s₄ = .step s₅ ∧
      get? s₅.frame.locals 4 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      m₅.stack.frames = #[tf₅] ∧
      (tf₅.locals[4]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩)))) :=
  Witness.wit_lm3_2_mut_ref_move_write_read_reborrow_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    StateRel lm32DanglingReborrowBody lm32DanglingReborrowAnnealPre lm32DanglingReborrowMiriPre :=
  Witness.lm32DanglingReborrow_stateRel_pre

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    StateRel lm32RawPtrIntReborrowBody
      lm32RawPtrIntReborrowAnnealPre lm32RawPtrIntReborrowMiriPre :=
  Witness.lm32RawPtrIntReborrow_stateRel_pre

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let hooks := annealStepHooks lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts
      let entry := refAllocMapEntry lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts .shared 1 1 lm31AllocId1
      stepMirFn lm32DanglingReborrowBody lm32DanglingReborrowAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32DanglingReborrowMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₁ m₁ [entry] ∧
      stepMirFn lm32DanglingReborrowBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₂ m₂ [entry] ∧
      stepMirFn lm32DanglingReborrowBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (stepMirFn lm32RawPtrIntReborrowBody lm32RawPtrIntReborrowAnnealPre = MirStepNode.fail .ub ∧
      ∃ m' tf',
        Miri.Interpreter.Step.step
          (annealStepHooks lm32RawPtrIntReborrowBody.localDecls lm32RawPtrIntReborrowBody.layouts)
          () lm32RawPtrIntReborrowMiriPre = (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧
        (tf'.locals[2]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0)))))) :=
  Witness.wit_lm3_2_safeRef_dangling_reborrow_and_rawPtr_int_divergences

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    lm32RunValidateRefBoolShallow none = .ok (.ok ()) ∧
    lm32RunVisitRefBoolRecursive none =
      .ok (.error (.undefinedBehavior "read of uninitialized memory")) ∧
    lm32RunValidateRefBoolShallow (some 2) = .ok (.ok ()) ∧
    (∃ msg, lm32RunVisitRefBoolRecursive (some 2) = .ok (.error (.undefinedBehavior msg))) ∧
    lm32RunVisitRefBoolRecursive (some 1) = .ok (.ok true) :=
  Witness.wit_lm3_2_recursive_ref_pointee_validity

/-! ## `LM-3.2`: safe references, reborrows, and validity -/

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  lookupRefDerefPointeeLayout
  annealSafeRefDerefCheck
  annealDerefSafeRefToMemPlace
  LocalRelLM3_2
  FrameRelLM3_2
  StateRelLM3_2
  ImmediateRelLM3_2
  StepRelLM3_2
  annealValidityPlaceHooks
  annealValidityProjectionHooks
  annealValidityClassify
  annealValidityPointeeLayout
  annealValidityPlaceOperand
  annealValidityAccessCheck
  annealValidityHooks
  AnnealScalarValid
  refBorrowPerm
  refAllocMapEntry
  Witness.refU64Ty
  Witness.refU64Decl
  Witness.lm32RefBody
  Witness.lm32RefAnnealPre
  Witness.lm32RefMiriFramePre
  Witness.lm32RefMiriPre
  Witness.lm32ValidityFrame
  Witness.lm32ValidityState
  Witness.lm32Validate
  Witness.charTyLM32
  Witness.boolTyLM32
  Witness.neverTyLM32
  LocalRelLM3_2.cachedLayout_eq
  LocalRelLM3_2.mono_cons
  LocalRelLM3_2.map_preserve
  LocalRelLM3_2.of_live_base
  LocalRelLM3_2.indirect_base
  FrameRelLM3_1.toLM3_2
  StateRelLM3_1.toLM3_2
  StepRelLM3_1.toLM3_2
  FrameRelLM3_2.toLM3_1
  StateRelLM3_2.toLM3_1
  FrameRelLM3_2.lookup_local
  FrameRelLM3_2.cache_local_layout
  FrameRelLM3_2.mono_cons
  FrameRelLM3_2.of_live_base
  FrameRelLM3_2.update_local
  FrameRelLM3_2.indirect_allocId
  FrameRelLM3_2.advance
  StateRelLM3_2.frame_rel_singleton
  StateRelLM3_2.cache_layout
  StateRelLM3_2.immediate_not_in_allocMap
  annealStackBaseAddr_add_ne_zero
  annealSafeRefDerefCheck_live_ok
  annealSafeRefDerefCheck_dead_err
  annealSafeRefDerefCheck_oob_err
  annealSafeRefDerefCheck_misaligned_err
  annealSafeRefDerefCheck_int_null_err
  annealSafeRefDerefCheck_int_dangling_err
  annealValidityPlaceOperand_local
  annealValidityClassify_prim
  fromScalarInt_toBool_ok_iff
  annealValidityHooks_readImmediate_local
  validityVisitor_scalar_bool_simulation
  mem_eq_of_map_nodup
  PtrRel.allocId_of_entry
  annealValidityHooks_checkPointerAccess_eq
  annealValidityAccessCheck_stack
  validityVisitor_ref_dereferenceable_simulation
  evalRvalue_ref_live_eq
  evalRvalue_ref_dead_eq
  evalRvalueIntoPlace_ref_ok
  evalRvalueIntoPlace_ref_force_error
  evalRvalue_ref_simulation
  evalRvalue_reborrow_root_ok
  LocalRelLM3_2.toLM3_1_of_rawPtr
  LocalRelLM3_2.ref_immediate_cases
  evalRvalue_reborrow_simulation
  evalRvalue_reborrow_dangling_divergence
  evalRvalue_reborrow_perm_divergence
  Witness.lm32Ref_stateRel_pre
  Witness.lm32Ref_immediate_pre
  Witness.wit_lm3_2_ref_step
  Witness.wit_lm3_2_validity_visitor_runs
  fromScalarInt_toChar_ok_iff
  annealValidityPlaceOperand_dead_local
  annealValidityPlaceOperand_memory
  annealValidityHooks_readImmediate_uninit_local
  annealValidityHooks_readImmediate_dead_local
  annealValidityHooks_readImmediate_memory
  annealValidityHooks_withGhostValidation_eq
  annealValidityHooks_typeName_eq
  validatePlace_annealValidityHooks_nonrecursive_eq
  visit_primitive_cases
  visit_reference_cases
  validatePlace_prim_scalar_simulation
  validatePlace_ref_nonrecursive_simulation
  visit_ref_recursive_pointee_simulation
  lookupDerefPointeeLayout_safeRef_eq
  lookupRefDerefPointeeLayout_safeRef_eq
  annealDerefOperandToMemPlace_safeRef_uninit
  annealDerefOperandToMemPlace_safeRef_scalarInt
  annealDerefOperandToMemPlace_safeRef_pointer_eq
  evalRvalue_ref_indirect_simulation
  evalRvalue_reborrow_rawPtr_int_divergence
  annealDerefOperandToMemPlace_safeRef_ptr_dead
  annealDerefOperandToMemPlace_safeRef_ptr_live
  evalRvalue_reborrow_safeRef_simulation
  evalRvalue_reborrow_safeRef_dangling_divergence
  LocalRelLM3_2.of_setLiveAllocation_ne
  FrameRelLM3_2.map_preserve
  StateRelLM3_2.advance_write_immediate_perm_map
  StateRelLM3_2.deinit_immediate_local
  step_safeRef_use_simulation
  step_safeRef_deref_read_simulation_explicit
  step_safeRef_deref_read_simulation
  StateRelLM3_2.advance_write_deref_scalar
  evalOperand_scalar_lm3_2_simulation
  step_safeRef_deref_write_simulation_explicit
  step_safeRef_deref_write_simulation
  LocalRelLM3_2.allocLive
  LocalRelLM3_2.of_dealloc
  step_storageDead_lm3_2_simulation
  step_storageLive_lm3_2_simulation
  Witness.checkImmediateInTopFrame
  Witness.isImmediate_of_checkImmediateInTopFrame
  Witness.wit_lm3_2_ref_deref_read_storageDead_real_steps
  Witness.refMutU64Ty
  Witness.refMutU64Decl
  Witness.lm32MutRefChainBody
  Witness.lm32MutRefChainAnnealPre
  Witness.lm32MutRefChainMiriFramePre
  Witness.lm32MutRefChainMiriPre
  Witness.lm32MutRefChain_stateRel_pre
  Witness.wit_lm3_2_mut_ref_move_write_read_reborrow_real_steps
  Witness.lm32DanglingReborrowBody
  Witness.lm32DanglingReborrowAnnealPre
  Witness.lm32DanglingReborrowMiriFramePre
  Witness.lm32DanglingReborrowMiriPre
  Witness.lm32DanglingReborrow_stateRel_pre
  Witness.lm32RawPtrIntReborrowBody
  Witness.lm32RawPtrIntReborrowAnnealPre
  Witness.lm32RawPtrIntReborrowMiriFramePre
  Witness.lm32RawPtrIntReborrowMiriPre
  Witness.lm32RawPtrIntReborrow_stateRel_pre
  Witness.wit_lm3_2_safeRef_dangling_reborrow_and_rawPtr_int_divergences
  Witness.refBoolTyLM32
  Witness.lm32BoolPointeeAlloc?
  Witness.lm32RefBoolValidityState
  Witness.lm32RunValidateRefBoolShallow
  Witness.lm32RunVisitRefBoolRecursive
  Witness.wit_lm3_2_recursive_ref_pointee_validity

/-! ### `LM-3.2` A1 statement pins -/

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : MirAst.LocalDecl} {srcMut dstMut : Mutability}
    {dstPointee : RigidTy} {targetDecl : MirAst.LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut targetDecl.ty.kind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry}
    (hslot_src : get? s.frame.locals srcIdx = some (.init (.ptr p 8)))
    (hptr : PtrRel allocMap p mptr) (he : e ∈ allocMap) (htag : e.tag = p.tag)
    (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) (hlt : srcIdx < tf.locals.size)
    (hval_src : (tf.locals[srcIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    (fuel : Nat) :
    evalOperand s.frame.locals (.copy ⟨srcIdx, .nil⟩) s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.ptr p 8) s.frame.locals ∧
    StepRelLM3_2 body m allocMap (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) srcDecl.ty
        (fuel + 1) ⟨.local 0 srcIdx none tf.localsIdentity, translateTy srcDecl.ty body.layouts⟩
        false false m =
      .error (.undefinedBehavior
        "validation: encountered a dangling reference (use-after-free)") m :=
  step_safeRef_copy_dangling_validity_divergence hstate hphase hbb hstmt hdecl_dst hdecl_src hsrc_ty hdst_ty himm hslot_src hptr he htag hdecl_t hdead_t hframes hlt hval_src fuel

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  step_safeRef_copy_dangling_validity_divergence

/-! ### `LM-3.2` B2 statement pins -/

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {pointeeTy : Ty} (hprim : IsPrimScalarTy pointeeTy)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut pointeeTy.kind)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry}
    (hptr : PtrRel allocMap p mptr) (he : e ∈ allocMap) (htag : e.tag = p.tag)
    {allocDecl : MirAst.LocalDecl} (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {slot : LocalSlot} (hslot : get? s.frame.locals e.localIdx = some slot)
    (hlive_slot : slot ≠ .dead)
    (hinbounds : p.offsetBytes + (translateTy pointeeTy body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis_err : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat p.offsetBytes))
      (translateTy pointeeTy body.layouts).layout.align.abi = .ok (some mis))
    (hval : (tf.locals[refIdx]'hlt).value =
      .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))))
    (fuel : Nat) :
    let mutBool : Bool := match refMut with | .mut => true | .not => false
    Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
      (fuel + 1) ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
      false false m =
      .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
        ⟨"", #[]⟩ (.reference mutBool) mis) m :=
  validatePlace_ref_misaligned_simulation hstate hframes hlt hprim hrefTy hptr he htag hdecl_a
    hslot hlive_slot hinbounds hmis_err hval fuel

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {refIdx : Nat} (hlt : refIdx < tf.locals.size)
    {refTy : Ty} {refMut : Mutability}
    (hrefTy : refTy.kind = .ref refMut (.tuple .nil))
    (fuel : Nat) :
    let place : Miri.Interpreter.RuntimePlace AnnealProv :=
      ⟨.local 0 refIdx none tf.localsIdentity, translateTy refTy body.layouts⟩
    (∀ {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt},
      ScalarRel sc msc → sc.sizeBytes = 8 → sc.bits < 2 ^ 64 →
      (tf.locals[refIdx]'hlt).value = .live (.immediate (.scalar (.fromScalarInt msc))) →
      (sc.bits = 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m =
          .error (.undefinedBehavior "validation: null or maybe-null safe pointer") m) ∧
      (sc.bits ≠ 0 →
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
          (fuel + 1) place false false m = .ok () m)) ∧
    (∀ {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} {e : AllocMapEntry},
      PtrRel allocMap p mptr → e ∈ allocMap → e.tag = p.tag →
      (tf.locals[refIdx]'hlt).value =
        .live (.immediate (.scalar (.fromPointer annealTargetDataLayout mptr))) →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts) refTy
        (fuel + 1) place false false m = .ok () m) :=
  validatePlace_ref_unit_zst_simulation hstate hframes hlt hrefTy fuel

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl targetDecl : MirAst.LocalDecl} {srcMut dstMut : Mutability}
    {srcPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .ref srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut targetDecl.ty.kind)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    {p : ProvenancePtr} {e : AllocMapEntry}
    (hslot_src : get? s.frame.locals srcIdx = some (.init (.ptr p 8)))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he : e ∈ allocMap) (htag : e.tag = p.tag)
    (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead) :
    ∃ s' m' tf',
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM3_2 body s' m' allocMap ∧
      m'.stack.frames = #[tf'] ∧
      get? s'.frame.locals dstIdx = some (.init (.ptr p 8)) ∧
      dstIdx < tf'.locals.size ∧
      ∀ fuel,
        Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks body.layouts)
          dstDecl.ty (fuel + 1)
          ⟨.local 0 dstIdx none tf'.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          false false m' =
        .error (.undefinedBehavior
          "validation: encountered a dangling reference (use-after-free)") m' :=
  step_safeRef_use_dangling_post_validity_divergence hstate hphase hopKind hbb hstmt hdecl_dst
    hdecl_src hsrc_ty hdst_ty himm hslot_src hdst_live he htag hdecl_t hdead_t

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl allocDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry}
    (hptrRel : PtrRel allocMap ptrVal mptr)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (hlive_a : get? s.frame.locals e.localIdx ≠ some .dead)
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat)
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .error (.undefinedBehavior "dereferencing a dangling reference") st :=
  annealDerefOperandToMemPlace_safeRef_ptr_oob hstate hdecl hty hpk hptrRel he htag hdecl_a
    hlive_a hoob ptrLay hmach

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    {refIdx : Local} {refDecl allocDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? body.localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {ptrVal : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    {e : AllocMapEntry}
    (hptrRel : PtrRel allocMap ptrVal mptr)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (hlive_a : get? s.frame.locals e.localIdx ≠ some .dead)
    (hinbounds : ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
      .ok (some mis))
    (ptrLay : Miri.Interpreter.LocalLayout)
    {st : AnnealStepState} (hmach : st.machine = m.machine) :
    annealDerefOperandToMemPlace body.localDecls body.layouts refIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .error (.undefinedBehavior "dereferencing an unaligned reference") st :=
  annealDerefOperandToMemPlace_safeRef_ptr_misaligned hstate hdecl hty hpk hptrRel he htag hdecl_a
    hlive_a hinbounds hmis ptrLay hmach

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl allocDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) :=
  step_safeRef_deref_read_oob_divergence hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref
    href_ty hdst_prim himm_ref hslot_r he htag hperm hdecl_a htarget hoob hdst_live

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl allocDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {sl_a : LocalSlot} (hsl_a : get? s.frame.locals e.localIdx = some sl_a)
    (hsl_ne : sl_a ≠ .dead)
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals e.localIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) :=
  step_safeRef_deref_write_oob_divergence hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim hop
    himm_ref hop_ok hslot_r he htag hperm hdecl_a hsl_a hsl_ne hoob

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl allocDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok (some mis))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) :=
  step_safeRef_deref_read_misaligned_divergence hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref
    href_ty hdst_prim himm_ref hslot_r he htag hperm hdecl_a htarget hinbounds hmis hdst_live

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl allocDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    {sl_a : LocalSlot} (hsl_a : get? s.frame.locals e.localIdx = some sl_a)
    (hsl_ne : sl_a ≠ .dead)
    (hinbounds : ptrVal.offsetBytes +
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
      .ok (some mis)) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals e.localIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) :=
  step_safeRef_deref_write_misaligned_divergence hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim
    hop himm_ref hop_ok hslot_r he htag hperm hdecl_a hsl_a hsl_ne hinbounds hmis

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : MirAst.LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hperm : e.perm = .frozen ∨ e.perm = .disabled)
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' msc alloc' memKind,
      ScalarRel sc msc ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.machine.memory.live.find? (fun x => x.1 == e.allocId) =
        some (e.allocId, ⟨memKind, alloc'⟩) ∧
      alloc'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
        .ok (.fromScalarInt msc) :=
  step_safeRef_deref_write_perm_divergence hstate hphase hbb hstmt hdecl_ref href_ty hval_prim
    hval_kind hop himm_ref hop_ok hslot_r he htag hoff0 hperm hlive_t htgt_kind

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl : MirAst.LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hperm : e.perm = .disabled)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = dstDecl.ty.kind)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' msc,
      ScalarRel sc msc ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) :=
  step_safeRef_deref_read_disabled_divergence hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref
    href_ty hdst_prim himm hslot_r he htag hoff0 hperm htarget htgt_kind hdst_live

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Mutability}
    {pointeeKind dstPointee : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hperm : e.perm = .disabled ∨ (e.perm = .frozen ∧ bk ≠ .shared))
    (hlive_t : get? s.frame.locals e.localIdx ≠ some .dead)
    (htgt_kind : ∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
      tgtDecl.ty.kind = pointeeKind)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩)))) :=
  evalRvalue_reborrow_safeRef_perm_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ref href_ty
    hdst_ty hpk_prim himm hslot_r he htag hoff0 hperm hlive_t htgt_kind hdst_live

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention ⟨loc, .nil⟩, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hlive : get? s.frame.locals loc ≠ some .dead) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_placeMention_local_lm3_2_simulation hstate hphase hbb hstmt hdecl hlive

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hvalid_or_dead :
      get? s.frame.locals refIdx = some .dead ∨
      ∃ ptrVal e,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧ ptrVal.offsetBytes = 0 ∧
        get? s.frame.locals e.localIdx ≠ some .dead ∧
        (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
          tgtDecl.ty.kind = pointeeKind)) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_placeMention_safeRef_deref_simulation hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim
    himm_ref hvalid_or_dead

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {refDecl : MirAst.LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨refIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hbad :
      get? s.frame.locals refIdx = some .uninit ∨
      (∃ sc, get? s.frame.locals refIdx = some (.init (.scalar sc))) ∨
      (∃ ptrVal e,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? s.frame.locals e.localIdx = some .dead) ∨
      (∃ ptrVal e allocDecl,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? body.localDecls e.localIdx = some allocDecl ∧
        get? s.frame.locals e.localIdx ≠ some .dead ∧
        (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
          ptrVal.offsetBytes +
            (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat) ∨
      (∃ ptrVal e allocDecl mis,
        get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? body.localDecls e.localIdx = some allocDecl ∧
        get? s.frame.locals e.localIdx ≠ some .dead ∧
        ptrVal.offsetBytes +
          (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
          (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat ∧
        annealOffsetMisalignment
          (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
          (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok (some mis))) :
    stepMirFn body s = .step (advanceStmt s s.frame.locals) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_placeMention_safeRef_deref_divergence hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim
    himm_ref hbad

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.nop, span⟩) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_nop_lm3_2_simulation hstate hphase hbb hstmt

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : MirAst.LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_scalar_use_lm3_2_simulation hstate hphase hbb hstmt hdecl_dst hdst_prim hval_kind hop
    himm_dst

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : MirAst.LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (hmem_dst : ∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx) :
    StepRelLM3_2 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_direct_write_promoted_lm3_2_simulation hstate hphase hbb hstmt hdecl_dst hdst_prim
    hval_kind hop hmem_dst

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRelLM3_2 body m allocMap aRes mRes) :
    StepObsRelLM3_2 body m allocMap aRes mRes :=
  StepRelLM3_2.toStepObsRelLM3_2 h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_1 body m allocMap aRes mRes) :
    StepObsRelLM3_2 body m allocMap aRes mRes :=
  StepObsRelLM3_1.toLM3_2 h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap aRes mRes) :
    (∃ obs s', aRes = .emitStep obs s' ∧ StateRelLM3_2 body s' mRes.1 allocMap) ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames ≠ #[]) :=
  StepObsRelLM3_2.emitStep_iff h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap aRes mRes) :
    (∃ retVal mem', aRes = .retNormal retVal mem') ↔
      (mRes.2 = .ok true ∧ mRes.1.stack.frames = #[]) :=
  StepObsRelLM3_2.retNormal_iff h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {retVal : Value} {mem' : Memory}
    {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap (.retNormal retVal mem') mRes) :
    ∃ decl0 imm0,
      get? body.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2 allocMap decl0.ty body.layouts retVal imm0 ∧
      mRes = ({ m with stack := ⟨#[]⟩ }, .ok true) :=
  StepObsRelLM3_2.retNormal_rel h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepObsRelLM3_2 body m allocMap aRes mRes) :
    (aRes = .fail .ub) ↔ (∃ msg, mRes.2 = .error (.undefinedBehavior msg)) :=
  StepObsRelLM3_2.ub_iff h

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm :
      (∃ target, bb.terminator.kind = .goto target) ∨
      (bb.terminator.kind = .return_ ∧
        ∃ decl0,
          get? body.localDecls 0 = some decl0 ∧
          (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
          ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) ∨
      bb.terminator.kind = .unreachable) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_goto_return_lm3_2_simulation hstate hphase hbb hstmt_none hstmt_len hcleanup hterm

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
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
    StepObsRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_switchInt_lm3_2_simulation hstate hphase hbb hstmt_none hstmt_len hterm hty
    hdiscr hcases

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    {cond : MirAst.Operand} {condTy : Ty} {expected : Bool} {target : BasicBlockIdx}
    (hterm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hbool : condTy.kind = .bool)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame cond condTy) :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_assert_lm3_2_simulation hstate hphase hbb hstmt_none hstmt_len hterm hbool hop

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : MirAst.Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_2StateStmt body s m allocMap stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm3_2_state_simulation hstate hphase hbb hstmt hwt hsupply

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hwt : WellTypedLM3_2StateTerminator body m bb) :
    StepObsRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_lm3_2_state_simulation hstate hphase hbb hstmt_none hstmt_len hwt

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hloc :
      (∃ stmt, get? bb.statements s.frame.stmtIdx = some stmt ∧
        WellTypedLM3_2StateStmt body s m allocMap stmt) ∨
      (get? bb.statements s.frame.stmtIdx = none ∧
        s.frame.stmtIdx = length bb.statements ∧
        WellTypedLM3_2StateTerminator body m bb))
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    ∃ allocMap' : List AllocMapEntry,
      StepObsRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_mir_lm3_2_state_simulation hstate hphase hbb hloc hsupply

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    (∃ (b : CapturedMir) (s₀ s₁ : MachineState) (m₀ m₁ : AnnealStepState)
        (tf₀ tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (_ : 1 < tf₀.locals.size) (_ : 1 < tf₁.locals.size),
      StateRel b s₀ m₀ ∧ m₀.stack.frames = #[tf₀] ∧
      get? s₀.frame.locals 1 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refUnitTyLM32 4
        ⟨.local 0 1 none tf₀.localsIdentity, translateTy refUnitTyLM32 b.layouts⟩
        false false m₀ =
        .error (.undefinedBehavior "validation: null or maybe-null safe pointer") m₀ ∧
      StateRel b s₁ m₁ ∧ m₁.stack.frames = #[tf₁] ∧
      get? s₁.frame.locals 1 = some (.init (.scalar ⟨1, 8⟩)) ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refUnitTyLM32 4
        ⟨.local 0 1 none tf₁.localsIdentity, translateTy refUnitTyLM32 b.layouts⟩
        false false m₁ = .ok () m₁) ∧
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
        (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 b s₂ m₂ [entry] ∧
      m₂.stack.frames = #[tf₂] ∧
      get? s₂.frame.locals 1 = some .dead ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refUnitTyLM32 4
        ⟨.local 0 2 none tf₂.localsIdentity, translateTy refUnitTyLM32 b.layouts⟩
        false false m₂ = .ok () m₂) ∧
    (∃ (b : CapturedMir) (s_mis : MachineState) (m_mis : AnnealStepState)
        (tf_mis : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      m_mis.stack.frames = #[tf_mis] ∧
      get? s_mis.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refMutU16TyLM32 4
        ⟨.local 0 3 none tf_mis.localsIdentity, translateTy refMutU16TyLM32 b.layouts⟩
        false false m_mis =
      .error (Miri.Interpreter.ValidityVisitor.classifyPointerAlignmentError
        ⟨"", #[]⟩ (.reference true) lm32MisalignU16At1) m_mis) :=
  Witness.wit_lm3_2_unit_zst_and_misaligned_ref_validity

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
            layout := some (translateTy u8TyLM32) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 0 = some (.init (.scalar ⟨7, 1⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
            layout := some (translateTy u8TyLM32) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 1 = some (.init (.scalar ⟨99, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (∃ (b : CapturedMir) (s_mis s_out : MachineState) (m_mis m_out : AnnealStepState),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      stepMirFn b s_mis = .step s_out ∧
      get? s_out.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩)) ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m_mis =
        (m_out, .error (.undefinedBehavior "dereferencing an unaligned reference"))) ∧
    (∃ (b : CapturedMir) (s_mis s_out : MachineState) (m_mis m_out : AnnealStepState),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      stepMirFn b s_mis = .step s_out ∧
      get? s_out.frame.locals 1 = some (.init (.scalar ⟨7, 2⟩)) ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m_mis =
        (m_out, .error (.undefinedBehavior "dereferencing an unaligned reference"))) :=
  Witness.wit_lm3_2_oob_and_misaligned_deref_divergences

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    (∃ (b : CapturedMir) (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
        (tf₃ tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b refU64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2 b s₃ m₃ [entry] ∧
      m₃.stack.frames = #[tf₃] ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refU64Ty 4 ⟨.local 0 3 none tf₃.localsIdentity, translateTy refU64Ty b.layouts⟩
        false false m₃ =
        .error (.undefinedBehavior
          "validation: encountered a dangling reference (use-after-free)") m₃ ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 b s₄ m₄ [entry] ∧
      m₄.stack.frames = #[tf₄] ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refU64Ty 4 ⟨.local 0 0 none tf₄.localsIdentity, translateTy refU64Ty b.layouts⟩
        false false m₄ =
        .error (.undefinedBehavior
          "validation: encountered a dangling reference (use-after-free)") m₄) ∧
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true)) ∧
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true)) ∧
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState)
        (tf₃ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (msc : Miri.Memory.ScalarInt),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 b s₂ m₂ [{ entry with perm := .disabled }] ∧
      stepMirFn b s₂ = .fail .ub ∧
      ScalarRel ⟨77, 8⟩ msc ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      m₃.stack.frames = #[tf₃] ∧
      (tf₃.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc))))) :=
  Witness.wit_lm3_2_dangling_copy_move_and_perm_divergences_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    (∃ (b : CapturedMir) (s₁ s₂ s₃ s₄ s₅ : MachineState)
        (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
        (decl0 : MirAst.LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      stepMirFn b (mkPre4AnnealLM32 b .uninit) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b refU64Ty { value := .live (.immediate .uninit), layout := none }) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_2 b s₅ m₅ [{ entry with perm := .active }] ∧
      (∃ am, StepObsRelLM3_2 b m₅ am (stepMirFn b s₅) (Miri.Interpreter.Step.step hooks () m₅)) ∧
      stepMirFn b s₅ = .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₅.memory ∧
      Miri.Interpreter.Step.step hooks () m₅ = ({ m₅ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₅ = (m₅, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2 [{ entry with perm := .active }] decl0.ty b.layouts
        (.ptr { allocId := 1, offsetBytes := 0 } 8) imm0) ∧
    (∃ (b : CapturedMir) (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
            layout := some (translateTy u64Ty) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step (advanceStmt s₂ s₂.frame.locals) ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg))) :=
  Witness.wit_lm3_2_placeMention_and_unified_return_ref_real_steps

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  validatePlace_ref_misaligned_simulation
  validatePlace_ref_unit_zst_simulation
  step_safeRef_use_dangling_post_validity_divergence
  annealDerefOperandToMemPlace_safeRef_ptr_oob
  annealDerefOperandToMemPlace_safeRef_ptr_misaligned
  step_safeRef_deref_read_oob_divergence
  step_safeRef_deref_write_oob_divergence
  step_safeRef_deref_read_misaligned_divergence
  step_safeRef_deref_write_misaligned_divergence
  step_safeRef_deref_write_perm_divergence
  step_safeRef_deref_read_disabled_divergence
  evalRvalue_reborrow_safeRef_perm_divergence
  step_placeMention_local_lm3_2_simulation
  step_placeMention_safeRef_deref_simulation
  step_placeMention_safeRef_deref_divergence
  step_nop_lm3_2_simulation
  step_scalar_use_lm3_2_simulation
  step_direct_write_promoted_lm3_2_simulation
  StepObsRelLM3_2
  StepRelLM3_2.toStepObsRelLM3_2
  StepObsRelLM3_1.toLM3_2
  StepObsRelLM3_2.emitStep_iff
  StepObsRelLM3_2.retNormal_iff
  StepObsRelLM3_2.retNormal_rel
  StepObsRelLM3_2.ub_iff
  step_terminator_goto_return_lm3_2_simulation
  step_terminator_switchInt_lm3_2_simulation
  step_terminator_assert_lm3_2_simulation
  WellTypedLM3_2StateStmt
  step_stmt_lm3_2_state_simulation
  WellTypedLM3_2StateTerminator
  step_terminator_lm3_2_state_simulation
  step_mir_lm3_2_state_simulation
  Witness.refUnitTyLM32
  Witness.refUnitDeclLM32
  Witness.u8TyLM32
  Witness.u8DeclLM32
  Witness.u16TyLM32
  Witness.u16DeclLM32
  Witness.refMutU16TyLM32
  Witness.refMutU16DeclLM32
  Witness.constU16LM32
  Witness.lm32MisalignU16At1
  Witness.mkPre4AnnealLM32
  Witness.mkPre4MiriFrameLM32
  Witness.mkPre4MiriLM32
  Witness.wit_lm3_2_unit_zst_and_misaligned_ref_validity
  Witness.wit_lm3_2_oob_and_misaligned_deref_divergences
  Witness.wit_lm3_2_dangling_copy_move_and_perm_divergences_real_steps
  Witness.wit_lm3_2_placeMention_and_unified_return_ref_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {dstIdx refIdx : MirAst.Local}
    {opKind : MirAst.Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (MirAst.Rvalue.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl allocDecl : MirAst.LocalDecl}
    {mutability : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    (hdecl_dst : Trusted.Sequence.get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_r : Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hoff0 : ptrVal.offsetBytes = 0)
    (hperm : e.perm ≠ .disabled)
    (hdecl_a : Trusted.Sequence.get? body.localDecls e.localIdx = some allocDecl)
    (htarget : Trusted.Sequence.get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hsize : (translateTy dstDecl.ty body.layouts).layout.size =
      (translateTy allocDecl.ty body.layouts).layout.size)
    (hinvalid : ¬ AnnealScalarValid dstDecl.ty sc)
    (hdst_live : Trusted.Sequence.get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      Trusted.Sequence.get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) :=
  step_safeRef_deref_read_invalid_scalar_divergence hstate hphase hopKind hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_prim himm_ref hslot_r he htag hoff0 hperm
    hdecl_a htarget hsize hinvalid hdst_live

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {dstIdx refIdx : MirAst.Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : MirAst.BorrowKind} {refMut dstMut : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind dstPointee : MirAst.RigidTy}
    {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (MirAst.Rvalue.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : Trusted.Sequence.get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_zero_perm : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false) :
    StepRelLM3_2Tree body m
      (reborrowTreeMapNext body.localDecls body.layouts bk s.frame.locals treeMap refIdx
        s.memory.nextTag)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_reborrow_safeRef_tree_simulation_explicit htree hphase hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hanc_read

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {dstIdx refIdx : MirAst.Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : MirAst.BorrowKind} {refMut dstMut : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind dstPointee : MirAst.RigidTy}
    {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (MirAst.Rvalue.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : Trusted.Sequence.get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref refMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .ref dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_zero_perm : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ s' m',
      stepMirFn body s = MirStepNode.step s' →
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) →
      ∃ (treeMap' : List ReborrowMapEntry),
        StepRelLM3_2Tree body m treeMap' (MirStepNode.step s') (m', .ok true)) :=
  evalRvalue_reborrow_safeRef_tree_simulation htree hphase hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hanc_read

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {dstIdx refIdx : MirAst.Local}
    {opKind : MirAst.Place → Operand} {span : String}
    (hopKind : opKind = Operand.copy ∨ opKind = Operand.move)
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (MirAst.Rvalue.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl refDecl : MirAst.LocalDecl} {mutability : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    (hdecl_dst : Trusted.Sequence.get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal, Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, Trusted.Sequence.get? body.localDecls e.localIdx = some decl →
            decl.ty.kind = dstDecl.ty.kind))
    (hanc_read : ∀ ptrVal,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false) :
    StepRelLM3_2Tree body m (derefReadNextTreeMap s.frame.locals treeMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_read_tree_simulation htree hphase hopKind hbb hstmt
    hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref hanc_read

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData} {refIdx : MirAst.Local} {op : MirAst.Operand} {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (MirAst.Rvalue.use op), span⟩)
    {refDecl : MirAst.LocalDecl} {mutability : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind : MirAst.RigidTy} {valTy : MirAst.Ty}
    (hdecl_ref : Trusted.Sequence.get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind)
    (hanc_write : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .write s.memory.borrows e.parentTag = false) :
    StepRelLM3_2Tree body m (derefWriteNextTreeMap s.frame.locals treeMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_write_tree_simulation htree hphase hbb hstmt
    hdecl_ref href_ty hval_prim hval_kind hop himm_ref hlive_ref hanc_write

example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : MirAst.BasicBlockData}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : Trusted.Sequence.get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = bb.statements.length)
    (hwt_term : WellTypedLM3_2StateTerminator body m bb)
    (hgoto_ret : (∃ target, bb.terminator.kind = .goto target) ∨
      bb.terminator.kind = .return_ ∨ bb.terminator.kind = .unreachable) :
    StepRelLM3_2Tree body m treeMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_terminator_goto_return_tree_simulation htree hphase hbb hstmt_none hstmt_len
    hwt_term hgoto_ret

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  annealDerefOperandToMemPlace_safeRef_ptr_same_size
  step_safeRef_deref_read_invalid_scalar_divergence
  lookupTreeMapByTag
  ReborrowMapEntry.updateOnRead
  derefReadMapFnTree
  derefReadNextTreeMap
  ReborrowMapEntry.updateOnWrite
  derefWriteNextTreeMap
  reborrowPermOf
  reborrowTreeMapNext
  SameAllocSkeleton
  StateRelLM3_2Tree
  StepRelLM3_2Tree
  step_reborrow_safeRef_tree_simulation_explicit
  evalRvalue_reborrow_safeRef_tree_simulation
  step_safeRef_deref_read_tree_simulation
  step_safeRef_deref_write_tree_simulation
  treeMap_ancestorOrSelf_not_disabled
  hasTreeReadUB_treeMap_eq_false
  derefReadTreeUB_treeMap_eq_false
  derefWriteTreeUB_treeMap_eq_false
  step_terminator_goto_return_tree_simulation

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
        (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (msg₀ msg₁ : String),
      let b := lm32RefNeverBody
      let m₀ := mkPre4MiriLM32 b u64Ty lm32Mls42
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
          refNeverTyLM32 4
          ⟨.local 0 2 none (.ofAllocationToken 0), translateTy refNeverTyLM32 b.layouts⟩
          false false m₀ =
        .error (.undefinedBehavior msg₀) m₀ ∧
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₀ =
        (m₁, .ok true) ∧
      StateRelLM3_2 b s₁ m₁ [refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1] ∧
      get? s₁.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      m₁.stack.frames = #[tf₁] ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
          refNeverTyLM32 4
          ⟨.local 0 2 none tf₁.localsIdentity, translateTy refNeverTyLM32 b.layouts⟩
          false false m₁ =
        .error (.undefinedBehavior msg₁) m₁) ∧
    (∀ (place : Miri.Interpreter.RuntimePlace AnnealProv) (m : AnnealStepState),
      place.layout = translateTy voidTyLM32 lm32EnumLayouts →
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks lm32EnumLayouts)
          voidTyLM32 4 place false false m =
        .error (.undefinedBehavior "validation: zero-variant enum value") m) ∧
    (∀ bytes, decodeValueFromBytes 4 lm32EnumLayouts voidTyLM32 bytes = none) ∧
    lm32ValidateTag2 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 0))) =
      .ok () (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 0)))) ∧
    decodeValueFromBytes 4 lm32EnumLayouts tag2TyLM32 [.init (UInt8.ofNat 0) none] =
      some (.aggregate 0 .nil) ∧
    lm32ValidateTag2 (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2))) =
      .error (.undefinedBehavior "InvalidTag(outside valid range)")
        (lm32ValidityState (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 2)))) ∧
    decodeValueFromBytes 4 lm32EnumLayouts tag2TyLM32 [.init (UInt8.ofNat 2) none] = none :=
  Witness.wit_lm3_2_ref_never_and_enum_discriminant_validity

open Witness in
example :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm32InvalidBoolReadBody
      let hooks := annealStepHooks b.localDecls b.layouts
      ¬ AnnealScalarValid boolTyLM32 ⟨2, 1⟩ ∧
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨2, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkPre4MiriLM32 b boolTyLM32 lm32MlsU8Two) =
        (m₁, .ok true) ∧
      StateRelLM3_2 b s₁ m₁ [refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1] ∧
      get? s₁.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 0 = some (.init (.scalar ⟨2, 1⟩)) ∧
      stepMirFn b s₂ = .retNormal (.scalar ⟨2, 1⟩) s₂.memory ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "reading invalid value")) :=
  Witness.wit_lm3_2_invalid_bool_deref_read_divergence_real_steps

open Witness in
example :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
        (decl0 : MirAst.LocalDecl) (imm0 : Miri.Interpreter.Immediate AnnealProv),
      let b := lm32ReborrowTreeBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨42, 8⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkPre4MiriLM32 b u64Ty lm32Mls42) =
        (m₁, .ok true) ∧
      StateRelLM3_2Tree b s₁ m₁ [lm32TreeRoot .reserved] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2Tree b s₂ m₂ [lm32TreeChild .reserved, lm32TreeRoot .reserved] ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_2Tree b s₃ m₃ [lm32TreeChild .active, lm32TreeRoot .active] ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨99, 8⟩)) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2Tree b s₄ m₄ [lm32TreeChild .frozen, lm32TreeRoot .active] ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      stepMirFn b s₄ = .retNormal (.scalar ⟨99, 8⟩) s₄.memory ∧
      Miri.Interpreter.Step.step hooks () m₄ = ({ m₄ with stack := ⟨#[]⟩ }, .ok true) ∧
      get? b.localDecls 0 = some decl0 ∧
      annealControlHooks.returnOperand () m₄ = (m₄, .ok (.immediate imm0)) ∧
      ImmediateRelLM3_2
        ([lm32TreeChild .frozen, lm32TreeRoot .active].map ReborrowMapEntry.toAllocMapEntry)
        decl0.ty b.layouts (.scalar ⟨99, 8⟩) imm0 :=
  Witness.wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  Witness.lm32Mls42
  Witness.refNeverTyLM32
  Witness.refNeverDeclLM32
  Witness.lm32RefNeverBody
  Witness.lm32VoidLayout
  Witness.lm32Tag2Range
  Witness.lm32Tag2Layout
  Witness.lm32EnumLayouts
  Witness.voidTyLM32
  Witness.tag2TyLM32
  Witness.lm32ValidateTag2
  Witness.wit_lm3_2_ref_never_and_enum_discriminant_validity
  Witness.boolDeclLM32
  Witness.refBoolDeclLM32
  Witness.lm32MlsU8Two
  Witness.lm32InvalidBoolReadBody
  Witness.wit_lm3_2_invalid_bool_deref_read_divergence_real_steps
  Witness.lm32TreeRoot
  Witness.lm32TreeChild
  Witness.lm32ReborrowTreeBody
  Witness.wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps


/-! ### `LM-3.3`: six-state Tree Borrows correspondence -/

example (perm : TreeBorrowPerm) :
    miriPermToAnneal (annealPermToMiri perm) = perm :=
  @miriPermToAnneal_annealPermToMiri perm

example (perm : Miri.TreeBorrows.Permission) :
    annealPermToMiri (miriPermToAnneal perm) = perm :=
  @annealPermToMiri_miriPermToAnneal perm

example :
    (∀ perm : TreeBorrowPerm, miriPermToAnneal (annealPermToMiri perm) = perm) ∧
    (∀ perm : Miri.TreeBorrows.Permission,
      annealPermToMiri (miriPermToAnneal perm) = perm) :=
  @TreeBorrowsBijection

example {a b : TreeBorrowPerm}
    (h : annealPermToMiri a = annealPermToMiri b) :
    a = b :=
  @annealPermToMiri_injective a b h

example :
    annealPermToMiri .active = .Unique ∧
    annealPermToMiri .reserved = .ReservedFrz false ∧
    annealPermToMiri .cell = .Cell ∧
    annealPermToMiri .reservedIM = .ReservedIM ∧
    TreeBorrowPerm.cell ≠ .reservedIM ∧
    TreeBorrowPerm.cell ≠ .frozen :=
  @annealPermToMiri_legacy

example (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    annealTransitionToMiri (treeBorrowPermTransition kind rel perm isProtected) =
      Miri.TreeBorrows.performAccess
        (annealAccessKindToMiri kind) (annealRelatednessToMiri rel)
        (annealPermToMiri perm) isProtected :=
  @performAccess_permission_simulation kind rel perm isProtected

example (kind : Miri.TreeBorrows.AccessKind) (rel : Miri.TreeBorrows.AccessRelatedness)
    (perm : Miri.TreeBorrows.Permission) (isProtected : Bool) :
    Miri.TreeBorrows.performAccess kind rel perm isProtected =
      annealTransitionToMiri
        (treeBorrowPermTransition
          (miriAccessKindToAnneal kind) (miriRelatednessToAnneal rel)
          (miriPermToAnneal perm) isProtected) :=
  @performAccess_permission_simulation_miri kind rel perm isProtected

example (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    treeBorrowPermTransition kind rel perm isProtected = .protectedReservedIM ↔
      perm = .reservedIM ∧ isProtected = true ∧ rel = .foreignAccess :=
  @protectedReservedIM_characterization kind rel perm isProtected

example (mutability : Mutability) (pointee : RigidTy) :
    fnEntryRetagPerm mutability pointee ≠ .reservedIM :=
  @fnEntryRetagPerm_ne_reservedIM mutability pointee

example (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool)
    (sifa : Miri.TreeBorrows.IdempotentForeignAccess)
    (hskip : rel = .foreignAccess → perm ≠ .disabled) :
    match treeBorrowNodeAccess kind rel perm isProtected with
    | .transition next =>
      ∃ transition,
        Miri.TreeBorrows.Tree.LocationState.performAccess
            ⟨annealPermToMiri perm, true, sifa⟩
            (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
          .Success ⟨annealPermToMiri next, true, sifa⟩ transition
    | .ub =>
      ∃ state error,
        Miri.TreeBorrows.Tree.LocationState.performAccess
            ⟨annealPermToMiri perm, true, sifa⟩
            (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
          .Error state error
    | .protectedReservedIM =>
      Miri.TreeBorrows.Tree.LocationState.performAccess
          ⟨annealPermToMiri perm, true, sifa⟩
          (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
        .PermissionInvariantFailure ⟨annealPermToMiri perm, true, sifa⟩ :=
  @nodeAccess_locationState_simulation kind rel perm isProtected sifa hskip

example (accessed : Bool) (sifa : Miri.TreeBorrows.IdempotentForeignAccess)
    (kind : TreeBorrowAccessKind) (isProtected : Bool) :
    Miri.TreeBorrows.Tree.LocationState.skipIfKnownNoop
        ⟨.Disabled, accessed, sifa⟩ (annealAccessKindToMiri kind) .ForeignAccess =
      .SkipSelfAndChildren ∧
    treeBorrowNodeAccess kind .foreignAccess .disabled isProtected =
      .transition .disabled :=
  @disabled_foreign_access_skipped accessed sifa kind isProtected

example (rel : TreeBorrowRelatedness) (perm next : TreeBorrowPerm)
    (h : treeBorrowNodeAccess .write rel perm true = .transition next) :
    treeBorrowNodeAccess .write rel perm false = .transition next :=
  @protected_write_success_eq_unprotected rel perm next h

example :
    (∀ (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable) (place : Place)
        (ty : Ty),
      placeTy localDecls layouts place = some ty →
      sharedBorrowPerm localDecls layouts place =
        (if tyIsFreeze ty then .frozen else .cell)) ∧
    (∀ (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
        (config : Miri.TreeBorrows.RetagPolicy.PolicyConfig)
        (mode : Miri.TreeBorrows.RetagPolicy.RetagMode),
      mode ≠ .None →
      ∃ policy,
        Miri.TreeBorrows.RetagPolicy.create facts .Shared mode config = some policy ∧
        policy.outsidePermission =
          annealPermToMiri (if facts.isFreeze then .frozen else .cell) ∧
        policy.nonfreezePermission = annealPermToMiri .cell ∧
        policy.freezePermission = annealPermToMiri .frozen) ∧
    (∀ (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness) (isProtected : Bool),
      treeBorrowNodeAccess kind rel .cell isProtected = .transition .cell ∧
      Miri.TreeBorrows.performAccess
          (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) .Cell isProtected =
        .Transition .Cell) ∧
    (∀ isProtected : Bool,
      treeBorrowNodeAccess .write .localAccess .frozen isProtected = .ub ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess .Frozen isProtected =
        .UndefinedBehavior) ∧
    (treeBorrowNodeAccess .write .foreignAccess .frozen false = .transition .disabled ∧
      Miri.TreeBorrows.performAccess .Write .ForeignAccess .Frozen false =
        .Transition .Disabled) ∧
    (treeBorrowNodeAccess .write .localAccess .reservedIM false = .transition .unique ∧
      treeBorrowNodeAccess .read .foreignAccess .unique false = .transition .frozen ∧
      treeBorrowNodeAccess .write .foreignAccess .unique false = .transition .disabled ∧
      treeBorrowNodeAccess .write .foreignAccess .reservedIM false =
        .transition .reservedIM ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess .ReservedIM false =
        .Transition .Unique ∧
      Miri.TreeBorrows.performAccess .Read .ForeignAccess .Unique false =
        .Transition .Frozen ∧
      Miri.TreeBorrows.performAccess .Write .ForeignAccess .ReservedIM false =
        .Transition .ReservedIM) :=
  @unsafeCell_permission_simulation

example :
    (treeBorrowNodeAccess .read .foreignAccess (.reservedFrz false) true =
        .transition (.reservedFrz true) ∧
      Miri.TreeBorrows.performAccess .Read .ForeignAccess (.ReservedFrz false) true =
        .Transition (.ReservedFrz true)) ∧
    (treeBorrowNodeAccess .write .localAccess (.reservedFrz true) true = .ub ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess (.ReservedFrz true) true =
        .UndefinedBehavior) ∧
    (treeBorrowNodeAccess .write .localAccess (.reservedFrz true) false =
        .transition .unique ∧
      Miri.TreeBorrows.performAccess .Write .LocalAccess (.ReservedFrz true) false =
        .Transition .Unique) ∧
    (∀ conflicted : Bool,
      treeBorrowNodeAccess .read .foreignAccess (.reservedFrz conflicted) false =
        .transition (.reservedFrz conflicted) ∧
      Miri.TreeBorrows.performAccess .Read .ForeignAccess (.ReservedFrz conflicted) false =
        .Transition (.ReservedFrz conflicted)) ∧
    (∀ (conflicted isProtected : Bool) (kind : TreeBorrowAccessKind)
        (rel : TreeBorrowRelatedness),
      annealTransitionToMiri
          (treeBorrowPermTransition kind rel (.reservedFrz conflicted) isProtected) =
        Miri.TreeBorrows.performAccess (annealAccessKindToMiri kind)
          (annealRelatednessToMiri rel) (.ReservedFrz conflicted) isProtected) :=
  @reservedFrz_conflicted_bijection

example :
    treeBorrowNodeAccess .read .foreignAccess (.reservedFrz true) true =
        .transition (.reservedFrz true) ∧
    treeBorrowNodeAccess .write .foreignAccess (.reservedFrz true) true = .ub ∧
    Miri.TreeBorrows.performAccess .Write .ForeignAccess (.ReservedFrz true) true =
      .Transition .Disabled :=
  @reservedFrz_conflicted_protected_foreign

example (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable) (place : Place)
    (ty : Ty) (hty : placeTy localDecls layouts place = some ty)
    (mutability : Mutability) (pointee : RigidTy) :
    sharedBorrowPerm localDecls layouts place =
      annealRetagPerm .default .not (tyIsFreeze ty) ∧
    mutableBorrowPerm localDecls layouts place =
      annealRetagPerm .default .mut (tyIsFreeze ty) ∧
    mutableBorrowPerm localDecls layouts place =
      annealRetagPerm .twoPhase .mut (tyIsFreeze ty) ∧
    fnEntryRetagPerm mutability pointee =
      annealRetagPerm .fnEntry mutability (rigidTyIsFreeze 16 pointee) :=
  @annealRetagPerm_eq_trusted localDecls layouts place ty hty mutability pointee

example (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool)
    (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
    (hunpin : facts.isUnpin = true) (hunsafeUnpin : facts.isUnsafeUnpin = true)
    (hfreeze : facts.isFreeze = frozen) :
    ∃ policy,
      Miri.TreeBorrows.RetagPolicy.create facts (annealRefKindToMiri mutability)
          (annealRetagModeToMiri mode) ⟨false, false⟩ = some policy ∧
      policy.outsidePermission = annealPermToMiri (annealRetagPerm mode mutability frozen) ∧
      (if frozen then policy.freezePermission else policy.nonfreezePermission) =
        annealPermToMiri (annealRetagPerm mode mutability frozen) ∧
      (policy.protector.isSome = true ↔ mode = .fnEntry) ∧
      (∃ state,
        Miri.TreeBorrows.RetagPolicy.initialLocationState policy frozen = .ok state ∧
        state.permission = annealPermToMiri (annealRetagPerm mode mutability frozen) ∧
        (state.accessed = true ↔ annealRetagPerm mode mutability frozen ≠ .cell)) ∧
      (mode = .fnEntry → annealRetagPerm mode mutability frozen ≠ .reservedIM) :=
  @retag_pipeline_simulation mode mutability frozen facts hunpin hunsafeUnpin hfreeze

example (facts : Miri.TreeBorrows.RetagPolicy.TypeFacts)
    (kind : Miri.TreeBorrows.RetagPolicy.ReferenceKind)
    (config : Miri.TreeBorrows.RetagPolicy.PolicyConfig)
    (policy : Miri.TreeBorrows.RetagPolicy.NewPermission)
    (h : Miri.TreeBorrows.RetagPolicy.create facts kind .FnEntry config = some policy) :
    policy.freezePermission ≠ .ReservedIM ∧
    policy.nonfreezePermission ≠ .ReservedIM ∧
    policy.outsidePermission ≠ .ReservedIM :=
  @miri_fnEntry_policy_never_reservedIM facts kind config policy h

example (tree : Miri.TreeBorrows.Tree.TraversalTree) (start : Nat) :
    tree.ancestorPath start = traversalAncestorPathAux tree tree.nodes.size start :=
  @ancestorPath_eq_traversalAncestorPathAux tree start

example (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (skipNodes : List Nat) :
    ∀ (fuel index : Nat) (event : Miri.TreeBorrows.Tree.TraversalEvent),
      event ∈ traversalForeignPostorder tree skipNodes fuel index →
      event.relatedness = .ForeignAccess :=
  @traversalForeignPostorder_foreign tree skipNodes

example (tree : Miri.TreeBorrows.Tree.TraversalTree)
    (start : Nat) (mode : Miri.TreeBorrows.Tree.ChildrenVisitMode) (skipNodes : List Nat) :
    ∃ foreignEvents,
      (tree.traverse start mode skipNodes).2 =
        (tree.ancestorPath start).map (fun index => ⟨index, .LocalAccess⟩) ++ foreignEvents ∧
      ∀ event ∈ foreignEvents, event.relatedness = .ForeignAccess :=
  @traverse_local_then_foreign tree start mode skipNodes

example {α : Type} (xs : List α) :
    length xs = xs.length :=
  @sequence_length_eq α xs

example (borrows : List BorrowEntry) :
    (annealTraversalTree borrows).nodes.size = borrows.length :=
  @annealTraversalTree_size borrows

example (borrows : List BorrowEntry) (s : Nat)
    (hs : s < borrows.length) :
    (annealTraversalTree borrows).nodes[s]?.getD ⟨none, []⟩ =
      annealTraversalNode borrows borrows[s] :=
  @annealTraversalTree_node borrows s hs

example {entry : BorrowEntry} {rest : List BorrowEntry}
    (h : BorrowTagsUnique (entry :: rest)) :
    BorrowTagsUnique rest :=
  @BorrowTagsUnique.tail entry rest h

example {entry : BorrowEntry} {rest : List BorrowEntry}
    (h : BorrowTagsUnique (entry :: rest)) (j : Nat) (hj : j < rest.length) :
    entry.tag ≠ rest[j].tag :=
  @BorrowTagsUnique.head_ne entry rest h j hj

example (borrows : List BorrowEntry) (huniq : BorrowTagsUnique borrows)
    (j : Nat) (hj : j < borrows.length) :
    lookupBorrow borrows borrows[j].tag = some borrows[j] :=
  @lookupBorrow_getElem borrows huniq j hj

example (borrows : List BorrowEntry)
    (huniq : BorrowTagsUnique borrows) (j : Nat) (hj : j < borrows.length) :
    borrowIndexOfTag borrows borrows[j].tag = some j :=
  @borrowIndexOfTag_getElem borrows huniq j hj

example (borrows : List BorrowEntry) (tag p : Nat)
    (h : borrowIndexOfTag borrows tag = some p) :
    ∃ hp : p < borrows.length, borrows[p].tag = tag :=
  @borrowIndexOfTag_some borrows tag p h

example (borrows : List BorrowEntry) (tag : Nat)
    (h : borrowIndexOfTag borrows tag = none) :
    lookupBorrow borrows tag = none ∧
      ∀ (j : Nat) (hj : j < borrows.length), borrows[j].tag ≠ tag :=
  @borrowIndexOfTag_none borrows tag h

example (borrows : List BorrowEntry) (tag : Nat)
    (hlookup : lookupBorrow borrows tag = none)
    (hne : ∀ (j : Nat) (hj : j < borrows.length), borrows[j].tag ≠ tag)
    (n i : Nat) (hi : i < borrows.length) :
    isBorrowDescendantOrSelfAux n borrows tag borrows[i].tag = false :=
  @isBorrowDescendantOrSelfAux_absent borrows tag hlookup hne n i hi

example (borrows : List BorrowEntry)
    (huniq : BorrowTagsUnique borrows) (i : Nat) (hi : i < borrows.length) :
    ∀ (n s : Nat) (hs : s < borrows.length),
      i ∈ traversalAncestorPathAux (annealTraversalTree borrows) n s ↔
        isBorrowDescendantOrSelfAux n borrows borrows[s].tag borrows[i].tag = true :=
  @traversalAncestorPathAux_iff borrows huniq i hi

example (borrows : List BorrowEntry)
    (huniq : BorrowTagsUnique borrows) (s : Nat) (hs : s < borrows.length)
    (mode : Miri.TreeBorrows.Tree.ChildrenVisitMode) (skipNodes : List Nat) :
    (∃ foreignEvents,
      ((annealTraversalTree borrows).traverse s mode skipNodes).2 =
        ((annealTraversalTree borrows).ancestorPath s).map
            (fun index => ⟨index, .LocalAccess⟩) ++ foreignEvents ∧
      ∀ event ∈ foreignEvents, event.relatedness = .ForeignAccess) ∧
    (∀ (i : Nat) (hi : i < borrows.length),
      i ∈ (annealTraversalTree borrows).ancestorPath s ↔
        isBorrowDescendantOrSelf borrows borrows[s].tag borrows[i].tag = true) ∧
    (∀ (i : Nat) (hi : i < borrows.length) (kind : TreeBorrowAccessKind)
        (isProtected : Bool) (sifa : Miri.TreeBorrows.IdempotentForeignAccess),
      let rel : TreeBorrowRelatedness :=
        if isBorrowDescendantOrSelf borrows borrows[s].tag borrows[i].tag = true
        then .localAccess else .foreignAccess
      (rel = .foreignAccess → borrows[i].perm ≠ .disabled) →
      match treeBorrowNodeAccess kind rel borrows[i].perm isProtected with
      | .transition next =>
        ∃ transition,
          Miri.TreeBorrows.Tree.LocationState.performAccess
              ⟨annealPermToMiri borrows[i].perm, true, sifa⟩
              (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
            .Success ⟨annealPermToMiri next, true, sifa⟩ transition
      | .ub =>
        ∃ state error,
          Miri.TreeBorrows.Tree.LocationState.performAccess
              ⟨annealPermToMiri borrows[i].perm, true, sifa⟩
              (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
            .Error state error
      | .protectedReservedIM =>
        Miri.TreeBorrows.Tree.LocationState.performAccess
            ⟨annealPermToMiri borrows[i].perm, true, sifa⟩
            (annealAccessKindToMiri kind) (annealRelatednessToMiri rel) isProtected =
          .PermissionInvariantFailure ⟨annealPermToMiri borrows[i].perm, true, sifa⟩) :=
  @normalTree_relative_access_simulation borrows huniq s hs mode skipNodes

example (borrows : List BorrowEntry)
    (h : (borrows.map BorrowEntry.tag).Nodup) :
    BorrowTagsUnique borrows :=
  @borrowTagsUnique_of_nodup borrows h

example (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    (annealPermToMiri (annealRetagPerm mode mutability frozen)).associatedAccess =
      (match annealRetagPerm mode mutability frozen with
       | .cell => none
       | _ => some Miri.TreeBorrows.AccessKind.Read) :=
  @retagPointerValue_associatedAccess_simulation mode mutability frozen

example (state : Miri.TreeBorrows.RetagPipeline.MachineState Unit)
    (request : Miri.TreeBorrows.RetagPipeline.Request)
    (hshape : request.typeShape = .rawPointer) :
    Miri.TreeBorrows.RetagPipeline.retagPointerValue state request =
      if request.mode = .Raw then
        { state := state, outcome := .ok none, events := #[] }
      else
        { state := state, outcome := .error .rawPointerWrongMode, events := #[] } :=
  @retagPointerValue_rawPointer_simulation state request hshape

example (allBorrows : List BorrowEntry) (tag : Nat) :
    isBorrowDescendantOrSelf allBorrows tag tag = true :=
  @isBorrowDescendantOrSelf_self_eq_true allBorrows tag

example (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    treeBorrowWriterRelatedness entry
      (resolveTreeBorrowWriterTag allBorrows entry writerTag) =
      treeBorrowAccessRelatedness allBorrows entry writerTag :=
  @treeBorrowWriterRelatedness_resolveTreeBorrowWriterTag allBorrows entry writerTag

example (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (hloc : entry.targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = true) :
    borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
        readProj readRangeOff readRangeLen =
      treeBorrowTransitionIsUB
        (treeBorrowNodeAccess .read
          (treeBorrowAccessRelatedness allBorrows entry readerTag)
          entry.perm
          (isBorrowProtected activeProtectors entry)) :=
  @borrowEntryReadUB_eq_nodeAccess allBorrows activeProtectors entry targetLocal
    readerTag readProj readRangeOff readRangeLen hloc hov

example (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hloc : entry.targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = true) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors =
      applyTreeBorrowTransition entry
        (treeBorrowNodeAccess .read
          (treeBorrowAccessRelatedness allBorrows entry readerTag)
          entry.perm
          (isBorrowProtected activeProtectors entry)) :=
  @updateBorrowPermOnReadAtProj_eq_nodeAccess allBorrows entry targetLocal readerTag
    readProj readRangeOff readRangeLen activeProtectors hloc hov

example (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat) :
    hasTreeReadUB allBorrows borrows activeProtectors targetLocal readerTag
        readProj readRangeOff readRangeLen = true ↔
      ∃ entry ∈ borrows,
        borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
          readProj readRangeOff readRangeLen = true :=
  @hasTreeReadUB_iff_exists allBorrows borrows activeProtectors targetLocal
    readerTag readProj readRangeOff readRangeLen

example (allBorrows : List BorrowEntry)
    (entry : BorrowEntry)
    (writerTag : Option Nat) :
    borrowEntryWriteConflicts entry
        (resolveTreeBorrowWriterTag allBorrows entry writerTag) =
      treeBorrowTransitionIsUB
        (treeBorrowNodeAccess .write
          (treeBorrowAccessRelatedness allBorrows entry writerTag)
          entry.perm
          true) :=
  @borrowEntryWriteConflicts_resolve_eq_nodeAccess allBorrows entry writerTag

example (allBorrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (entry : BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hloc : entry.targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = true)
    (hno_prot_ub :
      Bool.and (isBorrowProtected activeProtectors entry)
        (borrowEntryWriteConflicts entry
          (resolveTreeBorrowWriterTag allBorrows entry writerTag)) = false) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag
        writeProj writeRangeOff writeRangeLen =
      applyTreeBorrowTransition entry
        (treeBorrowNodeAccess .write
          (treeBorrowAccessRelatedness allBorrows entry writerTag)
          entry.perm
          (isBorrowProtected activeProtectors entry)) :=
  @updateBorrowPermTreeAtProj_eq_nodeAccess allBorrows activeProtectors entry targetLocal
    writerTag writeProj writeRangeOff writeRangeLen hloc hov hno_prot_ub

example (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    hasProtectedTreeWriteConflict allBorrows borrows activeProtectors targetLocal
        writerTag writeProj writeRangeOff writeRangeLen = true ↔
      ∃ entry ∈ borrows,
        Bool.and (Nat.beq entry.targetLocal targetLocal)
          (Bool.and (borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen)
            (Bool.and (isBorrowProtected activeProtectors entry)
              (treeBorrowTransitionIsUB
                (treeBorrowNodeAccess .write
                  (treeBorrowAccessRelatedness allBorrows entry writerTag)
                  entry.perm true)))) = true :=
  @hasProtectedTreeWriteConflict_iff_exists allBorrows borrows activeProtectors targetLocal
    writerTag writeProj writeRangeOff writeRangeLen

example (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat) :
    freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal readerTag
        readProj readRangeOff readRangeLen activeProtectors =
      borrows.map (fun e =>
        updateBorrowPermOnReadAtProj allBorrows e targetLocal readerTag
          readProj readRangeOff readRangeLen activeProtectors) :=
  @freezeTreeBorrowsOnReadAtProj_eq_map allBorrows borrows targetLocal readerTag
    readProj readRangeOff readRangeLen activeProtectors

example (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    invalidateTreeBorrowsAtProj allBorrows borrows targetLocal writerTag
        writeProj writeRangeOff writeRangeLen =
      borrows.map (fun e =>
        updateBorrowPermTreeAtProj allBorrows e targetLocal writerTag
          writeProj writeRangeOff writeRangeLen) :=
  @invalidateTreeBorrowsAtProj_eq_map allBorrows borrows targetLocal writerTag
    writeProj writeRangeOff writeRangeLen

example (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (i : Nat) (hi : i < borrows.length) :
    (basedNormalTree borrows activeProtectors).stateAt i =
      some ⟨annealPermToMiri borrows[i].perm, true, .None⟩ :=
  @basedNormalTree_stateAt_lt borrows activeProtectors i hi

example (borrows : List BorrowEntry) (activeProtectors : List Nat) :
    (basedNormalTree borrows activeProtectors).stateAt borrows.length =
      some ⟨.Unique, true, .None⟩ :=
  @basedNormalTree_stateAt_base borrows activeProtectors

example (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (hnodup : (borrows.map BorrowEntry.tag).Nodup) :
    TreeBorrowsRel borrows activeProtectors (basedNormalTree borrows activeProtectors) :=
  @basedNormalTree_rel borrows activeProtectors hnodup

example (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hnodup : (borrows.map BorrowEntry.tag).Nodup) :
    let borrows' := freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal
      readerTag readProj readRangeOff readRangeLen activeProtectors
    (borrows'.map BorrowEntry.tag).Nodup ∧
      TreeBorrowsRel borrows' activeProtectors (basedNormalTree borrows' activeProtectors) :=
  @freezeTreeBorrowsOnReadAtProj_preserves_rel allBorrows borrows targetLocal
    readerTag readProj readRangeOff readRangeLen activeProtectors hnodup

example (allBorrows borrows : List BorrowEntry)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (activeProtectors : List Nat)
    (hnodup : (borrows.map BorrowEntry.tag).Nodup) :
    let borrows' := invalidateTreeBorrowsAtProj allBorrows borrows targetLocal
      writerTag writeProj writeRangeOff writeRangeLen
    (borrows'.map BorrowEntry.tag).Nodup ∧
      TreeBorrowsRel borrows' activeProtectors (basedNormalTree borrows' activeProtectors) :=
  @invalidateTreeBorrowsAtProj_preserves_rel allBorrows borrows targetLocal
    writerTag writeProj writeRangeOff writeRangeLen activeProtectors hnodup

example (retagKind : RetagKind) (mutability : Mutability) (pointee : RigidTy) :
    retagPerm retagKind mutability pointee =
      annealRetagPerm (retagKindToAnnealMode retagKind) mutability
        (rigidTyIsFreeze 16 pointee) :=
  @annealRetagPerm_eq_retagPerm retagKind mutability pointee

example (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    let rootTree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let facts : Miri.TreeBorrows.RetagPolicy.TypeFacts :=
      { isUnpin := true, isUnsafeUnpin := true, isFreeze := frozen }
    let perm := annealRetagPerm mode mutability frozen
    ∃ policy st,
      Miri.TreeBorrows.RetagPolicy.create facts (annealRefKindToMiri mutability)
        (annealRetagModeToMiri mode) ⟨false, false⟩ = some policy ∧
      Miri.TreeBorrows.RetagPolicy.initialLocationState policy frozen = .ok st ∧
      let inside := Miri.DataStructures.DedupRangeMap.new (Miri.ABI.Size.ofBytes 8) st
      let child := rootTree.newChild Miri.ABI.Size.ZERO (.concrete retagParentTag)
        retagChildTag inside policy.outsidePermission policy.protector.isSome
      child.outcome = .ok () ∧
      child.tree.nthParent retagChildTag 1 = .ok retagParentTag ∧
      (borrowTreeTagLocationState child.tree retagChildTag).map
          (fun s => (s.permission, s.accessed)) =
        some (annealPermToMiri perm, annealPermToMiri perm != .Cell) :=
  @borrowTree_newChild_reference_simulation mode mutability frozen

example (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    let res := Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest Miri.ABI.Size.ZERO mode mutability frozen)
    res.outcome = .ok (some (.concrete retagTestAllocId retagChildTag)) ∧
    res.state.global.protectedTags.contains retagChildTag = (mode == .fnEntry) ∧
    res.state.frame.protectedTags =
      (if mode == .fnEntry then #[(retagTestAllocId, retagChildTag)] else #[]) ∧
    (res.state.global.endCall res.state.frame).protectedTags.contains retagChildTag = false ∧
    Miri.TreeBorrows.RetagPipeline.Event.childInserted retagChildTag ∈ res.events.toList ∧
    (res.state.memory.live.find? fun e => e.1 == retagTestAllocId).bind
        (fun e => (e.2.allocation.extra.nthParent retagChildTag 1).toOption) =
      some retagParentTag :=
  @retagPointerValue_zst_reference_simulation mode mutability frozen

example (mode : AnnealRetagMode) :
    let res := Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest (Miri.ABI.Size.ofBytes 8) mode .not false)
    res.outcome = .ok (some (.concrete retagTestAllocId retagChildTag)) ∧
    res.state.global.protectedTags.contains retagChildTag = (mode == .fnEntry) ∧
    res.state.frame.protectedTags =
      (if mode == .fnEntry then #[(retagTestAllocId, retagChildTag)] else #[]) ∧
    (res.state.global.endCall res.state.frame).protectedTags.contains retagChildTag = false ∧
    (∀ k r, Miri.TreeBorrows.RetagPipeline.Event.parentTreeAccess k r ∉ res.events.toList) ∧
    Miri.TreeBorrows.RetagPipeline.Event.childInserted retagChildTag ∈ res.events.toList ∧
    (res.state.memory.live.find? fun e => e.1 == retagTestAllocId).bind
        (fun e => (e.2.allocation.extra.nthParent retagChildTag 1).toOption) =
      some retagParentTag ∧
    (liveTagLocationState res.state.memory retagChildTag).map
        (fun s => (s.permission, s.accessed)) =
      some (.Cell, false) :=
  @retagPointerValue_cell_8byte_simulation mode

example (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    let res := (hooksTwoNodeTree perm).performNormalAccessAt (hooksLocTree perm)
      (hooksAccessIndex rel) (annealAccessKindToMiri kind)
      (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
    let out := treeBorrowNodeAccess kind rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    res.outcome = .ok () ∧
    (res.access.status = .Completed ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.access.status = .Completed →
      (res.location.perms.get ⟨1⟩).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) :=
  @borrowTree_performNormalAccessAt_simulation kind rel perm isProtected

example (isProtected : Bool) :
    let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId retagParentTag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete retagParentTag) range
    res.outcome = .ok () ∧ res.memory = mem :=
  @machineMemoryHooks_fresh_root_write_simulation isProtected

example (size : Miri.ABI.Size) (hpos : size.bytes ≠ 0)
    (borrows : List BorrowEntry) (activeProtectors : List Nat)
    (start : Nat) (kind : Miri.TreeBorrows.AccessKind)
    (mode : Miri.TreeBorrows.Tree.ChildrenVisitMode) :
    let nt := basedNormalTree borrows activeProtectors
    let rt := Miri.TreeBorrows.Tree.RangedNormalTreeState.new size
      nt.topology nt.defaultStates nt.protectedNodes nt.locationStates
    let nres := nt.performAccess start kind mode
    let rres := rt.performAccessRange Miri.ABI.Size.ZERO size start kind mode
    rres.locations = #[⟨⟨0, size.bytes⟩, nres⟩] ∧
    (rres.status = .Completed ↔ nres.status = .Completed) ∧
    rres.state.locations = Miri.DataStructures.DedupRangeMap.new size nres.tree.locationStates :=
  @rangedNormalTree_performAccessRange_simulation size hpos borrows activeProtectors start kind mode

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (perm : TreeBorrowPerm) (isProtected : Bool) :
    TreeBorrowsRel (childState perm isProtected).memory.borrows (activeOf isProtected)
      (basedNormalTree (childState perm isProtected).memory.borrows (activeOf isProtected)) ∧
    StepTreeRel (stepMirFn childWriteBody (childState perm isProtected))
      ((basedNormalTree (childState perm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Write .VisitChildrenOfAccessed) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_child_write_step perm isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (perm : TreeBorrowPerm) (isProtected : Bool) :
    StepTreeRel (stepMirFn childReadBody (childState perm isProtected))
      ((basedNormalTree (childState perm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Read .VisitChildrenOfAccessed) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_child_read_step perm isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (perm : TreeBorrowPerm) (isProtected : Bool) :
    TreeBorrowsRel (foreignState perm .unique isProtected).memory.borrows
      (activeOf isProtected)
      (basedNormalTree (foreignState perm .unique isProtected).memory.borrows
        (activeOf isProtected)) ∧
    StepTreeRel (stepMirFn foreignWriteBody (foreignState perm .unique isProtected))
      ((basedNormalTree (foreignState perm .unique isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Write .VisitChildrenOfAccessed) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_foreign_write_step perm isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (perm : TreeBorrowPerm) (isProtected : Bool) :
    StepTreeRel (stepMirFn foreignReadBody (foreignState perm .frozen isProtected))
      ((basedNormalTree (foreignState perm .frozen isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Read .VisitChildrenOfAccessed) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_foreign_read_step perm isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (parentPerm childPerm : TreeBorrowPerm) (isProtected : Bool) :
    TreeBorrowsRel (reborrowHierarchyState parentPerm childPerm isProtected).memory.borrows
      (activeOf isProtected)
      (basedNormalTree (reborrowHierarchyState parentPerm childPerm isProtected).memory.borrows
        (activeOf isProtected)) ∧
    StepTreeRel
      (stepMirFn foreignWriteBody (reborrowHierarchyState parentPerm childPerm isProtected))
      ((basedNormalTree (reborrowHierarchyState parentPerm childPerm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 0 .Write .VisitChildrenOfAccessed) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_reborrow_child_write_step
    parentPerm childPerm isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (childPerm : TreeBorrowPerm) (isProtected : Bool) :
    StepTreeRel
      (stepMirFn childWriteBody (reborrowHierarchyState .unique childPerm isProtected))
      ((basedNormalTree (reborrowHierarchyState .unique childPerm isProtected).memory.borrows
        (activeOf isProtected)).performAccess 1 .Write .VisitChildrenOfAccessed) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_reborrow_parent_write_invalidates_child_step
    childPerm isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (rk : RetagKind) (mutability : Mutability) (frozen : Bool) :
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability frozen
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let siblingPerm := match childPerm with | .cell => TreeBorrowPerm.unique | _ => .frozen
    let activeProts := match rk with | .fnEntry => [2] | _ => []
    ∃ s' : MachineState,
      stepMirFn (retagRefBody rk mutability frozen) retagRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt, entry 2 siblingPerm, entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_ref_step rk mutability frozen

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (rk : RetagKind) (mutability : Mutability)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    match rk with
    | .raw =>
      ∃ s' : MachineState,
        stepMirFn (retagRawBody rk mutability) (childState perm isProtected) = .step s' ∧
        s'.memory = (childState perm isProtected).memory ∧
        get? s'.frame.locals 2 = some (.init (.ptr ⟨1, 0⟩ 8))
    | .default | .twoPhase | .fnEntry =>
      stepMirFn (retagRawBody rk mutability) (childState perm isProtected) = .fail .ub :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_raw_step rk mutability perm isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyA initA = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyA s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .reserved (some 1), entry 1 .reserved] ∧
      stepMirFn bodyA s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .frozen (some 1), entry 2 .reserved (some 1), entry 1 .reserved] ∧
      stepMirFn bodyA s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .disabled (some 1), entry 2 .unique (some 1), entry 1 .unique] ∧
      get? s₄.frame.locals 1 = some (.init (.scalar ⟨99, 8⟩)) ∧
      stepMirFn bodyA s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 3 .disabled (some 1), entry 2 .frozen (some 1), entry 1 .unique] ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      TreeBorrowsRel s₃.memory.borrows []
        (basedNormalTree s₃.memory.borrows []) ∧
      ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₄.memory.borrows []
        ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree.performAccess 2 .Read
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₅.memory.borrows []
        (((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree.performAccess 2 .Read
          .VisitChildrenOfAccessed).tree :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_reborrow_hierarchy_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ : MachineState,
      stepMirFn bodyB initBC = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyB s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      s₂.memory.activeProtectors = [1] ∧
      get? s₂.frame.locals 2 = some (.init (.ptr ⟨2, 0⟩ 8)) ∧
      stepMirFn bodyB s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn bodyB s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz true) (some 1) (some 1), entry 1 .reserved] ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨5, 8⟩)) ∧
      stepMirFn bodyB s₄ = .fail .ub ∧
      TreeBorrowsRel s₃.memory.borrows [1] (basedNormalTree s₃.memory.borrows [1]) ∧
      ((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₄.memory.borrows [1]
        ((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₃.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).tree.performAccess 1 .Write
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden (.ReservedFrz true)) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_protected_conflict_ub_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ : MachineState,
      stepMirFn bodyC initBC = .step s₁ ∧
      stepMirFn bodyC s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn bodyC s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨9, 8⟩)) ∧
      stepMirFn bodyC s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyC s₄ = .fail .ub ∧
      TreeBorrowsRel s₄.memory.borrows [1] (basedNormalTree s₄.memory.borrows [1]) ∧
      ((basedNormalTree s₄.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ProtectedDisabled .Unique) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_protected_unique_foreign_read_ub_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    (∃ s₁ s₂ s₃ s₄ : MachineState,
      stepMirFn (bodyD unsafeCellU32T) initD = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .cell] ∧
      stepMirFn (bodyD unsafeCellU32T) s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .unique, entry 1 .cell] ∧
      stepMirFn (bodyD unsafeCellU32T) s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .cell] ∧
      stepMirFn (bodyD unsafeCellU32T) s₃ = .step s₄ ∧
      get? s₄.frame.locals 0 = some (.init (.scalar ⟨7, 4⟩)) ∧
      ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₃.memory.borrows []
        ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree.performAccess 1 .Read
          .VisitChildrenOfAccessed).status = .Completed) ∧
    (∃ s₁ s₂ s₃ : MachineState,
      stepMirFn (bodyD u32T) initD = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .frozen] ∧
      stepMirFn (bodyD u32T) s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .unique, entry 1 .frozen] ∧
      stepMirFn (bodyD u32T) s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .disabled] ∧
      stepMirFn (bodyD u32T) s₃ = .fail .ub ∧
      ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₃.memory.borrows []
        ((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree ∧
      (((basedNormalTree s₂.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree.performAccess 1 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden .Disabled)) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_unsafe_cell_vs_freeze_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyE initD = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reservedIM] ∧
      stepMirFn bodyE s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .unique, entry 1 .reservedIM] ∧
      stepMirFn bodyE s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .reservedIM] ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨10, 4⟩)) ∧
      stepMirFn bodyE s₃ = .step s₄ ∧
      s₄.memory.borrows = [entry 2 .disabled, entry 1 .unique] ∧
      get? s₄.frame.locals 1 = some (.init (.scalar ⟨20, 4⟩)) ∧
      stepMirFn bodyE s₄ = .step s₅ ∧
      s₅.memory.borrows = [entry 2 .disabled, entry 1 .disabled] ∧
      stepMirFn bodyE s₅ = .fail .ub ∧
      ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₄.memory.borrows []
        ((basedNormalTree s₃.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree ∧
      ((basedNormalTree s₅.memory.borrows []).performAccess 1 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 1 (.ChildAccessForbidden .Disabled) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_reservedIM_lifecycle_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyF initF = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .cell] ∧
      stepMirFn bodyF s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .reservedIM, entry 1 .cell] ∧
      stepMirFn bodyF s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique, entry 1 .cell] ∧
      stepMirFn bodyF s₃ = .step s₄ ∧
      s₄.memory.borrows = [entry 3 .cell (some 1), entry 2 .unique, entry 1 .cell] ∧
      stepMirFn bodyF s₄ = .step s₅ ∧
      s₅.memory.borrows = [entry 3 .cell (some 1), entry 2 .unique, entry 1 .cell] ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨99, 4⟩)) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_cell_reborrow_preserves_unique_real_steps

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  annealPermToMiri
  miriPermToAnneal
  annealAccessKindToMiri
  annealRelatednessToMiri
  miriAccessKindToAnneal
  miriRelatednessToAnneal
  annealTransitionToMiri
  AnnealRetagMode
  annealRetagModeToMiri
  annealRetagPerm
  annealRefKindToMiri
  retagKindToAnnealMode
  retagTestAllocId
  retagParentTag
  retagChildTag
  baseRetagAllocation
  liveTreeAllocation
  liveTreeMemory
  borrowTreeTagLocationState
  liveTagLocationState
  retagInitialMachineState
  retagRefRequest
  hooksLocTree
  hooksTwoNodes
  hooksTwoNodeTree
  hooksForChildProtected
  hooksAccessIndex
  traversalAncestorPathAux
  traversalForeignPostorder
  borrowIndexOfTag
  annealTraversalNode
  annealTraversalTree
  BorrowTagsUnique
  basedParentIndex
  basedChildren
  basedTraversalTree
  protectedIndices
  basedNormalTree
  normalTreePerms
  TreeBorrowsRel
  treeBorrowAccessRelatedness
  SimLM3_3.StepTreeRel
  SimLM3_3.childWriteBody
  SimLM3_3.childReadBody
  SimLM3_3.foreignWriteBody
  SimLM3_3.foreignReadBody
  SimLM3_3.childState
  SimLM3_3.foreignState
  SimLM3_3.reborrowHierarchyState
  SimLM3_3.retagPointeeTy
  SimLM3_3.retagRefBody
  SimLM3_3.retagRefState
  SimLM3_3.retagRawBody
  WitnessLM3_3.bodyA
  WitnessLM3_3.bodyB
  WitnessLM3_3.bodyC
  WitnessLM3_3.bodyD
  WitnessLM3_3.bodyE
  WitnessLM3_3.bodyF
  WitnessLM3_3.initF
  miriPermToAnneal_annealPermToMiri
  annealPermToMiri_miriPermToAnneal
  TreeBorrowsBijection
  annealPermToMiri_injective
  annealPermToMiri_legacy
  performAccess_permission_simulation
  performAccess_permission_simulation_miri
  protectedReservedIM_characterization
  fnEntryRetagPerm_ne_reservedIM
  nodeAccess_locationState_simulation
  disabled_foreign_access_skipped
  protected_write_success_eq_unprotected
  unsafeCell_permission_simulation
  reservedFrz_conflicted_bijection
  reservedFrz_conflicted_protected_foreign
  annealRetagPerm_eq_trusted
  annealRetagPerm_eq_retagPerm
  retag_pipeline_simulation
  miri_fnEntry_policy_never_reservedIM
  retagPointerValue_associatedAccess_simulation
  retagPointerValue_rawPointer_simulation
  borrowTree_newChild_reference_simulation
  retagPointerValue_zst_reference_simulation
  retagPointerValue_cell_8byte_simulation
  borrowTree_performNormalAccessAt_simulation
  machineMemoryHooks_fresh_root_write_simulation
  ancestorPath_eq_traversalAncestorPathAux
  traversalForeignPostorder_foreign
  traverse_local_then_foreign
  sequence_length_eq
  annealTraversalTree_size
  annealTraversalTree_node
  BorrowTagsUnique.tail
  BorrowTagsUnique.head_ne
  lookupBorrow_getElem
  borrowIndexOfTag_getElem
  borrowIndexOfTag_some
  borrowIndexOfTag_none
  isBorrowDescendantOrSelfAux_absent
  traversalAncestorPathAux_iff
  normalTree_relative_access_simulation
  borrowTagsUnique_of_nodup
  isBorrowDescendantOrSelf_self_eq_true
  treeBorrowWriterRelatedness_resolveTreeBorrowWriterTag
  borrowEntryReadUB_eq_nodeAccess
  updateBorrowPermOnReadAtProj_eq_nodeAccess
  hasTreeReadUB_iff_exists
  borrowEntryWriteConflicts_resolve_eq_nodeAccess
  updateBorrowPermTreeAtProj_eq_nodeAccess
  hasProtectedTreeWriteConflict_iff_exists
  freezeTreeBorrowsOnReadAtProj_eq_map
  invalidateTreeBorrowsAtProj_eq_map
  basedNormalTree_stateAt_lt
  basedNormalTree_stateAt_base
  basedNormalTree_rel
  freezeTreeBorrowsOnReadAtProj_preserves_rel
  invalidateTreeBorrowsAtProj_preserves_rel
  rangedNormalTree_performAccessRange_simulation
  SimLM3_3.sim_lm3_3_child_write_step
  SimLM3_3.sim_lm3_3_child_read_step
  SimLM3_3.sim_lm3_3_foreign_write_step
  SimLM3_3.sim_lm3_3_foreign_read_step
  SimLM3_3.sim_lm3_3_reborrow_child_write_step
  SimLM3_3.sim_lm3_3_reborrow_parent_write_invalidates_child_step
  SimLM3_3.sim_lm3_3_retag_ref_step
  SimLM3_3.sim_lm3_3_retag_raw_step
  WitnessLM3_3.wit_lm3_3_reborrow_hierarchy_real_steps
  WitnessLM3_3.wit_lm3_3_protected_conflict_ub_real_steps
  WitnessLM3_3.wit_lm3_3_protected_unique_foreign_read_ub_real_steps
  WitnessLM3_3.wit_lm3_3_unsafe_cell_vs_freeze_real_steps
  WitnessLM3_3.wit_lm3_3_reservedIM_lifecycle_real_steps
  WitnessLM3_3.wit_lm3_3_cell_reborrow_preserves_unique_real_steps

end StatementPins

-- Exhaustively verify standard axioms across all imported `LeanMiriSpec.*` and
-- `Miri.*` modules AND every constant elaborated in `LeanMiriSpec.Audit` itself.
#assert_all_leanmirispec_and_miri_standard_axioms

end LeanMiriSpec.Audit
