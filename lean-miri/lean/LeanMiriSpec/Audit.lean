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
import LeanMiriSpec.Correspondence.LayoutLM2_2
import LeanMiriSpec.Correspondence.ProjLM2_2
import LeanMiriSpec.Correspondence.SimLM2_2
import LeanMiriSpec.Correspondence.WitLM2_2
import LeanMiriSpec.Correspondence.EnumLM2_3
import LeanMiriSpec.Correspondence.SimLM2_3
import LeanMiriSpec.Correspondence.WitLM2_3
import LeanMiriSpec.Correspondence.UnionLM2_4
import LeanMiriSpec.Correspondence.SimLM2_4
import LeanMiriSpec.Correspondence.WitLM2_4
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
`Lean.ofReduceBool` (which native-code `decide` evaluation would introduce).

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
  step_binOp_offset_disabled_divergence
  step_binOp_offset_oob_dangling_miri_ub
  WellTypedLM3_1StateStmt
  step_stmt_lm3_1_state_simulation
  Witness.wit_lm3_1_rawPtr_step
  Witness.wit_lm3_1_addrOf_write_read_deref
  Witness.wit_lm3_1_binOp_offset_inbounds_and_oob
  Witness.wit_lm3_1_anneal_offset_deref_agreement
  Witness.wit_lm3_1_anneal_storage_revive_agreement
  Witness.wit_lm3_1_anneal_deref_type_pun_agreement
  step_deref_oob_simulation
  lookupBorrow_map_toBorrowEntry_parentTag
  derefWriteTreeUB_map_toBorrowEntry_eq_false
  hasTreeReadUB_map_toBorrowEntry_eq_false
  perm_ne_disabled_of_tag_eq_of_nodup
  derefReadTreeUB_map_toBorrowEntry_eq_false
  Witness.wit_lm3_1_use_after_storageDead_ub
  Witness.wit_lm3_1_addrOf_deref_storageDead_real_steps
  Witness.wit_lm3_1_use_after_storageDead_real_steps
  Witness.wit_lm3_1_ptrToPtr_and_offset_real_steps
  Witness.lm31OffsetDisabledBody
  Witness.wit_lm3_1_binOp_offset_disabled_divergence
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
  step_deref_misaligned_simulation
  step_deref_invalid_bool_simulation
  ptrOffsetInbounds_neg_one_live_ok
  step_binOp_offset_stride_simulation
  step_binOp_offset_neg_isize_simulation
  Witness.wit_lm3_1_two_promotions_reborrow_and_direct_write_real_steps
  Witness.wit_lm3_1_invalid_bool_cast_deref_real_steps
  Witness.wit_lm3_1_offset_stride_and_neg_isize_real_steps
  step_placeMention_local_lm3_1_simulation
  step_placeMention_deref_lm3_1_simulation
  evalCast_ptrToPtr_annealCastHooks_simulation
  lookupDerefPointeeLayout_ref_eq_none
  annealValidateScalarForTyId_never_false
  annealValidateScalarForTyId_nonNullPtr_null_false
  step_deref_invalid_char_simulation
  step_deref_write_invalid_bool_simulation
  step_placeMention_deref_uninit_simulation
  annealForceAllocation_memory_eq
  memPlace_toRef_withoutProvenance
  step_rawPtr_deref_null_correspondence
  step_rawPtr_deref_nonzero_offset_correspondence
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
  step_cast_ptrToPtr_scalar_correspondence
  step_binOp_offset_scalar_zero_correspondence
  step_binOp_offset_scalar_nonzero_simulation
  step_rawPtr_deref_perm_correspondence
  step_rawPtr_deref_zero_offset_correspondence
  Witness.wit_lm3_1_rawPtr_use_move_and_expose_scalar_real_steps
  Witness.wit_lm3_1_null_ptrToPtr_and_offset_correspondences_real_steps
  Witness.wit_lm3_1_rawPtr_deref_zero_and_perm_correspondence_real_steps
  annealExecutionScalarLeaves
  annealDerefValidity
  annealDerefValidity_nonThin_or_ref_err
  step_rawPtr_cmp_scalar_lm3_1_simulation
  step_binOp_offset_zero_any_stride_lm3_1_simulation
  step_unaryOp_ptrMetadata_thin_rawPtr_ub_simulation
  step_unaryOp_ptrMetadata_thin_rawPtr_correspondence
  step_rawPtr_cmp_ptr_divergence
  step_cast_ptrToPtr_move_scalar_correspondence
  step_binOp_offset_move_scalar_zero_correspondence
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
  step_binOp_offset_move_scalar_nonzero_simulation
  WellTypedLM3_1StateTerminator
  step_terminator_lm3_1_state_simulation
  step_mir_lm3_1_state_simulation
  Witness.wit_lm3_1_cmp_symm_move_ub_and_unified_step_real_steps
  step_safeRef_deref_read_invalid_scalar_simulation
  evalRvalue_reborrow_safeRef_tree_simulation
  step_safeRef_deref_read_tree_simulation
  step_safeRef_deref_write_tree_simulation
  treeMap_ancestorOrSelf_not_disabled
  hasTreeReadUB_treeMap_eq_false
  derefReadTreeUB_treeMap_eq_false
  derefWriteTreeUB_treeMap_eq_false
  step_terminator_goto_return_tree_simulation
  Witness.wit_lm3_2_ref_never_and_enum_discriminant_validity
  Witness.wit_lm3_2_invalid_bool_deref_read_ub_real_steps
  Witness.wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  annealReadImmediateLM2_2
  annealWriteImmediateLM2_2
  annealCastHooksLM2_2
  annealTerminatorHooksLM2_2
  annealStepHooksLM2_2
  valueLeafBytes
  annealFieldLayout
  annealMutablePlaceHooks
  annealWriteProjectedLocalImmediate
  annealAggregateHooksLM2_2
  InitMaskWordRel
  initMaskWordRel_new_false
  initMaskWordRel_get
  initMaskWordRel_not_isRangeInitialized_of_get_false
  initMaskWordRel_isRangeInitialized
  initMaskWordRel_setRange_true
  alloc_readScalar_at_offset
  alloc_readScalar_congr
  alloc_writeScalar_at_offset
  StructFieldDesc
  isStructPaddingByte
  ValidStructLayout
  ValidStructLayout.arbitrary_flat
  ValidStructLayout.sumFieldBytes_lt_iff_exists_padding
  ValidStructLayout.byte_mem_field_of_size_le_sumFieldBytes
  writeField_preserves_other_fields_and_padding
  writeScalarPairField_preserves_other_fields_and_padding
  IsRoundtripTy
  ValidFieldProjChain
  ValidAggregateFieldPath
  DisjointFieldPaths
  StructMemPlaceRel
  StructMemPlaceRel.toMemPlaceRel
  UninitStructMemPlaceRel.toMemPlaceRel
  StructMemPlaceRel.has_uninit_of_padding_byte
  UninitStructMemPlaceRel
  StructTypeEnv
  ImmediateStructRel
  AllocIdWatermark
  AllocIdSupplyValid
  LocalRelLM2_2
  FrameRelLM2_2
  LM2_2StaticEnv
  StateRelLM2_2
  StateRel.toLM2_2
  StateRelLM2_2.toStateRel_of_flat_imm
  StepRelLM2_2
  ProjectedReadSimRelLM2_2
  WellTypedLM2_2ProjectedRead
  evalProjection_nested_field_read_simulation
  IsImmediateStructTy
  WellTypedLM2_2Operand
  IsTupleOrSingleAdtKind
  WellTypedLM2_2AggFieldSpec
  WellTypedLM2_2AggFields
  WellTypedLM2_2Aggregate
  evalRvalue_aggregate_tuple_struct_simulation
  WellTypedLM2_2FieldWrite
  step_assign_nested_field_write_simulation
  step_assign_nested_field_write_post_structMemPlaceRel
  WellTypedLM2_2UseAssign
  step_assign_use_lm2_2_simulation
  StructMemPlaceRel.of_overwrite_immediate
  StructMemPlaceRel.overwrite_immediate
  UninitStructMemPlaceRel.overwrite_immediate
  annealWriteImmediate_unprojected_indirect_eq
  useStructPostStaticEnv
  WellTypedLM2_2UseAssignStruct
  step_assign_use_struct_lm2_2_simulation
  step_nop_lm2_2_simulation
  step_storageLive_lm2_2_simulation
  step_storageDead_lm2_2_simulation
  WellTypedLM2_2Stmt
  step_stmt_lm2_2_simulation
  step_two_stmts_lm2_2_simulation
  WellTypedLM2_2Stmts
  step_stmts_lm2_2_simulation
  Witness.lm22PairBody
  Witness.lm22PairMiriInit
  Witness.lm22Pair_validStructLayout
  Witness.lm22Pair_isImmediateStructTy
  Witness.lm22Pair_trailing_padding_bytes
  Witness.lm22Pair_stateRelLM2_2_init
  Witness.lm22Pair_full_trace_and_returns_agree
  Witness.lm22UnpaddedBody
  Witness.lm22UnpaddedMiriInit
  Witness.lm22Unpadded_validStructLayout
  Witness.lm22Unpadded_no_padding_bytes
  Witness.lm22Unpadded_stateRelLM2_2_init
  Witness.lm22Unpadded_full_trace_and_returns_agree
  Witness.lm22InnerU32_validStructLayout
  Witness.lm22InnerU32_isImmediateStructTy
  Witness.lm22Padded_validStructLayout
  Witness.lm22Padded_interfield_padding_bytes
  Witness.lm22Padded_writeField_preserves_witness
  Witness.lm22PaddedBody
  Witness.lm22PaddedMiriInit
  Witness.lm22Padded_stateRelLM2_2_init
  Witness.lm22Padded_full_trace_and_returns_agree
  Witness.lm22InnerPair_validStructLayout
  Witness.lm22InnerPair_isImmediateStructTy
  Witness.lm22Nested_validStructLayout
  Witness.lm22Nested_all_five_padding_bytes
  Witness.lm22NestedBody
  Witness.lm22NestedMiriInit
  Witness.lm22Nested_stateRelLM2_2_init
  Witness.lm22Nested_full_trace_and_returns_agree
  Witness.lm22ReassignBody
  Witness.lm22ReassignMiriInit
  Witness.lm22Reassign_stateRelLM2_2_init
  Witness.lm22Reassign_useStruct_wt
  Witness.lm22Reassign_full_trace_and_returns_agree
  Witness.lm22Reassign_block_wt
  Witness.lm22Reassign_block_stmts_simulation
  maskBlocksGetBit
  initWordsFalse
  initWordsTrue
  ValidAggregateFieldPath.prefix_of_append
  ValidAggregateFieldPath.read_substruct_scalarPair
  StructMemPlaceRel.write_substruct_scalarPair
  WellTypedLM2_2ProjectedSubStructRead
  ProjectedSubStructReadSimRelLM2_2
  evalProjection_nested_substruct_read_at_local
  evalOperand_nested_substruct_read_simulation
  WellTypedLM2_2SubStructWrite
  step_assign_nested_substruct_write_simulation
  Witness.lm22Nested_projChain_inner_substruct
  Witness.lm22SubStructBody
  Witness.lm22SubStructMiriInit
  Witness.lm22SubStruct_stateRelLM2_2_init
  Witness.lm22SubStruct_read_wt
  Witness.lm22SubStruct_write_wt
  Witness.lm22SubStruct_full_trace_and_returns_agree
  Witness.lm22LargeTy
  Witness.lm22LargeLayoutTable
  Witness.lm22LargeFields
  Witness.lm22LargePaths
  Witness.lm22LargeEnv
  Witness.lm22Large_validStructLayout
  Witness.lm22Large_multi_block_padding_bytes
  Witness.lm22LargeBody
  Witness.lm22LargeMiriInit
  Witness.lm22Large_stateRelLM2_2_init
  Witness.lm22Large_full_trace_and_returns_agree
  step_terminator_goto_lm2_2_simulation
  step_terminator_return_lm2_2_simulation
  Witness.lm22_return_agree_of_stateRelLM2_2
  Witness.lm22LiveRetBody
  Witness.lm22LiveRetMiriInit
  Witness.lm22LiveRet_stateRelLM2_2_init
  Witness.lm22LiveRet_full_trace_and_returns_agree
  usesStructMemCopyDest
  annealStructMemCopyOp
  StructMemPlaceRel.of_copy_fresh
  StructMemPlaceRel.of_copy_overwrite
  annealStructMemCopyOp_dead_ub
  annealStructMemCopyOp_uninitImm_ok
  annealStructMemCopyOp_indirect_ok
  ValidAggregateFieldPath.read_substruct_scalarWrap
  StructMemPlaceRel.write_substruct_scalarWrap
  WellTypedLM2_2ProjectedScalarWrapRead
  ProjectedScalarWrapReadSimRelLM2_2
  evalProjection_nested_scalar_wrap_read_at_local
  evalOperand_nested_scalar_wrap_read_simulation
  evalStatement_assign_use_mem_eq
  WellTypedLM2_2ScalarWrapWrite
  step_assign_nested_scalar_wrap_write_simulation
  StateRelLM2_2.extract_structMemPlaceRel
  WellTypedLM2_2UseAssignMemStruct
  step_assign_use_memory_struct_lm2_2_simulation
  Witness.lm22MemMoveBody
  Witness.lm22MemMoveMiriInit
  Witness.lm22MemMove_stateRelLM2_2_init
  Witness.lm22MemMove_move2to3_wt
  Witness.lm22MemMove_copy3to4_wt
  Witness.lm22MemMove_full_trace_and_returns_agree
  Witness.lm22Padded_projChain_inner_wrap
  Witness.lm22ScalarWrapSubBody
  Witness.lm22ScalarWrapSubMiriInit
  Witness.lm22ScalarWrapSub_stateRelLM2_2_init
  Witness.lm22ScalarWrapSub_read_wt
  Witness.lm22ScalarWrapSub_write_wt
  Witness.lm22ScalarWrapSub_full_trace_and_returns_agree
  Witness.lm22Realistic80Ty
  Witness.lm22Realistic80LayoutTable
  Witness.lm22Realistic80Fields
  Witness.lm22Realistic80Paths
  Witness.lm22Realistic80Env
  Witness.lm22Realistic80_validStructLayout
  Witness.lm22Realistic80_all_padding_bytes
  Witness.lm22Realistic80Body
  Witness.lm22Realistic80MiriInit
  Witness.lm22Realistic80_stateRelLM2_2_init
  Witness.lm22Realistic80_full_trace_and_returns_agree
  copyWholeStructAllocation
  copyWholeStructAllocation_props
  annealStructMemCopyOp_readOnly_ub
  Witness.lm22PairWrap_read_wt
  Witness.lm22PairWrap_full_trace_and_returns_agree
  Witness.lm22MemMoveUb_faults_with_ub_on_both
  Witness.lm22ReadOnlyCopy_ub
  Witness.lm22SuperOuter_agg_hooks_ok
  Witness.lm22SuperOuter_step1_stateRel
  Witness.lm22SuperOuter_full_trace_and_returns_agree
  annealStructMemCopyOp_dangling_src_ub
  annealStructMemCopyOp_dangling_dest_ub
  annealStructMemCopyOp_overlap_ub
  WellTypedLM2_2SelfMoveMemStruct
  step_assign_self_move_memory_struct_lm2_2_simulation
  step_assign_self_copy_memory_struct_divergence
  annealControlHooks_returnOperand_indirect
  StepRelStructReturnLM2_2
  step_terminator_return_struct_lm2_2_simulation
  Witness.lm22DanglingSrcCopy_ub
  Witness.lm22DanglingDestCopy_ub
  Witness.lm22StructRetBody
  Witness.lm22StructRetMiriInit
  Witness.lm22StructRet_stateRelLM2_2_init
  Witness.lm22StructRet_full_trace_and_struct_return
  Witness.lm22SelfMoveBody
  Witness.lm22SelfMoveMiriInit
  Witness.lm22SelfMove_stateRelLM2_2_init
  Witness.lm22SelfMove_full_trace_and_returns_agree
  Witness.lm22SelfCopyBody
  Witness.lm22SelfCopyAnnealInit
  Witness.lm22SelfCopyMiriInit
  Witness.lm22SuperTripleInitAlloc_selfCopy_err
  Witness.lm22SelfCopyOverlap_ub
  Witness.lm22SelfCopy_stateRel
  Witness.lm22SelfCopy_divergence

open LeanMiriSpec.Correspondence in
#assert_standard_axioms
  isUnionLayout
  isUnionLocal
  unionFieldLayoutOf
  annealUnionProjectionCx
  annealUnionAggregateCx
  annealSubsliceLayout
  annealSubsliceProjectionCx
  isSubsliceElem
  annealSetTopFrame
  annealEvalUnionField
  annealEvalSubsliceOperand
  annealEvalOperandLM2_4
  annealEvalUnionFieldPlace
  annealEvalPlaceLM2_4
  usesMemCopy
  annealMemCopyError
  annealMemCopyOp
  annealUnionAggregateField
  annealAggregateHooksLM2_4
  annealRvalueHooksLM2_4
  lm24Place
  lm24Operand
  lm24Rvalue
  lm24Assign
  annealStepHooksLM2_4
  annealStepHooksLM2_4_assign_of_not_lm24
  lm24Stmt
  evalStatement_LM2_4_of_not_lm24
  BodyFreeOfLM2_4
  step_LM2_4_eq_of_bodyFree
  unionPrefixMask
  unionPrefixMask_fresh
  unionPrefixMask_rewrite
  unionPrefixMask_init
  unionPrefixMask_uninit
  unionPrefixMask_whole_iff
  vendoredUnionMaskCopy
  unionCopiedPrefixMask
  IsUnionPrefixMask
  IsUnionPrefixMask.of_fresh
  IsUnionPrefixMask.of_copied
  IsUnionPrefixMask.init
  IsUnionPrefixMask.uninit
  IsUnionPrefixMask.whole_iff
  IsUnionPrefixMask.setRange_ge
  IsUnionPrefixMask.get_byte
  unionPrefixMask_vendoredCopy
  unionAllocRaw
  union_readScalar_prefix
  union_readScalar_uninit
  union_writeScalar_prefix
  tryNew_uninit_raw
  union_copy_freshAlloc_spec
  WellTypedUnionTy
  WellTypedUnionTy.of_fullRangeScalarFields
  UnionMemRel
  UnionLocalRel
  FrameRelLM2_4
  StateRelLM2_4
  StateRel.toLM2_4
  StateRelLM2_4.toStateRel
  StepRelLM2_4
  FrameRelLM2_4.lookup_local
  FrameRelLM2_4.update_local
  UnionLocalRel.cache_layout
  FrameRelLM2_4.cache_local_layout
  UnionMemRel.f0_size
  UnionLocalRel.layout_eq
  projectionMemoryOffset_zero
  memPlace_offset_zero_eq
  projectField_union
  annealEvalUnionField_indirect
  IsPrimScalarTy.fields_primitive
  annealReadImmediate_unionMem
  UnionLocalRel.of_immediate
  write_after_rvalue_simulation_LM2_4
  unionFieldReadOperand
  isUnionLocal_of_wellTyped
  evalOperand_unionFieldRead_spec
  step_union_field_read_simulation
  freshUnionAlloc_spec
  annealPlaceHooks_allocateStack_eq
  forceAllocation_uninit_eq
  projectField_unionAggregate
  writeAggregate_union_def
  annealEvalOperandLM2_4_scalar
  evalScalarOperand_union_dst
  setFrameLocalIndirect_congr
  annealWriteImmediate_unionFresh
  annealUnionAggregateField_fresh
  annealStackBaseAddr_add_lt
  primScalar_ne_union_local
  aggLM2_4_placeLayout
  aggLM2_4_projectDowncast
  aggLM2_4_projectField
  aggLM2_4_copyOpNoValidate
  aggLM2_4_writeDiscriminant
  aggLM2_4_enforceValidity
  aggLM2_4_validate
  step_union_aggregate_simulation
  UnionMemRel.of_live_base
  UnionLocalRel.of_live_base
  UnionLocalRel.indirect_allocId
  FrameRelLM2_4.indirect_allocId
  UnionMemRel.initMask_spec
  encodeLittleEndianBytes_eq_allocLeBytes
  replicateUninitBytes_eq_replicate
  writeAbstractBytesAt_replicateUninitBytes_zero
  encodeUnionFieldsWith_matches_unionMemRel
  annealMemCopyOp_freshUnion
  union_whole_copy_initMask_preservation_simulation
  union_whole_move_initMask_preservation_simulation
  union_uninit_bytes_read_ub_simulation
  union_field_write_read_same_field_simulation
  dropValues_eq_drop
  takeValues_eq_take
  subsliceEnd
  SubsliceInBounds
  extractSubslice_inBounds
  extractSubslice_fromEnd_oob
  extractSubslice_inverted
  ArraySliceRel.subslice
  elemSize_mul_ok
  evalProjection_subslice_simulation
  evalProjection_subslice_inverted_divergence
  evalProjection_subslice_fromEndFalse_oob_divergence
  evalRvalue_union_aggregate_activeField_simulation
  Witness.lm24U8Layout
  Witness.lm24U32Layout
  Witness.lm24ULayout
  Witness.lm24Layouts
  Witness.lm24U8Ty
  Witness.lm24U32Ty
  Witness.lm24UTy
  Witness.lm24Decl
  Witness.lm24ConstU8
  Witness.lm24AggStmt
  Witness.lm24_wt_U
  Witness.lm24_isPrim_u8
  Witness.lm24_isPrim_u32
  Witness.lm24FnAbi
  Witness.lm24Body
  Witness.lm24_phase
  Witness.lm24InitAnneal
  Witness.lm24InitMiriFrame
  Witness.lm24InitMiri
  Witness.lm24_init_stateRel
  Witness.lm24_init_imm
  Witness.lm24_init_frame_imm
  Witness.lm24_nodup_empty
  Witness.lm24_canReserve_empty
  Witness.lm24_constU8_wt
  Witness.lm24Bb1S1
  Witness.lm24Bb1S2
  Witness.lm24_bb1_anneal₁
  Witness.lm24_bb1_anneal₂
  Witness.lm24_write_read_same_field_steps
  Witness.lm24_agg_copy_chain
  Witness.lm24AnnealState
  Witness.lm24USlot
  Witness.lm24_bb0_anneal₁
  Witness.lm24_bb0_anneal₂
  Witness.lm24_bb0_anneal₃
  Witness.lm24_bb2_anneal₁
  Witness.lm24_bb2_anneal₂
  Witness.lm24_bb2_anneal₃
  Witness.lm24_copy_initMask_steps
  Witness.lm24_copy_larger_field_ub
  Witness.lm24_subslice_witness
  annealEvalUnionFieldPlace_indirect
  evalScalarOperand_LM2_4
  MemPlaceRel.of_entry
  UnionMemRel.of_entry
  UnionLocalRel.of_entry
  annealWriteImmediate_unionInplace
  step_union_field_write_simulation
  annealEvalUnionFieldPlace_uninit
  step_union_field_write_uninit_simulation
  Witness.lm24FieldWriteStmt
  Witness.lm24_agg_step
  Witness.lm24U7Slot
  Witness.lm24_bb3_anneal₁
  Witness.lm24_bb3_anneal₂
  Witness.lm24_bb3_anneal₃
  Witness.lm24_bb4_anneal
  Witness.lm24_bb5_anneal₁
  Witness.lm24_bb5_anneal₂
  Witness.lm24_bb5_anneal₃
  Witness.lm24_field_write_read_steps
  Witness.lm24_field_write_uninit_simulation
  Witness.lm24_bb8_anneal
  Witness.lm24_field1_write_uninit_simulation
  Witness.lm24_move_read_steps
  annealCheckIndirectInitialized_uninit_array_ub
  subsliceReadOperand
  annealEvalOperandLM2_4_subslice
  evalSubsliceOperand_simulation
  Witness.lm24_subslice_operand_witness
  allocLeBytes_extract_prefix
  union_readScalar_prefix_le
  getBytesUnchecked_at
  zero_array_fromBytes_spec
  array_copy_freshAlloc_spec
  IsUnionPrefixMask.setRange_any
  step_union_type_punning_read_simulation
  step_union_nonzero_field_write_simulation
  writeProjectedForLocal_union_field_lt
  unionSpliceLowScalar
  step_union_narrower_field_write_correspondence
  miri_step_union_field_read_of_unionMemRel
  Witness.lm24USplicedSlot
  Witness.lm24_bb9_anneal₁
  Witness.lm24_bb9_anneal₂
  Witness.lm24_bb9_anneal₃
  Witness.lm24_narrower_field_write_retains_high_bytes_correspondence
  evalSubsliceOperand_zero_uninit_indirect_characterization
  annealMemCopyOp_freshArray
  step_subslice_assign_simulation
  Witness.lm24ConstU32
  Witness.lm24AggU32Stmt
  Witness.lm24Field1WriteU32Stmt
  Witness.lm24_constU32_wt
  Witness.lm24_rvalue_union_aggregate_activeField_witness
  Witness.lm24UU32Slot
  Witness.lm24_bb6_anneal₁
  Witness.lm24_bb6_anneal₂
  Witness.lm24_type_punning_read_simulation
  Witness.lm24_bb7_anneal₁
  Witness.lm24_bb7_anneal₂
  Witness.lm24_nonzero_field_write_simulation
  Witness.lm24U16Arr2Ty
  Witness.lm24U16Arr2Decl
  Witness.lm24_wf_u16Arr2
  Witness.lm24SubsliceBody
  Witness.lm24_subslice_phase
  Witness.lm24SubsliceAnneal
  Witness.lm24SubsliceMiriFrame
  Witness.lm24SubsliceMiri
  Witness.lm24SubsliceUninitMiri
  Witness.lm24_subslice_stateRel
  Witness.lm24_subslice_uninit_stateRel
  Witness.lm24_highWater_arr
  Witness.lm24_subslice_imm
  Witness.lm24_subslice_assign_steps
  Witness.lm24_subslice_assign_oob_and_uninit_ub
  Witness.lm24ZeroUninitFrame
  Witness.lm24ZeroUninitMiri
  Witness.lm24_zero_uninit_indirect_subslice_witness
  annealForceUnionAllocation
  annealForceUnionAllocation_of_ok
  annealEvalSubslicePlace
  initMask_setRange_full_overwrite
  IsUnionPrefixMask.len_eq
  IsUnionPrefixMask.setRange_le
  IsUnionPrefixMask.setRange_max
  union_writeScalar_prefix_preserve_high
  union_copy_alloc_spec
  union_copy_self_overlap_err
  union_copy_uninit_alloc_spec
  array_copy_alloc_spec
  UnionLocalRel.dead_value
  annealForceUnionAllocation_dead_err
  annealForceUnionAllocation_indirect_eq
  annealMemCopyOp_inplaceUnion
  unionWholeOperand
  step_union_whole_copy_or_move_overwrite_simulation
  step_union_self_copy_overlap_divergence
  step_union_copy_indirect_uninit_divergence
  annealUnionAggregateField_dead_err
  annealUnionAggregateField_inplace
  annealWriteImmediate_unionInplace_ge
  step_union_aggregate_overwrite_simulation
  step_union_aggregate_smaller_overwrite_divergence
  annealMemCopyOp_inplaceArray
  step_subslice_assign_overwrite_simulation
  evalProjection_nested_subslice_simulation
  step_subslice_elem_write_simulation
  step_repeat_union_field_simulation
  UnionLocalRel.allocLive
  UnionMemRel.of_filter_live
  UnionLocalRel.of_dealloc
  FrameRelLM2_4.update_local_dealloc
  step_storageLive_LM2_4_simulation
  step_storageDead_LM2_4_simulation
  Witness.lm24U8Arr3Ty
  Witness.lm24U8Arr3Decl
  Witness.lm24_wf_u8Arr3
  Witness.lm24A2UnionBody
  Witness.lm24A2_phase
  Witness.lm24A2InitAnneal
  Witness.lm24A2AnnealState
  Witness.lm24A2InitMiriFrame
  Witness.lm24A2InitMiri
  Witness.lm24A2_init_stateRel
  Witness.lm24A2_init_imm
  Witness.lm24A2_init_frame_imm
  Witness.lm24A2_constU8_wt
  Witness.lm24A2_constU32_wt
  Witness.lm24UU32Slot2
  Witness.lm24_overwrite_and_lifecycle_steps
  Witness.lm24_union_self_copy_overlap_divergence
  Witness.lm24InitAlloc4
  Witness.lm24UninitAlloc4
  Witness.lm24BaseMemPlace
  Witness.lm24A2UninitIndirectFrame
  Witness.lm24A2UninitIndirectMiri
  Witness.lm24_union_copy_indirect_uninit_divergence
  Witness.lm24_union_agg_smaller_overwrite_divergence
  Witness.lm24_repeat_union_field_steps
  Witness.lm24_nested_subslice_witness
  Witness.lm24ConstU16
  Witness.lm24A2SubsliceBody
  Witness.lm24A2_subslice_phase
  Witness.lm24Arr2Alloc
  Witness.lm24Arr2Elems
  Witness.lm24SecondAllocId
  Witness.lm24SecondBaseAddr
  Witness.lm24Arr2MemPlace
  Witness.lm24TwoArrMachine
  Witness.lm24A2SubsliceAnneal
  Witness.lm24A2SubsliceFrame
  Witness.lm24A2TwoArrMiri
  Witness.lm24A2DeadDstMiri
  Witness.lm24A2SubsliceMiri
  Witness.lm24A2SubsliceUninitMiri
  Witness.lm24_subslice_overwrite_and_elem_write_witness
  Witness.lm24_union_self_move_steps
  isEnumLayout
  isEnumLocal
  downcastEnumLayout
  annealEnumProjectionCx
  annealEvalEnumProjection
  annealDiscriminantHooksLM2_3
  annealAggregateHooksLM2_3
  annealProjectEnumPlaceElem
  annealProjectEnumPlaceList
  annealEvalEnumProjectedPlace
  annealEvalPlaceLM2_3
  annealRvalueHooksLM2_3
  annealStepHooksLM2_3
  BodyFreeOfLM2_3
  step_LM2_3_eq_of_bodyFree
  ValidEnumVariantFields
  ValidEnumLayout
  isVariantUninhabited_translateVariantsShape_multiple
  EnumMemRel
  EnumMemRel.of_copy_fresh
  EnumMemRel.of_copy_overwrite
  UninitEnumMemRel
  LocalRelLM2_3
  EnumLocalByteUninit
  EnumLocalByteUninit.of_dealloc_other
  FrameRelLM2_3
  FrameRelLM2_3.update_local_dealloc
  StateRelLM2_3
  StepRelLM2_3
  StepRelLM2_3.ub_iff
  StateRel.toLM2_3_empty
  StateRel.toLM2_3
  IsImmediateStepLocal
  IsEnumDiscrDestTy
  WellTypedEnumScalarOp
  evalRvalue_aggregate_enum_simulation
  writeDiscriminant_local_of_forced_ok
  writeDiscriminant_indirect_local_ok
  writeDiscriminant_dead_local_err
  writeDiscriminant_uninit_imm_local_ok
  step_setDiscriminant_simulation
  step_setDiscriminant_uninit_divergence
  evalRvalue_discriminant_simulation
  evalProjection_downcast_field_simulation
  evalProjection_downcast_field_initialized_divergence
  enum_match_switchInt_simulation
  step_goto_lm2_3_simulation
  step_return_scalar_lm2_3_simulation
  step_storageLive_LM2_3_simulation
  step_storageDead_LM2_3_simulation
  usesStructMemCopyDest_true_of_validEnum
  step_enum_copy_move_simulation
  annealEvalPlaceLM2_3_downcast_field_ok
  step_downcast_field_write_simulation
  step_downcast_field_write_inactive_divergence
  step_downcast_field_write_uninit_divergence
  step_enum_self_move_simulation
  EnumMemRel.copy_self_overlap_err
  UninitEnumMemRel.copy_uninit_self_ok
  step_enum_self_copy_dead_or_uninit_simulation
  step_enum_self_copy_overlap_divergence
  step_enum_copy_move_uninitInd_divergence
  annealControlHooks_returnOperand_indirect_lm2_3
  StepRelEnumReturnLM2_3
  step_return_enum_lm2_3_simulation
  step_return_enum_uninitInd_divergence
  Witness.lm23EnumLayout
  Witness.lm23Layouts
  Witness.lm23Variants
  Witness.lm23Env
  Witness.lm23_validEnumLayout
  Witness.lm23_env_valid
  Witness.lm23Body
  Witness.lm23_init_stateRel
  Witness.lm23_init_stateRelLM2_3
  Witness.wit_lm2_3_full_pipeline_trace
  Witness.wit_lm2_3_inactive_variant_downcast_ub
  Witness.wit_lm2_3_setDiscriminant_then_inactive_ub
  Witness.wit_lm2_3_switch_otherwise_and_goto_trace
  Witness.wit_lm2_3_uninit_and_dead_ub
  Witness.wit_lm2_3_setDiscriminant_uninit_divergence
  Witness.wit_lm2_3_inactive_variant_initialized_divergence
  Witness.wit_lm2_3_prefix_setDiscriminant_read
  Witness.wit_lm2_3_upcast_setDiscriminant_read_and_trailing_ub
  Witness.wit_lm2_3_bodyFree_divBody
  Witness.wit_lm2_3_upcast_field_write_move_and_storage_lifecycle
  Witness.wit_lm2_3_copy_move_and_downcast_write_ub
  Witness.wit_lm2_3_downcast_write_inactive_divergence
  Witness.wit_lm2_3_downcast_write_uninit_divergence
  Witness.wit_lm2_3_field_overwrite_self_move_and_copy_overwrite
  Witness.lm23_materialize_uninitInd
  Witness.wit_lm2_3_self_copy_dead_and_uninit_ub
  Witness.wit_lm2_3_self_copy_overlap_divergence
  Witness.wit_lm2_3_uninitInd_copy_and_move_divergence
  Witness.lm23ReturnEnumBody
  Witness.lm23Ret_init_stateRelLM2_3
  Witness.lm23Ret_dead_stateRelLM2_3
  Witness.lm23Ret_materialize_uninitInd0
  Witness.wit_lm2_3_return_enum_and_ub


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
    (hop : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls =
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
    (∀ v0 v1 v2, writeProjectedValue (Witness.lm21ArrAnneal 3 .uninit).frame.locals
      (.aggregate 0 Witness.lm21ArrElems) [.subslice 0 3 false] (.aggregate 0 [v0, v1, v2]) =
      .ok (.aggregate 0 [v0, v1, v2])) ∧
    (∀ v0 v1 v2, writeProjectedValue (Witness.lm21ArrAnneal 3 .uninit).frame.locals
      (.aggregate 0 Witness.lm21ArrElems) [.subslice 0 0 true] (.aggregate 0 [v0, v1, v2]) =
      .ok (.aggregate 0 [v0, v1, v2])) ∧
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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m
      [rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩]
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_addrOf_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm hsupply hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {s : MachineState} {mach : AnnealMachine}
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
    (hoff_slot : get? s.frame.locals offLoc = some (.init (.scalar offsetSc)))
    (hsc_sz : offsetSc.sizeBytes = 8)
    (hnot_dis : ∀ e, lookupBorrow s.memory.borrows ptrVal.tag = some e → e.perm ≠ .disabled)
    (hbound : ∀ b, ptrAllocByteBound? s.frame.locals s.memory [] emptyLayoutTable ptrVal = some b →
      localAlloc.allocation.byteSize.bytes.toNat ≤ b ∧ b < 2 ^ 63)  :
    -- (1) Exact in-bounds success characterization (iff)
    ((∃ ptr',
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr.offset, some mptr.provenance⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) = .ok ptr') ↔
      ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) ∧
    -- (2) In-bounds lockstep evaluation and PtrRel preservation
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
    -- (3) Out-of-bounds UB in ptrOffsetInbounds vs. wrappingSignedOffset success
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
  evalBinOp_offset_inbounds_simulation ptrLoc offLoc ptrVal mptr deltaBytes offsetSc allocId borTag localAlloc hptr_rel hprov hbase hlive hoff_in hdelta hsc_bits hptr_slot hoff_slot hsc_sz hnot_dis hbound

open Trusted.Rustc.V2026_06_01.Layout in
example
    {allocMap : List AllocMapEntry}
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List MirAst.LocalDecl) (layouts : LayoutTable)
    (m : AnnealStepState)
    (srcLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (srcMut dstMut : Mutability) (srcPointee dstPointee : RigidTy)
    (srcTy dstTy : Ty)
    (hsrcTy : srcTy.kind = .rawPtr srcMut srcPointee)
    (hdstTy : dstTy.kind = .rawPtr dstMut dstPointee)
    (hsrc_slot : get? locals srcLoc = some (.init (.ptr ptrVal 8)))
    (hptr_rel : PtrRel allocMap ptrVal mptr)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (hsrc_not_arr :
      arrayPtrOrRefElemLen? (operandTy localDecls layouts (.copy ⟨srcLoc, .nil⟩)) dstPointee =
        none)
    (hptr8 : layoutPointerBytes layouts = 8)  :
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
  evalCast_ptrToPtr_simulation locals mem localDecls layouts m srcLoc ptrVal mptr srcMut dstMut srcPointee dstPointee srcTy dstTy hsrcTy hdstTy hsrc_slot hptr_rel hdst_thin hsrc_not_arr hptr8

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_1Stmt body m stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    ∃ allocMap : List AllocMapEntry,
      StepRelLM3_1 body m allocMap
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm3_1_simulation hstate hphase hbb hstmt hwt hsupply hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    annealOutcomeIsUB
      (runAnnealBounded lm31OffsetDerefBody 10 (initMachineState lm31OffsetDerefBody [])) =
      true ∧
    ∃ alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      alloc.byteSize = Miri.ABI.Size.ofBytes 8 ∧
      ∃ err, Miri.Memory.checkAndDerefPtr annealPointerArithmetic
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 8),
          some (.concrete lm31AllocId1 Miri.Memory.BorTag.one)⟩
        ((8 : Nat) : Int) .memoryAccess
        (annealResolvePtr (mkSingleAllocMachine lm31AllocId1 alloc))
        (annealLookupAlloc (mkSingleAllocMachine lm31AllocId1 alloc)) = .error err :=
  Witness.wit_lm3_1_anneal_offset_deref_agreement

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0)  :
    StepRelLM3_1 body m (disableAllocMapLocal allocMap loc)
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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_addrOf_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm hsupply hptr8

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
          (∀ decl, get? body.localDecls e.localIdx = some decl → decl.ty.kind = dstDecl.ty.kind))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap',
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_read_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_prim himm hlive_ptr hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
        tgtDecl.ty.kind = pointeeKind)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_write_simulation hstate hphase hbb hstmt hdecl_ptr hptr_ty hval_prim hval_kind hop himm_ptr hlive_ptr hlay_coh

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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hno_int : ∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_cast_ptrToPtr_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hno_int hptr8

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
      e.perm ≠ .disabled ∧
      ((sc.bits = 0 ∧ ptrVal.offsetBytes = 0) ∨
        (get? s.frame.locals e.localIdx ≠ some .dead ∧
          ptrVal.offsetBytes + sc.bits ≤
            (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_binOp_offset_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hno_int hinbounds hptr8

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    {ptrVal : ProvenancePtr} {sc : MirAst.ScalarInt} {e : AllocMapEntry}
    {tgtDecl : MirAst.LocalDecl}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hrhs_ok : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag) (hdis : e.perm = .disabled)
    (htgt_decl : get? body.localDecls e.localIdx = some tgtDecl)
    (hinb :
      (sc.bits = 0 ∧ ptrVal.offsetBytes = 0) ∨
      (get? s.frame.locals e.localIdx ≠ some .dead ∧
        ptrVal.offsetBytes + sc.bits ≤
          (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hptr8 : layoutPointerBytes body.layouts = 8) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) :=
  step_binOp_offset_disabled_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty
    hdst_ty hpt hrhs_ty hop_rhs himm hno_int hslot_p hrhs_ok he htag hdis htgt_decl hinb
    hdst_live hptr8

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (h_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he_mem : e ∈ allocMap)
    (he_tag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (hpos : 0 < sc.bits)
    (hbits_lt : sc.bits < 2 ^ 32)
    (hbad : get? s.frame.locals e.localIdx = some .dead ∨
      (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat <
        ptrVal.offsetBytes + sc.bits)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_binOp_offset_oob_dangling_miri_ub hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hpt hrhs_ty hop_rhs himm hptr_slot hrhs_eval h_hdst_live he_mem he_tag hdecl_tgt hpos hbits_lt hbad hptr8

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_1StateStmt body s m allocMap stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm3_1_state_simulation hstate hphase hbb hstmt hwt hsupply hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (allocMap₂ allocMap₃ : List AllocMapEntry),
      let hooks := annealStepHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts
      stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31AddrOfMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₁ m₁
        [rawPtrAllocMapEntry lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 1
          lm31AllocId1] ∧
      stepMirFn lm31AddrOfBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₂ m₂ allocMap₂ ∧
      stepMirFn lm31AddrOfBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₃ m₃ allocMap₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      (∀ tf₃, m₃.stack.frames = #[tf₃] →
        (tf₃.locals[0]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99))))) ∧
      stepMirFn lm31AddrOfBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₄ m₄ (disableAllocMapLocal allocMap₃ 2) ∧
      stepMirFn lm31AddrOfBody s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₅ m₅
        (disableAllocMapLocal (disableAllocMapLocal allocMap₃ 2) 1) ∧
      m₅.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none :=
  Witness.wit_lm3_1_addrOf_deref_storageDead_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks lm31DanglingBody.localDecls lm31DanglingBody.layouts
      let entry := rawPtrAllocMapEntry lm31DanglingBody.localDecls lm31DanglingBody.layouts
        .not 1 1 lm31AllocId1
      stepMirFn lm31DanglingBody lm31DanglingAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31DanglingMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 lm31DanglingBody s₁ m₁ [entry] ∧
      stepMirFn lm31DanglingBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31DanglingBody s₂ m₂ (disableAllocMapLocal [entry] 1) ∧
      m₂.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none ∧
      stepMirFn lm31DanglingBody s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm3_1_use_after_storageDead_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks lm31PtrCastOffsetBody.localDecls lm31PtrCastOffsetBody.layouts
      let entry := rawPtrAllocMapEntry lm31PtrCastOffsetBody.localDecls
        lm31PtrCastOffsetBody.layouts .mut 1 1 lm31AllocId1
      stepMirFn lm31PtrCastOffsetBody (mkSixLocalAnnealPre lm31PtrCastOffsetBody) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre lm31PtrCastOffsetBody u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 lm31PtrCastOffsetBody s₁ m₁ [entry] ∧
      stepMirFn lm31PtrCastOffsetBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31PtrCastOffsetBody s₂ m₂ [entry] ∧
      stepMirFn lm31PtrCastOffsetBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 lm31PtrCastOffsetBody s₃ m₃ [entry] ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn lm31PtrCastOffsetBody s₃ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm3_1_ptrToPtr_and_offset_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let hooks := annealStepHooks lm31OffsetDisabledBody.localDecls lm31OffsetDisabledBody.layouts
      let entry := rawPtrAllocMapEntry lm31OffsetDisabledBody.localDecls
        lm31OffsetDisabledBody.layouts .mut 1 1 lm31AllocId1
      stepMirFn lm31OffsetDisabledBody (mkSixLocalAnnealPre lm31OffsetDisabledBody) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre lm31OffsetDisabledBody u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 lm31OffsetDisabledBody s₁ m₁ [entry] ∧
      stepMirFn lm31OffsetDisabledBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31OffsetDisabledBody s₂ m₂ [entry] ∧
      stepMirFn lm31OffsetDisabledBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 lm31OffsetDisabledBody s₃ m₃ [{ entry with perm := .disabled }] ∧
      stepMirFn lm31OffsetDisabledBody s₃ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) :=
  Witness.wit_lm3_1_binOp_offset_disabled_divergence

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) Real-step one-past-end OOB dereference (`offset = 8` on 8-byte `_1`)
    (∃ (s₄ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefOobRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      stepMirFn b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) ∧
    -- (2) Real-step in-bounds misaligned `u32` dereference (`offset = 2`, `2 + 4 ≤ 8`)
    (∃ (s₄ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefMisalignedRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) :=
  Witness.wit_lm3_1_deref_oob_and_misaligned_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    annealOutcomeIsUB
      (runAnnealBounded lm31ReviveBody 10 (initMachineState lm31ReviveBody [])) = true ∧
    Miri.Memory.checkAndDerefPtr annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0),
        some (.concrete lm31AllocId1 Miri.Memory.BorTag.one)⟩
      ((8 : Nat) : Int) .memoryAccess
      (annealResolvePtr { AnnealMachine.empty with
        addresses := { AnnealMachine.empty.addresses with
          baseAddr := #[⟨lm31AllocId1, annealStackBaseAddr lm31AllocId1⟩] } })
      (annealLookupAlloc { AnnealMachine.empty with
        addresses := { AnnealMachine.empty.addresses with
          baseAddr := #[⟨lm31AllocId1, annealStackBaseAddr lm31AllocId1⟩] } }) =
      .error (.allocationLookup (.deadAllocation lm31AllocId1)) :=
  Witness.wit_lm3_1_anneal_storage_revive_agreement

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_rawPtr_addrOf_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm hsupply hptr8

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    annealOutcomeScalarBits 4
      (runAnnealBounded lm31TypePunBody 10 (initMachineState lm31TypePunBody [])) =
      some 5 :=
  Witness.wit_lm3_1_anneal_deref_type_pun_agreement

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    {sc : MirAst.ScalarInt}
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub :=
  step_deref_oob_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty himm_ptr hslot_p he htag hfind_la hoob htarget

example (pointee : RigidTy) (hthin : isThinRawPtrPointee pointee = true) :
    ∃ inner, castTypeInfoOfEncodedTyId (encodeRawPtrTyId pointee) = .ok (.rawPointer inner) :=
  castTypeInfoOfEncodedTyId_encodeRawPtrTyId pointee hthin

example (pointee : RigidTy) (hnot : isThinRawPtrPointee pointee = false) :
    ∃ msg, castTypeInfoOfEncodedTyId (encodeRawPtrTyId pointee) =
      .error (.unsupported msg) :=
  castTypeInfoOfEncodedTyId_nonThin_err pointee hnot

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
          (∀ decl, get? body.localDecls e.localIdx = some decl → decl.ty.kind = dstDecl.ty.kind))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_1 body m (derefReadNextAllocMap s.frame.locals allocMap ptrIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_read_simulation_explicit hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_prim himm hlive_ptr hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
        tgtDecl.ty.kind = pointeeKind)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_1 body m (derefWriteNextAllocMap s.frame.locals allocMap ptrIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_deref_write_simulation_explicit hstate hphase hbb hstmt hdecl_ptr hptr_ty hval_prim hval_kind hop himm_ptr hlive_ptr hlay_coh

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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = targetIdx)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        e₀.allocId :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_addrOf_indirect_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm_dst he₀ he₀_loc hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    {sc : MirAst.ScalarInt}
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub :=
  step_deref_misaligned_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty himm_ptr hslot_p he htag hfind_la hinbounds hmis htarget hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hdst_bool : dstDecl.ty.kind = .bool)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_byte : tgtDecl.ty.kind = .uint .u8 ∨ tgtDecl.ty.kind = .int .i8)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinvalid : 2 ≤ sc.bits)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub :=
  step_deref_invalid_bool_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hdst_bool hptr_ty himm_ptr hslot_p hoff0 he htag hdecl_tgt htgt_byte htarget hinvalid

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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hperm : e.perm ≠ .disabled)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_ty : tgtDecl.ty.kind = .uint .u64)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx (.init (.ptr { ptrVal with offsetBytes := 8 } 8)))
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
  step_binOp_offset_stride_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hrhs_ty hop_rhs himm hptr_slot hoff0 hrhs_eval hdst_live he_mem he_tag hperm hdecl_tgt htgt_ty htgt_live hptr8

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hperm : e.perm ≠ .disabled)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead)
    (hlo_off : 1 ≤ ptrVal.offsetBytes)
    (hhi_off : ptrVal.offsetBytes ≤
      (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes - 1 } 8)))
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
  step_binOp_offset_neg_isize_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hrhs_ty hop_rhs himm hptr_slot hrhs_eval hdst_live he_mem he_tag hperm hdecl_tgt htgt_live hlo_off hhi_off hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let b := lm31InvalidBoolDerefBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      stepMirFn b lm31InvalidBoolAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31InvalidBoolMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm3_1_invalid_bool_cast_deref_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) `*const u64` + `1_usize` stride simulation (`+ 8` in both)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31StrideOffsetRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + 8),
              .concrete lm31AllocId1 borTag⟩))))) ∧
    -- (2) `*const u8` at offset `2` + `(-1_isize)` signed delta simulation (`+ 1` in both)
    (∃ (s₃ s₄ : MachineState) (m₃ m₄ : AnnealStepState)
      (tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31NegIsizeOffsetRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₃ m₃
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₃ = .step s₄ ∧
      get? s₄.frame.locals 5 =
        some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      m₄.stack.frames = #[tf₄] ∧
      (tf₄.locals[5]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + 1),
              .concrete lm31AllocId1 borTag⟩))))) :=
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

open Trusted.Rustc.V2026_06_01.Layout in
example
    {allocMap : List AllocMapEntry}
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List MirAst.LocalDecl) (layouts : LayoutTable)
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
    (hptr_rel : PtrRel allocMap ptrVal mptr)
    (hsrc_not_arr :
      arrayPtrOrRefElemLen? (operandTy localDecls layouts (.copy ⟨srcLoc, .nil⟩)) dstPointee =
        none)
    (hptr8 : layoutPointerBytes layouts = 8)  :
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
  evalCast_ptrToPtr_annealCastHooks_simulation locals mem localDecls layouts m srcLoc ptrVal mptr srcMut dstMut srcPointee dstPointee srcTy dstTy hsrcTy hdstTy hsrc_thin hdst_thin hsrc_slot hptr_rel hsrc_not_arr hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
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
    (h_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) :=
  step_deref_invalid_char_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hdst_char hptr_ty himm_ptr hslot_p hoff0 he htag hperm hdecl_tgt htgt_word htarget hinvalid h_hdst_live

open Trusted.Rustc.V2026_06_01.Layout in
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
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "writing invalid value")) :=
  step_deref_write_invalid_bool_simulation hstate hphase hbb hstmt hdecl_ptr hptr_ty hc_val hc_ty hb_lo hb_hi himm_ptr hslot_p hoff0 he htag hperm hdecl_tgt htgt_1 htgt_live

open Trusted.Rustc.V2026_06_01.Layout in
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
    (huninit : get? s.frame.locals ptrIdx = some .uninit)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "read of uninitialized local")) :=
  step_placeMention_deref_uninit_simulation hstate hphase hbb hstmt hdecl_ptr hptr_ty hpk_prim himm_ptr huninit

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' tf' msc_ref,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc_ref ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_ref)))) :=
  step_rawPtr_deref_null_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (h_hperm : e.perm = .active)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr ptrVal 8))) ∧
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
  step_rawPtr_deref_nonzero_offset_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p he htag h_hperm hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s' addr, stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.scalar ⟨addr, 8⟩))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported "exposeProvenance in cast")) :=
  step_cast_expose_provenance_ptr_unsupported hstate hphase hbb hstmt hdecl_dst hdecl_src hsrc_ty hsrc_thin hdst_ty hcast_ty himm_src hdst_live hslot_s hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hexp : s.memory.exposedAllocIds = [])
    (hglob : s.memory.globals = [])
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.scalar ⟨bits, 8⟩))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported "pointerFromExposedAddress in cast")) :=
  step_cast_with_exposed_provenance_divergence hstate hphase hbb hstmt hdecl_dst hdst_ty hcast_ty hdst_thin hc_ty hc_val hbits_lt hdst_live hexp hglob hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) `&raw const (*_1)` on null `0 as *const u64`
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31RawPtrDerefNullBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (2) `&raw const (*_4)` at `offsetBytes = 1`
    (∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
      (tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31RawPtrDerefOffsetBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₃ m₃
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1] ∧
      s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      m₄.stack.frames = #[tf₄] ∧
      (tf₄.locals[5]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + 1),
              .concrete lm31AllocId1 borTag⟩))))) :=
  Witness.wit_lm3_1_rawPtr_deref_null_and_offset_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) `PointerWithExposedProvenance` keeps unexposed `65536` scalar and faults on `*_4`
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm31ForgedProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 4 = some (.init (.scalar ⟨65536, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.unsupported "pointerFromExposedAddress in cast")) ∧
      stepMirFn b s₂ = .fail .ub) ∧
    -- (2) `PointerExposeProvenance`: exposes address in Anneal vs. `.unsupported`
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState) (addrBits : Nat),
      let b := lm31ExposeProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.scalar ⟨addrBits, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.unsupported "exposeProvenance in cast"))) :=
  Witness.wit_lm3_1_anneal_forged_provenance_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) Invalid `char` surrogate read (`0xD800_u32`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := lm31InvalidCharDerefBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0xD800, 4⟩
      let m₀ := mkFourLocalScalarMiriPre b charTyLM31 u32TyLM31 lm31ScalarSurrogateU32
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "reading invalid value"))) ∧
    -- (2) Invalid `bool` dereference write (`2`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := lm31WriteInvalidBoolBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 1⟩
      let m₀ := mkFourLocalScalarMiriPre b u8TyLM31 u8TyLM31 lm31Scalar0U8
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1] ∧
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "writing invalid value"))) ∧
    -- (3) `PlaceMention(*_1)` lockstep -> `PlaceMention(*_2)` UB
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm31PlaceMentionDerefBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      stepMirFn b s₁ = .fail .ub ∧
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

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hno_int : ∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_cast_ptrToPtr_move_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hno_int hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
      e.perm ≠ .disabled ∧
      ((sc.bits = 0 ∧ ptrVal.offsetBytes = 0) ∨
        (get? s.frame.locals e.localIdx ≠ some .dead ∧
          ptrVal.offsetBytes + sc.bits ≤
            (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_binOp_offset_move_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hno_int hinbounds hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hno_ptr : ∀ ptrVal, get? s.frame.locals srcIdx ≠ some (.init (.ptr ptrVal 8)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_cast_expose_provenance_scalar_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_src hsrc_ty hsrc_thin hdst_ty hcast_ty himm hno_ptr hptr8

example
    (localDecls : List MirAst.LocalDecl) (layouts : Layout.LayoutTable)
    (localId : Local) (decl : MirAst.LocalDecl)
    (hdecl : get? localDecls localId = some decl) :
    lookupDerefPointeeLayout localDecls layouts localId (translateTy decl.ty layouts) =
      lookupDerefPointeeLayout .nil layouts localId (translateTy decl.ty layouts) :=
  lookupDerefPointeeLayout_decl_eq_encoded localDecls layouts localId decl hdecl

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' tf' msc,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) :=
  step_cast_ptrToPtr_scalar_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_src hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hdst_live hslot_s hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hrhs_zero : sc_rhs.bits = 0)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' tf' msc_out,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc_out ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_out)))) :=
  step_binOp_offset_scalar_zero_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hdst_live hslot_p hrhs_eval hrhs_zero hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hrhs_lt : sc_rhs.bits < 2 ^ 32)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "pointer Offset out of bounds")) :=
  step_binOp_offset_scalar_nonzero_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hpt hrhs_ty hop_rhs himm_ptr hslot_p hrhs_eval hrhs_pos hrhs_lt hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (h_hperm : e.perm = .disabled ∨ (e.perm = .frozen ∧ rawMut = .mut))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.ptr ptrVal 8))) ∧
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
  step_rawPtr_deref_perm_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hdst_live hslot_p he htag h_hperm hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ rawMut = .mut))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
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
          some (.init (.ptr ptrVal 8))) ∧
      ∃ m' tf' borTag,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧
        (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                .concrete e.allocId borTag⟩))))) :=
  step_rawPtr_deref_zero_offset_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hno_int hzero_perm hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) `PtrToPtr` on null `0 as *const u64`
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31NullPtrToPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (2) `Offset(0 as *const u8, 0_usize)`
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31NullOffsetZeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (3) `Offset(0 as *const u8, 1_usize)`
    (∃ (m₁ : AnnealStepState),
      let b := lm31NullOffsetOneBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₀ =
        (m₁, .error (.undefinedBehavior "pointer Offset out of bounds"))) :=
  Witness.wit_lm3_1_null_ptrToPtr_and_offset_correspondences_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) Zero-offset correspondence on `&raw mut (*_2)` (`e.perm = .active`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31RawPtrDerefZeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩))))) ∧
    -- (2) `&raw mut (*_2)` (`e.perm = .frozen`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31RawPtrDerefFrozenMutBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩))))) :=
  Witness.wit_lm3_1_rawPtr_deref_zero_and_perm_correspondence_real_steps

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

open Trusted.Rustc.V2026_06_01.Layout in
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
      sc.bits = 0)
    (hptr_ok : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      e.perm ≠ .disabled ∧
      (ptrVal.offsetBytes = 0 ∨
        (get? s.frame.locals e.localIdx ≠ some .dead ∧
          ptrVal.offsetBytes ≤
            (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)))
    (hstride : ∃ st, st ≤ 16 ∧
      pointeeElemByteStride body.localDecls body.layouts (opKind ⟨ptrIdx, .nil⟩) = some st)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_binOp_offset_zero_any_stride_lm3_1_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hexact hrhs_ty hop_rhs himm hno_int hzero hptr_ok hstride hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
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
      get? s.frame.locals ptrIdx ≠ some .dead ∧ get? s.frame.locals ptrIdx ≠ some .uninit)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init .unit)) ∧
    ∃ m' tf',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate .uninit)) :=
  step_unaryOp_ptrMetadata_thin_rawPtr_correspondence hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr hptr_ty hexact hdst_ty himm hdst_live hptr_init hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hmove_disj : opKind₁ = MirAst.Operand.move → lhsIdx ≠ rhsIdx)  :
    (∃ s' aRes, stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar (boolToScalar aRes)))) ∧
    ∃ m' tf' b,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool b))))) :=
  step_rawPtr_cmp_ptr_divergence hstate hphase hopKind₁ hopKind₂ hbop hbb hstmt hdecl_dst hdecl_lhs hdecl_rhs hlhs_ty hrhs_ty hdst_ty himm hdst_live hlhs_ptr hrhs_init hmove_disj

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.scalar sc)))
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' tf' msc,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) :=
  step_cast_ptrToPtr_move_scalar_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_src hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hdst_live hslot_s hptr8

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hbits0 : sc_r.bits = 0)
    (hstride : ∃ st,
      pointeeElemByteStride body.localDecls body.layouts (.move ⟨ptrIdx, .nil⟩) = some st)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc_p))) ∧
    ∃ m' tf' msc_out,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc_p msc_out ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_out)))) :=
  step_binOp_offset_move_scalar_zero_correspondence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hexact hrhs_ty hop_rhs himm hdst_live hslot_p ha_rhs hbits0 hstride hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) Provenance-less `Eq(copy _1, copy _1)` lockstep simulation
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState),
      let b := lm31RawPtrCmpScalarBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨1, 1⟩))) ∧
    -- (2) Tracked raw-pointer `Eq(copy _2, copy _2)`: both step, results unrelated
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (aRes eqRes : Bool),
      let b := lm31RawPtrCmpPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.scalar (boolToScalar aRes))) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool eqRes)))))) ∧
    -- (3) Move-operand provenance-less `PtrToPtr` correspondence
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31MoveNullPtrToPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (4) Move-operand null `Offset(..., 0)` correspondence (`stride = 8`)
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31MoveNullOffsetZeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (5) `PtrMetadata` UB simulation on `.uninit` and thin-pointer correspondence
    (∃ (st' : MachineState) (m_ub m_ok : AnnealStepState) (msg : String)
      (tf_ok : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let bu := lm31PtrMetadataUninitBody
      let bt := lm31PtrMetadataThinBody
      let su := mkFourLocalScalarAnnealPre bu ⟨0, 8⟩
      let mu := mkFourLocalScalarMiriPre bu u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let st := mkFourLocalScalarAnnealPre bt ⟨0, 8⟩
      let mt := mkFourLocalScalarMiriPre bt u64Ty rawPtrConstU64Ty lm31Scalar0U64
      stepMirFn bu su = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks bu.localDecls bu.layouts) () mu =
        (m_ub, .error (.undefinedBehavior msg)) ∧
      stepMirFn bt st = .step st' ∧
      get? st'.frame.locals 3 = some (.init .unit) ∧
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

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hrhs_ptr : get? s.frame.locals rhsIdx = some (.init (.ptr ptrVal₂ 8)))  :
    (∃ s' aRes, stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar (boolToScalar aRes)))) ∧
    ∃ m' tf' b,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool b))))) :=
  step_rawPtr_cmp_scalar_ptr_divergence hstate hphase hopKind₁ hopKind₂ hbop hbb hstmt hdecl_dst hdecl_lhs hdecl_rhs hlhs_ty hrhs_ty hdst_ty himm hdst_live hlhs_sc hrhs_ptr

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hrhs_lt : sc_r.bits < 2 ^ 32)
    (hptr8 : layoutPointerBytes body.layouts = 8)  :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "pointer Offset out of bounds")) :=
  step_binOp_offset_move_scalar_nonzero_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hpt hrhs_ty hop_rhs himm_ptr hslot_p ha_rhs hrhs_pos hrhs_lt hptr8

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

open Trusted.Rustc.V2026_06_01.Layout in
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
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap' : List AllocMapEntry,
      StepObsRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_mir_lm3_1_state_simulation hstate hphase hbb hloc hsupply hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    -- (1) Symmetric `(.scalar, .ptr)` pointer comparison (`null() == p`): both step, results unrelated
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (aRes eqRes : Bool),
      let b := lm31RawPtrCmpScalarPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b boolTyLM31 rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 0 = some (.init (.scalar (boolToScalar aRes))) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool eqRes)))))) ∧
    -- (2) Tracked-pointer use-after-move `Eq(move _2, copy _2)` lockstep UB via
    --     unified `step_mir_lm3_1_state_simulation`
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := lm31RawPtrCmpMoveUbBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg))) ∧
    -- (3) Move-operand non-zero `Offset(move _1, const 1_usize)` on null pointer
    (∃ (m₁ : AnnealStepState),
      let b := lm31MoveNullOffsetNonzeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .fail .ub ∧
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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
      get? s.frame.locals e.localIdx ≠ some .dead ∧
      get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
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
  evalRvalue_reborrow_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty hdst_ty hpk_prim himm hno_int hzero_perm hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    {targetDecl : MirAst.LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl)  :
    stepMirFn body s = MirStepNode.fail .ub ∧
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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (huninit_t : get? s.frame.locals e.localIdx = some .uninit)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    {targetDecl : MirAst.LocalDecl} (hdecl_t : get? body.localDecls e.localIdx = some targetDecl) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              .concrete e.allocId borTag⟩)))) ∧
      annealValidityAccessCheck m'.machine
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId), some (.concrete e.allocId borTag)⟩
        (translateTy targetDecl.ty body.layouts).layout.size = .ok () :=
  evalRvalue_reborrow_uninit_target_divergence hstate hphase hbb hstmt hdecl_dst hdecl_ptr hptr_ty
    hdst_ty hpk_prim himm hno_int hzero_perm hslot_p he htag huninit_t hdst_live hdecl_t

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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
      get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
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
  evalRvalue_reborrow_safeRef_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (h_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_r : get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hdead_t : get? s.frame.locals e.localIdx = some .dead)  :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) :=
  evalRvalue_reborrow_safeRef_dangling_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ref href_ty hpk_prim himm_ref h_hdst_live hslot_r he htag hdead_t

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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
            decl.ty.kind = dstDecl.ty.kind))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_2 body m (derefReadNextAllocMap s.frame.locals allocMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_read_simulation_explicit hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
            decl.ty.kind = dstDecl.ty.kind))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_read_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref hlay_coh

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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
        tgtDecl.ty.kind = pointeeKind)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_2 body m (derefWriteNextAllocMap s.frame.locals allocMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_write_simulation_explicit hstate hphase hbb hstmt hdecl_ref href_ty hval_prim hval_kind hop himm_ref hlive_ref hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
        tgtDecl.ty.kind = pointeeKind)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap',
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_write_simulation hstate hphase hbb hstmt hdecl_ref href_ty hval_prim hval_kind hop himm_ref hlive_ref hlay_coh

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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0)  :
    StepRelLM3_2 body m (disableAllocMapLocal allocMap loc)
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
      StateRelLM3_2 lm32RefBody s₄ m₄ [{ entry with perm := .disabled }] ∧
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
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let hooks := annealStepHooks lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts
      let entry := refAllocMapEntry lm32DanglingReborrowBody.localDecls
        lm32DanglingReborrowBody.layouts .shared 1 1 lm31AllocId1
      stepMirFn lm32DanglingReborrowBody lm32DanglingReborrowAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32DanglingReborrowMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₁ m₁ [entry] ∧
      stepMirFn lm32DanglingReborrowBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_2 lm32DanglingReborrowBody s₂ m₂ [{ entry with perm := .disabled }] ∧
      stepMirFn lm32DanglingReborrowBody s₂ = .fail .ub ∧
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
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let hooks := annealStepHooks lm32UninitTargetReborrowBody.localDecls
        lm32UninitTargetReborrowBody.layouts
      let entry := rawPtrAllocMapEntry lm32UninitTargetReborrowBody.localDecls
        lm32UninitTargetReborrowBody.layouts .not 1 1 lm31AllocId1
      stepMirFn lm32UninitTargetReborrowBody lm32UninitTargetReborrowAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm32UninitTargetReborrowMiriPre = (m₁, .ok true) ∧
      StateRelLM3_2 lm32UninitTargetReborrowBody s₁ m₁ [entry] ∧
      stepMirFn lm32UninitTargetReborrowBody s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩)))) ∧
      annealValidityAccessCheck m₂.machine
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
          some (.concrete lm31AllocId1 borTag)⟩
        (translateTy u64Ty lm32UninitTargetReborrowBody.layouts).layout.size = .ok () :=
  Witness.wit_lm3_2_reborrow_uninit_target_divergence

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
  evalRvalue_reborrow_uninit_target_divergence
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
  evalRvalue_reborrow_safeRef_dangling_simulation
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
  Witness.lm32UninitTargetReborrowBody
  Witness.lm32UninitTargetReborrowAnnealPre
  Witness.lm32UninitTargetReborrowMiriFramePre
  Witness.lm32UninitTargetReborrowMiriPre
  Witness.lm32UninitTargetReborrow_stateRel_pre
  Witness.wit_lm3_2_reborrow_uninit_target_divergence
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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (h_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hoob : (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)
    (h_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)  :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) :=
  step_safeRef_deref_read_oob_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm_ref hslot_r he htag h_hperm hdecl_a htarget hoob h_hdst_live

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
        (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat)
    (hsl_init : get? s.frame.locals e.localIdx ≠ some .uninit)
    (hsc_sz : sc.sizeBytes =
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat)  :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing a dangling reference")) :=
  step_safeRef_deref_write_oob_simulation hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim hop himm_ref hop_ok hslot_r he htag hperm hdecl_a hsl_a hsl_ne hoob hsl_init hsc_sz

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (h_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      (translateTy allocDecl.ty body.layouts).layout.size.bytes.toNat)
    {mis : Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes))
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok (some mis))
    (h_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) :=
  step_safeRef_deref_read_misaligned_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm_ref hslot_r he htag h_hperm hdecl_a htarget hinbounds hmis h_hdst_live hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
      .ok (some mis))
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "dereferencing an unaligned reference")) :=
  step_safeRef_deref_write_misaligned_simulation hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim hop himm_ref hop_ok hslot_r he htag hperm hdecl_a hsl_a hsl_ne hinbounds hmis hlay_coh

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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hun : get? s.frame.locals refIdx = some .uninit)  :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "read of uninitialized local")) :=
  step_placeMention_safeRef_deref_uninit_simulation hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim himm_ref hun

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
          .ok (some mis)))  :
    stepMirFn body s = .step (advanceStmt s s.frame.locals) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  step_placeMention_safeRef_deref_divergence hstate hphase hbb hstmt hdecl_ref href_ty hpk_prim himm_ref hbad

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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_2 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_2StateStmt body s m allocMap stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm3_2_state_simulation hstate hphase hbb hstmt hwt hsupply hlay_coh

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
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    ∃ allocMap' : List AllocMapEntry,
      StepObsRelLM3_2 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_mir_lm3_2_state_simulation hstate hphase hbb hloc hsupply hlay_coh

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
      StateRelLM3_2 b s₂ m₂ [{ entry with perm := .disabled }] ∧
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
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
            layout := some (translateTy u8TyLM32) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (∃ (b : CapturedMir) (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨7, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkPre4MiriLM32 b u64Ty
          { value := .live (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt8 7)))),
            layout := some (translateTy u8TyLM32) }) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "dereferencing a dangling reference"))) ∧
    (∃ (b : CapturedMir) (s_mis : MachineState) (m_mis m_out : AnnealStepState),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      stepMirFn b s_mis = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m_mis =
        (m_out, .error (.undefinedBehavior "dereferencing an unaligned reference"))) ∧
    (∃ (b : CapturedMir) (s_mis : MachineState) (m_mis m_out : AnnealStepState),
      let entry := refAllocMapEntry b.localDecls b.layouts (.mut false) 1 1 lm31AllocId1
      StateRelLM3_2 b s_mis m_mis [entry] ∧
      stepMirFn b s_mis = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m_mis =
        (m_out, .error (.undefinedBehavior "dereferencing an unaligned reference"))) :=
  Witness.wit_lm3_2_oob_and_misaligned_deref_ub_simulations

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
      StateRelLM3_2 b s₃ m₃ [{ entry with perm := .disabled }] ∧
      m₃.stack.frames = #[tf₃] ∧
      Miri.Interpreter.ValidityVisitor.validatePlace (annealValidityHooks b.layouts)
        refU64Ty 4 ⟨.local 0 3 none tf₃.localsIdentity, translateTy refU64Ty b.layouts⟩
        false false m₃ =
        .error (.undefinedBehavior
          "validation: encountered a dangling reference (use-after-free)") m₃ ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_2 b s₄ m₄ [{ entry with perm := .disabled }] ∧
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
  step_safeRef_deref_read_oob_simulation
  step_safeRef_deref_write_oob_simulation
  step_safeRef_deref_read_misaligned_simulation
  step_safeRef_deref_write_misaligned_simulation
  step_safeRef_deref_write_perm_divergence
  step_safeRef_deref_read_disabled_divergence
  evalRvalue_reborrow_safeRef_perm_divergence
  step_placeMention_local_lm3_2_simulation
  step_placeMention_safeRef_deref_simulation
  step_placeMention_safeRef_deref_uninit_simulation
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
  Witness.wit_lm3_2_oob_and_misaligned_deref_ub_simulations
  Witness.wit_lm3_2_dangling_copy_move_and_perm_divergences_real_steps
  Witness.wit_lm3_2_placeMention_and_unified_return_ref_real_steps

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
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
    (hoff0 : ptrVal.offsetBytes = 0)
    (h_hperm : e.perm ≠ .disabled)
    (hdecl_a : get? body.localDecls e.localIdx = some allocDecl)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hsize : (translateTy dstDecl.ty body.layouts).layout.size =
      (translateTy allocDecl.ty body.layouts).layout.size)
    (hinvalid : ¬ AnnealScalarValid dstDecl.ty sc)
    (h_hdst_live : get? s.frame.locals dstIdx ≠ some .dead)  :
    StepRelLM3_2 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) :=
  step_safeRef_deref_read_invalid_scalar_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm_ref hslot_r he htag hoff0 h_hperm hdecl_a htarget hsize hinvalid h_hdst_live

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind dstPointee : RigidTy}
    {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
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
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_2Tree body m
      (reborrowTreeMapNext body.localDecls body.layouts bk s.frame.locals treeMap refIdx
        s.memory.nextTag)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_reborrow_safeRef_tree_simulation_explicit htree hphase hbb hstmt hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hanc_read hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind dstPointee : RigidTy}
    {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.ref bk ⟨refIdx, .cons .deref .nil⟩), span⟩)
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
      Trusted.Sequence.get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, Trusted.Sequence.get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      Trusted.Sequence.get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
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
  evalRvalue_reborrow_safeRef_tree_simulation htree hphase hbb hstmt hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hanc_read hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {opKind : Place → Operand} {span : String}
    (hopKind : opKind = Operand.copy ∨ opKind = Operand.move)
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨refIdx, .cons .deref .nil⟩)), span⟩)
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
        treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_2Tree body m (derefReadNextTreeMap s.frame.locals treeMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_read_tree_simulation htree hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref hanc_read hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : Operand} {span : String}
    (hbb : Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : Trusted.Sequence.get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : MirAst.LocalDecl} {mutability : Trusted.Rustc.V2026_06_01.MirAst.Mutability}
    {pointeeKind : RigidTy} {valTy : Ty}
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
      treeBorrowAncestorsChildAccessUB .write s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    StepRelLM3_2Tree body m (derefWriteNextTreeMap s.frame.locals treeMap refIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_safeRef_deref_write_tree_simulation htree hphase hbb hstmt hdecl_ref href_ty hval_prim hval_kind hop himm_ref hlive_ref hanc_write hlay_coh

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
  step_safeRef_deref_read_invalid_scalar_simulation
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

open Trusted.Rustc.V2026_06_01.Layout in
open Witness in
example :
    ∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm32InvalidBoolReadBody
      let hooks := annealStepHooks b.localDecls b.layouts
      ¬ AnnealScalarValid boolTyLM32 ⟨2, 1⟩ ∧
      stepMirFn b (mkPre4AnnealLM32 b (.init (.scalar ⟨2, 1⟩))) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkPre4MiriLM32 b boolTyLM32 lm32MlsU8Two) =
        (m₁, .ok true) ∧
      StateRelLM3_2 b s₁ m₁ [refAllocMapEntry b.localDecls b.layouts .shared 1 1 lm31AllocId1] ∧
      get? s₁.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "reading invalid value")) :=
  Witness.wit_lm3_2_invalid_bool_deref_read_ub_real_steps

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
  Witness.wit_lm3_2_invalid_bool_deref_read_ub_real_steps
  Witness.lm32TreeRoot
  Witness.lm32TreeChild
  Witness.lm32ReborrowTreeBody
  Witness.wit_lm3_2_reborrow_tree_write_and_parent_read_real_steps

section LM2_2Pins

open Trusted.Rustc.V2026_06_01.Layout

-- `LocalRel.indirect` keeps its upstream whole-value view: an initialized
-- memory-backed slot `.init v` carries `MemPlaceRel … (some v)`, an uninitialized
-- one `MemPlaceRel … none`. `LM-2.2` leaves `Relation.lean` unchanged.
example {mach : AnnealMachine} {decl : MirAst.LocalDecl} {layouts : LayoutTable}
    {v : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (hc : ∀ l ∈ c, l = translateTy decl.ty layouts)
    (hmp : MemPlaceRel mach decl.ty layouts (some v) mp) :
    LocalRel mach decl layouts (.init v) ⟨.live (.indirect mp), c⟩ :=
  .indirect (.init v) mp c hc (by nofun) hmp

example
    {layout : Miri.ABI.LayoutData}
    {fields : List StructFieldDesc}
    (hvalid : ValidStructLayout layout fields)
    {i : Nat} (hi : i < fields.length)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc)
    (hfield_sz : (fields[i]'hi).fieldLayout.size = translateSizeBytes sc.sizeBytes)
    {E : Type} {A : Miri.Memory.Allocation AnnealProv E} {words : Array UInt64}
    (hbsize : A.byteSize = layout.size)
    (hlen : A.len = A.byteSize.bytes.toNat)
    (hmut : A.mutability = .Mut)
    (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel A.initializationMask A.byteSize words) :
    ∃ (A' : Miri.Memory.Allocation AnnealProv E) (words' : Array UInt64),
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i]'hi).offset msc.size)
          (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () A' ∧
      A'.byteSize = layout.size ∧
      A'.len = A'.byteSize.bytes.toNat ∧
      A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      InitMaskWordRel A'.initializationMask A'.byteSize words' ∧
      (∀ b, b < layout.size.bytes.toNat →
        maskBlocksGetBit words' b =
          (maskBlocksGetBit words b ||
            decide ((fields[i]'hi).offset.bytes.toNat ≤ b ∧
              b < (fields[i]'hi).offset.bytes.toNat +
                (fields[i]'hi).fieldLayout.size.bytes.toNat))) ∧
      A'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange (fields[i]'hi).offset (fields[i]'hi).fieldLayout.size) =
        .ok (.ok ()) ∧
      A'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange (fields[i]'hi).offset (fields[i]'hi).fieldLayout.size) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) ∧
      (∀ j (hj : j < fields.length), j ≠ i →
        0 < (fields[j]'hj).fieldLayout.size.bytes.toNat →
        (∀ b, (fields[j]'hj).offset.bytes.toNat ≤ b →
          b < (fields[j]'hj).offset.bytes.toNat +
            (fields[j]'hj).fieldLayout.size.bytes.toNat →
          maskBlocksGetBit words b = true) →
        A'.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) =
          .ok (.ok ()) ∧
        A'.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) false =
          A.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange (fields[j]'hj).offset (fields[j]'hj).fieldLayout.size) false) ∧
      (∀ p, isStructPaddingByte fields layout.size p →
        A'.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) =
          A.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat p))) :=
  writeField_preserves_other_fields_and_padding hvalid hi hrel hfield_sz hbsize hlen hmut hprov hmask

example
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    {p : Nat} (hp : isStructPaddingByte fields (translateTy ty layouts).layout.size p) :
    ∃ allocId localAlloc,
      (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
      mach.memory.live.find? (fun (k, _) => k == allocId) = some (allocId, localAlloc) ∧
      (∀ q, isStructPaddingByte fields (translateTy ty layouts).layout.size q →
        localAlloc.allocation.initializationMask.get
          (Miri.ABI.Size.ofBytes (UInt64.ofNat q)) = .ok false) ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty layouts).layout.size) ≠
        .ok (.ok ()) :=
  StructMemPlaceRel.has_uninit_of_padding_byte h hp

example
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (not_array : ∀ ek c, ty.kind ≠ RigidTy.array ek c)
    (h : StructMemPlaceRel mach ty layouts fields paths rootVal mp)
    (hunpad : (translateTy ty layouts).layout.size.bytes.toNat ≤ structSumFieldBytes fields) :
    MemPlaceRel mach ty layouts (some rootVal) mp :=
  StructMemPlaceRel.toMemPlaceRel not_array h hunpad

example
    {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UninitStructMemPlaceRel mach ty layouts fields mp) :
    MemPlaceRel mach ty layouts none mp :=
  UninitStructMemPlaceRel.toMemPlaceRel h

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) :
    StateRelLM2_2 body emptyStructTypeEnv {} 0 s m :=
  StateRel.toLM2_2 h

example
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv : LM2_2StaticEnv} {allocBudget : Nat}
    {s : MachineState} {m : AnnealStepState}
    (h : StateRelLM2_2 body env stEnv allocBudget s m)
    (henv_valid : ∀ ty fs ps, env ty = some (fs, ps) → ∀ ek c, ty.kind ≠ RigidTy.array ek c)
    (hflat : ∀ (i : Nat) (decl : MirAst.LocalDecl) (v : Value)
      (imm : Miri.Interpreter.Immediate AnnealProv)
      (lay : Option Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      env decl.ty ≠ none →
      get? s.frame.locals i = some (.init v) →
      (∃ tf, m.stack.frames = #[tf] ∧ tf.locals[i]? = some ⟨.live (.immediate imm), lay⟩) →
      ImmediateRel decl.ty body.layouts v imm)
    (hunpad : ∀ (i : Nat) (decl : MirAst.LocalDecl) (v : Value)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (lay : Option Miri.Interpreter.LocalLayout)
      (fields : List StructFieldDesc) (paths : List (List ProjectionElem)),
      get? body.localDecls i = some decl →
      env decl.ty = some (fields, paths) →
      get? s.frame.locals i = some (.init v) →
      (∃ tf, m.stack.frames = #[tf] ∧ tf.locals[i]? = some ⟨.live (.indirect mp), lay⟩) →
      (translateTy decl.ty body.layouts).layout.size.bytes.toNat ≤ structSumFieldBytes fields) :
    StateRel body s m :=
  StateRelLM2_2.toStateRel_of_flat_imm h henv_valid hflat hunpad

example
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local}
    {projs : List ProjectionElem} {leafTy : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2 body env m.machine af topFrame)
    (hwt : WellTypedLM2_2ProjectedRead body env idx projs leafTy)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    ProjectedReadSimRelLM2_2 body env af topFrame m leafTy
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediateLM2_2) m) :=
  evalProjection_nested_field_read_simulation hframes hframe hwt globals known

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local}
    {kind : MirAst.AggregateKind} {ops : List MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate kind ops), span⟩)
    (hwt : WellTypedLM2_2Aggregate body env stEnv dstIdx kind ops) :
    StepRelLM2_2 body env (aggPostStaticEnv stEnv dstIdx ops) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  evalRvalue_aggregate_tuple_struct_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2FieldWrite body env stEnv dstIdx projs op) :
    StepRelLM2_2 body env (fieldWritePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_assign_nested_field_write_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s s' : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2FieldWrite body env stEnv dstIdx projs op)
    (hstep : stepMirFn body s = .step s') :
    ∃ decl fields paths rootVal mp,
      get? body.localDecls dstIdx = some decl ∧
      env decl.ty = some (fields, paths) ∧
      get? s'.frame.locals dstIdx = some (.init rootVal) ∧
      StructMemPlaceRel
        (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m).1.machine
        decl.ty body.layouts fields paths rootVal mp ∧
      ∃ tf lay,
        (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m).1.stack.frames =
          #[tf] ∧
        tf.locals[dstIdx]? = some ⟨.live (.indirect mp), lay⟩ :=
  step_assign_nested_field_write_post_structMemPlaceRel hstate hphase hbb hstmt hwt hstep

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2UseAssign body env stEnv dstIdx op) :
    StepRelLM2_2 body env (usePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_assign_use_lm2_2_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv stEnv' : LM2_2StaticEnv} {k_bud k_bud' : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM2_2Stmt body env stEnv k_bud stmt stEnv' k_bud') :
    StepRelLM2_2 body env stEnv' k_bud' m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_stmt_lm2_2_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir} {env : StructTypeEnv}
    {stEnv₀ stEnv₁ stEnv₂ : LM2_2StaticEnv} {k₀ k₁ k₂ : Nat}
    {s₀ : MachineState} {m₀ : AnnealStepState}
    (hstate₀ : StateRelLM2_2 body env stEnv₀ k₀ s₀ m₀)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt₁ stmt₂ : Statement}
    (hbb : get? body.basicBlocks s₀.frame.blockIdx = some bb)
    (hstmt₁ : get? bb.statements s₀.frame.stmtIdx = some stmt₁)
    (hstmt₂ : get? bb.statements (s₀.frame.stmtIdx + 1) = some stmt₂)
    (hwt₁ : WellTypedLM2_2Stmt body env stEnv₀ k₀ stmt₁ stEnv₁ k₁)
    (hwt₂ : WellTypedLM2_2Stmt body env stEnv₁ k₁ stmt₂ stEnv₂ k₂) :
    (stepMirFn body s₀ = .fail .ub ∧
      ∃ m_err msg,
        Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m₀ =
          (m_err, .error (.undefinedBehavior msg))) ∨
    (∃ s₁ m₁,
      stepMirFn body s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m₀ =
        (m₁, .ok true) ∧
      StateRelLM2_2 body env stEnv₁ k₁ s₁ m₁ ∧
      StepRelLM2_2 body env stEnv₂ k₂ m₁
        (stepMirFn body s₁)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m₁)) :=
  step_two_stmts_lm2_2_simulation hstate₀ hphase hbb hstmt₁ hstmt₂ hwt₁ hwt₂

example :
    StateRelLM2_2 Witness.lm22PairBody Witness.lm22PairEnv
      { initLocals := [2, 1], immLocals := [2, 3, 2, 0] } 1
      (Witness.lm22StepAnnealN Witness.lm22PairBody 5
        (initMachineState Witness.lm22PairBody []))
      (Witness.lm22StepMiriN Witness.lm22PairBody 5 Witness.lm22PairMiriInit) ∧
    (∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22PairBody 7 Witness.lm22PairMiriInit).machine
        Witness.lm22PairTy Witness.lm22PairLayoutTable
        Witness.lm22PairFields Witness.lm22PairPaths
        (.aggregate 0 [.scalar ⟨0x99AABBCC, 4⟩, .scalar ⟨0x5566, 2⟩]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22PairBody 7 Witness.lm22PairMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 6) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 7) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ())) ∧
    StateRel Witness.lm22PairBody
      (Witness.lm22StepAnnealN Witness.lm22PairBody 11
        (initMachineState Witness.lm22PairBody []))
      (Witness.lm22StepMiriN Witness.lm22PairBody 11 Witness.lm22PairMiriInit) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22PairBody 12
        (initMachineState Witness.lm22PairBody [])) = some 0x99AABBCC ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22PairBody 12 Witness.lm22PairMiriInit) = some 0x99AABBCC :=
  Witness.lm22Pair_full_trace_and_returns_agree

example :
    (∃ mp,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22UnpaddedBody 3 Witness.lm22UnpaddedMiriInit).machine
        Witness.lm22UnpaddedTy Witness.lm22UnpaddedLayoutTable
        Witness.lm22UnpaddedFields Witness.lm22UnpaddedPaths
        (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨77, 4⟩, .scalar ⟨30, 4⟩]) mp) ∧
    StateRel Witness.lm22UnpaddedBody
      (Witness.lm22StepAnnealN Witness.lm22UnpaddedBody 3
        (initMachineState Witness.lm22UnpaddedBody []))
      (Witness.lm22StepMiriN Witness.lm22UnpaddedBody 3 Witness.lm22UnpaddedMiriInit) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22UnpaddedBody 6
        (initMachineState Witness.lm22UnpaddedBody [])) = some 77 ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22UnpaddedBody 6 Witness.lm22UnpaddedMiriInit) = some 77 :=
  Witness.lm22Unpadded_full_trace_and_returns_agree

example :
    ValidStructLayout
      (translateTy Witness.lm22InnerU32Ty Witness.lm22PaddedLayoutTable).layout
      [Witness.lm22InnerU32Field0] ∧
    ValidStructLayout
      (translateTy Witness.lm22PaddedTy Witness.lm22PaddedLayoutTable).layout
      Witness.lm22PaddedFields ∧
    (∃ (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      (∃ raw,
        Miri.Memory.Allocation.tryNew (Miri.ABI.Size.ofBytes 8)
          (translateAlignBytes 4) .Uninit annealZeroedStorage = .ok raw ∧
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4))
          (Miri.Memory.Scalar.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 99))
          (raw.withExtra (none : Option Miri.TreeBorrows.BorrowTree)) = .ok () A') ∧
      A'.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes 4) (Miri.ABI.Size.ofBytes 4)) = .ok (.ok ()) ∧
      A'.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      A'.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      A'.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false) :=
  ⟨Witness.lm22InnerU32_validStructLayout,
    Witness.lm22Padded_validStructLayout,
    Witness.lm22Padded_writeField_preserves_witness⟩

example :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22PaddedBody 5 Witness.lm22PaddedMiriInit).machine
        Witness.lm22PaddedTy Witness.lm22PaddedLayoutTable
        Witness.lm22PaddedFields Witness.lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨99, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22PaddedBody 5 Witness.lm22PaddedMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ())) ∧
    StateRelLM2_2 Witness.lm22PaddedBody Witness.lm22PaddedEnv
      { initLocals := [2, 0, 1], immLocals := [2, 0, 2, 0] } 0
      (Witness.lm22StepAnnealN Witness.lm22PaddedBody 7
        (initMachineState Witness.lm22PaddedBody []))
      (Witness.lm22StepMiriN Witness.lm22PaddedBody 7 Witness.lm22PaddedMiriInit) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22PaddedBody 9
        (initMachineState Witness.lm22PaddedBody [])) = some 99 ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22PaddedBody 9 Witness.lm22PaddedMiriInit) = some 99 :=
  Witness.lm22Padded_full_trace_and_returns_agree

example :
    ValidStructLayout
      (translateTy Witness.lm22InnerPairTy Witness.lm22NestedLayoutTable).layout
      Witness.lm22InnerPairFields ∧
    ValidStructLayout
      (translateTy Witness.lm22NestedTy Witness.lm22NestedLayoutTable).layout
      Witness.lm22NestedFields ∧
    ((∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22NestedBody 7 Witness.lm22NestedMiriInit).machine
        Witness.lm22NestedTy Witness.lm22NestedLayoutTable
        Witness.lm22NestedFields Witness.lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0xBEEF, 2⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22NestedBody 7 Witness.lm22NestedMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) ≠ .ok (.ok ())) ∧
    StateRelLM2_2 Witness.lm22NestedBody Witness.lm22NestedEnv
      { initLocals := [0, 4, 3, 2], immLocals := [0, 4, 3, 1, 4, 3, 0] } 0
      (Witness.lm22StepAnnealN Witness.lm22NestedBody 10
        (initMachineState Witness.lm22NestedBody []))
      (Witness.lm22StepMiriN Witness.lm22NestedBody 10 Witness.lm22NestedMiriInit) ∧
    get? (Witness.lm22StepAnnealN Witness.lm22NestedBody 10
      (initMachineState Witness.lm22NestedBody [])).frame.locals 3 =
      some (.init (.scalar ⟨7, 1⟩)) ∧
    get? (Witness.lm22StepAnnealN Witness.lm22NestedBody 10
      (initMachineState Witness.lm22NestedBody [])).frame.locals 4 =
      some (.init (.scalar ⟨0x11112222, 4⟩)) ∧
    Witness.annealOutcomeScalarBits 2
      (runAnnealBounded Witness.lm22NestedBody 15
        (initMachineState Witness.lm22NestedBody [])) = some 0xBEEF ∧
    Witness.miriOutcomeScalarBits 2
      (runMiriBoundedLM2_2 Witness.lm22NestedBody 15 Witness.lm22NestedMiriInit) = some 0xBEEF) :=
  ⟨Witness.lm22InnerPair_validStructLayout,
    Witness.lm22Nested_validStructLayout,
    Witness.lm22Nested_full_trace_and_returns_agree⟩

/-! Whole-value reassignment of memory-backed immediate-ABI structs (`[adv B2]`). -/

example
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {val : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {dstLay : Miri.Interpreter.LocalLayout}
    {id0 : Miri.Interpreter.LocalsIdentity}
    (hframes : m.stack.frames = #[topFrame])
    (hget : topFrame.getLocal dstIdx = .ok ⟨.live (.indirect mp), lay⟩) :
    annealWriteImmediateLM2_2 val ⟨.local 0 dstIdx none id0, dstLay⟩ m =
      annealWriteIndirectImmediate val mp Miri.ABI.Size.ZERO dstLay m :=
  annealWriteImmediate_unprojected_indirect_eq hframes hget

example
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {newVal : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc} {words0 : Array UInt64}
    (himm : ImmediateStructRel ty layouts fields paths newVal imm)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hmis : mp.misaligned = none)
    (hmeta : mp.metadata = .none)
    (hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hovf : baseAddr.toNat + (translateTy ty layouts).layout.size.bytes.toNat < 2 ^ 64)
    (hmut : localAlloc.allocation.mutability = .Mut)
    (halign : mp.ptr.offset.isAligned (translateTy ty layouts).layout.align.abi = .ok true)
    (hbs : localAlloc.allocation.byteSize = (translateTy ty layouts).layout.size)
    (hlen : localAlloc.allocation.len = localAlloc.allocation.byteSize.bytes.toNat)
    (hpmap : localAlloc.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : InitMaskWordRel localAlloc.allocation.initializationMask
      localAlloc.allocation.byteSize words0)
    (hpad : ∀ p, isStructPaddingByte fields (translateTy ty layouts).layout.size p →
      localAlloc.allocation.initializationMask.get
        (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) :
    ∃ (u : Nat) (hu_lt : u < m.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } ∧
      StructMemPlaceRel (updateAllocMachine m.machine u allocId localAlloc.kind alloc')
        ty layouts fields paths newVal mp :=
  StructMemPlaceRel.of_overwrite_immediate himm hprov hmis hmeta hlive hbase hptr hovf
    hmut halign hbs hlen hpmap hmask hpad

example
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {oldVal newVal : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmp : StructMemPlaceRel m.machine ty layouts fields paths oldVal mp)
    (himm : ImmediateStructRel ty layouts fields paths newVal imm) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (localAlloc : AnnealLocalAlloc)
      (u : Nat) (hu_lt : u < m.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } ∧
      StructMemPlaceRel (updateAllocMachine m.machine u allocId localAlloc.kind alloc')
        ty layouts fields paths newVal mp :=
  StructMemPlaceRel.overwrite_immediate hmp himm

example
    {m : AnnealStepState} {ty : Ty} {layouts : LayoutTable}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {newVal : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmp : UninitStructMemPlaceRel m.machine ty layouts fields mp)
    (himm : ImmediateStructRel ty layouts fields paths newVal imm) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (localAlloc : AnnealLocalAlloc)
      (u : Nat) (hu_lt : u < m.machine.memory.live.size)
      (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      m.machine.memory.live[u]'hu_lt = (allocId, localAlloc) ∧
      annealWriteIndirectImmediate imm mp Miri.ABI.Size.ZERO (translateTy ty layouts) m =
        .ok () { m with machine := updateAllocMachine m.machine u allocId localAlloc.kind alloc' } ∧
      StructMemPlaceRel (updateAllocMachine m.machine u allocId localAlloc.kind alloc')
        ty layouts fields paths newVal mp :=
  UninitStructMemPlaceRel.overwrite_immediate hmp himm

example (stEnv : LM2_2StaticEnv) (dstIdx : Local) (op : MirAst.Operand) :
    useStructPostStaticEnv stEnv dstIdx op =
      { initLocals := dstIdx :: (operandPostStaticEnv stEnv op).initLocals
        immLocals := (operandPostStaticEnv stEnv op).immLocals.filter (· != dstIdx) } := rfl

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv}
    {dstIdx : Local} {op : MirAst.Operand}
    (decl : MirAst.LocalDecl) (fields : List StructFieldDesc) (paths : List (List ProjectionElem))
    (hdecl : get? body.localDecls dstIdx = some decl)
    (hstruct : IsImmediateStructTy env body.layouts decl.ty fields paths)
    (hop : WellTypedLM2_2Operand body env stEnv op decl.ty) :
    WellTypedLM2_2UseAssignStruct body env stEnv dstIdx op :=
  .mk decl fields paths hdecl hstruct hop

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2UseAssignStruct body env stEnv dstIdx op) :
    StepRelLM2_2 body env (useStructPostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_assign_use_struct_lm2_2_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir} {env : StructTypeEnv}
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {stEnv stEnv' : LM2_2StaticEnv} {k_bud k_bud' : Nat} {stmts : List Statement}
    (hwt : WellTypedLM2_2Stmts body env stEnv k_bud stmts stEnv' k_bud')
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmts : ∀ i (hi : i < stmts.length),
      get? bb.statements (s.frame.stmtIdx + i) = some (stmts[i]'hi)) :
    (runAnnealBounded body stmts.length s = .faulted .ub ∧
      ∃ m_err msg,
        runMiriBoundedLM2_2 body stmts.length m = .error m_err (.undefinedBehavior msg)) ∨
    (∃ s' m',
      runAnnealBounded body stmts.length s = .running s' ∧
      runMiriBoundedLM2_2 body stmts.length m = .running m' ∧
      StateRelLM2_2 body env stEnv' k_bud' s' m' ∧
      s'.frame.blockIdx = s.frame.blockIdx ∧
      s'.frame.stmtIdx = s.frame.stmtIdx + stmts.length) :=
  step_stmts_lm2_2_simulation hphase hwt hstate hbb hstmts

example :
    (∃ tf mp lay,
      (Witness.lm22StepMiriN Witness.lm22ReassignBody 6 Witness.lm22ReassignMiriInit).stack.frames =
        #[tf] ∧
      tf.locals[1]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22ReassignBody 6 Witness.lm22ReassignMiriInit).machine
        Witness.lm22PairTy Witness.lm22PairLayoutTable Witness.lm22PairFields Witness.lm22PairPaths
        (.aggregate 0 [.scalar ⟨0x01020304, 4⟩, .scalar ⟨0x5566, 2⟩]) mp) ∧
    get? (Witness.lm22StepAnnealN Witness.lm22ReassignBody 7
      (initMachineState Witness.lm22ReassignBody [])).frame.locals 1 =
      some (.init (.aggregate 0 [.scalar ⟨0xAABBCCDD, 4⟩, .scalar ⟨0x7788, 2⟩])) ∧
    StateRelLM2_2 Witness.lm22ReassignBody Witness.lm22PairEnv
      { initLocals := [1, 2, 1], immLocals := [3, 0] } 0
      (Witness.lm22StepAnnealN Witness.lm22ReassignBody 7
        (initMachineState Witness.lm22ReassignBody []))
      (Witness.lm22StepMiriN Witness.lm22ReassignBody 7 Witness.lm22ReassignMiriInit) ∧
    get? (Witness.lm22StepAnnealN Witness.lm22ReassignBody 9
      (initMachineState Witness.lm22ReassignBody [])).frame.locals 3 =
      some (.init (.scalar ⟨0x7788, 2⟩)) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22ReassignBody 13
        (initMachineState Witness.lm22ReassignBody [])) = some 0xAABBCCDD ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22ReassignBody 13 Witness.lm22ReassignMiriInit) =
        some 0xAABBCCDD :=
  Witness.lm22Reassign_full_trace_and_returns_agree

example :
    ∃ s' m',
      runAnnealBounded Witness.lm22ReassignBody 12
        (initMachineState Witness.lm22ReassignBody []) = .running s' ∧
      runMiriBoundedLM2_2 Witness.lm22ReassignBody 12 Witness.lm22ReassignMiriInit = .running m' ∧
      StateRelLM2_2 Witness.lm22ReassignBody Witness.lm22PairEnv
        { initLocals := [1, 2, 3, 0, 3, 1, 2, 1], immLocals := [1, 2, 3, 0, 3, 3, 0] } 0 s' m' ∧
      s'.frame.blockIdx = 0 ∧ s'.frame.stmtIdx = 12 :=
  Witness.lm22Reassign_block_stmts_simulation

/-! Non-leaf `ScalarPair` sub-struct read/write & multi-block `InitMask` (`[adv A2]`). -/

example
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local}
    {projs : List ProjectionElem} {subTy : Ty}
    {sf₀ sf₁ : StructFieldDesc} {mid₀ mid₁ : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2 body env m.machine af topFrame)
    (hwt : WellTypedLM2_2ProjectedSubStructRead body env idx projs subTy sf₀ sf₁ mid₀ mid₁)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    ProjectedSubStructReadSimRelLM2_2 body env af topFrame m subTy sf₀ sf₁ mid₀ mid₁
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediateLM2_2) m) :=
  evalOperand_nested_substruct_read_simulation hframes hframe hwt globals known

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2SubStructWrite body env stEnv dstIdx projs op) :
    StepRelLM2_2 body env (fieldWritePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_assign_nested_substruct_write_simulation hstate hphase hbb hstmt hwt

example :
    (get? (Witness.lm22StepAnnealN Witness.lm22SubStructBody 7
      (initMachineState Witness.lm22SubStructBody [])).frame.locals 3 =
      some (.init (.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩])) ∧
     ∃ imm,
      ImmediateStructRel Witness.lm22InnerPairTy Witness.lm22NestedLayoutTable
        Witness.lm22InnerPairFields Witness.lm22InnerPairPaths
        (.aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]) imm) ∧
    (∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22SubStructBody 9 Witness.lm22SubStructMiriInit).machine
        Witness.lm22NestedTy Witness.lm22NestedLayoutTable
        Witness.lm22NestedFields Witness.lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x55556666, 4⟩, .scalar ⟨0x7788, 2⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22SubStructBody 9 Witness.lm22SubStructMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 12)) ≠ .ok (.ok ())) ∧
    Witness.annealOutcomeScalarBits 2
      (runAnnealBounded Witness.lm22SubStructBody 15
        (initMachineState Witness.lm22SubStructBody [])) = some 0x7788 ∧
    Witness.miriOutcomeScalarBits 2
      (runMiriBoundedLM2_2 Witness.lm22SubStructBody 15 Witness.lm22SubStructMiriInit) = some 0x7788 :=
  Witness.lm22SubStruct_full_trace_and_returns_agree

example :
    ValidStructLayout
      (translateTy Witness.lm22LargeTy Witness.lm22LargeLayoutTable).layout
      Witness.lm22LargeFields ∧
    ((∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22LargeBody 3 Witness.lm22LargeMiriInit).machine
        Witness.lm22LargeTy Witness.lm22LargeLayoutTable
        Witness.lm22LargeFields Witness.lm22LargePaths
        (.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨100, 4⟩, .scalar ⟨999, 4⟩]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22LargeBody 3 Witness.lm22LargeMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 64) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 72) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 80)) ≠ .ok (.ok ())) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22LargeBody 6
        (initMachineState Witness.lm22LargeBody [])) = some 999 ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22LargeBody 6 Witness.lm22LargeMiriInit) = some 999) :=
  ⟨Witness.lm22Large_validStructLayout, Witness.lm22Large_full_trace_and_returns_agree⟩

/-! Terminators under `StateRelLM2_2` and return with a live padded struct (`[adv B3]`). -/

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hterm : (∃ target, bb.terminator.kind = .goto target) ∨
      bb.terminator.kind = .unreachable) :
    StepRelLM2_2 body env stEnv k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_terminator_goto_lm2_2_simulation hstate hphase hbb hstmt_none hstmt_len hterm

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : MirAst.LocalDecl}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (henv0 : env decl0.ty = none)
    (hsz0 : (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (himm0 : 0 ∈ stEnv.immLocals) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_terminator_return_lm2_2_simulation hstate hphase hbb hstmt_none hstmt_len hcleanup
    hret hdecl0 henv0 hsz0 himm0

example :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22LiveRetBody 7 Witness.lm22LiveRetMiriInit).machine
        Witness.lm22PaddedTy Witness.lm22PaddedLayoutTable
        Witness.lm22PaddedFields Witness.lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨99, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22LiveRetBody 7
          Witness.lm22LiveRetMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false) ∧
    StateRelLM2_2 Witness.lm22LiveRetBody Witness.lm22PaddedEnv
      { initLocals := [2, 0, 1], immLocals := [2, 0, 2, 0] } 0
      (Witness.lm22StepAnnealN Witness.lm22LiveRetBody 7
        (initMachineState Witness.lm22LiveRetBody []))
      (Witness.lm22StepMiriN Witness.lm22LiveRetBody 7 Witness.lm22LiveRetMiriInit) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22LiveRetBody 8
        (initMachineState Witness.lm22LiveRetBody [])) = some 99 ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22LiveRetBody 8 Witness.lm22LiveRetMiriInit) = some 99 :=
  Witness.lm22LiveRet_full_trace_and_returns_agree

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    {idx : Local} {decl : MirAst.LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {rootVal : Value}
    (hdecl : get? body.localDecls idx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hmem : (translateTy decl.ty body.layouts).layout.backendRepr = .Memory (sized := true))
    (hslot : get? s.frame.locals idx = some (.init rootVal)) :
    ∃ mp tf lay,
      m.stack.frames = #[tf] ∧
      tf.locals[idx]? = some ⟨.live (.indirect mp), lay⟩ ∧
      StructMemPlaceRel m.machine decl.ty body.layouts fields paths rootVal mp :=
  StateRelLM2_2.extract_structMemPlaceRel hstate hdecl henv hmem hslot

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {isMove : Bool} {srcIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (mkPlaceOperand isMove ⟨srcIdx, .nil⟩)), span⟩)
    (hwt : WellTypedLM2_2UseAssignMemStruct body env stEnv dstIdx isMove srcIdx) :
    StepRelLM2_2 body env
      (useStructPostStaticEnv stEnv dstIdx (mkPlaceOperand isMove ⟨srcIdx, .nil⟩))
      k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_assign_use_memory_struct_lm2_2_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir} {env : StructTypeEnv} {af : StackFrame}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {m : AnnealStepState} {isMove : Bool} {idx : Local}
    {projs : List ProjectionElem} {subTy : Ty}
    {sf₀ : StructFieldDesc} {mid₀ : Ty}
    (hframes : m.stack.frames = #[topFrame])
    (hframe : FrameRelLM2_2 body env m.machine af topFrame)
    (hwt : WellTypedLM2_2ProjectedScalarWrapRead body env idx projs subTy sf₀ mid₀)
    (globals : List CapturedAllocation)
    (known : Option Miri.Interpreter.LocalLayout) :
    ProjectedScalarWrapReadSimRelLM2_2 body env af topFrame m subTy sf₀ mid₀
      (evalOperand af.locals (mkPlaceOperand isMove ⟨idx, projs⟩) .nil globals body.layouts .nil)
      ((annealEvalOperand body.localDecls body.layouts
          (translateOperand (mkPlaceOperand isMove ⟨idx, projs⟩)) known >>=
        annealReadImmediateLM2_2) m) :=
  evalOperand_nested_scalar_wrap_read_simulation hframes hframe hwt globals known

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {projs : List ProjectionElem}
    {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, projs⟩ (.use op), span⟩)
    (hwt : WellTypedLM2_2ScalarWrapWrite body env stEnv dstIdx projs op) :
    StepRelLM2_2 body env (fieldWritePostStaticEnv stEnv dstIdx op) k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_assign_nested_scalar_wrap_write_simulation hstate hphase hbb hstmt hwt

example :
    (get? (Witness.lm22StepAnnealN Witness.lm22MemMoveBody 7
        (initMachineState Witness.lm22MemMoveBody [])).frame.locals 2 =
      some .uninit ∧
     ∃ mp3 alloc3,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22MemMoveBody 7 Witness.lm22MemMoveMiriInit).machine
        Witness.lm22NestedTy Witness.lm22NestedLayoutTable
        Witness.lm22NestedFields Witness.lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]]) mp3 ∧
      (∃ allocId3,
        (∃ tag, mp3.ptr.provenance = some (.concrete allocId3 tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22MemMoveBody 7
          Witness.lm22MemMoveMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId3) = some (allocId3, alloc3)) ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false) ∧
    (∃ mp4 alloc4,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22MemMoveBody 10 Witness.lm22MemMoveMiriInit).machine
        Witness.lm22NestedTy Witness.lm22NestedLayoutTable
        Witness.lm22NestedFields Witness.lm22NestedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0x11112222, 4⟩, .scalar ⟨0x3344, 2⟩]]) mp4 ∧
      (∃ allocId4,
        (∃ tag, mp4.ptr.provenance = some (.concrete allocId4 tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22MemMoveBody 10
          Witness.lm22MemMoveMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId4) = some (allocId4, alloc4)) ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 10) = .ok false ∧
      alloc4.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 11) = .ok false) ∧
    Witness.annealOutcomeScalarBits 2
      (runAnnealBounded Witness.lm22MemMoveBody 16
        (initMachineState Witness.lm22MemMoveBody [])) = some 0x3344 ∧
    Witness.miriOutcomeScalarBits 2
      (runMiriBoundedLM2_2 Witness.lm22MemMoveBody 16 Witness.lm22MemMoveMiriInit) = some 0x3344 :=
  Witness.lm22MemMove_full_trace_and_returns_agree

example :
    (get? (Witness.lm22StepAnnealN Witness.lm22ScalarWrapSubBody 7
        (initMachineState Witness.lm22ScalarWrapSubBody [])).frame.locals 3 =
      some (.init (.aggregate 0 [.scalar ⟨42, 4⟩])) ∧
     ∃ imm,
      ImmediateStructRel Witness.lm22InnerU32Ty Witness.lm22PaddedLayoutTable
        [Witness.lm22InnerU32Field0] [[.field 0 Witness.lm22U32Ty]]
        (.aggregate 0 [.scalar ⟨42, 4⟩]) imm) ∧
    (∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22ScalarWrapSubBody 9
          Witness.lm22ScalarWrapSubMiriInit).machine
        Witness.lm22PaddedTy Witness.lm22PaddedLayoutTable
        Witness.lm22PaddedFields Witness.lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xCAFEBABE, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22ScalarWrapSubBody 9
          Witness.lm22ScalarWrapSubMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) ≠ .ok (.ok ())) ∧
    get? (Witness.lm22StepAnnealN Witness.lm22ScalarWrapSubBody 10
        (initMachineState Witness.lm22ScalarWrapSubBody [])).frame.locals 4 =
      some (.init (.scalar ⟨42, 4⟩)) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22ScalarWrapSubBody 16
        (initMachineState Witness.lm22ScalarWrapSubBody [])) = some 0xCAFEBABE ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22ScalarWrapSubBody 16 Witness.lm22ScalarWrapSubMiriInit) =
        some 0xCAFEBABE :=
  Witness.lm22ScalarWrapSub_full_trace_and_returns_agree

example :
    ValidStructLayout
      (translateTy Witness.lm22Realistic80Ty Witness.lm22Realistic80LayoutTable).layout
      Witness.lm22Realistic80Fields ∧
    ((∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22Realistic80Body 5
          Witness.lm22Realistic80MiriInit).machine
        Witness.lm22Realistic80Ty Witness.lm22Realistic80LayoutTable
        Witness.lm22Realistic80Fields Witness.lm22Realistic80Paths
        (.aggregate 0
          [.scalar ⟨1, 1⟩, .scalar ⟨10, 8⟩, .scalar ⟨20, 8⟩, .scalar ⟨30, 8⟩,
           .scalar ⟨40, 8⟩, .scalar ⟨50, 8⟩, .scalar ⟨60, 8⟩, .scalar ⟨70, 8⟩,
           .scalar ⟨0x1122334455667788, 8⟩, .scalar ⟨0xAB, 1⟩]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22Realistic80Body 5
          Witness.lm22Realistic80MiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 80 ∧
      (∀ p, ((1 ≤ p ∧ p ≤ 7) ∨ (73 ≤ p ∧ p ≤ 79)) →
        localAlloc.allocation.initializationMask.get
          (Miri.ABI.Size.ofBytes (UInt64.ofNat p)) = .ok false) ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 80)) ≠ .ok (.ok ())) ∧
    get? (Witness.lm22StepAnnealN Witness.lm22Realistic80Body 6
        (initMachineState Witness.lm22Realistic80Body [])).frame.locals 2 =
      some (.init (.scalar ⟨0x1122334455667788, 8⟩)) ∧
    Witness.annealOutcomeScalarBits 1
      (runAnnealBounded Witness.lm22Realistic80Body 10
        (initMachineState Witness.lm22Realistic80Body [])) = some 0xAB ∧
    Witness.miriOutcomeScalarBits 1
      (runMiriBoundedLM2_2 Witness.lm22Realistic80Body 10 Witness.lm22Realistic80MiriInit) =
        some 0xAB) :=
  ⟨Witness.lm22Realistic80_validStructLayout,
    Witness.lm22Realistic80_full_trace_and_returns_agree⟩

/-! Mutability-normalized whole-struct copy, read-only destination UB,
    immediate `ScalarPair` scalar-wrapper read, `.Memory` move-then-use UB,
    and `.Memory` sub-struct (`sf.length = 3`) aggregate/projection pins. -/

example
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (extra : Option Miri.TreeBorrows.BorrowTree) :
    let alloc' := copyWholeStructAllocation alloc extra
    alloc'.mutability = .Mut ∧
    alloc'.byteSize = alloc.byteSize ∧
    alloc'.len = alloc.len ∧
    alloc'.provenanceMap = alloc.provenanceMap ∧
    alloc'.initializationMask = alloc.initializationMask ∧
    (∀ dl r rp, alloc'.readScalar dl r rp = alloc.readScalar dl r rp) :=
  copyWholeStructAllocation_props alloc extra

example
    {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {srcMp destMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {srcId destId : Miri.Memory.AllocId}
    {srcBase destBase : UInt64}
    {srcLocal destLocal : AnnealLocalAlloc}
    {destAlloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect destMp), c⟩)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hptr_s : srcMp.ptr.offset = Miri.ABI.Size.ofBytes srcBase)
    (hlive_s : LiveAllocEntry m.machine.memory.live srcId srcLocal)
    {tag_d : Miri.Memory.BorTag}
    (hprov_d : destMp.ptr.provenance = some (.concrete destId tag_d))
    (hbase_d : m.machine.lookupBaseAddr destId = some destBase)
    (hptr_d : destMp.ptr.offset = Miri.ABI.Size.ofBytes destBase)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx_d : m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some u)
    (hget_d : m.machine.memory.live[u]'hu_lt = (destId, destLocal))
    (hmut_d : destLocal.allocation.mutability = .Not)
    (hcopy_err : Miri.Memory.Allocation.copy srcLocal.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO wholeLay.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (srcId == destId) true
        destLocal.allocation = .error .readOnlyAllocation destAlloc') :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "write to read-only allocation") m :=
  annealStructMemCopyOp_readOnly_ub hframes hlt hind hprov_s hbase_s hptr_s
    hlive_s hprov_d hbase_d hptr_d hu_lt hfidx_d hget_d hmut_d hcopy_err

example :
    (∃ imm3,
      ImmediateStructRel Witness.lm22PairWrapTy Witness.lm22PairWrapLayoutTable
        Witness.lm22PairWrapFields Witness.lm22PairWrapPaths
        (.aggregate 0 [.scalar ⟨0x11223344, 4⟩, .aggregate 0 [.scalar ⟨0x13579BDF, 4⟩]]) imm3) ∧
    (∃ imm4,
      ImmediateStructRel Witness.lm22InnerU32Ty Witness.lm22PairWrapLayoutTable
        [Witness.lm22InnerU32Field0] [[.field 0 Witness.lm22U32Ty]]
        (.aggregate 0 [.scalar ⟨0x13579BDF, 4⟩]) imm4) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22PairWrapBody 14
        (initMachineState Witness.lm22PairWrapBody [])) = some 0x13579BDF ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22PairWrapBody 14 Witness.lm22PairWrapMiriInit) =
        some 0x13579BDF :=
  Witness.lm22PairWrap_full_trace_and_returns_agree

example :
    runAnnealBounded Witness.lm22MemMoveUbBody 8
        (initMachineState Witness.lm22MemMoveUbBody []) = .faulted .ub ∧
    ∃ m_err msg,
      runMiriBoundedLM2_2 Witness.lm22MemMoveUbBody 8 Witness.lm22MemMoveUbMiriInit =
        .error m_err (.undefinedBehavior msg) :=
  Witness.lm22MemMoveUb_faults_with_ub_on_both

example :
    annealStructMemCopyOp Witness.lm22MemMoveUbBody.localDecls
      Witness.lm22NestedLayoutTable
      ⟨.indirect (stackAllocPlace Witness.lm22AllocId1),
        translateTy Witness.lm22NestedTy Witness.lm22NestedLayoutTable⟩
      ⟨.local 0 2 none (.ofAllocationToken 0),
        translateTy Witness.lm22NestedTy Witness.lm22NestedLayoutTable⟩
      Witness.lm22ReadOnlyCopyState =
    .error (.undefinedBehavior "write to read-only allocation")
      Witness.lm22ReadOnlyCopyState :=
  Witness.lm22ReadOnlyCopy_ub

example :
    let m1 := Witness.lm22StepMiriN Witness.lm22SuperOuterBody 1
      Witness.lm22SuperOuterMiriInit
    (Miri.Interpreter.Step.step
      (annealStepHooksLM2_2 Witness.lm22SuperOuterBody.localDecls
        Witness.lm22SuperOuterBody.layouts) ()
      Witness.lm22SuperOuterMiriInit).2 = .ok true ∧
    (∃ la1,
      m1.machine.memory.live[0]? = some (Witness.lm22AllocId1, la1) ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 0) = .ok true ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false ∧
      la1.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 4) = .ok true) :=
  Witness.lm22SuperOuter_agg_hooks_ok

example :
    (∃ mp3 alloc3,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22SuperOuterBody 4
          Witness.lm22SuperOuterMiriInit).machine
        Witness.lm22SuperOuterTy Witness.lm22SuperLayoutTable
        Witness.lm22SuperOuterFields Witness.lm22SuperOuterPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩,
          .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨0x778899AA, 4⟩]]) mp3 ∧
      (∃ allocId3,
        (∃ tag, mp3.ptr.provenance = some (.concrete allocId3 tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22SuperOuterBody 4
          Witness.lm22SuperOuterMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId3) = some (allocId3, alloc3)) ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc3.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22SuperOuterBody 9
        Witness.lm22SuperOuterAnnealInit) = some 0x778899AA ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22SuperOuterBody 9
        Witness.lm22SuperOuterMiriInit) = some 0x778899AA :=
  Witness.lm22SuperOuter_full_trace_and_returns_agree

/-! Dangling-allocation copy UB, self-move vs. self-copy (`copyRangesOverlap` UB),
    and tuple/struct-returning root `Return` simulation pins. -/

example
    {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {srcMp destMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {srcId : Miri.Memory.AllocId}
    {srcBase : UInt64}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect destMp), c⟩)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hdead_s : m.machine.memory.live.find? (fun (k, _) => k == srcId) = none) :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "dangling allocation in memory copy") m :=
  annealStructMemCopyOp_dangling_src_ub hframes hlt hind hprov_s hbase_s hdead_s

example
    {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {srcMp destMp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {srcId destId : Miri.Memory.AllocId}
    {srcBase destBase : UInt64}
    {srcLocal : AnnealLocalAlloc}
    (hframes : m.stack.frames = #[tf])
    (hlt : dstIdx < tf.locals.size)
    (hind : tf.locals[dstIdx]'hlt = ⟨.live (.indirect destMp), c⟩)
    {tag_s : Miri.Memory.BorTag}
    (hprov_s : srcMp.ptr.provenance = some (.concrete srcId tag_s))
    (hbase_s : m.machine.lookupBaseAddr srcId = some srcBase)
    (hlive_s : LiveAllocEntry m.machine.memory.live srcId srcLocal)
    {tag_d : Miri.Memory.BorTag}
    (hprov_d : destMp.ptr.provenance = some (.concrete destId tag_d))
    (hbase_d : m.machine.lookupBaseAddr destId = some destBase)
    (hdead_d : m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = none) :
    annealStructMemCopyOp ld ly ⟨.indirect srcMp, srcLay⟩
        ⟨.local 0 dstIdx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "dangling allocation in memory copy") m :=
  annealStructMemCopyOp_dangling_dest_ub hframes hlt hind hprov_s hbase_s hlive_s
    hprov_d hbase_d hdead_d

example
    {ld : List MirAst.LocalDecl} {ly : LayoutTable}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {srcLay wholeLay : Miri.Interpreter.LocalLayout}
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {idx : Miri.MIR.LocalId}
    {iden : Miri.Interpreter.LocalsIdentity}
    {c : Option Miri.Interpreter.LocalLayout}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {baseAddr : UInt64}
    {localAlloc : AnnealLocalAlloc}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {u : Nat}
    (hframes : m.stack.frames = #[tf])
    (hlt : idx < tf.locals.size)
    (hind : tf.locals[idx]'hlt = ⟨.live (.indirect mp), c⟩)
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr : mp.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hlive : LiveAllocEntry m.machine.memory.live allocId localAlloc)
    (hu_lt : u < m.machine.memory.live.size)
    (hfidx : m.machine.memory.live.findIdx? (fun (k, _) => k == allocId) = some u)
    (hget : m.machine.memory.live[u]'hu_lt = (allocId, localAlloc))
    (hcopy_err : Miri.Memory.Allocation.copy localAlloc.allocation
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO wholeLay.layout.size)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
        localAlloc.allocation = .error .copyRangesOverlap alloc') :
    annealStructMemCopyOp ld ly ⟨.indirect mp, srcLay⟩
        ⟨.local 0 idx none iden, wholeLay⟩ m =
      .error (.undefinedBehavior "whole-value copy between overlapping ranges") m :=
  annealStructMemCopyOp_overlap_ub hframes hlt hind hprov hbase hptr hlive hu_lt hfidx hget hcopy_err

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv (k_bud + 1) s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {idx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨idx, .nil⟩ (.use (.move ⟨idx, .nil⟩)), span⟩)
    (hwt : WellTypedLM2_2SelfMoveMemStruct body env stEnv idx) :
    StepRelLM2_2 body env
      (useStructPostStaticEnv stEnv idx (.move ⟨idx, .nil⟩))
      k_bud m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_assign_self_move_memory_struct_lm2_2_simulation hstate hphase hbb hstmt hwt

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {idx : Local} {decl : MirAst.LocalDecl}
    {fields : List StructFieldDesc} {paths : List (List ProjectionElem)}
    {topOffsets : Array Miri.ABI.Size} {memoryIndex : Array Nat}
    {rootVal : Value} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)), span⟩)
    (hdecl : get? body.localDecls idx = some decl)
    (henv : env decl.ty = some (fields, paths))
    (hmem_repr : (translateTy decl.ty body.layouts).layout.backendRepr = .Memory (sized := true))
    (harb : (translateTy decl.ty body.layouts).layout.fields =
      .Arbitrary topOffsets memoryIndex)
    (hnz_sz : (translateTy decl.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO)
    (hslot : get? s.frame.locals idx = some (.init rootVal))
    (hcopy_err : ∀ (allocId : Miri.Memory.AllocId) (localAlloc : AnnealLocalAlloc),
      LiveAllocEntry m.machine.memory.live allocId localAlloc →
      localAlloc.allocation.byteSize = (translateTy decl.ty body.layouts).layout.size →
      ∃ alloc',
        Miri.Memory.Allocation.copy localAlloc.allocation
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy decl.ty body.layouts).layout.size)
          Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
          localAlloc.allocation = .error .copyRangesOverlap alloc') :
    stepMirFn body s =
      MirStepNode.step (advanceStmt s (s.frame.locals.set idx (.init rootVal)) s.memory) ∧
    ∃ m_err,
      Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m =
        (m_err, .error (.undefinedBehavior "whole-value copy between overlapping ranges")) :=
  step_assign_self_copy_memory_struct_divergence hstate hphase hbb hstmt hdecl henv
    hmem_repr harb hnz_sz hslot hcopy_err

example
    {body : CapturedMir} {env : StructTypeEnv} {stEnv : LM2_2StaticEnv} {k_bud : Nat}
    {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_2 body env stEnv k_bud s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hret : bb.terminator.kind = .return_)
    {decl0 : MirAst.LocalDecl}
    {fields : List StructFieldDesc}
    {paths : List (List ProjectionElem)}
    (hdecl0 : get? body.localDecls 0 = some decl0)
    (henv0 : env decl0.ty = some (fields, paths))
    (h0_state : 0 ∈ stEnv.initLocals ∨ 0 ∈ stEnv.immLocals) :
    StepRelStructReturnLM2_2 body fields paths m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_2 body.localDecls body.layouts) () m) :=
  step_terminator_return_struct_lm2_2_simulation hstate hphase hbb hstmt_none hstmt_len
    hcleanup hret hdecl0 henv0 h0_state

example :
    annealStructMemCopyOp Witness.lm22MemMoveUbBody.localDecls
      Witness.lm22NestedLayoutTable
      ⟨.indirect (stackAllocPlace Witness.lm22AllocId1),
        translateTy Witness.lm22NestedTy Witness.lm22NestedLayoutTable⟩
      ⟨.local 0 2 none (.ofAllocationToken 0),
        translateTy Witness.lm22NestedTy Witness.lm22NestedLayoutTable⟩
      Witness.lm22DanglingSrcCopyState =
    .error (.undefinedBehavior "dangling allocation in memory copy")
      Witness.lm22DanglingSrcCopyState :=
  Witness.lm22DanglingSrcCopy_ub

example :
    annealStructMemCopyOp Witness.lm22MemMoveUbBody.localDecls
      Witness.lm22NestedLayoutTable
      ⟨.indirect (stackAllocPlace Witness.lm22AllocId1),
        translateTy Witness.lm22NestedTy Witness.lm22NestedLayoutTable⟩
      ⟨.local 0 2 none (.ofAllocationToken 0),
        translateTy Witness.lm22NestedTy Witness.lm22NestedLayoutTable⟩
      Witness.lm22DanglingDestCopyState =
    .error (.undefinedBehavior "dangling allocation in memory copy")
      Witness.lm22DanglingDestCopyState :=
  Witness.lm22DanglingDestCopy_ub

example :
    runAnnealBounded Witness.lm22StructRetBody 6
        (initMachineState Witness.lm22StructRetBody []) =
      .returned (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xDEADBEEF, 4⟩]])
        (initMachineState Witness.lm22StructRetBody []).memory ∧
    ∃ m_ret mp0 alloc0,
      runMiriBoundedLM2_2 Witness.lm22StructRetBody 6 Witness.lm22StructRetMiriInit =
        .returned m_ret (.ok (.indirect mp0)) ∧
      StructMemPlaceRel m_ret.machine Witness.lm22PaddedTy Witness.lm22PaddedLayoutTable
        Witness.lm22PaddedFields Witness.lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xDEADBEEF, 4⟩]]) mp0 ∧
      (∃ allocId0,
        (∃ tag, mp0.ptr.provenance = some (.concrete allocId0 tag)) ∧
        m_ret.machine.memory.live.find? (fun (k, _) => k == allocId0) = some (allocId0, alloc0)) ∧
      alloc0.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      alloc0.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      alloc0.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false :=
  Witness.lm22StructRet_full_trace_and_struct_return

example :
    (∃ mp localAlloc,
      StructMemPlaceRel
        (Witness.lm22StepMiriN Witness.lm22SelfMoveBody 5
          Witness.lm22SelfMoveMiriInit).machine
        Witness.lm22PaddedTy Witness.lm22PaddedLayoutTable
        Witness.lm22PaddedFields Witness.lm22PaddedPaths
        (.aggregate 0 [.scalar ⟨7, 1⟩, .aggregate 0 [.scalar ⟨0xCAFE1234, 4⟩]]) mp ∧
      (∃ allocId,
        (∃ tag, mp.ptr.provenance = some (.concrete allocId tag)) ∧
        (Witness.lm22StepMiriN Witness.lm22SelfMoveBody 5
          Witness.lm22SelfMoveMiriInit).machine.memory.live.find?
          (fun (k, _) => k == allocId) = some (allocId, localAlloc)) ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 1) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 2) = .ok false ∧
      localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes 3) = .ok false) ∧
    Witness.annealOutcomeScalarBits 4
      (runAnnealBounded Witness.lm22SelfMoveBody 9
        (initMachineState Witness.lm22SelfMoveBody [])) = some 0xCAFE1234 ∧
    Witness.miriOutcomeScalarBits 4
      (runMiriBoundedLM2_2 Witness.lm22SelfMoveBody 9 Witness.lm22SelfMoveMiriInit) =
        some 0xCAFE1234 :=
  Witness.lm22SelfMove_full_trace_and_returns_agree

example :
    annealStructMemCopyOp Witness.lm22SelfCopyBody.localDecls
      Witness.lm22UnpaddedLayoutTable
      ⟨.indirect (stackAllocPlace Witness.lm22AllocId1),
        translateTy Witness.lm22UnpaddedTy Witness.lm22UnpaddedLayoutTable⟩
      ⟨.local 0 1 none (.ofAllocationToken 0),
        translateTy Witness.lm22UnpaddedTy Witness.lm22UnpaddedLayoutTable⟩
      Witness.lm22SelfCopyMiriInit =
    .error (.undefinedBehavior "whole-value copy between overlapping ranges")
      Witness.lm22SelfCopyMiriInit :=
  Witness.lm22SelfCopyOverlap_ub

example :
    stepMirFn Witness.lm22SelfCopyBody Witness.lm22SelfCopyAnnealInit =
      MirStepNode.step (advanceStmt Witness.lm22SelfCopyAnnealInit
        (Witness.lm22SelfCopyAnnealInit.frame.locals.set 1
          (.init (.aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩])))
        Witness.lm22SelfCopyAnnealInit.memory) ∧
    ∃ m_err,
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_2 Witness.lm22SelfCopyBody.localDecls
            Witness.lm22SelfCopyBody.layouts) ()
          Witness.lm22SelfCopyMiriInit =
        (m_err, .error (.undefinedBehavior "whole-value copy between overlapping ranges")) :=
  Witness.lm22SelfCopy_divergence

end LM2_2Pins

/-! ### `LM-2.4` (`UnionLM2_4`, `SimLM2_4`, `WitLM2_4`) statement pins -/

section LM2_4Pins

open Trusted.Rustc.V2026_06_01.Layout

example
    {S k : Nat}
    (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k)
    (hle : k ≤ S)
    (destInit : Bool) :
    ∃ M, vendoredUnionMaskCopy S (Miri.Memory.InitMask.new (translateSizeBytes S) destInit)
        (unionPrefixMask S k) = .ok M ∧
      ∀ j, ValidScalarBytes j → j ≤ S →
        (M.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes j)) = .ok (.ok ()) ↔
          j ≤ k) :=
  unionPrefixMask_vendoredCopy hS hk hle destInit

open Trusted.Rustc.V2026_06_01.Layout in
example
    {layouts : LayoutTable} {uTy : Ty} {S : Nat}
    (hsz : ValidScalarBytes S)
    (hfu : ∃ n, (translateTy uTy layouts).layout.fields = .Union n ∧ 0 < n)
    (hsize : (translateTy uTy layouts).layout.size = translateSizeBytes S)
    (hsized : (translateTy uTy layouts).layout.isSized = true)
    (halign : (translateTy uTy layouts).layout.align.abi.pow2 ≤ 29)
    {defPath : DefPath} {args : List RigidTy} {tl : TypeLayout} {n : Nat}
    (hkind : uTy.kind = .adt defPath args)
    (hidx_pos : 0 < uTy.layoutIdx)
    (hidx_lt : uTy.layoutIdx < 900)
    (hlook : layouts.lookup uTy.layoutIdx = some tl)
    (htl_fields : tl.fields = .union n)
    (htl_var : tl.variants = .single 0)
    (htl_uninh : tl.isUninhabited = false)
    (htl_sz : tl.size.bytes = S)
    (htl_len : tl.fieldLayouts.length = n)
    (hptr : layouts.pointerBits = 64)
    (hle : layouts.isLittleEndian = true)
    (hfields : ∀ idx flIdx, get? tl.fieldLayouts idx = some flIdx →
      ∃ fTl, layouts.lookup flIdx = some fTl ∧
        fTl.isUninhabited = false ∧
        ValidScalarBytes fTl.size.bytes ∧
        fTl.size.bytes ≤ S ∧
        (∀ prim vr, fTl.backendRepr = .scalar (.initialized prim vr) →
          vr.start = 0 ∧ vr.end_ + 1 = scalarModulus fTl.size.bytes)) :
    WellTypedUnionTy layouts uTy S :=
  WellTypedUnionTy.of_fullRangeScalarFields hsz hfu hsize hsized halign hkind hidx_pos hidx_lt
    hlook htl_fields htl_var htl_uninh htl_sz htl_len hptr hle hfields

example
    (localDecls : List MirAst.LocalDecl)
    (layouts : LayoutTable)
    (mbody : Miri.MIR.Body)
    (hfree : BodyFreeOfLM2_4 localDecls layouts mbody)
    (m : AnnealStepState)
    (hbody : ∀ frame, m.stack.currentFrame? = some frame → frame.body = mbody) :
    Miri.Interpreter.Step.step (annealStepHooksLM2_4 localDecls layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooksLM2_2 localDecls layouts) () m :=
  step_LM2_4_eq_of_bodyFree localDecls layouts mbody hfree m hbody

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {u : Local}
    {d : DefPath}
    {f : Nat}
    {op : MirAst.Operand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    {f0Ty : Ty}
    (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc : MirAst.ScalarInt) (mp : Miri.Interpreter.MemPlace AnnealProv)
        (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc) s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ u →
          IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
        (∀ j, j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 1 (m', .ok true)) :=
  step_union_aggregate_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_u hwt hfields hf hfl hfl_sized hu_uninit hu_imm hprim0 hop hf0_le hadt hfl_sz hdecls_adt

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {r u j : Local}
    {fty : Ty}
    {isMove : Bool}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩)
    {rDecl uDecl : MirAst.LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hr_ty : rDecl.ty = fty)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty)
    {w : Nat}
    (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    (hj : j < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size) :
    (j = f → fty = f0Ty →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
      (∀ s', stepMirFn body s = .step s' →
        get? s'.frame.locals r = some (.init (.scalar sc))) ∧
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m).1.machine =
        m.machine) ∧
    (j ≠ f → sc.sizeBytes < w → w ≤ S →
      stepMirFn body s = .fail .ub ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) :=
  step_union_field_read_simulation hstate hnodup hphase hbb hstmt hdecl_r hr_ty hdecl_u hprim hw hsz hwt hfields hf hj hu_slot hu_mls hmem hr_imm hfl

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {r u j : Local}
    {fty : Ty}
    {isMove : Bool}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩)
    {rDecl uDecl : MirAst.LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hr_ty : rDecl.ty = fty)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty)
    {w : Nat}
    (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    (hj : j < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hjne : j ≠ f)
    (hkw : sc.sizeBytes < w)
    (hwS : w ≤ S)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size) :
    stepMirFn body s = .fail .ub ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  union_uninit_bytes_read_ub_simulation hstate hnodup hphase hbb hstmt hdecl_r hr_ty hdecl_u hprim hw hsz hwt hfields hf hj hu_slot hu_mls hmem hr_imm hjne hkw hwS hfl

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {u r : Local}
    {d : DefPath}
    {f : Nat}
    {op : MirAst.Operand}
    {isMove : Bool}
    {span₁ span₂ : String}
    {f0Ty : Ty}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt₁ : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span₁⟩)
    (hstmt₂ : get? bb.statements (s.frame.stmtIdx + 1) =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u f f0Ty)), span₂⟩)
    {uDecl rDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hr_ty : rDecl.ty = f0Ty)
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    ∀ s₁, stepMirFn body s = .step s₁ →
      ∃ (m₁ : AnnealStepState) (sc : MirAst.ScalarInt),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m₁, .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc) s.frame.locals ∧
        StepRelLM2_4 body m₁ (stepMirFn body s₁)
          (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m₁) ∧
        ∀ s₂, stepMirFn body s₁ = .step s₂ →
          get? s₂.frame.locals r = some (.init (.scalar sc)) :=
  union_field_write_read_same_field_simulation hstate hnodup hcanRes hphase hbb hstmt₁ hstmt₂ hdecl_u hdecl_r hr_ty hwt hfields hf hfl hfl_sized hu_uninit hu_imm hr_imm hprim0 hop hf0_le hadt hfl_sz hdecls_adt

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {w u : Local}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : MirAst.LocalDecl}
    (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hty : wDecl.ty = uDecl.ty)
    {S n f : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    ∃ (s' : MachineState) (m' : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM2_4 body s' m' ∧
      get? s'.frame.locals w =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
      (∀ j, j ≠ w → get? s'.frame.locals j = get? s.frame.locals j) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
      UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
      UnionMemRel m'.machine wDecl.ty body.layouts S f0Ty sc mp_w ∧
      LiveAllocsNodup m'.machine ∧
      (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
        IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
      StepPreservesHighWater m 1 (m', .ok true) :=
  union_whole_copy_initMask_preservation_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_w hdecl_u hty hwt hfields_u hf hu_slot hu_mls hmem hw_uninit hw_imm

example
    {mach : AnnealMachine}
    {uTy : Ty}
    {layouts : LayoutTable}
    {S : Nat}
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp)
    (hS : ValidScalarBytes S) :
    ∃ allocId tag localAlloc,
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ mach.memory.live.toList ∧
      IsUnionPrefixMask S sc.sizeBytes localAlloc.allocation.initializationMask ∧
      localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
        .ok (.ok ()) ∧
      (localAlloc.allocation.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S)) = .ok (.ok ()) ↔
        sc.sizeBytes = S) ∧
      (∀ idx : Nat, idx < S →
        localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat idx)) =
          .ok (decide (idx < sc.sizeBytes))) :=
  UnionMemRel.initMask_spec h hS

example
    {mach : AnnealMachine}
    {uTy : Ty}
    {layouts : LayoutTable}
    {S : Nat}
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp)
    (hS : ValidScalarBytes S) :
    let bs := (allocLeBytes sc.bits sc.sizeBytes).toList.map (fun b => AbstractByte.init b none) ++
      replicateUninitBytes (S - sc.sizeBytes)
    encodeUnionFieldsWith (encodeUntypedValueToBytes 1) S [.scalar sc] = some bs ∧
    bs.length = S ∧
    ∃ allocId tag localAlloc,
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ mach.memory.live.toList ∧
      ∃ hraw_len : (unionAllocRaw localAlloc.allocation).size = S,
        ∀ idx : Nat, (hidx : idx < S) →
          ∃ ab : AbstractByte,
            get? bs idx = some ab ∧
            ab.isInit = decide (idx < sc.sizeBytes) ∧
            localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat idx)) =
              .ok ab.isInit ∧
            (idx < sc.sizeBytes →
              ab = .init ((unionAllocRaw localAlloc.allocation)[idx]'(by omega)) none) :=
  encodeUnionFieldsWith_matches_unionMemRel h hS

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {w u : Local}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.move ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : MirAst.LocalDecl}
    (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hty : wDecl.ty = uDecl.ty)
    {S n f : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    ∃ (s' : MachineState) (m' : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      stepMirFn body s = .step s' ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      StateRelLM2_4 body s' m' ∧
      get? s'.frame.locals w =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
      get? s'.frame.locals u = some .uninit ∧
      (∀ j, j ≠ w → j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      (∃ c, tf'.locals[u]? = some ⟨.live (.immediate .uninit), c⟩) ∧
      UnionMemRel m'.machine wDecl.ty body.layouts S f0Ty sc mp_w ∧
      LiveAllocsNodup m'.machine ∧
      IsImmediateFrameLocal tf' u ∧
      (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ w →
        IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
      s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
      StepPreservesHighWater m 1 (m', .ok true) :=
  union_whole_move_initMask_preservation_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_w hdecl_u hty hwt hfields_u hf hu_slot hu_mls hmem hw_uninit hw_imm

example
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable}
    {arrTy : Ty}
    {elemKind : RigidTy}
    {count : Nat}
    {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool) :
    let cx := annealSubsliceProjectionCx frame layouts mach
    let arrLay := translateTy arrTy layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    let sub := (elems.drop fromIdx).take cnt
    (SubsliceInBounds count fromIdx toIdx fromEnd →
      readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx fromEnd] =
        .ok (.aggregate 0 sub) ∧
      annealProjectList cx ⟨.indirect mp, arrLay⟩ [.Subslice fromIdx toIdx fromEnd] =
        .ok ⟨.indirect { mp with
                ptr := { mp.ptr with
                  offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
                metadata := .none },
             { ty := arrLay.ty,
               layout := { arrLay.layout with
                 fields := .Array es (UInt64.ofNat cnt),
                 size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }⟩ ∧
      ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
        (relOffset : Miri.ABI.Size)
        (localAlloc : Miri.Memory.LocalAllocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind),
        mp.ptr.provenance = some (.concrete allocId tag) ∧
        (allocId, localAlloc) ∈ mach.memory.live.toList ∧
        mach.lookupBaseAddr allocId = some baseAddr ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes) ∧
        ArraySliceRel elemKind cnt layouts sub
          (Miri.ABI.Size.ofBytes (relOffset.bytes + UInt64.ofNat (fromIdx * es.bytes.toNat)))
          localAlloc.allocation) ∧
    (fromEnd = true → count < fromIdx + toIdx → fromIdx + toIdx < 2 ^ 64 →
      readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx fromEnd] = .ub ∧
      ∃ msg, (annealProjectList cx ⟨.indirect mp, arrLay⟩
        [.Subslice fromIdx toIdx fromEnd]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) :=
  evalProjection_subslice_simulation frame locals hwf hnodup hmp fromIdx toIdx fromEnd

example
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable}
    {arrTy : Ty}
    {elemKind : RigidTy}
    {count : Nat}
    {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    {fromIdx toIdx : Nat}
    (hinv : toIdx < fromIdx)
    (hfrom : fromIdx ≤ count) :
    readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx false] = .ub ∧
    (annealProjectList (annealSubsliceProjectionCx frame layouts mach)
        ⟨.indirect mp, translateTy arrTy layouts⟩ [.Subslice fromIdx toIdx false]).mapError
        annealLiftProjectionError =
      .error (.invalidProgram "subslice length underflow") :=
  evalProjection_subslice_inverted_divergence frame locals hwf hinv hfrom

example
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable}
    {arrTy : Ty}
    {elemKind : RigidTy}
    {count : Nat}
    {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp)
    {fromIdx toIdx : Nat}
    (hfrom : fromIdx ≤ count)
    (hoob : count < toIdx)
    (hto_mul : toIdx * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat < 2 ^ 64)
    (hto_lt64 : toIdx < 2 ^ 64) :
    let cx := annealSubsliceProjectionCx frame layouts mach
    let arrLay := translateTy arrTy layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let cnt := toIdx - fromIdx
    readProjectedValue locals (.aggregate 0 elems) [.subslice fromIdx toIdx false] = .ub ∧
    annealProjectList cx ⟨.indirect mp, arrLay⟩ [.Subslice fromIdx toIdx false] =
      .ok ⟨.indirect { mp with
              ptr := { mp.ptr with
                offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
              metadata := .none },
           { ty := arrLay.ty,
             layout := { arrLay.layout with
               fields := .Array es (UInt64.ofNat cnt),
               size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }⟩ :=
  evalProjection_subslice_fromEndFalse_oob_divergence frame locals hwf hnodup hmp hfrom hoob hto_mul hto_lt64

example :
    evalRvalue (Witness.lm24InitAnneal 6).frame.locals
        (.aggregate (.adt "U" 0 (some 1)) [.constant (Witness.lm24ConstU32 0x01020304)])
        (Witness.lm24InitAnneal 6).memory Witness.lm24Body.localDecls Witness.lm24Body.layouts =
      .ok (.aggregate 0 [.unit, .scalar ⟨0x01020304, 4⟩])
        (Witness.lm24InitAnneal 6).frame.locals (Witness.lm24InitAnneal 6).memory :=
  Witness.lm24_rvalue_union_aggregate_activeField_witness

example :
    ∃ m₁ m₂ : AnnealStepState,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 1) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body Witness.lm24Bb1S1 m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body Witness.lm24Bb1S2 m₂ ∧
      get? Witness.lm24Bb1S2.frame.locals 2 = some (.init (.scalar ⟨5, 1⟩)) :=
  Witness.lm24_write_read_same_field_steps

example :
    ∃ (m₁ m₂ m₃ : AnnealStepState) (mp_w : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 0) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 0 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 0 2 [.uninit, Witness.lm24USlot, .uninit, .uninit, Witness.lm24USlot]) m₂ ∧
      UnionMemRel m₂.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U8Ty ⟨5, 1⟩ mp_w ∧
      (∃ allocId tag localAlloc,
        mp_w.ptr.provenance = some (.concrete allocId tag) ∧
        (allocId, localAlloc) ∈ m₂.machine.memory.live.toList ∧
        IsUnionPrefixMask 4 1 localAlloc.allocation.initializationMask ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) = .ok (.ok ()) ∧
        localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 4)) ≠ .ok (.ok ()) ∧
        (∀ idx : Nat, idx < 4 →
          localAlloc.allocation.initializationMask.get (Miri.ABI.Size.ofBytes (UInt64.ofNat idx)) =
            .ok (decide (idx < 1)))) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₂ = (m₃, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 0 3 [.uninit, Witness.lm24USlot, .init (.scalar ⟨5, 1⟩), .uninit, Witness.lm24USlot]) m₃ :=
  Witness.lm24_copy_initMask_steps

example :
    ∃ (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 2) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 2 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 2 2 [.uninit, Witness.lm24USlot, .uninit, .uninit, Witness.lm24USlot]) m₂ ∧
      stepMirFn Witness.lm24Body (Witness.lm24AnnealState 2 2 [.uninit, Witness.lm24USlot, .uninit, .uninit, Witness.lm24USlot]) =
        .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₂ = (m₃, .error (.undefinedBehavior msg)) :=
  Witness.lm24_copy_larger_field_ub

example :
    let cx := annealSubsliceProjectionCx (Witness.lm21InitMiriFrame 0) emptyLayoutTable
      (Witness.witnessMachineOf Witness.lm21ArrAlloc)
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect Witness.witnessMemPlace, translateTy Witness.lm21U16Arr3Ty emptyLayoutTable⟩
    readProjectedValue [] (.aggregate 0 Witness.lm21ArrElems) [.subslice 1 3 false] =
      .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩]) ∧
    (∃ op, annealProjectList cx base [.Subslice 1 3 false] = .ok op ∧
      ∃ mp, op.op = .indirect mp ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (Witness.witnessMemPlace.ptr.offset.bytes + 2)) ∧
    readProjectedValue [] (.aggregate 0 Witness.lm21ArrElems) [.subslice 1 1 true] =
      .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩]) ∧
    readProjectedValue [] (.aggregate 0 Witness.lm21ArrElems) [.subslice 2 2 true] = .ub ∧
    ∃ msg, (annealProjectList cx base [.Subslice 2 2 true]).mapError annealLiftProjectionError =
      .error (.undefinedBehavior msg) :=
  Witness.lm24_subslice_witness

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {u : Local}
    {f : Nat}
    {f0Ty : Ty}
    {op : MirAst.Operand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field f f0Ty]⟩ (.use op), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc' : MirAst.ScalarInt) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc') s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc')))) ∧
        (∀ j, j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc' mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ j,
          IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_union_field_write_simulation hstate hnodup hphase hbb hstmt hdecl_u hwt hfields hf hu_slot hu_mls hmem hop hfl

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {u j : Local}
    {fty : Ty}
    {op : MirAst.Operand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    (hprim : IsPrimScalarTy fty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op fty)
    (hf_le : (translateTy fty body.layouts).layout.size.bytes.toNat ≤ S)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc : MirAst.ScalarInt) (mp : Miri.Interpreter.MemPlace AnnealProv)
        (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc) s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n j (.scalar sc)))) ∧
        (∀ k, k ≠ u → get? s'.frame.locals k = get? s.frame.locals k) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c', tf'.locals[u]? = some ⟨.live (.indirect mp), c'⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S fty sc mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ k, k ≠ u →
          IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 1 (m', .ok true)) :=
  step_union_field_write_uninit_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_u hwt hfields hj hu_uninit hu_imm hprim hop hf_le hfl

example :
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 3) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 3 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 3 2 [.uninit, Witness.lm24U7Slot, .uninit, .uninit, .uninit]) m₂ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₂ = (m₃, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 3 3 [.uninit, Witness.lm24U7Slot, .init (.scalar ⟨7, 1⟩), .uninit, .uninit]) m₃ :=
  Witness.lm24_field_write_read_steps

example :
    stepMirFn Witness.lm24Body (Witness.lm24InitAnneal 4) =
      .step (Witness.lm24AnnealState 4 1 [.uninit, Witness.lm24U7Slot, .uninit, .uninit, .uninit]) ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 4) = (m', .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 4 1 [.uninit, Witness.lm24U7Slot, .uninit, .uninit, .uninit]) m' ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c', tf'.locals[1]? = some ⟨.live (.indirect mp), c'⟩) ∧
      UnionMemRel m'.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U8Ty ⟨7, 1⟩ mp :=
  Witness.lm24_field_write_uninit_simulation

example :
    stepMirFn Witness.lm24Body (Witness.lm24InitAnneal 8) =
      .step (Witness.lm24AnnealState 8 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 8) = (m', .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 8 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) m' ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c', tf'.locals[1]? = some ⟨.live (.indirect mp), c'⟩) ∧
      UnionMemRel m'.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U32Ty
        ⟨0x01020304, 4⟩ mp :=
  Witness.lm24_field1_write_uninit_simulation

example :
    ∃ (m₁ m₂ m₃ : AnnealStepState)
      (tf₃ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv)
      (msc₃ : Miri.Memory.ScalarInt),
      let hooks := annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts
      stepMirFn Witness.lm24Body (Witness.lm24InitAnneal 9) =
        .step (Witness.lm24AnnealState 9 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step hooks () (Witness.lm24InitMiri 9) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 9 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn Witness.lm24Body
        (Witness.lm24AnnealState 9 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) =
          .step (Witness.lm24AnnealState 9 2
            [.uninit, Witness.lm24USplicedSlot, .uninit, .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      UnionMemRel m₂.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U32Ty
        ⟨0x01020377, 4⟩ mp ∧
      stepMirFn Witness.lm24Body
        (Witness.lm24AnnealState 9 2 [.uninit, Witness.lm24USplicedSlot, .uninit, .uninit, .uninit]) =
          .step (Witness.lm24AnnealState 9 3
            [.uninit, Witness.lm24USplicedSlot, .uninit, .init (.scalar ⟨0x01020377, 4⟩), .uninit]) ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      ScalarRel ⟨0x01020377, 4⟩ msc₃ ∧
      m₃.stack.frames = #[tf₃] ∧
      (∃ c, tf₃.locals[3]? =
        some ⟨.live (.immediate (.scalar (.fromScalarInt msc₃))), c⟩) :=
  Witness.lm24_narrower_field_write_retains_high_bytes_correspondence

example :
    ∃ m₁ m₂ m₃ : AnnealStepState,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 5) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 5 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 5 2 [.uninit, .uninit, .uninit, .uninit, Witness.lm24USlot]) m₂ ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₂ = (m₃, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 5 3 [.uninit, .uninit, .init (.scalar ⟨5, 1⟩), .uninit, Witness.lm24USlot]) m₃ :=
  Witness.lm24_move_read_steps

example
    {mach : AnnealMachine}
    {layouts : LayoutTable}
    {arrTy : Ty}
    {elemKind : RigidTy}
    {count : Nat}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts none mp)
    (hpos : 0 < count) :
    annealCheckIndirectInitialized mach mp (translateTy arrTy layouts).layout.size =
      .error (.undefinedBehavior "access to uninitialized indirect place") :=
  annealCheckIndirectInitialized_uninit_array_ub hwf hnodup hmp hpos

example
    (localDecls : List MirAst.LocalDecl)
    (layouts : LayoutTable)
    (isMove : Bool)
    (arrIdx : Local)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool)
    (known : Option Miri.Interpreter.LocalLayout) :
    annealEvalOperandLM2_4 localDecls layouts
        (translateOperand (subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd)) known =
      annealEvalSubsliceOperand localDecls layouts
        ⟨arrIdx, #[.Subslice fromIdx toIdx fromEnd]⟩ known :=
  annealEvalOperandLM2_4_subslice localDecls layouts isMove arrIdx fromIdx toIdx fromEnd known

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRelLM2_4 body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : Local}
    {arrDecl : MirAst.LocalDecl}
    {elemKind : RigidTy}
    {count : Nat}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (isMove : Bool)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool)
    (known : Option Miri.Interpreter.LocalLayout) :
    let op := subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd
    let arrLay := translateTy arrDecl.ty body.layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    ((get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ IsImmediateFrameLocal topFrame arrIdx))) →
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls = .ub ∧
      ∃ m' msg, annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
        known m = .error (.undefinedBehavior msg) m') ∧
    (∀ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) →
      ∃ (mp : Miri.Interpreter.MemPlace AnnealProv)
        (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        MemPlaceRel m.machine arrDecl.ty body.layouts (some (.aggregate 0 elems)) mp ∧
        (∃ c, topFrame.locals[arrIdx]? = some ⟨.live (.indirect mp), c⟩) ∧
        topFrame'.locals[arrIdx]? = some ⟨.live (.indirect mp), some arrLay⟩ ∧
        (∀ k, k ≠ arrIdx → topFrame'.locals[k]? = topFrame.locals[k]?) ∧
        topFrame' = { topFrame with locals := topFrame'.locals } ∧
        StateRelLM2_4 body s { m with stack := ⟨#[topFrame']⟩ } ∧
        (SubsliceInBounds count fromIdx toIdx fromEnd →
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ok (.aggregate 0 ((elems.drop fromIdx).take cnt)) s.frame.locals ∧
          annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known m =
            .ok ⟨.indirect { mp with
                    ptr := { mp.ptr with
                      offset := Miri.ABI.Size.ofBytes
                        (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat fromIdx) },
                    metadata := .none },
                 { ty := arrLay.ty,
                   layout := { arrLay.layout with
                     fields := .Array es (UInt64.ofNat cnt),
                     size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt) } }⟩
              { m with stack := ⟨#[topFrame']⟩ } ∧
          ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
            (relOffset : Miri.ABI.Size)
            (localAlloc : Miri.Memory.LocalAllocation AnnealProv
              (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind),
            mp.ptr.provenance = some (.concrete allocId tag) ∧
            (allocId, localAlloc) ∈ m.machine.memory.live.toList ∧
            m.machine.lookupBaseAddr allocId = some baseAddr ∧
            mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes) ∧
            ArraySliceRel elemKind cnt body.layouts ((elems.drop fromIdx).take cnt)
              (Miri.ABI.Size.ofBytes
                (relOffset.bytes + UInt64.ofNat (fromIdx * es.bytes.toNat)))
              localAlloc.allocation) ∧
        (fromEnd = true → count < fromIdx + toIdx → fromIdx + toIdx < 2 ^ 64 →
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ub ∧
          ∃ msg, annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op)
            known m = .error (.undefinedBehavior msg) { m with stack := ⟨#[topFrame']⟩ })) :=
  evalSubsliceOperand_simulation hstate hframes hnodup hdecl_arr hwf isMove fromIdx toIdx fromEnd known

example :
    evalOperand (Witness.lm21ArrAnneal 0 .uninit).frame.locals (.copy ⟨1, [.subslice 1 3 false]⟩) .nil
        (Witness.lm21ArrAnneal 0 .uninit).memory.globals Witness.lm21Body.layouts .nil =
      .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩])
        (Witness.lm21ArrAnneal 0 .uninit).frame.locals ∧
    (∃ (op : Miri.Interpreter.OpTy AnnealProv) (m' : AnnealStepState)
        (mp : Miri.Interpreter.MemPlace AnnealProv),
      annealEvalOperandLM2_4 Witness.lm21Body.localDecls Witness.lm21Body.layouts
          (.Copy ⟨1, #[.Subslice 1 3 false]⟩) none (Witness.lm21ArrMiri 0 .uninit) = .ok op m' ∧
      StateRelLM2_4 Witness.lm21Body (Witness.lm21ArrAnneal 0 .uninit) m' ∧
      op.op = .indirect mp ∧
      mp.ptr.offset = Miri.ABI.Size.ofBytes (Witness.witnessMemPlace.ptr.offset.bytes + 2)) ∧
    evalOperand (Witness.lm21ArrAnneal 0 .uninit).frame.locals (.move ⟨1, [.subslice 2 2 true]⟩) .nil
        (Witness.lm21ArrAnneal 0 .uninit).memory.globals Witness.lm21Body.layouts .nil = .ub ∧
    (∃ (m' : AnnealStepState) (msg : String),
      annealEvalOperandLM2_4 Witness.lm21Body.localDecls Witness.lm21Body.layouts
          (.Move ⟨1, #[.Subslice 2 2 true]⟩) none (Witness.lm21ArrMiri 0 .uninit) =
        .error (.undefinedBehavior msg) m') ∧
    evalOperand (Witness.lm21InitAnneal 0).frame.locals (.copy ⟨1, [.subslice 1 3 false]⟩) .nil
        (Witness.lm21InitAnneal 0).memory.globals Witness.lm21Body.layouts .nil = .ub ∧
    (∃ (m' : AnnealStepState) (msg : String),
      annealEvalOperandLM2_4 Witness.lm21Body.localDecls Witness.lm21Body.layouts
          (.Copy ⟨1, #[.Subslice 1 3 false]⟩) none (Witness.lm21InitMiri 0) =
        .error (.undefinedBehavior msg) m') :=
  Witness.lm24_subslice_operand_witness

example
    (elemKind : RigidTy)
    (layouts : LayoutTable)
    {align : Miri.ABI.Align}
    (hal : align.pow2 ≤ 29)
    (extra : Option Miri.TreeBorrows.BorrowTree) :
    ∃ zeroAlloc : Miri.Memory.Allocation AnnealProv Unit,
      Miri.Memory.Allocation.fromBytes #[] align .Mut = .ok zeroAlloc ∧
      let dest' := zeroAlloc.withExtra extra
      dest'.byteSize = Miri.ABI.Size.ZERO ∧
      dest'.len = 0 ∧
      dest'.align = align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new Miri.ABI.Size.ZERO true ∧
      dest'.extra = extra ∧
      dest'.nativeBuffer = none ∧
      ArraySliceRel elemKind 0 layouts [] Miri.ABI.Size.ZERO dest' :=
  zero_array_fromBytes_spec elemKind layouts hal extra

example
    {elemKind : RigidTy}
    {cnt : Nat}
    {layouts : LayoutTable}
    {elems : List Value}
    {srcOff : Miri.ABI.Size}
    {src dest : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind cnt layouts elems srcOff src)
    (hpos : 0 < cnt)
    (helem_pos : 0 < (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hraw_dst : unionAllocRaw dest =
      Array.replicate
        (cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat) 0)
    (hsz_dst : dest.byteSize =
      Miri.ABI.Size.ofBytes
        (UInt64.ofNat
          (cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask = Miri.Memory.InitMask.new dest.byteSize false) :
    let totalBytes :=
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat
    let totalSz := Miri.ABI.Size.ofBytes (UInt64.ofNat totalBytes)
    ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      ArraySliceRel elemKind cnt layouts elems Miri.ABI.Size.ZERO dest' :=
  array_copy_freshAlloc_spec hslice hpos helem_pos hraw_dst hsz_dst hmut_dst hprov_dst hmask_dst

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {r u j : Local}
    {fty : Ty}
    {isMove : Bool}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u j fty)), span⟩)
    {rDecl uDecl : MirAst.LocalDecl}
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hr_ty : rDecl.ty = fty)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty)
    {w : Nat}
    (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    (hj : j < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hjne : j ≠ f)
    (hw_le : w ≤ sc.sizeBytes)
    (hbool : fty.kind = .bool → sc.bits % scalarModulus w = 0 ∨ sc.bits % scalarModulus w = 1)
    (hchar : fty.kind = .char → isValidCharCode (sc.bits % scalarModulus w) = true)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      get? s'.frame.locals r = some (.init (.scalar ⟨sc.bits % scalarModulus w, w⟩))) ∧
    (get? s.frame.locals r ≠ some .dead →
      ∃ (s' : MachineState) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (msc_w : Miri.Memory.ScalarInt),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals r = some (.init (.scalar ⟨sc.bits % scalarModulus w, w⟩)) ∧
        m'.machine = m.machine ∧
        m'.stack.frames = #[tf'] ∧
        ScalarRel ⟨sc.bits % scalarModulus w, w⟩ msc_w ∧
        ∃ c, tf'.locals[r]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc_w))), c⟩) :=
  step_union_type_punning_read_simulation hstate hnodup hphase hbb hstmt hdecl_r hr_ty hdecl_u hprim
    hw hsz hwt hfields hf hj hu_slot hu_mls hmem hr_imm hjne hw_le hbool hchar hfl

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {u j : Local}
    {fty : Ty}
    {op : MirAst.Operand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    (hj : j < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c', topFrame.locals[u]? = some ⟨.live (.indirect mp), c'⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hprim : IsPrimScalarTy fty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op fty)
    (hk_ge_ty : sc.sizeBytes ≤ (translateTy fty body.layouts).layout.size.bytes.toNat)
    (hfty_le : (translateTy fty body.layouts).layout.size.bytes.toNat ≤ S)
    (hfl0 : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hfl' : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size) :
    StepRelLM2_4 body m (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ (sc' : MirAst.ScalarInt) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
          .ok (.scalar sc') s.frame.locals ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals u = some (.init (.aggregate 0 (unionSlotFields n j (.scalar sc')))) ∧
        (∀ k, k ≠ u → get? s'.frame.locals k = get? s.frame.locals k) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c', tf'.locals[u]? = some ⟨.live (.indirect mp), c'⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S fty sc' mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_union_nonzero_field_write_simulation hstate hnodup hphase hbb hstmt hdecl_u hwt hfields hf
    hj hu_slot hu_mls hmem hprim hop hk_ge_ty hfty_le hfl0 hfl'

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u j : Local} {fty : Ty} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field j fty]⟩ (.use op), span⟩)
    {uDecl : MirAst.LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc_old : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc_old)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c', topFrame.locals[u]? = some ⟨.live (.indirect mp), c'⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc_old mp)
    (hprim : IsPrimScalarTy fty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op fty)
    (hlt_width : (translateTy fty body.layouts).layout.size.bytes.toNat < sc_old.sizeBytes)
    (hfl0 : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hfl' : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) j = some fl ∧
      fl.layout.size = (translateTy fty body.layouts).layout.size) :
    (evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ sc', evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
        .ok (.scalar sc') s.frame.locals →
      let mergedBytes :=
        encodeLittleEndianBytes sc'.bits sc'.sizeBytes none ++
          ((encodeLittleEndianBytes sc_old.bits sc_old.sizeBytes none).drop sc'.sizeBytes ++
            replicateUninitBytes (S - sc_old.sizeBytes))
      let s' := advanceStmt s
        (s.frame.locals.set u (.init (.aggregate 0
          (unionSlotFields n j (.scalar sc') ++
            [.aggregate 0 (encodeRawAbstractByteVals mergedBytes)])))) s.memory
      stepMirFn body s = .step s' ∧
      ∃ (m' : AnnealStepState) (msc' : Miri.Memory.ScalarInt)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
        (allocId : Miri.Memory.AllocId)
        (la_old : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
        (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        ScalarRel sc' msc' ∧
        m'.stack.frames = #[tf'] ∧
        tf'.body = translateBody body ∧
        tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ ∧
        tf'.locals.size = body.localDecls.length ∧
        tf'.locals[u]? = some ⟨.live (.indirect mp), some (translateTy uDecl.ty body.layouts)⟩ ∧
        (∀ i decl slot mls, i ≠ u →
          get? body.localDecls i = some decl →
          get? s'.frame.locals i = some slot →
          tf'.locals[i]? = some mls →
          UnionLocalRel m'.machine decl body.layouts slot mls) ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ k,
          IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) ∧
        (allocId, la_old) ∈ m.machine.memory.live.toList ∧
        (allocId, ⟨la_old.kind, A'⟩) ∈ m'.machine.memory.live.toList ∧
        LiveAllocsNodup m'.machine ∧
        IsUnionPrefixMask S sc_old.sizeBytes A'.initializationMask ∧
        A'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc'.sizeBytes)) false =
            .ok (.fromScalarInt msc') ∧
        (unionAllocRaw A').extract sc'.sizeBytes S =
          (unionAllocRaw la_old.allocation).extract sc'.sizeBytes S ∧
        (f0Ty.kind ≠ .bool → f0Ty.kind ≠ .char →
          UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty
            (unionSpliceLowScalar sc_old sc') mp) ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_union_narrower_field_write_correspondence hstate hnodup hphase hbb hstmt hdecl_u hwt hfields hf
    hj hu_slot hu_mls hmem hprim hop hlt_width hfl0 hfl'

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hstate : StateRelLM2_4 body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrIdx : Local}
    {arrDecl : MirAst.LocalDecl}
    {elemKind : RigidTy}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind 0)
    (huninit : get? s.frame.locals arrIdx = some .uninit)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    {c : Option Miri.Interpreter.LocalLayout}
    (hind : topFrame.locals[arrIdx]? = some ⟨.live (.indirect mp), c⟩) :
    ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
      (localAlloc : Miri.Memory.LocalAllocation AnnealProv
        (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)
      (topFrame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      mp.ptr.provenance = some (.concrete allocId tag) ∧
      (allocId, localAlloc) ∈ m.machine.memory.live.toList ∧
      StateRelLM2_4 body s { m with stack := ⟨#[topFrame']⟩ } ∧
      (localAlloc.allocation.initializationMask.blocks = .Lazy false →
        ∀ isMove fromIdx toIdx fromEnd known,
          let op := subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ub ∧
          annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known m =
            .error (.undefinedBehavior "access to uninitialized indirect place")
              { m with stack := ⟨#[topFrame']⟩ }) ∧
      (localAlloc.allocation.initializationMask =
          Miri.Memory.InitMask.new localAlloc.allocation.byteSize true →
        ∀ isMove fromEnd known,
          let op := subsliceReadOperand isMove arrIdx 0 0 fromEnd
          let arrLay := translateTy arrDecl.ty body.layouts
          let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil body.localDecls =
            .ub ∧
          annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known m =
            .ok ⟨.indirect mp,
                 { ty := arrLay.ty,
                   layout := { arrLay.layout with
                     fields := .Array es 0,
                     size := Miri.ABI.Size.ZERO } }⟩
              { m with stack := ⟨#[topFrame']⟩ }) :=
  evalSubsliceOperand_zero_uninit_indirect_characterization hstate hframes hnodup hdecl_arr hwf
    huninit hind

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {d arrIdx : Local}
    {isMove : Bool}
    {fromIdx toIdx : Nat}
    {fromEnd : Bool}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨d, .nil⟩ (.use (subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd)),
            span⟩)
    {dDecl arrDecl : MirAst.LocalDecl}
    {elemKind : RigidTy}
    {count : Nat}
    (hdecl_d : get? body.localDecls d = some dDecl)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf_arr : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hwf_d : WellTypedArrayTy body.layouts dDecl.ty elemKind
      (subsliceEnd count toIdx fromEnd - fromIdx))
    (hd_uninit : get? s.frame.locals d = some .uninit)
    (hd_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame d) :
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    ((get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf arrIdx))) →
      stepMirFn body s = .fail .ub ∧
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) →
      (fromEnd = true → count < fromIdx + toIdx → fromIdx + toIdx < 2 ^ 64 →
        stepMirFn body s = .fail .ub ∧
        StepRelLM2_4 body m (stepMirFn body s)
          (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
      (SubsliceInBounds count fromIdx toIdx fromEnd →
        ∃ (s' : MachineState) (m' : AnnealStepState)
          (mp_d : Miri.Interpreter.MemPlace AnnealProv)
          (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
          stepMirFn body s = .step s' ∧
          Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
            (m', .ok true) ∧
          StateRelLM2_4 body s' m' ∧
          get? s'.frame.locals d = some (.init (.aggregate 0 ((elems.drop fromIdx).take cnt))) ∧
          get? s'.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
          (∀ j, j ≠ d → get? s'.frame.locals j = get? s.frame.locals j) ∧
          m'.stack.frames = #[tf'] ∧
          (∃ c, tf'.locals[d]? = some ⟨.live (.indirect mp_d), c⟩) ∧
          MemPlaceRel m'.machine dDecl.ty body.layouts
            (some (.aggregate 0 ((elems.drop fromIdx).take cnt))) mp_d ∧
          LiveAllocsNodup m'.machine ∧
          (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ d →
            IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
          s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
          StepPreservesHighWater m 1 (m', .ok true))) :=
  step_subslice_assign_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_d hdecl_arr
    hwf_arr hwf_d hd_uninit hd_imm

example :
    ∃ (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (msc_w : Miri.Memory.ScalarInt),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 6) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 6 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn Witness.lm24Body
        (Witness.lm24AnnealState 6 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) =
          .step (Witness.lm24AnnealState 6 2
            [.uninit, Witness.lm24UU32Slot, .init (.scalar ⟨0x04, 1⟩), .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 6 2
          [.uninit, Witness.lm24UU32Slot, .init (.scalar ⟨0x04, 1⟩), .uninit, .uninit]) m₂ ∧
      m₂.stack.frames = #[tf₂] ∧
      (∃ c, tf₂.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc_w))), c⟩) ∧
      msc_w.data = 0x04 ∧
      msc_w.size = Miri.ABI.Size.ofBytes 1 :=
  Witness.lm24_type_punning_read_simulation

example :
    ∃ (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 7) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 7 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn Witness.lm24Body
        (Witness.lm24AnnealState 7 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) =
          .step (Witness.lm24AnnealState 7 2 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 7 2 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) m₂ ∧
      m₂.stack.frames = #[tf₂] ∧
      (∃ c, tf₂.locals[1]? = some ⟨.live (.indirect mp), c⟩) ∧
      UnionMemRel m₂.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U32Ty ⟨0x01020304, 4⟩ mp :=
  Witness.lm24_nonzero_field_write_simulation

example :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (mp₂ mp₃ : Miri.Interpreter.MemPlace AnnealProv),
      stepMirFn Witness.lm24SubsliceBody
        (Witness.lm24SubsliceAnneal 0 (.init (.aggregate 0 Witness.lm21ArrElems))) = .step s₁ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24SubsliceBody.localDecls Witness.lm24SubsliceBody.layouts) ()
          (Witness.lm24SubsliceMiri 0) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24SubsliceBody s₁ m₁ ∧
      get? s₁.frame.locals 2 =
        some (.init (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩])) ∧
      get? s₁.frame.locals 1 = some (.init (.aggregate 0 Witness.lm21ArrElems)) ∧
      MemPlaceRel m₁.machine Witness.lm24U16Arr2Ty emptyLayoutTable
        (some (.aggregate 0 [.scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩])) mp₂ ∧
      stepMirFn Witness.lm24SubsliceBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24SubsliceBody.localDecls Witness.lm24SubsliceBody.layouts) ()
          m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24SubsliceBody s₂ m₂ ∧
      get? s₂.frame.locals 3 = some (.init (.aggregate 0 [])) ∧
      MemPlaceRel m₂.machine Witness.lm21U16Arr0Ty emptyLayoutTable (some (.aggregate 0 [])) mp₃ :=
  Witness.lm24_subslice_assign_steps

example :
    (stepMirFn Witness.lm24SubsliceBody
      (Witness.lm24SubsliceAnneal 2 (.init (.aggregate 0 Witness.lm21ArrElems))) = .fail .ub ∧
     StepRelLM2_4 Witness.lm24SubsliceBody (Witness.lm24SubsliceMiri 2)
      (stepMirFn Witness.lm24SubsliceBody
        (Witness.lm24SubsliceAnneal 2 (.init (.aggregate 0 Witness.lm21ArrElems))))
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 Witness.lm24SubsliceBody.localDecls Witness.lm24SubsliceBody.layouts) ()
        (Witness.lm24SubsliceMiri 2))) ∧
    (stepMirFn Witness.lm24SubsliceBody (Witness.lm24SubsliceAnneal 0 .uninit) = .fail .ub ∧
     StepRelLM2_4 Witness.lm24SubsliceBody (Witness.lm24SubsliceUninitMiri 0)
      (stepMirFn Witness.lm24SubsliceBody (Witness.lm24SubsliceAnneal 0 .uninit))
      (Miri.Interpreter.Step.step
        (annealStepHooksLM2_4 Witness.lm24SubsliceBody.localDecls Witness.lm24SubsliceBody.layouts) ()
        (Witness.lm24SubsliceUninitMiri 0))) :=
  Witness.lm24_subslice_assign_oob_and_uninit_ub

example :
    (evalOperand (Witness.lm24SubsliceAnneal 0 .uninit).frame.locals
        (subsliceReadOperand false 3 0 0 false) .nil
        (Witness.lm24SubsliceAnneal 0 .uninit).memory.globals emptyLayoutTable .nil = .ub ∧
     ∃ topFrame',
       annealEvalOperandLM2_4 Witness.lm24SubsliceBody.localDecls emptyLayoutTable
         (translateOperand (subsliceReadOperand false 3 0 0 false)) none
         (Witness.lm24ZeroUninitMiri Witness.witnessUninitAlloc) =
       .error (.undefinedBehavior "access to uninitialized indirect place")
         { (Witness.lm24ZeroUninitMiri Witness.witnessUninitAlloc) with stack := ⟨#[topFrame']⟩ }) ∧
    (evalOperand (Witness.lm24SubsliceAnneal 0 .uninit).frame.locals
        (subsliceReadOperand false 3 0 0 false) .nil
        (Witness.lm24SubsliceAnneal 0 .uninit).memory.globals emptyLayoutTable .nil = .ub ∧
     ∃ (op : Miri.Interpreter.OpTy AnnealProv) (topFrame' : Miri.Interpreter.Frame AnnealProv
         Miri.Interpreter.LocalLayout Unit),
       annealEvalOperandLM2_4 Witness.lm24SubsliceBody.localDecls emptyLayoutTable
         (translateOperand (subsliceReadOperand false 3 0 0 false)) none
         (Witness.lm24ZeroUninitMiri Witness.lm21ArrAlloc) =
       .ok op { (Witness.lm24ZeroUninitMiri Witness.lm21ArrAlloc) with stack := ⟨#[topFrame']⟩ } ∧
       op.op = .indirect Witness.witnessMemPlace) :=
  Witness.lm24_zero_uninit_indirect_subslice_witness

example
    {localDecls : List MirAst.LocalDecl} {layouts : LayoutTable}
    {dest : Miri.Interpreter.RuntimePlace AnnealProv} {st st' : AnnealStepState}
    {forced : Miri.Interpreter.MPlaceTy AnnealProv}
    (h : Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) () dest st =
      .ok forced st') :
    annealForceUnionAllocation localDecls layouts dest st = .ok forced st' :=
  annealForceUnionAllocation_of_ok h

example
    (mask : Miri.Memory.InitMask)
    (range : Miri.Memory.AllocRange) (finish : Miri.ABI.Size) (newState : Bool)
    (hend : range.endExclusive = .ok finish)
    (hstart : range.start.bytes = 0)
    (hlen : mask.len.bytes ≤ finish.bytes) :
    mask.setRange range newState = .ok ⟨.Lazy newState, finish⟩ :=
  initMask_setRange_full_overwrite mask range finish newState hend hstart hlen

example
    {S k : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) :
    M.len = translateSizeBytes S :=
  IsUnionPrefixMask.len_eq hM

example
    {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hk'k : k' ≤ k) (hkS : k ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S k M' :=
  IsUnionPrefixMask.setRange_le hM hS hk hk' hk'k hkS

example
    {S k k' : Nat} {M : Miri.Memory.InitMask}
    (hM : IsUnionPrefixMask S k M) (hS : ValidScalarBytes S)
    (hk : ValidScalarBytes k) (hk' : ValidScalarBytes k') (hkS : k ≤ S) (hk'S : k' ≤ S) :
    ∃ M', M.setRange
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes k')) true = .ok M' ∧
      IsUnionPrefixMask S (max k k') M' :=
  IsUnionPrefixMask.setRange_max hM hS hk hk' hkS hk'S

example
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {E : Type} {A : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hlen : A.len = S) (hsz : A.byteSize = translateSizeBytes S) (hS : S ≤ 16)
    (hle : sc.sizeBytes ≤ S)
    (hmut : A.mutability = .Mut) (hprov : A.provenanceMap = Miri.Memory.ProvenanceMap.new)
    {M' : Miri.Memory.InitMask}
    (hset : A.initializationMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
        .ok M') :
    ∃ A' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
        (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () A' ∧
      A'.byteSize = A.byteSize ∧
      A'.len = S ∧
      A'.align = A.align ∧
      A'.mutability = .Mut ∧
      A'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      A'.initializationMask = M' ∧
      A'.extra = A.extra ∧
      A'.nativeBuffer = A.nativeBuffer ∧
      (unionAllocRaw A').extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes ∧
      (unionAllocRaw A').extract sc.sizeBytes S = (unionAllocRaw A).extract sc.sizeBytes S :=
  union_writeScalar_prefix_preserve_high hrel hlen hsz hS hle hmut hprov hset

example
    {E : Type}
    {src dest : Miri.Memory.Allocation AnnealProv E} {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (hlen_src : src.len = S) (hsz_src : src.byteSize = translateSizeBytes S)
    (hprov_src : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_src : IsUnionPrefixMask S k src.initializationMask)
    (hlen_dst : dest.len = S)
    (hsz_dst : dest.byteSize = translateSizeBytes S)
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = translateSizeBytes S) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = unionCopiedPrefixMask S k ∧
      IsUnionPrefixMask S k dest'.initializationMask ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = unionAllocRaw src :=
  union_copy_alloc_spec hS hk hle hlen_src hsz_src hprov_src hmask_src hlen_dst hsz_dst hmut_dst
    hprov_dst hmask_dst

example
    {E : Type}
    {src : Miri.Memory.Allocation AnnealProv E} {S k : Nat}
    (hS : ValidScalarBytes S) (hk : ValidScalarBytes k) (hle : k ≤ S)
    (hlen : src.len = S) (hsz : src.byteSize = translateSizeBytes S)
    (hmut : src.mutability = .Mut)
    (hprov : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask : IsUnionPrefixMask S k src.initializationMask) :
    ∃ st' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true src =
        .error .copyRangesOverlap st' :=
  union_copy_self_overlap_err hS hk hle hlen hsz hmut hprov hmask

example
    {E : Type}
    {src dest : Miri.Memory.Allocation AnnealProv E} {S : Nat}
    (hS : ValidScalarBytes S) (sameAlloc : Bool)
    (hlen_src : src.len = S) (hsz_src : src.byteSize = translateSizeBytes S)
    (hprov_src : src.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_src : src.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false)
    (hlen_dst : dest.len = S) (hsz_dst : dest.byteSize = translateSizeBytes S)
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = translateSizeBytes S) :
    ∃ dest' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.copy src
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes S))
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) sameAlloc true dest = .ok () dest' ∧
      dest'.byteSize = translateSizeBytes S ∧
      dest'.len = S ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new (translateSizeBytes S) false ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      unionAllocRaw dest' = unionAllocRaw dest :=
  union_copy_uninit_alloc_spec hS sameAlloc hlen_src hsz_src hprov_src hmask_src hlen_dst hsz_dst
    hmut_dst hprov_dst hmask_dst

example
    {elemKind : RigidTy} {cnt : Nat} {layouts : LayoutTable} {elems : List Value}
    {srcOff : Miri.ABI.Size}
    {src dest : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hslice : ArraySliceRel elemKind cnt layouts elems srcOff src)
    (hpos : 0 < cnt)
    (helem_pos : 0 < (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hlen_dst_in : dest.len =
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)
    (hsz_dst : dest.byteSize =
      Miri.ABI.Size.ofBytes
        (UInt64.ofNat
          (cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat)))
    (hmut_dst : dest.mutability = .Mut)
    (hprov_dst : dest.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_dst : dest.initializationMask.len = dest.byteSize) :
    let totalBytes :=
      cnt * (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size.bytes.toNat
    let totalSz := Miri.ABI.Size.ofBytes (UInt64.ofNat totalBytes)
    ∃ dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      Miri.Memory.Allocation.copy src (Miri.Memory.allocRange srcOff totalSz)
        Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) false true dest = .ok () dest' ∧
      dest'.byteSize = totalSz ∧
      dest'.len = totalBytes ∧
      dest'.align = dest.align ∧
      dest'.mutability = .Mut ∧
      dest'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
      dest'.initializationMask = Miri.Memory.InitMask.new totalSz true ∧
      dest'.extra = dest.extra ∧
      dest'.nativeBuffer = dest.nativeBuffer ∧
      ArraySliceRel elemKind cnt layouts elems Miri.ABI.Size.ZERO dest' :=
  array_copy_alloc_spec hslice hpos helem_pos hlen_dst_in hsz_dst hmut_dst hprov_dst hmask_dst

example
    {mach : AnnealMachine} {decl : MirAst.LocalDecl} {layouts : LayoutTable}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts .dead mls) :
    mls.value = .dead :=
  UnionLocalRel.dead_value h

example
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} (hlt : idx < tf.locals.size)
    (hdead : (tf.locals[idx]'hlt).value = .dead)
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout) :
    annealForceUnionAllocation body.localDecls body.layouts ⟨.local 0 idx none ident, lay⟩ m =
      .error (.undefinedBehavior "write to dead local") m :=
  annealForceUnionAllocation_dead_err hframes hlt hdead ident lay

example
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} (hlt : idx < tf.locals.size)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hind : (tf.locals[idx]'hlt).value = .live (.indirect mp))
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout) :
    annealForceUnionAllocation body.localDecls body.layouts ⟨.local 0 idx none ident, lay⟩ m =
      .ok ⟨mp, lay⟩ m :=
  annealForceUnionAllocation_indirect_eq hframes hlt hind ident lay

example
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {w : Nat} {wDecl : MirAst.LocalDecl} (hlt : w < tf.locals.size)
    {mp_w : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (tf.locals[w]'hlt).value = .live (.indirect mp_w))
    (hnodup : LiveAllocsNodup m.machine)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {allocId destId : Miri.Memory.AllocId}
    {tag_u tag_w : Miri.Memory.BorTag} {base_u base_w : UInt64}
    {la_u la_w : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov_u : mp_u.ptr.provenance = some (.concrete allocId tag_u))
    (hlive_u : (allocId, la_u) ∈ m.machine.memory.live.toList)
    (hbase_u : m.machine.lookupBaseAddr allocId = some base_u)
    (hptr_u : mp_u.ptr.offset = Miri.ABI.Size.ofBytes base_u)
    (hprov_w : mp_w.ptr.provenance = some (.concrete destId tag_w))
    (hlive_w : (destId, la_w) ∈ m.machine.memory.live.toList)
    (hbase_w : m.machine.lookupBaseAddr destId = some base_w)
    (hptr_w : mp_w.ptr.offset = Miri.ABI.Size.ofBytes base_w)
    (hsz_nz : ((translateTy wDecl.ty body.layouts).layout.size.bytes == 0) = false)
    (srcLay : Miri.Interpreter.LocalLayout) (ident : Miri.Interpreter.LocalsIdentity) :
    ∃ (destIdx : Nat),
      m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some destIdx ∧
      m.machine.memory.live[destIdx]? = some (destId, la_w) ∧
      (∀ A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
        Miri.Memory.Allocation.copy la_u.allocation
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy wDecl.ty body.layouts).layout.size)
            Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (allocId == destId) true la_w.allocation =
          .ok () A' →
        annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, srcLay⟩
            ⟨.local 0 w none ident, translateTy wDecl.ty body.layouts⟩ m =
          .ok () { m with machine := inplaceMachine m.machine destIdx destId la_w.kind A' } ∧
        LiveAllocsNodup (inplaceMachine m.machine destIdx destId la_w.kind A') ∧
        (destId, ⟨la_w.kind, A'⟩) ∈
          (inplaceMachine m.machine destIdx destId la_w.kind A').memory.live.toList ∧
        (∀ a la, a ≠ destId → (a, la) ∈ m.machine.memory.live.toList →
          (a, la) ∈ (inplaceMachine m.machine destIdx destId la_w.kind A').memory.live.toList)) ∧
      (∀ err A_err,
        Miri.Memory.Allocation.copy la_u.allocation
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy wDecl.ty body.layouts).layout.size)
            Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (allocId == destId) true la_w.allocation =
          .error err A_err →
        annealMemCopyOp body.localDecls body.layouts ⟨.indirect mp_u, srcLay⟩
            ⟨.local 0 w none ident, translateTy wDecl.ty body.layouts⟩ m =
          .error (annealMemCopyError err) m) :=
  annealMemCopyOp_inplaceUnion hframes hlt hval hnodup hprov_u hlive_u hbase_u hptr_u hprov_w
    hlive_w hbase_w hptr_w hsz_nz srcLay ident

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {isMove : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (unionWholeOperand isMove u)), span⟩)
    {wDecl uDecl : MirAst.LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields_u : (translateTy uDecl.ty body.layouts).layout.fields = .Union n) :
    ((get? s.frame.locals u = some .dead ∨
        (get? s.frame.locals u = some .uninit ∧
          ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf u)) →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ f f0Ty sc mp_u,
      f < n →
      get? s.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      get? s.frame.locals w = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ f f_old f0Ty sc mp_u f0Ty_old sc_old mp_w,
      w ≠ u → f < n → f_old < n →
      get? s.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      get? s.frame.locals w =
        some (.init (.aggregate 0 (unionSlotFields n f_old (.scalar sc_old)))) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) →
      UnionMemRel m.machine wDecl.ty body.layouts S f0Ty_old sc_old mp_w →
      ∃ (s' : MachineState) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals w =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
        get? s'.frame.locals u =
          (if isMove then some .uninit
           else some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
        UnionMemRel m'.machine wDecl.ty body.layouts S f0Ty sc mp_w ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_union_whole_copy_or_move_overwrite_simulation hstate hnodup hphase hbb hstmt hdecl_w hdecl_u
    hty hwt hfields_u

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {uDecl : MirAst.LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "whole-value copy between overlapping ranges")) :=
  step_union_self_copy_overlap_divergence hstate hnodup hphase hbb hstmt hdecl_u hwt hu_slot hu_mls
    hmem

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {w u : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨w, .nil⟩ (.use (.copy ⟨u, .nil⟩)), span⟩)
    {wDecl uDecl : MirAst.LocalDecl} (hdecl_w : get? body.localDecls w = some wDecl)
    (hdecl_u : get? body.localDecls u = some uDecl) (hty : wDecl.ty = uDecl.ty)
    {S : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag} {baseAddr : UInt64}
    {la_u : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hprov_u : mp_u.ptr.provenance = some (.concrete allocId tag))
    (hlive_u : (allocId, la_u) ∈ m.machine.memory.live.toList)
    (hbase_u : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hptr_u : mp_u.ptr.offset = Miri.ABI.Size.ofBytes baseAddr)
    (hlen_u : la_u.allocation.len = S)
    (hsz_u : la_u.allocation.byteSize = translateSizeBytes S)
    (hp_u : la_u.allocation.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (hmask_u : la_u.allocation.initializationMask =
      Miri.Memory.InitMask.new (translateSizeBytes S) false)
    (hw_uninit : get? s.frame.locals w = some .uninit)
    (hw_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame w) :
    stepMirFn body s = .fail .ub ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp_w : Miri.Interpreter.MemPlace AnnealProv) (id : Miri.Memory.AllocId)
      (la_w : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      mp_w.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id ∧
      (id, la_w) ∈ m'.machine.memory.live.toList ∧
      la_w.allocation.initializationMask =
        Miri.Memory.InitMask.new (translateSizeBytes S) false :=
  step_union_copy_indirect_uninit_divergence hstate hnodup hcanRes hphase hbb hstmt hdecl_w hdecl_u
    hty hwt hu_uninit hu_mls hprov_u hlive_u hbase_u hptr_u hlen_u hsz_u hp_u hmask_u hw_uninit
    hw_imm

example
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {u : Nat} (hlt : u < tf.locals.size)
    (hdead : (tf.locals[u]'hlt).value = .dead)
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout)
    (f : Nat) :
    annealUnionAggregateField body.localDecls body.layouts ⟨.local 0 u none ident, lay⟩ f m =
      .error (.undefinedBehavior "write to dead local") m :=
  annealUnionAggregateField_dead_err hframes hlt hdead ident lay f

example
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {u : Nat} {uDecl : MirAst.LocalDecl}
    (hlt : u < tf.locals.size)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (tf.locals[u]'hlt).value = .live (.indirect mp))
    (hmeta : mp.metadata = .none)
    {n : Nat}
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hn : 0 < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) 0 = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (ident : Miri.Interpreter.LocalsIdentity) :
    annealUnionAggregateField body.localDecls body.layouts
        ⟨.local 0 u none ident, translateTy uDecl.ty body.layouts⟩ 0 m =
      .ok ⟨.memory mp, fl⟩ m :=
  annealUnionAggregateField_inplace hframes hlt hval hmeta hfields hn hfl hfl_sized ident

example
    {mach : AnnealMachine} (hnodup : LiveAllocsNodup mach)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {destLay : Miri.Interpreter.LocalLayout}
    {uTy : Ty} {layouts : LayoutTable} {S : Nat} {f0Ty_old f0Ty : Ty} {sc_old : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmem : UnionMemRel mach uTy layouts S f0Ty_old sc_old mp) (hS : ValidScalarBytes S)
    (hprim : IsPrimScalarTy f0Ty)
    {sc' : MirAst.ScalarInt} {msc' : Miri.Memory.ScalarInt} (hrel' : ScalarRel sc' msc')
    (hk_ge : sc_old.sizeBytes ≤ sc'.sizeBytes) (hk'S : sc'.sizeBytes ≤ S)
    (hf0imm' : ImmediateRel f0Ty layouts (.scalar sc') (.scalar (.fromScalarInt msc'))) :
    ∃ (allocIdx : Nat) (allocId : Miri.Memory.AllocId)
      (kind : Miri.Memory.MemoryKind Miri.Memory.MiriMemoryKind)
      (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
      (la₀ : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId ∧
      (allocId, la₀) ∈ mach.memory.live.toList ∧
      annealWriteImmediateLM2_2 (.scalar (.fromScalarInt msc')) ⟨.memory mp, destLay⟩
          { stack := ⟨#[tf]⟩, machine := mach } =
        .ok () { stack := ⟨#[tf]⟩, machine := inplaceMachine mach allocIdx allocId kind A' } ∧
      UnionMemRel (inplaceMachine mach allocIdx allocId kind A') uTy layouts S f0Ty sc' mp ∧
      LiveAllocsNodup (inplaceMachine mach allocIdx allocId kind A') ∧
      (∀ a la, a ≠ allocId → (a, la) ∈ mach.memory.live.toList →
        (a, la) ∈ (inplaceMachine mach allocIdx allocId kind A').memory.live.toList) :=
  annealWriteImmediate_unionInplace_ge hnodup hmem hS hprim hrel' hk_ge hk'S hf0imm'

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {d : DefPath} {f : Nat} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩)
    {uDecl : MirAst.LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    {f0Ty : Ty} (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l) :
    (get? s.frame.locals u = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ f_old f0Ty_old sc_old mp,
      f_old < n →
      get? s.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f_old (.scalar sc_old)))) →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty_old sc_old mp →
      sc_old.sizeBytes ≤ (translateTy f0Ty body.layouts).layout.size.bytes.toNat →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
      (∀ s', stepMirFn body s = .step s' →
        ∃ (sc : MirAst.ScalarInt) (m' : AnnealStepState)
          (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
          Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
            (m', .ok true) ∧
          StateRelLM2_4 body s' m' ∧
          get? s'.frame.locals u =
            some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
          m'.stack.frames = #[tf'] ∧
          (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
          UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
          LiveAllocsNodup m'.machine ∧
          StepPreservesHighWater m 0 (m', .ok true))) :=
  step_union_aggregate_overwrite_simulation hstate hnodup hphase hbb hstmt hdecl_u hwt hfields hf
    hfl hfl_sized hprim0 hop hf0_le hadt hfl_sz hdecls_adt

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {d : DefPath} {f : Nat} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some f)) [op]), span⟩)
    {uDecl : MirAst.LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S n f_old : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl)
    (hfl_sized : fl.layout.isSized = true)
    {f0Ty_old f0Ty : Ty} {sc_old : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f_old (.scalar sc_old)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
    {la_old : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    (hprov : mp.ptr.provenance = some (.concrete allocId tag))
    (hlive_old : (allocId, la_old) ∈ m.machine.memory.live.toList)
    (hmem_old : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty_old sc_old mp)
    (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hlt_width : (translateTy f0Ty body.layouts).layout.size.bytes.toNat < sc_old.sizeBytes)
    {sc : MirAst.ScalarInt}
    (hop_ok : evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
      .ok (.scalar sc) s.frame.locals)
    (hadt : ∃ args, uDecl.ty.kind = .adt d args)
    (hfl_sz : fl.layout.size = (translateTy f0Ty body.layouts).layout.size)
    (hdecls_adt : ∀ l ∈ collectAdtLayoutsInDecls body.layouts d body.localDecls,
      body.layouts.lookup uDecl.ty.layoutIdx = some l) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals u =
        some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc))))) ∧
    ∃ (m' : AnnealStepState) (msc : Miri.Memory.ScalarInt)
      (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      ScalarRel sc msc ∧
      (allocId, ⟨la_old.kind, A'⟩) ∈ m'.machine.memory.live.toList ∧
      IsUnionPrefixMask S sc_old.sizeBytes A'.initializationMask ∧
      A'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
          .ok (.fromScalarInt msc) ∧
      (unionAllocRaw A').extract sc.sizeBytes S =
        (unionAllocRaw la_old.allocation).extract sc.sizeBytes S :=
  step_union_aggregate_smaller_overwrite_divergence hstate hnodup hphase hbb hstmt hdecl_u hwt
    hfields hf hfl hfl_sized hu_slot hu_mls hprov hlive_old hmem_old hprim0 hop hlt_width hop_ok
    hadt hfl_sz hdecls_adt

example
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {d : Nat} {dDecl : MirAst.LocalDecl} {elemKind : RigidTy} {cnt : Nat}
    (hlt : d < tf.locals.size)
    (hwf_d : WellTypedArrayTy body.layouts dDecl.ty elemKind cnt)
    {mp_d : Miri.Interpreter.MemPlace AnnealProv}
    (hval : (tf.locals[d]'hlt).value = .live (.indirect mp_d))
    (hnodup : LiveAllocsNodup m.machine)
    {subMp : Miri.Interpreter.MemPlace AnnealProv}
    {allocId destId : Miri.Memory.AllocId} {tag tag_d : Miri.Memory.BorTag}
    {baseAddr base_d : UInt64} {srcOff : Miri.ABI.Size}
    {la la_d : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind}
    {sub oldElems : List Value}
    (hne : allocId ≠ destId)
    (hprov : subMp.ptr.provenance = some (.concrete allocId tag))
    (hlive : (allocId, la) ∈ m.machine.memory.live.toList)
    (hbase : m.machine.lookupBaseAddr allocId = some baseAddr)
    (hsrcOff : Miri.ABI.Size.ofBytes (subMp.ptr.offset.bytes - baseAddr) = srcOff)
    (hslice : ArraySliceRel elemKind cnt body.layouts sub srcOff la.allocation)
    (hprov_d : mp_d.ptr.provenance = some (.concrete destId tag_d))
    (hlive_d : (destId, la_d) ∈ m.machine.memory.live.toList)
    (hbase_d : m.machine.lookupBaseAddr destId = some base_d)
    (hptr_d : mp_d.ptr.offset = Miri.ABI.Size.ofBytes base_d)
    (hsz_d : la_d.allocation.byteSize = (translateTy dDecl.ty body.layouts).layout.size)
    (hal_d : la_d.allocation.align.pow2 ≤ 29)
    (hslice_d_old : ArraySliceRel elemKind cnt body.layouts oldElems Miri.ABI.Size.ZERO la_d.allocation)
    (srcLay : Miri.Interpreter.LocalLayout) (ident : Miri.Interpreter.LocalsIdentity) :
    ∃ (destIdx : Nat) (dest' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      m.machine.memory.live.findIdx? (fun (k, _) => k == destId) = some destIdx ∧
      annealMemCopyOp body.localDecls body.layouts ⟨.indirect subMp, srcLay⟩
          ⟨.local 0 d none ident, translateTy dDecl.ty body.layouts⟩ m =
        .ok () { m with machine := inplaceMachine m.machine destIdx destId la_d.kind dest' } ∧
      dest'.byteSize = (translateTy dDecl.ty body.layouts).layout.size ∧
      dest'.align = la_d.allocation.align ∧
      ArraySliceRel elemKind cnt body.layouts sub Miri.ABI.Size.ZERO dest' ∧
      LiveAllocsNodup (inplaceMachine m.machine destIdx destId la_d.kind dest') ∧
      (destId, ⟨la_d.kind, dest'⟩) ∈
        (inplaceMachine m.machine destIdx destId la_d.kind dest').memory.live.toList ∧
      (∀ a la', a ≠ destId → (a, la') ∈ m.machine.memory.live.toList →
        (a, la') ∈ (inplaceMachine m.machine destIdx destId la_d.kind dest').memory.live.toList) :=
  annealMemCopyOp_inplaceArray hframes hlt hwf_d hval hnodup hne hprov hlive hbase hsrcOff hslice
    hprov_d hlive_d hbase_d hptr_d hsz_d hal_d hslice_d_old srcLay ident

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {d arrIdx : Local} {isMove : Bool}
    {fromIdx toIdx : Nat} {fromEnd : Bool} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨d, .nil⟩ (.use (subsliceReadOperand isMove arrIdx fromIdx toIdx fromEnd)),
            span⟩)
    {dDecl arrDecl : MirAst.LocalDecl} {elemKind : RigidTy} {count : Nat}
    (hdecl_d : get? body.localDecls d = some dDecl)
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf_arr : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hwf_d : WellTypedArrayTy body.layouts dDecl.ty elemKind
      (subsliceEnd count toIdx fromEnd - fromIdx))
    {elems : List Value}
    (hinit_arr : get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)))
    (hin : SubsliceInBounds count fromIdx toIdx fromEnd) :
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    (get? s.frame.locals d = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ (oldElems : List Value) (mp_d : Miri.Interpreter.MemPlace AnnealProv)
      (destId : Miri.Memory.AllocId) (tag_d : Miri.Memory.BorTag) (base_d : UInt64)
      (la_d : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      d ≠ arrIdx →
      get? s.frame.locals d = some (.init (.aggregate 0 oldElems)) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[d]? = some ⟨.live (.indirect mp_d), c⟩) →
      mp_d.ptr.provenance = some (.concrete destId tag_d) →
      (destId, la_d) ∈ m.machine.memory.live.toList →
      m.machine.lookupBaseAddr destId = some base_d →
      mp_d.ptr.offset = Miri.ABI.Size.ofBytes base_d →
      la_d.allocation.byteSize = (translateTy dDecl.ty body.layouts).layout.size →
      la_d.allocation.align.pow2 ≤ 29 →
      MemPlaceRel m.machine dDecl.ty body.layouts (some (.aggregate 0 oldElems)) mp_d →
      ∃ (s' : MachineState) (m' : AnnealStepState),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals d = some (.init (.aggregate 0 ((elems.drop fromIdx).take cnt))) ∧
        get? s'.frame.locals arrIdx = some (.init (.aggregate 0 elems)) ∧
        MemPlaceRel m'.machine dDecl.ty body.layouts
          (some (.aggregate 0 ((elems.drop fromIdx).take cnt))) mp_d ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_subslice_assign_overwrite_simulation hstate hnodup hphase hbb hstmt hdecl_d hdecl_arr
    hwf_arr hwf_d hinit_arr hin

example
    {mach : AnnealMachine}
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (locals : List LocalSlot)
    {layouts : LayoutTable} {arrTy : Ty} {elemKind : RigidTy} {count : Nat}
    {elems : List Value} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hwf : WellTypedArrayTy layouts arrTy elemKind count)
    (hnodup : LiveAllocsNodup mach)
    (hmp : MemPlaceRel mach arrTy layouts (some (.aggregate 0 elems)) mp)
    (hovf : mp.ptr.offset.bytes.toNat + (translateTy arrTy layouts).layout.size.bytes.toNat < 2 ^ 64)
    {f1 t1 : Nat} {fe1 : Bool}
    (hin1 : SubsliceInBounds count f1 t1 fe1)
    (f2 t2 : Nat) (fe2 : Bool) :
    let cx := annealSubsliceProjectionCx frame layouts mach
    let arrLay := translateTy arrTy layouts
    let es := (translateTy { kind := elemKind, layoutIdx := 0 } layouts).layout.size
    let cnt1 := subsliceEnd count t1 fe1 - f1
    let sub1 := (elems.drop f1).take cnt1
    let cnt2 := subsliceEnd cnt1 t2 fe2 - f2
    let sub2 := (sub1.drop f2).take cnt2
    (SubsliceInBounds cnt1 f2 t2 fe2 →
      readProjectedValue locals (.aggregate 0 elems)
        [.subslice f1 t1 fe1, .subslice f2 t2 fe2] = .ok (.aggregate 0 sub2) ∧
      annealProjectList cx ⟨.indirect mp, arrLay⟩
        [.Subslice f1 t1 fe1, .Subslice f2 t2 fe2] =
        .ok ⟨.indirect { mp with
                ptr := { mp.ptr with
                  offset := Miri.ABI.Size.ofBytes
                    (mp.ptr.offset.bytes + es.bytes * UInt64.ofNat (f1 + f2)) },
                metadata := .none },
             { ty := arrLay.ty,
               layout := { arrLay.layout with
                 fields := .Array es (UInt64.ofNat cnt2),
                 size := Miri.ABI.Size.ofBytes (es.bytes * UInt64.ofNat cnt2) } }⟩ ∧
      ∃ (allocId : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag) (baseAddr : UInt64)
        (relOffset : Miri.ABI.Size)
        (localAlloc : Miri.Memory.LocalAllocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind),
        mp.ptr.provenance = some (.concrete allocId tag) ∧
        (allocId, localAlloc) ∈ mach.memory.live.toList ∧
        mach.lookupBaseAddr allocId = some baseAddr ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (baseAddr + relOffset.bytes) ∧
        ArraySliceRel elemKind cnt2 layouts sub2
          (Miri.ABI.Size.ofBytes
            (relOffset.bytes + UInt64.ofNat ((f1 + f2) * es.bytes.toNat)))
          localAlloc.allocation) ∧
    (fe2 = true → cnt1 < f2 + t2 → f2 + t2 < 2 ^ 64 →
      readProjectedValue locals (.aggregate 0 elems)
        [.subslice f1 t1 fe1, .subslice f2 t2 fe2] = .ub ∧
      ∃ msg, (annealProjectList cx ⟨.indirect mp, arrLay⟩
        [.Subslice f1 t1 fe1, .Subslice f2 t2 fe2]).mapError annealLiftProjectionError =
          .error (.undefinedBehavior msg)) :=
  evalProjection_nested_subslice_simulation frame locals hwf hnodup hmp hovf hin1 f2 t2 fe2

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {arrIdx : Local} {fromIdx toIdx off minLen : Nat} {fromEnd : Bool}
    {c : ConstOperand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨arrIdx, [.subslice fromIdx toIdx fromEnd, .constantIndex off minLen false]⟩
        (.use (.constant c)), span⟩)
    {arrDecl : MirAst.LocalDecl} {elemKind : RigidTy} {count : Nat}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    {sc : MirAst.ScalarInt}
    (hcty : c.ty = { kind := elemKind, layoutIdx := 0 })
    (hval : c.val = .scalar (.int sc))
    (hsz_c : ValidScalarBytes sc.sizeBytes)
    (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (helemsz : (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size =
      translateSizeBytes sc.sizeBytes)
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    let cnt := subsliceEnd count toIdx fromEnd - fromIdx
    ((get? s.frame.locals arrIdx = some .dead ∨
        (get? s.frame.locals arrIdx = some .uninit ∧
          (0 < count ∨ ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf arrIdx))) →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ elems, get? s.frame.locals arrIdx = some (.init (.aggregate 0 elems)) →
      SubsliceInBounds count fromIdx toIdx fromEnd →
      off < minLen → minLen ≤ cnt →
      (∀ mp, (∃ tf c_l, m.stack.frames = #[tf] ∧ tf.locals[arrIdx]? = some ⟨.live (.indirect mp), c_l⟩) →
        mp.ptr.offset.bytes.toNat + (translateTy arrDecl.ty body.layouts).layout.size.bytes.toNat < 2 ^ 64) →
      ∃ (s' : MachineState) (m' : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals arrIdx =
          some (.init (.aggregate 0 (elems.set (fromIdx + off) (.scalar sc)))) ∧
        MemPlaceRel m'.machine arrDecl.ty body.layouts
          (some (.aggregate 0 (elems.set (fromIdx + off) (.scalar sc)))) mp ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_subslice_elem_write_simulation hstate hnodup hphase hbb hstmt hdecl_arr hwf hcty hval
    hsz_c hcan helemsz hbool hchar

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {arrIdx u : Local} {j : Nat} {fty : Ty} {isMove : Bool}
    {count : Nat} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨arrIdx, .nil⟩ (.repeat (unionFieldReadOperand isMove u j fty) count), span⟩)
    {arrDecl uDecl : MirAst.LocalDecl} {elemKind : RigidTy}
    (hdecl_arr : get? body.localDecls arrIdx = some arrDecl)
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hprim : IsPrimScalarTy fty) {w : Nat} (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n f : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hf : f < n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u =
      some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u)
    (hf0_eq : f0Ty = { kind := elemKind, layoutIdx := 0 })
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    (hfl : ∃ fl, unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) f = some fl ∧
      fl.layout.size = (translateTy f0Ty body.layouts).layout.size) :
    (j ≠ f → sc.sizeBytes < w → w ≤ S →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (j = f → fty = f0Ty → get? s.frame.locals arrIdx = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (j = f → fty = f0Ty →
      get? s.frame.locals arrIdx = some .uninit →
      (∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf arrIdx) →
      CanReserveAllocId m.machine.memory →
      ∃ (s' : MachineState) (m' : AnnealStepState) (mp_arr : Miri.Interpreter.MemPlace AnnealProv)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals arrIdx =
          some (.init (.aggregate 0 (List.replicate count (.scalar sc)))) ∧
        get? s'.frame.locals u =
          some (.init (.aggregate 0 (unionSlotFields n f (.scalar sc)))) ∧
        m'.stack.frames = #[tf'] ∧
        MemPlaceRel m'.machine arrDecl.ty body.layouts
          (some (.aggregate 0 (List.replicate count (.scalar sc)))) mp_arr ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp_u ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 1 (m', .ok true)) :=
  step_repeat_union_field_simulation hstate hnodup hphase hbb hstmt hdecl_arr hdecl_u hwf hprim hw
    hsz hwt hfields hf hj hu_slot hu_mls hmem hf0_eq hbool hchar hfl

example
    {mach : AnnealMachine} {decl : MirAst.LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : UnionLocalRel mach decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value :=
  UnionLocalRel.allocLive h

example
    {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {uTy : Ty} {layouts : LayoutTable} {S : Nat} {f0Ty : Ty} {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (h : UnionMemRel mach uTy layouts S f0Ty sc mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    UnionMemRel { mach with memory := { mach.memory with
        live := mach.memory.live.filter (fun entry => entry.1 != id) } }
      uTy layouts S f0Ty sc mp :=
  UnionMemRel.of_filter_live h hne

example
    {mach : AnnealMachine} {decl : MirAst.LocalDecl} {layouts : LayoutTable}
    {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    (h : UnionLocalRel mach decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    UnionLocalRel { mach with memory := deallocLocalMemory mach.memory v } decl layouts slot mls :=
  UnionLocalRel.of_dealloc h hdisj

example
    {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM2_4 body mach af mf) (hdisj : MemoryAllocDisjoint mf)
    {idx : Nat} {decl : MirAst.LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : UnionLocalRel
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      decl body.layouts newSlot { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM2_4 body
      { mach with memory := deallocLocalMemory mach.memory (mf.locals[idx]'hlt_mf).value }
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } :=
  FrameRelLM2_4.update_local_dealloc hrel hdisj hdecl newSlot newVal hnew

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl) :
    StepRelLM2_4 body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) :=
  step_storageLive_LM2_4_simulation hstate hnodup hphase hbb hstmt hdecl

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne : loc ≠ 0) :
    StepRelLM2_4 body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesNodup
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
    StepPreservesHighWater m 0
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) :=
  step_storageDead_LM2_4_simulation hstate hnodup hphase hbb hstmt hdecl hne

example :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ : AnnealStepState)
      (mp₁ mp₄ : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          (Witness.lm24A2InitMiri 0) = (m₁, .ok true) ∧
      UnionMemRel m₁.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U8Ty ⟨5, 1⟩ mp₁ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          m₁ = (m₂, .ok true) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          m₂ = (m₃, .ok true) ∧
      UnionMemRel m₃.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U8Ty ⟨5, 1⟩ mp₄ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          m₃ = (m₄, .ok true) ∧
      UnionMemRel m₄.machine Witness.lm24UTy Witness.lm24Layouts 4 Witness.lm24U32Ty
        ⟨0x05060708, 4⟩ mp₄ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          m₄ = (m₅, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 0 5 [.uninit, .dead, .uninit, .uninit, Witness.lm24UU32Slot2])
        m₅ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          m₅ = (m₆, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 0 6 [.uninit, .uninit, .uninit, .uninit, Witness.lm24UU32Slot2])
        m₆ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          m₆ = (m₇, .ok true) ∧
      StepRelLM2_4 Witness.lm24A2UnionBody m₇
        (stepMirFn Witness.lm24A2UnionBody
          (Witness.lm24A2AnnealState 0 7 [.uninit, .dead, .uninit, .uninit, Witness.lm24UU32Slot2]))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts)
          () m₇) :=
  Witness.lm24_overwrite_and_lifecycle_steps

example :
    ∃ (m₁ m₂ : AnnealStepState) (s₂ : MachineState),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          (Witness.lm24A2InitMiri 1) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 1 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 1 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) =
        .step s₂ ∧
      get? s₂.frame.locals 1 = some Witness.lm24USlot ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts)
          () m₁ =
        (m₂, .error (.undefinedBehavior "whole-value copy between overlapping ranges")) :=
  Witness.lm24_union_self_copy_overlap_divergence

example :
    stepMirFn Witness.lm24A2UnionBody (Witness.lm24A2InitAnneal 2) = .fail .ub ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp_w : Miri.Interpreter.MemPlace AnnealProv) (id : Miri.Memory.AllocId)
      (la_w : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          Witness.lm24A2UninitIndirectMiri = (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c, tf'.locals[4]? = some ⟨.live (.indirect mp_w), c⟩) ∧
      mp_w.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some id ∧
      (id, la_w) ∈ m'.machine.memory.live.toList ∧
      la_w.allocation.initializationMask =
        Miri.Memory.InitMask.new (translateSizeBytes 4) false :=
  Witness.lm24_union_copy_indirect_uninit_divergence

example :
    ∃ (m₁ m₂ : AnnealStepState) (s₂ : MachineState) (msc : Miri.Memory.ScalarInt)
      (allocId : Miri.Memory.AllocId)
      (A' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          (Witness.lm24A2InitMiri 3) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 3 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit])
        m₁ ∧
      stepMirFn Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 3 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) =
        .step s₂ ∧
      get? s₂.frame.locals 1 = some (.init (.aggregate 0 [.scalar ⟨0x77, 1⟩, .unit])) ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts)
          () m₁ = (m₂, .ok true) ∧
      ScalarRel ⟨0x77, 1⟩ msc ∧
      (∃ kind, (allocId, ⟨kind, A'⟩) ∈ m₂.machine.memory.live.toList) ∧
      IsUnionPrefixMask 4 4 A'.initializationMask ∧
      A'.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes 1)) false =
          .ok (.fromScalarInt msc) ∧
      (unionAllocRaw A').extract 1 4 = #[0x03, 0x02, 0x01] :=
  Witness.lm24_union_agg_smaller_overwrite_divergence

example :
    ∃ (m₁ m₂ m₁_ub : AnnealStepState) (s₂ : MachineState)
      (mp_arr : Miri.Interpreter.MemPlace AnnealProv),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          (Witness.lm24A2InitMiri 4) = (m₁, .ok true) ∧
      stepMirFn Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 4 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) =
        .step s₂ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts)
          () m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2UnionBody s₂ m₂ ∧
      get? s₂.frame.locals 3 =
        some (.init (.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩])) ∧
      MemPlaceRel m₂.machine Witness.lm24U8Arr3Ty Witness.lm24Layouts
        (some (.aggregate 0 [.scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩, .scalar ⟨5, 1⟩])) mp_arr ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts) ()
          (Witness.lm24A2InitMiri 5) = (m₁_ub, .ok true) ∧
      stepMirFn Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 5 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) =
        .fail .ub ∧
      StepRelLM2_4 Witness.lm24A2UnionBody m₁_ub
        (stepMirFn Witness.lm24A2UnionBody
          (Witness.lm24A2AnnealState 5 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls Witness.lm24A2UnionBody.layouts)
          () m₁_ub) :=
  Witness.lm24_repeat_union_field_steps

example :
    let cx := annealSubsliceProjectionCx (Witness.lm21InitMiriFrame 0) emptyLayoutTable
      (Witness.witnessMachineOf Witness.lm21ArrAlloc)
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect Witness.witnessMemPlace, translateTy Witness.lm21U16Arr3Ty emptyLayoutTable⟩
    readProjectedValue [] (.aggregate 0 Witness.lm21ArrElems)
      [.subslice 0 3 false, .subslice 1 2 false] =
        .ok (.aggregate 0 [.scalar ⟨0x0304, 2⟩]) ∧
    (∃ op, annealProjectList cx base [.Subslice 0 3 false, .Subslice 1 2 false] = .ok op ∧
      ∃ mp, op.op = .indirect mp ∧
        mp.ptr.offset = Miri.ABI.Size.ofBytes (Witness.witnessMemPlace.ptr.offset.bytes + 2)) ∧
    readProjectedValue [] (.aggregate 0 Witness.lm21ArrElems)
      [.subslice 0 3 false, .subslice 2 2 true] = .ub ∧
    ∃ msg, (annealProjectList cx base
      [.Subslice 0 3 false, .Subslice 2 2 true]).mapError annealLiftProjectionError =
        .error (.undefinedBehavior msg) :=
  Witness.lm24_nested_subslice_witness

example :
    ∃ (s_ovw s_elem : MachineState) (m_ovw m_elem : AnnealStepState)
      (mp₁' : Miri.Interpreter.MemPlace AnnealProv),
      stepMirFn Witness.lm24A2SubsliceBody
        (Witness.lm24A2SubsliceAnneal 1 (.init (.aggregate 0 Witness.lm21ArrElems))
          (.init (.aggregate 0 Witness.lm24Arr2Elems))) = .step s_ovw ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2SubsliceBody.localDecls
            Witness.lm24A2SubsliceBody.layouts) ()
          (Witness.lm24A2TwoArrMiri 1) = (m_ovw, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2SubsliceBody s_ovw m_ovw ∧
      get? s_ovw.frame.locals 2 =
        some (.init (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩])) ∧
      MemPlaceRel m_ovw.machine Witness.lm24U16Arr2Ty emptyLayoutTable
        (some (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩])) Witness.lm24Arr2MemPlace ∧
      StepRelLM2_4 Witness.lm24A2SubsliceBody Witness.lm24A2DeadDstMiri
        (stepMirFn Witness.lm24A2SubsliceBody
          (Witness.lm24A2SubsliceAnneal 1 (.init (.aggregate 0 Witness.lm21ArrElems)) .dead))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2SubsliceBody.localDecls
            Witness.lm24A2SubsliceBody.layouts) ()
          Witness.lm24A2DeadDstMiri) ∧
      stepMirFn Witness.lm24A2SubsliceBody
        (Witness.lm24A2SubsliceAnneal 2 (.init (.aggregate 0 Witness.lm21ArrElems)) .uninit) =
        .step s_elem ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2SubsliceBody.localDecls
            Witness.lm24A2SubsliceBody.layouts) ()
          (Witness.lm24A2SubsliceMiri 2) = (m_elem, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2SubsliceBody s_elem m_elem ∧
      get? s_elem.frame.locals 1 =
        some (.init (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0099, 2⟩, .scalar ⟨0x0506, 2⟩])) ∧
      MemPlaceRel m_elem.machine Witness.lm21U16Arr3Ty emptyLayoutTable
        (some (.aggregate 0 [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0099, 2⟩, .scalar ⟨0x0506, 2⟩]))
        mp₁' ∧
      StepRelLM2_4 Witness.lm24A2SubsliceBody (Witness.lm24A2SubsliceUninitMiri 2)
        (stepMirFn Witness.lm24A2SubsliceBody (Witness.lm24A2SubsliceAnneal 2 .uninit .uninit))
        (Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2SubsliceBody.localDecls
            Witness.lm24A2SubsliceBody.layouts) ()
          (Witness.lm24A2SubsliceUninitMiri 2)) :=
  Witness.lm24_subslice_overwrite_and_elem_write_witness

example :
    ∃ (m₁ m₂ : AnnealStepState),
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls
            Witness.lm24A2UnionBody.layouts) ()
          (Witness.lm24A2InitMiri 6) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 6 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2UnionBody.localDecls
            Witness.lm24A2UnionBody.layouts) () m₁ = (m₂, .ok true) ∧
      StateRelLM2_4 Witness.lm24A2UnionBody
        (Witness.lm24A2AnnealState 6 2 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₂ :=
  Witness.lm24_union_self_move_steps

end LM2_4Pins

section LM2_3Pins

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

example :
    ∀ {localDecls : List MirAst.LocalDecl} {layouts : LayoutTable}
      {state : AnnealStepState},
      (∀ frame, state.stack.currentFrame? = some frame →
        BodyFreeOfLM2_3 localDecls layouts frame.body) →
      ∀ (choice : Unit),
        Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 localDecls layouts) choice state =
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_2 localDecls layouts) choice state :=
  @step_LM2_3_eq_of_bodyFree

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRel body s m →
      (∀ ty tb vs, env ty = some (tb, vs) →
        ValidEnumLayout ty body.layouts tb vs) →
      (∀ idx decl slot mls,
        get? body.localDecls idx = some decl →
        (env decl.ty).isSome = true →
        get? s.frame.locals idx = some slot →
        (∀ tf, m.stack.frames = #[tf] → tf.locals[idx]? = some mls →
          slot = .dead ∨
            (slot = .uninit ∧ mls.value = .live (.immediate .uninit)))) →
      AllocIdSupplyValid allocBudget m.machine.memory →
      StateRelLM2_3 body env allocBudget s m :=
  @StateRel.toLM2_3

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env (allocBudget + 1) s m →
      (∀ ty tb vs, env ty = some (tb, vs) →
        ValidEnumLayout ty body.layouts tb vs) →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx : Local} {dstDecl : MirAst.LocalDecl}
        {adtDefId : String} {variantIdx : Nat} {ops : List MirAst.Operand}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨dstIdx, .nil⟩
          (.aggregate (.adt adtDefId variantIdx .none) ops) →
        get? body.localDecls dstIdx = some dstDecl →
        env dstDecl.ty = some (tagBytes, variants) →
        (hv : variantIdx < variants.length) →
        (hops_len : ops.length = (variants[variantIdx]'hv).length) →
        (∀ topFrame (i : Nat) (hi : i < ops.length),
          m.stack.frames = #[topFrame] →
          WellTypedEnumScalarOp body topFrame (ops[i]'hi)
            ((variants[variantIdx]'hv)[i]'(by omega)).ty) →
        let mRes := Miri.Interpreter.Step.step
          (annealStepHooksLM2_3 body.localDecls body.layouts) () m
        StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
        ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
          (get? s.frame.locals dstIdx = some .uninit →
            ∀ b, tagBytes ≤ b →
              b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat →
              (∀ j (hj : j < (variants[variantIdx]'hv).length),
                b < ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat ∨
                  ((variants[variantIdx]'hv)[j]'hj).offset.bytes.toNat +
                    ((variants[variantIdx]'hv)[j]'hj).fieldLayout.size.bytes.toNat ≤ b) →
              EnumLocalByteUninit mRes.1 dstIdx b) ∧
          (∀ localId b, localId ≠ dstIdx →
            EnumLocalByteUninit m localId b →
            EnumLocalByteUninit mRes.1 localId b) ∧
          (∀ j, j ≠ dstIdx →
            IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j)) :=
  @evalRvalue_aggregate_enum_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx : Local} {dstDecl : MirAst.LocalDecl} {variantIdx : Nat}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .setDiscriminant ⟨dstIdx, .nil⟩ variantIdx →
        get? body.localDecls dstIdx = some dstDecl →
        env dstDecl.ty = some (tagBytes, variants) →
        (hv_lt : variantIdx < variants.length) →
        get? s.frame.locals dstIdx ≠ some .uninit →
        (∀ v_act (hv_act : v_act < variants.length) fieldVals,
          get? s.frame.locals dstIdx = some (.init (.aggregate v_act fieldVals)) →
          ∀ i (hi : i < (variants[variantIdx]'hv_lt).length),
            (∃ (hi_act : i < (variants[v_act]'hv_act).length),
              (variants[variantIdx]'hv_lt)[i]'hi = (variants[v_act]'hv_act)[i]'hi_act) ∨
            (get? fieldVals i = none ∧
              ∃ b,
                ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat ≤ b ∧
                b < ((variants[variantIdx]'hv_lt)[i]'hi).offset.bytes.toNat +
                  ((variants[variantIdx]'hv_lt)[i]'hi).fieldLayout.size.bytes.toNat ∧
                EnumLocalByteUninit m dstIdx b)) →
        StepRelLM2_3 body env allocBudget m
          (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m) ∧
        (∀ enumId b,
          (enumId ≠ dstIdx ∨
            (tagBytes ≤ b ∧
              b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)) →
          EnumLocalByteUninit m enumId b →
          EnumLocalByteUninit
            (Miri.Interpreter.Step.step
              (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
            enumId b) ∧
        (∀ j,
          IsImmediateStepLocal m j →
          IsImmediateStepLocal
            (Miri.Interpreter.Step.step
              (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
            j) :=
  @step_setDiscriminant_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env (allocBudget + 1) s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx : Local} {dstDecl : MirAst.LocalDecl} {variantIdx : Nat}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .setDiscriminant ⟨dstIdx, .nil⟩ variantIdx →
        get? body.localDecls dstIdx = some dstDecl →
        env dstDecl.ty = some (tagBytes, variants) →
        variantIdx < variants.length →
        get? s.frame.locals dstIdx = some .uninit →
        stepMirFn body s = .fail .ub ∧
        ∃ m', Miri.Interpreter.Step.step
          (annealStepHooksLM2_3 body.localDecls body.layouts) () m = (m', .ok true) :=
  @step_setDiscriminant_uninit_divergence

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx srcIdx : Local} {dstDecl srcDecl : MirAst.LocalDecl}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨dstIdx, .nil⟩ (.discriminant ⟨srcIdx, .nil⟩) →
        get? body.localDecls srcIdx = some srcDecl →
        get? body.localDecls dstIdx = some dstDecl →
        env srcDecl.ty = some (tagBytes, variants) →
        IsEnumDiscrDestTy dstDecl.ty →
        (∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) →
        StepRelLM2_3 body env allocBudget m
          (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m) ∧
        (∀ enumId b, enumId ≠ dstIdx →
          EnumLocalByteUninit m enumId b →
          EnumLocalByteUninit
            (Miri.Interpreter.Step.step
              (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
            enumId b) ∧
        (∀ j,
          IsImmediateStepLocal m j →
          IsImmediateStepLocal
            (Miri.Interpreter.Step.step
              (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
            j) :=
  @evalRvalue_discriminant_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx srcIdx : Local} {dstDecl srcDecl : MirAst.LocalDecl}
        {isMove : Bool} {vName : Option String} {variantIdx fieldIdx : Nat}
        {fieldTy : Ty} {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨dstIdx, .nil⟩
          (.use (if isMove then
            .move ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
          else
            .copy ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩)) →
        get? body.localDecls srcIdx = some srcDecl →
        get? body.localDecls dstIdx = some dstDecl →
        env srcDecl.ty = some (tagBytes, variants) →
        (hv_lt : variantIdx < variants.length) →
        (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length) →
        fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty →
        dstDecl.ty = fieldTy →
        (∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) →
        (∀ v_act fieldVals,
          get? s.frame.locals srcIdx = some (.init (.aggregate v_act fieldVals)) →
          variantIdx ≠ v_act →
          ∃ b,
            ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat ≤ b ∧
            b < ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat +
              ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).fieldLayout.size.bytes.toNat ∧
            EnumLocalByteUninit m srcIdx b) →
        StepRelLM2_3 body env allocBudget m
          (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m) ∧
        (∀ enumId b, enumId ≠ dstIdx →
          EnumLocalByteUninit m enumId b →
          EnumLocalByteUninit
            (Miri.Interpreter.Step.step
              (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
            enumId b) ∧
        (∀ j,
          IsImmediateStepLocal m j →
          IsImmediateStepLocal
            (Miri.Interpreter.Step.step
              (annealStepHooksLM2_3 body.localDecls body.layouts) () m).1
            j) :=
  @evalProjection_downcast_field_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx srcIdx : Local} {dstDecl srcDecl : MirAst.LocalDecl}
        {isMove : Bool} {vName : Option String} {variantIdx fieldIdx : Nat}
        {fieldTy : Ty} {tagBytes : Nat} {variants : List (List StructFieldDesc)}
        {v_act j : Nat} {fieldVals : List Value},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨dstIdx, .nil⟩
          (.use (if isMove then
            .move ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
          else
            .copy ⟨srcIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩)) →
        get? body.localDecls srcIdx = some srcDecl →
        get? body.localDecls dstIdx = some dstDecl →
        env srcDecl.ty = some (tagBytes, variants) →
        (hv_lt : variantIdx < variants.length) →
        (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length) →
        fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty →
        dstDecl.ty = fieldTy →
        (∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx) →
        get? s.frame.locals dstIdx ≠ some .dead →
        get? s.frame.locals srcIdx = some (.init (.aggregate v_act fieldVals)) →
        variantIdx ≠ v_act →
        (hv_act : v_act < variants.length) →
        (hj : j < (variants[v_act]'hv_act).length) →
        j < fieldVals.length →
        ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt) = ((variants[v_act]'hv_act)[j]'hj) →
        stepMirFn body s = .fail .ub ∧
        ∃ (sc : MirAst.ScalarInt) (m' : AnnealStepState),
          get? fieldVals j = some (.scalar sc) ∧
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m = (m', .ok true) ∧
          StateRelLM2_3 body env allocBudget
            (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory) m' ∧
          (∀ enumId b, enumId ≠ dstIdx →
            EnumLocalByteUninit m enumId b → EnumLocalByteUninit m' enumId b) ∧
          (∀ k, IsImmediateStepLocal m k → IsImmediateStepLocal m' k) :=
  @evalProjection_downcast_field_initialized_divergence

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ ty tb vs, env ty = some (tb, vs) →
        ValidEnumLayout ty body.layouts tb vs) →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = none →
        s.frame.stmtIdx = length bb.statements →
        ∀ {discr : MirAst.Operand} {targets : SwitchTargets} {ty : Ty},
          bb.terminator.kind = .switchInt discr targets →
          (ty.kind = .bool ∨ (∃ k, ty.kind = .int k) ∨ (∃ k, ty.kind = .uint k)) →
          (∀ topFrame, m.stack.frames = #[topFrame] →
            WellTypedEnumScalarOp body topFrame discr ty) →
          SwitchCasesFit ty targets →
          let mRes := Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m
          StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
          ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
            (∀ localId b, EnumLocalByteUninit m localId b →
              EnumLocalByteUninit mRes.1 localId b) ∧
            (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j)) :=
  @enum_match_switchInt_simulation

example :
    ∀ (lay : Miri.ABI.LayoutData) (tag : Layout.ScalarLayout) (tagField : Nat)
      (shapes : List Layout.FieldsShape),
      lay.variants = translateVariantsShape (.multiple tag tagField shapes) →
      ∀ {v : Nat}, v < shapes.length → lay.isVariantUninhabited v = false :=
  @isVariantUninhabited_translateVariantsShape_multiple

example :
    ValidEnumLayout Witness.lm23EnumTy Witness.lm23Layouts 4 Witness.lm23Variants :=
  Witness.lm23_validEnumLayout

example :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : AnnealStepState)
      (imm0 : Miri.Interpreter.Immediate AnnealProv),
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 0) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23PipeS1 m₁ ∧
      EnumLocalByteUninit m₁ 1 8 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23PipeS2 m₂ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23PipeS3 m₃ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23PipeS4 m₄ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23PipeS5 m₅ ∧
      EnumLocalByteUninit m₅ 1 8 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23PipeS6 m₆ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23PipeS7 m₇ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₇ = (m₈, .ok true) ∧
      annealControlHooks.returnOperand () m₇ = (m₇, .ok (.immediate imm0)) ∧
      ImmediateRel Witness.lm23U64Ty Witness.lm23Layouts (.scalar ⟨99, 8⟩) imm0 ∧
      m₈.stack.frames = #[] :=
  Witness.wit_lm2_3_full_pipeline_trace

example :
    ∃ (m₁ m₂ : AnnealStepState) (msg : String),
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 2) =
        .step Witness.lm23Bb2S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 2) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb2S1 m₁ ∧
      EnumLocalByteUninit m₁ 1 8 ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb2S1 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ =
        (m₂, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm2_3_inactive_variant_downcast_ub

example :
    ∃ (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 3) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb3S2 m₂ ∧
      EnumLocalByteUninit m₂ 1 8 ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb3S2 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ =
        (m₃, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm2_3_setDiscriminant_then_inactive_ub

example :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ : AnnealStepState)
      (imm0 : Miri.Interpreter.Immediate AnnealProv),
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 4) = (m₁, .ok true) ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb5S0 m₃ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb6S0 m₄ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₄ = (m₅, .ok true) ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₅ = (m₆, .ok true) ∧
      annealControlHooks.returnOperand () m₅ = (m₅, .ok (.immediate imm0)) ∧
      ImmediateRel Witness.lm23U64Ty Witness.lm23Layouts (.scalar ⟨88, 8⟩) imm0 :=
  Witness.wit_lm2_3_switch_otherwise_and_goto_trace

example :
    (stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 7) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step Witness.lm23Hooks ()
        (Witness.lm23InitMiri 7)).2 = .error (.undefinedBehavior msg)) ∧
    (stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 9) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step Witness.lm23Hooks ()
        (Witness.lm23InitMiri 9)).2 = .error (.undefinedBehavior msg)) ∧
    (stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 10) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step Witness.lm23Hooks ()
        (Witness.lm23InitMiri 10)).2 = .error (.undefinedBehavior msg)) ∧
    (stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 11) = .fail .ub ∧
      ∃ msg, (Miri.Interpreter.Step.step Witness.lm23Hooks ()
        (Witness.lm23InitMiri 11)).2 = .error (.undefinedBehavior msg)) :=
  Witness.wit_lm2_3_uninit_and_dead_ub

example :
    stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 8) = .fail .ub ∧
    ∃ m', Miri.Interpreter.Step.step Witness.lm23Hooks ()
      (Witness.lm23InitMiri 8) = (m', .ok true) :=
  Witness.wit_lm2_3_setDiscriminant_uninit_divergence

example :
    ∃ (m₁ m₂ : AnnealStepState),
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 12) =
        .step Witness.lm23Bb12S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
        (Witness.lm23InitMiri 12) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb12S1 m₁ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb12S1 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb12S2 m₂ :=
  Witness.wit_lm2_3_inactive_variant_initialized_divergence

example :
    ∃ (m₁ m₂ m₃ : AnnealStepState),
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 13) =
        .step Witness.lm23Bb13S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
        (Witness.lm23InitMiri 13) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb13S1 m₁ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb13S1 =
        .step Witness.lm23Bb13S2 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb13S2 m₂ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb13S2 =
        .step Witness.lm23Bb13S3 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb13S3 m₃ :=
  Witness.wit_lm2_3_prefix_setDiscriminant_read

example :
    ∃ (m₁ m₂ m₃ m₄ : AnnealStepState) (msg : String),
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 14) =
        .step Witness.lm23Bb14S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
        (Witness.lm23InitMiri 14) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb14S1 m₁ ∧
      EnumLocalByteUninit m₁ 1 8 ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb14S1 =
        .step Witness.lm23Bb14S2 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb14S2 m₂ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb14S2 =
        .step Witness.lm23Bb14S3 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb14S3 m₃ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb14S3 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₃ =
        (m₄, .error (.undefinedBehavior msg)) :=
  Witness.wit_lm2_3_upcast_setDiscriminant_read_and_trailing_ub

example (divisor : Nat) :
    BodyFreeOfLM2_3 (Witness.divBody divisor).localDecls
      (Witness.divBody divisor).layouts
      (translateBody (Witness.divBody divisor)) ∧
    Miri.Interpreter.Step.step
        (annealStepHooksLM2_3 (Witness.divBody divisor).localDecls
          (Witness.divBody divisor).layouts) () (Witness.miriInit divisor) =
      Miri.Interpreter.Step.step
        (annealStepHooksLM2_2 (Witness.divBody divisor).localDecls
          (Witness.divBody divisor).layouts) () (Witness.miriInit divisor) :=
  Witness.wit_lm2_3_bodyFree_divBody divisor

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩ →
        get? body.localDecls loc = some decl →
        let mRes :=
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m
        StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
        IsImmediateStepLocal mRes.1 loc ∧
        (∀ enumId b, enumId ≠ loc →
          EnumLocalByteUninit m enumId b → EnumLocalByteUninit mRes.1 enumId b) ∧
        (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j) :=
  @step_storageLive_LM2_3_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData} {loc : Local} {decl : MirAst.LocalDecl} {span : String},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩ →
        get? body.localDecls loc = some decl →
        loc ≠ 0 →
        let mRes :=
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m
        StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
        (∀ enumId b, enumId ≠ loc →
          EnumLocalByteUninit m enumId b → EnumLocalByteUninit mRes.1 enumId b) ∧
        (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j) :=
  @step_storageDead_LM2_3_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env (allocBudget + 1) s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) →
        ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx srcIdx : Local} {dstDecl srcDecl : MirAst.LocalDecl}
        {isMove : Bool} {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨dstIdx, .nil⟩
          (.use (if isMove then .move ⟨srcIdx, .nil⟩ else .copy ⟨srcIdx, .nil⟩)) →
        srcIdx ≠ dstIdx →
        get? body.localDecls srcIdx = some srcDecl →
        get? body.localDecls dstIdx = some dstDecl →
        env srcDecl.ty = some (tagBytes, variants) →
        dstDecl.ty = srcDecl.ty →
        (get? s.frame.locals srcIdx = some .uninit →
          IsImmediateStepLocal m srcIdx) →
        let mRes :=
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m
        StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
        ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
          (isMove = true → IsImmediateStepLocal mRes.1 srcIdx) ∧
          (∀ b, EnumLocalByteUninit m srcIdx b →
            EnumLocalByteUninit mRes.1 dstIdx b) ∧
          (∀ enumId b, enumId ≠ dstIdx → (isMove = true → enumId ≠ srcIdx) →
            EnumLocalByteUninit m enumId b →
            EnumLocalByteUninit mRes.1 enumId b) ∧
          (∀ j, j ≠ dstIdx → IsImmediateStepLocal m j →
            IsImmediateStepLocal mRes.1 j)) :=
  @step_enum_copy_move_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) →
        ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx : Local} {dstDecl : MirAst.LocalDecl}
        {vName : Option String} {variantIdx fieldIdx : Nat} {fieldTy : Ty}
        {op : MirAst.Operand}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign
          ⟨dstIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
          (.use op) →
        get? body.localDecls dstIdx = some dstDecl →
        env dstDecl.ty = some (tagBytes, variants) →
        (hv_lt : variantIdx < variants.length) →
        (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length) →
        fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty →
        (∀ tf, m.stack.frames = #[tf] →
          WellTypedEnumScalarOp body tf op fieldTy) →
        (get? s.frame.locals dstIdx = some .dead ∨
          ∃ fieldVals,
            get? s.frame.locals dstIdx =
              some (.init (.aggregate variantIdx fieldVals)) ∧
            fieldIdx ≤ fieldVals.length) →
        let mRes :=
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m
        StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
        ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
          (∀ enumId b,
            (enumId ≠ dstIdx ∨
              ((b < ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat ∨
                ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).offset.bytes.toNat +
                  ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).fieldLayout.size.bytes.toNat ≤
                  b) ∧
                b < (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)) →
            EnumLocalByteUninit m enumId b →
            EnumLocalByteUninit mRes.1 enumId b) ∧
          (∀ j, IsImmediateStepLocal m j → IsImmediateStepLocal mRes.1 j)) :=
  @step_downcast_field_write_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) →
        ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx : Local} {dstDecl : MirAst.LocalDecl}
        {vName : Option String} {variantIdx v_act fieldIdx : Nat} {fieldTy : Ty}
        {fieldVals : List Value} {op : MirAst.Operand}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign
          ⟨dstIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
          (.use op) →
        get? body.localDecls dstIdx = some dstDecl →
        env dstDecl.ty = some (tagBytes, variants) →
        (hv_lt : variantIdx < variants.length) →
        (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length) →
        fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty →
        (∀ tf, m.stack.frames = #[tf] →
          WellTypedEnumScalarOp body tf op fieldTy) →
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil ≠ .ub →
        get? s.frame.locals dstIdx = some (.init (.aggregate v_act fieldVals)) →
        variantIdx ≠ v_act →
        stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m',
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
          (m', .ok true) :=
  @step_downcast_field_write_inactive_divergence

example :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : AnnealStepState)
      (imm0 : Miri.Interpreter.Immediate AnnealProv),
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 15) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23Bb15S1 m₁ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23Bb15S2 m₂ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23Bb15S3 m₃ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23Bb15S4 m₄ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb15S5 m₅ ∧
      IsImmediateStepLocal m₅ 1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb15S6 m₆ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb15S7 m₇ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₇ = (m₈, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb15S8 m₈ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₈ = (m₉, .ok true) ∧
      annealControlHooks.returnOperand () m₈ = (m₈, .ok (.immediate imm0)) ∧
      ImmediateRel Witness.lm23U64Ty Witness.lm23Layouts (.scalar ⟨99, 8⟩) imm0 ∧
      m₉.stack.frames = #[] :=
  Witness.wit_lm2_3_upcast_field_write_move_and_storage_lifecycle

example :
    (∃ m₁ msg₁,
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 16) = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () (Witness.lm23InitMiri 16) =
        (m₁, .error (.undefinedBehavior msg₁))) ∧
    (∃ m₂ msg₂,
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 17) = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () (Witness.lm23InitMiri 17) =
        (m₂, .error (.undefinedBehavior msg₂))) ∧
    (∃ m₃ m₄ msg₃,
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 18) =
        .step Witness.lm23Bb18S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () (Witness.lm23InitMiri 18) =
        (m₃, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23Bb18S1 m₃ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb18S1 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₃ =
        (m₄, .error (.undefinedBehavior msg₃))) :=
  Witness.wit_lm2_3_copy_move_and_downcast_write_ub

example :
    ∃ (m₁ m₂ : AnnealStepState),
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 19) =
        .step Witness.lm23Bb19S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () (Witness.lm23InitMiri 19) =
        (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb19S1 m₁ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb19S1 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) :=
  Witness.wit_lm2_3_downcast_write_inactive_divergence

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env (allocBudget + 1) s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) →
        ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx : Local} {dstDecl : MirAst.LocalDecl}
        {vName : Option String} {variantIdx fieldIdx : Nat} {fieldTy : Ty}
        {op : MirAst.Operand}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign
          ⟨dstIdx, [.downcast vName variantIdx, .field fieldIdx fieldTy]⟩
          (.use op) →
        get? body.localDecls dstIdx = some dstDecl →
        env dstDecl.ty = some (tagBytes, variants) →
        (hv_lt : variantIdx < variants.length) →
        (hf_lt : fieldIdx < (variants[variantIdx]'hv_lt).length) →
        fieldTy = ((variants[variantIdx]'hv_lt)[fieldIdx]'hf_lt).ty →
        (∀ tf, m.stack.frames = #[tf] →
          WellTypedEnumScalarOp body tf op fieldTy) →
        evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil ≠ .ub →
        get? s.frame.locals dstIdx = some .uninit →
        stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m',
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
          (m', .ok true) :=
  @step_downcast_field_write_uninit_divergence

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env (allocBudget + 1) s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) →
        ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {idx : Local} {decl : MirAst.LocalDecl}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨idx, .nil⟩ (.use (.move ⟨idx, .nil⟩)) →
        get? body.localDecls idx = some decl →
        env decl.ty = some (tagBytes, variants) →
        (get? s.frame.locals idx = some .uninit →
          IsImmediateStepLocal m idx) →
        let mRes :=
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m
        StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
        ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
          (∀ enumId b,
            EnumLocalByteUninit m enumId b →
            EnumLocalByteUninit mRes.1 enumId b) ∧
          (∀ j, j ≠ idx → IsImmediateStepLocal m j →
            IsImmediateStepLocal mRes.1 j)) :=
  @step_enum_self_move_simulation

example :
    ∃ (m₁ : AnnealStepState),
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 20) = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () (Witness.lm23InitMiri 20) =
        (m₁, .ok true) :=
  Witness.wit_lm2_3_downcast_write_uninit_divergence

example :
    ∃ (m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ : AnnealStepState),
      Miri.Interpreter.Step.step Witness.lm23Hooks () (Witness.lm23InitMiri 21) =
        (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 3 Witness.lm23Bb21S1 m₁ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 3 Witness.lm23Bb21S2 m₂ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 2 Witness.lm23Bb21S3 m₃ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 2 Witness.lm23Bb21S4 m₄ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1 Witness.lm23Bb21S5 m₅ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb21S6 m₆ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb21S7 m₇ ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₇ = (m₈, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0 Witness.lm23Bb21S8 m₈ :=
  Witness.wit_lm2_3_field_overwrite_self_move_and_copy_overwrite

example :
    ∀ {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
      {tagBytes : Nat} {variants : List (List StructFieldDesc)}
      {v_act : Nat} {fieldVals : List Value}
      {mp : Miri.Interpreter.MemPlace AnnealProv}
      {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
      {localAlloc : AnnealLocalAlloc},
      EnumMemRel mach ty layouts tagBytes variants v_act fieldVals mp →
      mp.ptr.provenance = some (.concrete allocId tag) →
      LiveAllocEntry mach.memory.live allocId localAlloc →
      ∃ alloc',
        Miri.Memory.Allocation.copy localAlloc.allocation
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy ty layouts).layout.size)
          Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
          localAlloc.allocation = .error .copyRangesOverlap alloc' :=
  @EnumMemRel.copy_self_overlap_err

example :
    ∀ {mach : AnnealMachine} {ty : Ty} {layouts : LayoutTable}
      {tagBytes : Nat} {variants : List (List StructFieldDesc)}
      {mp : Miri.Interpreter.MemPlace AnnealProv}
      {allocId : Miri.Memory.AllocId} {tag : Miri.Memory.BorTag}
      {localAlloc : AnnealLocalAlloc},
      UninitEnumMemRel mach ty layouts tagBytes variants mp →
      mp.ptr.provenance = some (.concrete allocId tag) →
      LiveAllocEntry mach.memory.live allocId localAlloc →
      ∃ alloc',
        Miri.Memory.Allocation.copy localAlloc.allocation
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy ty layouts).layout.size)
          Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) true true
          localAlloc.allocation = .ok () alloc' :=
  @UninitEnumMemRel.copy_uninit_self_ok

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {idx : Local} {decl : MirAst.LocalDecl}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)) →
        get? body.localDecls idx = some decl →
        env decl.ty = some (tagBytes, variants) →
        (∀ v, get? s.frame.locals idx ≠ some (.init v)) →
        (get? s.frame.locals idx = some .uninit →
          IsImmediateStepLocal m idx) →
        let mRes :=
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m
        StepRelLM2_3 body env allocBudget m (stepMirFn body s) mRes ∧
        ((∀ msg, mRes.2 ≠ .error (.undefinedBehavior msg)) →
          (∀ enumId b,
            EnumLocalByteUninit m enumId b →
            EnumLocalByteUninit mRes.1 enumId b) ∧
          (∀ j, j ≠ idx → IsImmediateStepLocal m j →
            IsImmediateStepLocal mRes.1 j)) :=
  @step_enum_self_copy_dead_or_uninit_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {idx : Local} {decl : MirAst.LocalDecl} {rootVal : Value}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨idx, .nil⟩ (.use (.copy ⟨idx, .nil⟩)) →
        get? body.localDecls idx = some decl →
        env decl.ty = some (tagBytes, variants) →
        get? s.frame.locals idx = some (.init rootVal) →
        stepMirFn body s =
          MirStepNode.step
            (advanceStmt s (s.frame.locals.set idx (.init rootVal)) s.memory) ∧
        ∃ m_err,
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
          (m_err,
            .error
              (.undefinedBehavior
                "whole-value copy between overlapping ranges")) :=
  @step_enum_self_copy_overlap_divergence

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env (allocBudget + 1) s m →
      (∀ p, body.phase ≠ .other p) →
      (∀ t tb vs, env t = some (tb, vs) → ValidEnumLayout t body.layouts tb vs) →
      ∀ {bb : BasicBlockData} {stmt : Statement}
        {dstIdx srcIdx : Local} {dstDecl srcDecl : MirAst.LocalDecl}
        {isMove : Bool} {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        get? bb.statements s.frame.stmtIdx = some stmt →
        stmt.kind = .assign ⟨dstIdx, .nil⟩
          (.use (if isMove then .move ⟨srcIdx, .nil⟩ else .copy ⟨srcIdx, .nil⟩)) →
        get? body.localDecls srcIdx = some srcDecl →
        get? body.localDecls dstIdx = some dstDecl →
        env srcDecl.ty = some (tagBytes, variants) →
        dstDecl.ty = srcDecl.ty →
        get? s.frame.locals srcIdx = some .uninit →
        ¬ IsImmediateStepLocal m srcIdx →
        get? s.frame.locals dstIdx ≠ some .dead →
        stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m',
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
          (m', .ok true) :=
  @step_enum_copy_move_uninitInd_divergence

example :
    (∃ m₁ msg₁,
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 22) = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 22) =
        (m₁, .error (.undefinedBehavior msg₁))) ∧
    (∃ m₂ m₃ msg₂,
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 23) =
        .step Witness.lm23Bb23S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 23) = (m₂, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0
        Witness.lm23Bb23S1 m₂ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb23S1 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₂ =
        (m₃, .error (.undefinedBehavior msg₂))) :=
  Witness.wit_lm2_3_self_copy_dead_and_uninit_ub

example :
    ∃ (m₁ m_err : AnnealStepState),
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 24) =
        .step Witness.lm23Bb24S1 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks ()
          (Witness.lm23InitMiri 24) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 0
        Witness.lm23Bb24S1 m₁ ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb24S1 =
        .step Witness.lm23Bb24S2 ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m₁ =
        (m_err,
          .error
            (.undefinedBehavior
              "whole-value copy between overlapping ranges")) :=
  Witness.wit_lm2_3_self_copy_overlap_divergence

example :
    (∃ m_u1 m₁,
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1
        (Witness.lm23InitAnneal 22) m_u1 ∧
      ¬ IsImmediateStepLocal m_u1 1 ∧
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 22) = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m_u1 = (m₁, .ok true)) ∧
    (∃ m_u2 m₂,
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1
        (Witness.lm23InitAnneal 26) m_u2 ∧
      ¬ IsImmediateStepLocal m_u2 1 ∧
      stepMirFn Witness.lm23Body (Witness.lm23InitAnneal 26) = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m_u2 = (m₂, .ok true)) ∧
    (∃ m_u3 m₃,
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1
        Witness.lm23Bb25S1 m_u3 ∧
      ¬ IsImmediateStepLocal m_u3 1 ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb25S1 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m_u3 = (m₃, .ok true)) ∧
    (∃ m_u4 m₄,
      StateRelLM2_3 Witness.lm23Body Witness.lm23Env 1
        Witness.lm23Bb18S1 m_u4 ∧
      ¬ IsImmediateStepLocal m_u4 1 ∧
      stepMirFn Witness.lm23Body Witness.lm23Bb18S1 = .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23Hooks () m_u4 = (m₄, .ok true)) :=
  Witness.wit_lm2_3_uninitInd_copy_and_move_divergence

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData} {decl0 : MirAst.LocalDecl}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        bb.isCleanup = false →
        get? bb.statements s.frame.stmtIdx = none →
        s.frame.stmtIdx = length bb.statements →
        bb.terminator.kind = .return_ →
        get? body.localDecls 0 = some decl0 →
        env decl0.ty = some (tagBytes, variants) →
        (get? s.frame.locals 0 = some .uninit →
          IsImmediateStepLocal m 0) →
        StepRelEnumReturnLM2_3 body env m
          (stepMirFn body s)
          (Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m) :=
  @step_return_enum_lm2_3_simulation

example :
    ∀ {body : CapturedMir} {env : EnumTypeEnv} {allocBudget : Nat}
      {s : MachineState} {m : AnnealStepState},
      StateRelLM2_3 body env allocBudget s m →
      (∀ p, body.phase ≠ .other p) →
      ∀ {bb : BasicBlockData} {decl0 : MirAst.LocalDecl}
        {tagBytes : Nat} {variants : List (List StructFieldDesc)},
        get? body.basicBlocks s.frame.blockIdx = some bb →
        bb.isCleanup = false →
        get? bb.statements s.frame.stmtIdx = none →
        s.frame.stmtIdx = length bb.statements →
        bb.terminator.kind = .return_ →
        get? body.localDecls 0 = some decl0 →
        env decl0.ty = some (tagBytes, variants) →
        get? s.frame.locals 0 = some .uninit →
        ¬ IsImmediateStepLocal m 0 →
        stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ mp0,
          annealControlHooks.returnOperand () m = (m, .ok (.indirect mp0)) ∧
          UninitEnumMemRel m.machine decl0.ty body.layouts tagBytes variants
            mp0 ∧
          Miri.Interpreter.Step.step
            (annealStepHooksLM2_3 body.localDecls body.layouts) () m =
          ({ m with stack := ⟨#[]⟩ }, .ok true) :=
  @step_return_enum_uninitInd_divergence

example :
    (∃ m₁ m₂ mp0,
      Miri.Interpreter.Step.step Witness.lm23RetHooks ()
        (Witness.lm23RetInitMiri 0) = (m₁, .ok true) ∧
      StateRelLM2_3 Witness.lm23ReturnEnumBody Witness.lm23Env 0
        Witness.lm23RetBb0S1 m₁ ∧
      Miri.Interpreter.Step.step Witness.lm23RetHooks () m₁ = (m₂, .ok true) ∧
      annealControlHooks.returnOperand () m₁ = (m₁, .ok (.indirect mp0)) ∧
      EnumMemRel m₂.machine Witness.lm23EnumTy Witness.lm23Layouts 4
        Witness.lm23Variants 2 [.scalar ⟨42, 4⟩, .scalar ⟨99, 8⟩] mp0 ∧
      m₂ = { m₁ with stack := ⟨#[]⟩ }) ∧
    (∃ m_err1 msg1,
      stepMirFn Witness.lm23ReturnEnumBody (Witness.lm23RetInitAnneal 1) =
        .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23RetHooks ()
        (Witness.lm23RetInitMiri 1) =
        (m_err1, .error (.undefinedBehavior msg1))) ∧
    (∃ m_err2 msg2,
      stepMirFn Witness.lm23ReturnEnumBody (Witness.lm23RetDeadAnneal 1) =
        .fail .ub ∧
      Miri.Interpreter.Step.step Witness.lm23RetHooks ()
        (Witness.lm23RetDeadMiri 1) =
        (m_err2, .error (.undefinedBehavior msg2))) ∧
    (∃ m_u0 mp_u0,
      StateRelLM2_3 Witness.lm23ReturnEnumBody Witness.lm23Env 0
        (Witness.lm23RetInitAnneal 1) m_u0 ∧
      ¬ IsImmediateStepLocal m_u0 0 ∧
      stepMirFn Witness.lm23ReturnEnumBody (Witness.lm23RetInitAnneal 1) =
        .fail .ub ∧
      annealControlHooks.returnOperand () m_u0 = (m_u0, .ok (.indirect mp_u0)) ∧
      UninitEnumMemRel m_u0.machine Witness.lm23EnumTy Witness.lm23Layouts 4
        Witness.lm23Variants mp_u0 ∧
      Miri.Interpreter.Step.step Witness.lm23RetHooks () m_u0 =
        ({ m_u0 with stack := ⟨#[]⟩ }, .ok true)) :=
  Witness.wit_lm2_3_return_enum_and_ub

end LM2_3Pins


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

private theorem pin_nodeAccess_locationState_simulation (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
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
    res.access.root = 0 ∧
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
private theorem pin_sim_lm3_3_retag_raw_step (rk : RetagKind) (mutability : Mutability)
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

example (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool) :
    let res := Miri.TreeBorrows.RetagPipeline.retagPointerValue
      retagInitialMachineState (retagRefRequest (Miri.ABI.Size.ofBytes 8) mode mutability frozen)
    let perm := annealRetagPerm mode mutability frozen
    res.outcome = .ok (some (.concrete retagTestAllocId retagChildTag)) ∧
    res.state.global.protectedTags.contains retagChildTag = (mode == .fnEntry) ∧
    res.state.frame.protectedTags =
      (if mode == .fnEntry then #[(retagTestAllocId, retagChildTag)] else #[]) ∧
    (res.state.global.endCall res.state.frame).protectedTags.contains retagChildTag = false ∧
    (Miri.TreeBorrows.RetagPipeline.Event.parentTreeAccess .Read ⟨0, 8⟩ ∈ res.events.toList ↔
      perm ≠ .cell) ∧
    Miri.TreeBorrows.RetagPipeline.Event.childInserted retagChildTag ∈ res.events.toList ∧
    (res.state.memory.live.find? fun e => e.1 == retagTestAllocId).bind
        (fun e => (e.2.allocation.extra.nthParent retagChildTag 1).toOption) =
      some retagParentTag ∧
    (liveTagLocationState res.state.memory retagChildTag).map (fun s => (s.permission, s.accessed)) =
      some (annealPermToMiri perm, annealPermToMiri perm != .Cell) :=
  @retagPointerValue_8byte_reference_simulation mode mutability frozen

example (kind : TreeBorrowAccessKind) (rel : TreeBorrowRelatedness)
    (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let res := tree.performBorrowAccessRange (.concrete (hooksAccessTag rel))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8) (annealAccessKindToMiri kind)
      (hooksForChildProtected isProtected).protectedTags .VisitChildrenOfAccessed
    let out := treeBorrowNodeAccess kind rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    (res.status = .Completed ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.status = .Completed →
      (res.tree.locations.entries[0]?.bind (fun s => s.data.perms.get ⟨1⟩)).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) :=
  @borrowTree_performBorrowAccessRange_simulation kind rel perm isProtected

example (isProtected : Bool) :
    let tree := Miri.TreeBorrows.BorrowTree.new retagParentTag (Miri.ABI.Size.ofBytes 8)
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId retagParentTag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete retagParentTag) range
    res.outcome = .ok () ∧ res.memory = mem :=
  @machineMemoryHooks_fresh_root_read_simulation isProtected

example (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let tag := hooksAccessTag rel
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryRead
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete tag) range
    let out := treeBorrowNodeAccess .read rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    (res.outcome = .ok () ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.outcome = .ok () →
      (liveTagLocationState res.memory retagChildTag).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) :=
  @machineMemoryHooks_beforeMemoryRead_simulation rel perm isProtected

example (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let mem := liveTreeMemory tree
    let alloc := liveTreeAllocation tree
    let tag := hooksAccessTag rel
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
    let range := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryWrite
      mem ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete tag) range
    let out := treeBorrowNodeAccess .write rel perm isProtected
    let dummy : BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := perm }
    (res.outcome = .ok () ↔ treeBorrowTransitionIsUB out = false) ∧
    (res.outcome = .ok () →
      (liveTagLocationState res.memory retagChildTag).map (·.permission) =
        some (annealPermToMiri (applyTreeBorrowTransition dummy out).perm)) :=
  @machineMemoryHooks_beforeMemoryWrite_simulation rel perm isProtected

example (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (readerTag : Option Nat)
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (i : Nat) (hi : i < borrows.length)
    (hloc : borrows[i].targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite borrows[i] readProj readRangeOff readRangeLen = true)
    (hskip : treeBorrowAccessRelatedness allBorrows borrows[i] readerTag = .foreignAccess →
      borrows[i].perm ≠ .disabled)
    (hno_ub : hasTreeReadUB allBorrows borrows activeProtectors targetLocal readerTag
      readProj readRangeOff readRangeLen = false) :
    let borrows' := freezeTreeBorrowsOnReadAtProj allBorrows borrows targetLocal
      readerTag readProj readRangeOff readRangeLen activeProtectors
    let hi' : i < borrows'.length := by
      dsimp only [borrows']
      rw [freezeTreeBorrowsOnReadAtProj_length]
      exact hi
    let nt := basedNormalTree borrows activeProtectors
    let nt' := basedNormalTree borrows' activeProtectors
    let rel := treeBorrowAccessRelatedness allBorrows borrows[i] readerTag
    let isProt := isBorrowProtected activeProtectors borrows[i]
    borrowEntryReadUB allBorrows activeProtectors borrows[i] targetLocal readerTag
      readProj readRangeOff readRangeLen = false ∧
    nt.stateAt i = some ⟨annealPermToMiri borrows[i].perm, true, .None⟩ ∧
    nt'.stateAt i = some ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ ∧
    (∃ transition,
      Miri.TreeBorrows.Tree.LocationState.performAccess
        ⟨annealPermToMiri borrows[i].perm, true, .None⟩
        .Read (annealRelatednessToMiri rel) isProt =
      .Success ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ transition) :=
  @freezeTreeBorrowsOnReadAtProj_locationState_simulation allBorrows borrows activeProtectors
    targetLocal readerTag readProj readRangeOff readRangeLen i hi hloc hov hskip hno_ub

example (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetLocal : Local)
    (writerTag : Option Nat)
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (i : Nat) (hi : i < borrows.length)
    (hloc : borrows[i].targetLocal = targetLocal)
    (hov : borrowEntryOverlapsWrite borrows[i] writeProj writeRangeOff writeRangeLen = true)
    (hskip : treeBorrowAccessRelatedness allBorrows borrows[i] writerTag = .foreignAccess →
      borrows[i].perm ≠ .disabled)
    (hno_prot : hasProtectedTreeWriteConflict allBorrows borrows activeProtectors targetLocal
      writerTag writeProj writeRangeOff writeRangeLen = false)
    (hnode_ub :
      treeBorrowTransitionIsUB
        (treeBorrowNodeAccess .write
          (treeBorrowAccessRelatedness allBorrows borrows[i] writerTag)
          borrows[i].perm
          (isBorrowProtected activeProtectors borrows[i])) = false) :
    let borrows' := invalidateTreeBorrowsAtProj allBorrows borrows targetLocal
      writerTag writeProj writeRangeOff writeRangeLen
    let hi' : i < borrows'.length := by
      dsimp only [borrows']
      rw [invalidateTreeBorrowsAtProj_length]
      exact hi
    let nt := basedNormalTree borrows activeProtectors
    let nt' := basedNormalTree borrows' activeProtectors
    let rel := treeBorrowAccessRelatedness allBorrows borrows[i] writerTag
    let isProt := isBorrowProtected activeProtectors borrows[i]
    nt.stateAt i = some ⟨annealPermToMiri borrows[i].perm, true, .None⟩ ∧
    nt'.stateAt i = some ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ ∧
    (∃ transition,
      Miri.TreeBorrows.Tree.LocationState.performAccess
        ⟨annealPermToMiri borrows[i].perm, true, .None⟩
        .Write (annealRelatednessToMiri rel) isProt =
      .Success ⟨annealPermToMiri (borrows'[i]'hi').perm, true, .None⟩ transition) :=
  @invalidateTreeBorrowsAtProj_locationState_simulation allBorrows borrows activeProtectors
    targetLocal writerTag writeProj writeRangeOff writeRangeLen i hi hloc hov hskip hno_prot hnode_ub

open LeanMiriSpec.Correspondence.SimLM3_3 in
private theorem pin_sim_lm3_3_retag_raw_scalar_step (rk : RetagKind) (mutability : Mutability) :
    match rk with
    | .raw =>
      ∃ s' : MachineState,
        stepMirFn (retagRawBody rk mutability) childScalarRawState = .step s' ∧
        s'.memory = childScalarRawState.memory ∧
        get? s'.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩))
    | .default | .twoPhase | .fnEntry =>
      stepMirFn (retagRawBody rk mutability) childScalarRawState = .fail .ub :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_raw_scalar_step rk mutability

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ : MachineState,
      stepMirFn callerG initG = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn callerG s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      s₂.memory.activeProtectors = [1] ∧
      stepMirFn callerG s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn callerG s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz true) (some 1) (some 1), entry 1 .reserved] ∧
      s₄.memory.activeProtectors = [1] ∧
      stepMirFn callerG s₄ = .step s₅ ∧
      s₅.memory.activeProtectors = [] ∧
      s₅.memory.borrows =
        [entry 3 .frozen, entry 2 (.reservedFrz true) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn callerG s₅ = .step s₆ ∧
      s₆.memory.borrows =
        [entry 3 .disabled, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      get? s₆.frame.locals 1 = some (.init (.scalar ⟨9, 8⟩)) ∧
      ((basedNormalTree s₅.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₆.memory.borrows []
        ((basedNormalTree s₅.memory.borrows []).performAccess 1 .Write
          .VisitChildrenOfAccessed).tree :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_protector_release_on_return_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyH initH = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyH s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .reserved (some 1), entry 1 .reserved] ∧
      s₂.memory.activeProtectors = [] ∧
      stepMirFn bodyH s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entry 3 .reserved (some 2), entry 2 .reserved (some 1), entry 1 .reserved] ∧
      s₃.memory.nextTag = 4 ∧
      stepMirFn bodyH s₃ = .step s₄ ∧
      s₄.memory.borrows = s₃.memory.borrows ∧
      s₄.memory.nextTag = 4 ∧
      stepMirFn bodyH s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 3 .unique (some 2), entry 2 .unique (some 1), entry 1 .unique] ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨77, 8⟩)) ∧
      ((basedNormalTree s₄.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₅.memory.borrows []
        ((basedNormalTree s₄.memory.borrows []).performAccess 0 .Write
          .VisitChildrenOfAccessed).tree :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_non_fnEntry_retag_and_raw_retag_real_steps

example (offA lenA offB lenB : Nat) :
    byteRangesOverlapBool offA lenA offB lenB = true ↔
      0 < lenA ∧ 0 < lenB ∧ offA < offB + lenB ∧ offB < offA + lenA :=
  @byteRangesOverlapBool_iff offA lenA offB lenB

example (entry : BorrowEntry) (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat) :
    borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = true ↔
      if 0 < writeRangeLen ∧ 0 < entry.rangeLen then
        entry.rangeOffset < writeRangeOff + writeRangeLen ∧
          writeRangeOff < entry.rangeOffset + entry.rangeLen
      else
        projectionsOverlap entry.targetProjection writeProj = true :=
  @borrowEntryOverlapsWrite_iff entry writeProj writeRangeOff writeRangeLen

example (allBorrows : List BorrowEntry) (activeProtectors : List Nat)
    (entry : BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (hdisj : entry.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = false) :
    borrowEntryReadUB allBorrows activeProtectors entry targetLocal readerTag
      readProj readRangeOff readRangeLen = false :=
  @borrowEntryReadUB_of_disjoint allBorrows activeProtectors entry targetLocal
    readerTag readProj readRangeOff readRangeLen hdisj

example (allBorrows : List BorrowEntry) (entry : BorrowEntry)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hdisj : entry.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite entry readProj readRangeOff readRangeLen = false) :
    updateBorrowPermOnReadAtProj allBorrows entry targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors = entry :=
  @updateBorrowPermOnReadAtProj_of_disjoint allBorrows entry targetLocal
    readerTag readProj readRangeOff readRangeLen activeProtectors hdisj

example (allBorrows : List BorrowEntry) (entry : BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : entry.targetLocal ≠ targetLocal ∨
      (treeBorrowAccessRelatedness allBorrows entry writerTag = .foreignAccess ∧
        borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen = false)) :
    updateBorrowPermTreeAtProj allBorrows entry targetLocal writerTag
      writeProj writeRangeOff writeRangeLen = entry :=
  @updateBorrowPermTreeAtProj_of_foreign_disjoint allBorrows entry targetLocal
    writerTag writeProj writeRangeOff writeRangeLen hdisj

example (kind : TreeBorrowAccessKind) (b₀ : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 2)
    (hp₀ : b₀.parentTag = none) (hloc : b₀.targetLocal = targetLocal)
    (hproj : b₀.targetProjection = .nil) :
    let nres := (basedNormalTree [b₀] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [b₀] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [b₀] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) :=
  @basedNormalTree_performAccess_singleton_simulation kind b₀ activeProtectors
    targetLocal start hp₀ hloc hproj

example (kind : TreeBorrowAccessKind) (child parent : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 2)
    (hneq : child.tag ≠ parent.tag)
    (hcpar : child.parentTag = some parent.tag)
    (hppar : parent.parentTag = none)
    (hcloc : child.targetLocal = targetLocal)
    (hploc : parent.targetLocal = targetLocal)
    (hcproj : child.targetProjection = .nil)
    (hpproj : parent.targetProjection = .nil) :
    let nres := (basedNormalTree [child, parent] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [child, parent] activeProtectors targetLocal
      start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [child, parent] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) :=
  @basedNormalTree_performAccess_parent_child_simulation kind child parent activeProtectors
    targetLocal start hneq hcpar hppar hcloc hploc hcproj hpproj

example (kind : TreeBorrowAccessKind) (b₀ b₁ : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 3)
    (hneq : b₀.tag ≠ b₁.tag)
    (hp₀ : b₀.parentTag = none)
    (hp₁ : b₁.parentTag = none)
    (hloc₀ : b₀.targetLocal = targetLocal)
    (hloc₁ : b₁.targetLocal = targetLocal)
    (hproj₀ : b₀.targetProjection = .nil)
    (hproj₁ : b₁.targetProjection = .nil) :
    let nres := (basedNormalTree [b₀, b₁] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [b₀, b₁] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [b₀, b₁] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) :=
  @basedNormalTree_performAccess_siblings_simulation kind b₀ b₁ activeProtectors
    targetLocal start hneq hp₀ hp₁ hloc₀ hloc₁ hproj₀ hproj₁

example (allBorrows rest : List BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    hasTreeReadUB allBorrows rest activeProtectors targetLocal readerTag
      readProj readRangeOff readRangeLen = false :=
  @hasTreeReadUB_of_all_disjoint allBorrows rest activeProtectors targetLocal readerTag
    readProj readRangeOff readRangeLen hdisj

example (allBorrows : List BorrowEntry) (b₀ : BorrowEntry) (rest : List BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    hasTreeReadUB allBorrows (b₀ :: rest) activeProtectors targetLocal readerTag
      readProj readRangeOff readRangeLen =
    borrowEntryReadUB allBorrows activeProtectors b₀ targetLocal readerTag
      readProj readRangeOff readRangeLen :=
  @hasTreeReadUB_disjoint_tail allBorrows b₀ rest activeProtectors targetLocal readerTag
    readProj readRangeOff readRangeLen hdisj

example (allBorrows rest : List BorrowEntry) (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    freezeTreeBorrowsOnReadAtProj allBorrows rest targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors = rest :=
  @freezeTreeBorrowsOnReadAtProj_of_all_disjoint allBorrows rest targetLocal readerTag
    readProj readRangeOff readRangeLen activeProtectors hdisj

example (allBorrows : List BorrowEntry) (b₀ : BorrowEntry) (rest : List BorrowEntry)
    (targetLocal : Local) (readerTag : Option Nat)
    (readProj : List ProjectionElem) (readRangeOff readRangeLen : Nat)
    (activeProtectors : List Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e readProj readRangeOff readRangeLen = false) :
    freezeTreeBorrowsOnReadAtProj allBorrows (b₀ :: rest) targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors =
    updateBorrowPermOnReadAtProj allBorrows b₀ targetLocal readerTag
      readProj readRangeOff readRangeLen activeProtectors :: rest :=
  @freezeTreeBorrowsOnReadAtProj_disjoint_tail allBorrows b₀ rest targetLocal readerTag
    readProj readRangeOff readRangeLen activeProtectors hdisj

example (allBorrows rest : List BorrowEntry) (activeProtectors : List Nat)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      borrowEntryOverlapsWrite e writeProj writeRangeOff writeRangeLen = false) :
    hasProtectedTreeWriteConflict allBorrows rest activeProtectors targetLocal
      writerTag writeProj writeRangeOff writeRangeLen = false :=
  @hasProtectedTreeWriteConflict_of_all_disjoint allBorrows rest activeProtectors targetLocal
    writerTag writeProj writeRangeOff writeRangeLen hdisj

example (allBorrows rest : List BorrowEntry) (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      (treeBorrowAccessRelatedness allBorrows e writerTag = .foreignAccess ∧
        borrowEntryOverlapsWrite e writeProj writeRangeOff writeRangeLen = false)) :
    invalidateTreeBorrowsAtProj allBorrows rest targetLocal writerTag
      writeProj writeRangeOff writeRangeLen = rest :=
  @invalidateTreeBorrowsAtProj_of_all_foreign_disjoint allBorrows rest targetLocal writerTag
    writeProj writeRangeOff writeRangeLen hdisj

example (allBorrows : List BorrowEntry) (b₀ : BorrowEntry) (rest : List BorrowEntry)
    (targetLocal : Local) (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (writeRangeOff writeRangeLen : Nat)
    (hdisj : ∀ e ∈ rest, e.targetLocal ≠ targetLocal ∨
      (treeBorrowAccessRelatedness allBorrows e writerTag = .foreignAccess ∧
        borrowEntryOverlapsWrite e writeProj writeRangeOff writeRangeLen = false)) :
    invalidateTreeBorrowsAtProj allBorrows (b₀ :: rest) targetLocal writerTag
      writeProj writeRangeOff writeRangeLen =
    updateBorrowPermTreeAtProj allBorrows b₀ targetLocal writerTag
      writeProj writeRangeOff writeRangeLen :: rest :=
  @invalidateTreeBorrowsAtProj_disjoint_tail allBorrows b₀ rest targetLocal writerTag
    writeProj writeRangeOff writeRangeLen hdisj

example (kind : TreeBorrowAccessKind) (g c r : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none)
    (hgloc : g.targetLocal = targetLocal)
    (hcloc : c.targetLocal = targetLocal)
    (hrloc : r.targetLocal = targetLocal)
    (hgproj : g.targetProjection = .nil)
    (hcproj : c.targetProjection = .nil)
    (hrproj : r.targetProjection = .nil)
    (hgprot : isBorrowProtected activeProtectors g = false)
    (hcprot : isBorrowProtected activeProtectors c = false)
    (hrprot : isBorrowProtected activeProtectors r = false)
    (hinv : treeBorrowsChain3Inv g.perm c.perm r.perm = true) :
    let nres := (basedNormalTree [g, c, r] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [g, c, r] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) :=
  @basedNormalTree_performAccess_three_level_chain_simulation kind g c r activeProtectors
    targetLocal start hneq_gc hneq_gr hneq_cr hgpar hcpar hrpar hgloc hcloc hrloc
    hgproj hcproj hrproj hgprot hcprot hrprot hinv

example (kind : TreeBorrowAccessKind) (c₀ c₁ p : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq₀₁ : c₀.tag ≠ c₁.tag) (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none)
    (hloc₀ : c₀.targetLocal = targetLocal)
    (hloc₁ : c₁.targetLocal = targetLocal)
    (hlocp : p.targetLocal = targetLocal)
    (hproj₀ : c₀.targetProjection = .nil)
    (hproj₁ : c₁.targetProjection = .nil)
    (hprojp : p.targetProjection = .nil)
    (hc₀prot : isBorrowProtected activeProtectors c₀ = false)
    (hc₁prot : isBorrowProtected activeProtectors c₁ = false)
    (hpprot : isBorrowProtected activeProtectors p = false)
    (hinv : treeBorrowsBranch3Inv c₀.perm c₁.perm p.perm = true) :
    let nres := (basedNormalTree [c₀, c₁, p] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [c₀, c₁, p] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed → TreeBorrowsRel borrows' activeProtectors nres.tree) :=
  @basedNormalTree_performAccess_branching_children_simulation kind c₀ c₁ p activeProtectors
    targetLocal start hneq₀₁ hneq₀p hneq₁p hc₀par hc₁par hppar hloc₀ hloc₁ hlocp
    hproj₀ hproj₁ hprojp hc₀prot hc₁prot hpprot hinv

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (rk : RetagKind) (mutability : Mutability) :
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability true
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    ∃ s' : MachineState,
      stepMirFn (retagZstRefBody rk mutability) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_zst_ref_step rk mutability

open LeanMiriSpec.Correspondence.SimLM3_3 in
private theorem pin_sim_lm3_3_retag_zst_scalar_step
    (rk : RetagKind) (mutability : Mutability) (nonNull : Bool) :
    match nonNull with
    | true =>
      ∃ s' : MachineState,
        stepMirFn (retagZstRefBody rk mutability) (retagZstScalarState true) = .step s' ∧
        s'.memory = (retagZstScalarState true).memory ∧
        get? s'.frame.locals 2 = some (.init (.scalar ⟨8, 8⟩))
    | false =>
      stepMirFn (retagZstRefBody rk mutability) (retagZstScalarState false) = .fail .ub :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_zst_scalar_step rk mutability nonNull

open LeanMiriSpec.Correspondence in
example {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap) :
    (s.memory.borrows.map BorrowEntry.tag).Nodup ∧
      TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
        (basedNormalTree s.memory.borrows s.memory.activeProtectors) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.stateRelLM3_2Tree_treeBorrowsRel
    body s m treeMap htree

open Trusted.Rustc.V2026_06_01.Layout in
open LeanMiriSpec.Correspondence in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
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
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl →
            decl.ty.kind = dstDecl.ty.kind))
    (hanc_read : ∀ ptrVal,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ treeMap, e.tag = ptrVal.tag →
        treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    let treeMap' := derefReadNextTreeMap s.frame.locals treeMap refIdx
    TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
      (basedNormalTree s.memory.borrows s.memory.activeProtectors) ∧
    StepRelLM3_2Tree body m treeMap'
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ m',
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM3_2Tree body s' m' treeMap' ∧
        TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
          (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) :=
  LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_interpreter_deref_read_step htree hphase hopKind hbb hstmt hdecl_dst hdecl_ref href_ty hdst_prim himm hlive_ref hanc_read hlay_coh

open Trusted.Rustc.V2026_06_01.Layout in
open LeanMiriSpec.Correspondence in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {refIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨refIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {refDecl : MirAst.LocalDecl} {mutability : Mutability}
    {pointeeKind : RigidTy} {valTy : Ty}
    (hdecl_ref : get? body.localDecls refIdx = some refDecl)
    (href_ty : refDecl.ty.kind = .ref mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ref : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame refIdx)
    (hlive_ref : ∀ ptrVal e tgtDecl,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm ≠ .frozen ∧ e.perm ≠ .disabled) ∧
        tgtDecl.ty.kind = pointeeKind)
    (hanc_write : ∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .write s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    let treeMap' := derefWriteNextTreeMap s.frame.locals treeMap refIdx
    TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
      (basedNormalTree s.memory.borrows s.memory.activeProtectors) ∧
    StepRelLM3_2Tree body m treeMap'
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ m',
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM3_2Tree body s' m' treeMap' ∧
        TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
          (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) :=
  LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_interpreter_deref_write_step htree hphase hbb hstmt hdecl_ref href_ty hval_prim hval_kind hop himm_ref hlive_ref hanc_write hlay_coh

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    (∃ s₁ s₂ s₃ s₄ s₅ s₆ : MachineState,
      stepMirFn bodyI initI = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .reserved] ∧
      stepMirFn bodyI s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 (.reservedFrz false) (some 1) (some 1), entry 1 .reserved] ∧
      stepMirFn bodyI s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyI s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .frozen, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyI s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 4 .frozen (some 3) (some 2),
          entry 3 .frozen,
          entry 2 .unique (some 1) (some 1),
          entry 1 .unique] ∧
      s₅.memory.activeProtectors = [2, 1] ∧
      s₅.memory.nextTag = 5 ∧
      stepMirFn bodyI s₅ = .step s₆ ∧
      s₆.memory = s₅.memory ∧
      TreeBorrowsRel s₆.memory.borrows s₆.memory.activeProtectors
        (basedNormalTree s₆.memory.borrows s₆.memory.activeProtectors)) ∧
    stepMirFn bodyI initINullAt5 = .fail .ub :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_zst_retag_skips_read_and_dangling_scalar_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (rk : RetagKind) (mutability : Mutability) :
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability true
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    ∃ s' : MachineState,
      stepMirFn (retagPhantomRefBody rk mutability) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_phantom_ref_step rk mutability

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (bk : BorrowKind) :
    let childPerm : TreeBorrowPerm :=
      match bk with
      | .shared => .frozen
      | .mut _ => .reservedFrz false
    ∃ s' : MachineState,
      stepMirFn (zstDerefReborrowBody bk) zstDerefReborrowState = .step s' ∧
      get? s'.frame.locals 3 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) none,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = [1] ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_zst_deref_reborrow_step bk

open Trusted.Rustc.V2026_06_01.Layout in
open LeanMiriSpec.Correspondence in
example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {treeMap : List ReborrowMapEntry}
    (htree : StateRelLM3_2Tree body s m treeMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx refIdx : Local}
    {dstDecl refDecl : MirAst.LocalDecl}
    {bk : BorrowKind} {refMut dstMut : Mutability}
    {pointeeKind dstPointee : RigidTy}
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
      e ∈ treeMap → e.tag = ptrVal.tag →
      get? s.frame.locals e.localIdx ≠ some .dead ∧
      get? s.frame.locals e.localIdx ≠ some .uninit ∧
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ bk ≠ .shared) ∧
      (∀ tgtDecl, get? body.localDecls e.localIdx = some tgtDecl →
        tgtDecl.ty.kind = pointeeKind))
    (hanc_read : ∀ ptrVal e,
      get? s.frame.locals refIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ treeMap → e.tag = ptrVal.tag →
      treeBorrowAncestorsChildAccessUB .read s.memory.borrows e.parentTag = false)
    (hlay_coh : PrimLayoutsCoherent body.layouts)  :
    let treeMap' :=
      reborrowTreeMapNext body.localDecls body.layouts bk s.frame.locals treeMap refIdx
        s.memory.nextTag
    TreeBorrowsRel s.memory.borrows s.memory.activeProtectors
      (basedNormalTree s.memory.borrows s.memory.activeProtectors) ∧
    StepRelLM3_2Tree body m treeMap'
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) ∧
    (∀ s', stepMirFn body s = .step s' →
      ∃ m',
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM3_2Tree body s' m' treeMap' ∧
        TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
          (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) :=
  LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_interpreter_reborrow_step htree hphase hbb hstmt hdecl_dst hdecl_ref href_ty hdst_ty hpk_prim himm hlive_zero_perm hanc_read hlay_coh

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    (∃ s₁ s₂ s₃ s₄ s₅ : MachineState,
      stepMirFn bodyJDisjoint initJ = .step s₁ ∧
      s₁.memory.borrows = [entryProj 1 .reserved [.field 0 u64T]] ∧
      stepMirFn bodyJDisjoint s₁ = .step s₂ ∧
      s₂.memory.borrows =
        [entryProj 2 .frozen [.field 1 u64T],
         entryProj 1 .reserved [.field 0 u64T]] ∧
      stepMirFn bodyJDisjoint s₂ = .step s₃ ∧
      s₃.memory.borrows =
        [entryProj 3 .frozen [.field 1 u64T] (some 2) (some 1),
         entryProj 2 .frozen [.field 1 u64T],
         entryProj 1 .reserved [.field 0 u64T]] ∧
      s₃.memory.activeProtectors = [1] ∧
      stepMirFn bodyJDisjoint s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entryProj 3 .frozen [.field 1 u64T] (some 2) (some 1),
         entryProj 2 .frozen [.field 1 u64T],
         entryProj 1 .unique [.field 0 u64T]] ∧
      get? s₄.frame.locals 1 =
        some (.init (.aggregate 0 [.scalar ⟨99, 8⟩, .scalar ⟨20, 8⟩])) ∧
      stepMirFn bodyJDisjoint s₄ = .step s₅ ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨20, 8⟩))) ∧
    (∃ o₁ o₂ o₃ : MachineState,
      stepMirFn bodyJOverlap initJ = .step o₁ ∧
      stepMirFn bodyJOverlap o₁ = .step o₂ ∧
      stepMirFn bodyJOverlap o₂ = .step o₃ ∧
      o₃.memory.borrows =
        [entryProj 3 .frozen [.field 0 u64T] (some 2) (some 1),
         entryProj 2 .frozen [.field 0 u64T],
         entryProj 1 (.reservedFrz false) [.field 0 u64T]] ∧
      stepMirFn bodyJOverlap o₃ = .fail .ub) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_subprojection_disjoint_vs_overlapping_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ : MachineState,
      stepMirFn bodyK initK = .step s₁ ∧
      stepMirFn bodyK s₁ = .step s₂ ∧
      stepMirFn bodyK s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyK s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .reserved, entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyK s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 4 .frozen (some 3),
         entry 3 .reserved,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      stepMirFn bodyK s₅ = .step s₆ ∧
      stepMirFn bodyK s₆ = .step s₇ ∧
      s₇.memory.borrows =
        [{ tag := 6, targetLocal := 5, targetProjection := .nil, perm := .frozen,
           protector := some 2, parentTag := some 5 },
         { tag := 5, targetLocal := 5, targetProjection := .nil, perm := .frozen,
           protector := none, parentTag := none },
         entry 4 .frozen (some 3),
         entry 3 .reserved,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      s₇.memory.activeProtectors = [2, 1] ∧
      TreeBorrowsRel s₇.memory.borrows s₇.memory.activeProtectors
        (basedNormalTree s₇.memory.borrows s₇.memory.activeProtectors) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_zst_deref_reborrow_and_phantom_retag_real_steps

open LeanMiriSpec.Correspondence in
example (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let res := tree.deallocateBorrowRange (.concrete (hooksAccessTag rel))
      Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)
      (hooksForChildProtected isProtected).protectedTags
    let out := treeBorrowNodeAccess .write rel perm isProtected
    (treeBorrowTransitionIsUB out = true → ∃ err, res.status = .AccessFailure err) ∧
    (treeBorrowTransitionIsUB out = false → isProtected = true → perm ≠ .cell →
      res.status = .ProtectedDealloc ⟨0, 8⟩ ⟨1⟩) ∧
    (res.status = .Deallocated ↔
      (treeBorrowTransitionIsUB out = false ∧ (isProtected = false ∨ perm = .cell))) :=
  @borrowTree_deallocateBorrowRange_simulation rel perm isProtected

open LeanMiriSpec.Correspondence in
example (rel : TreeBorrowRelatedness) (perm : TreeBorrowPerm) (isProtected : Bool) :
    let tree := hooksTwoNodeTree perm
    let alloc := liveTreeAllocation tree
    let tag := hooksAccessTag rel
    let ptr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete retagTestAllocId tag)⟩
    let res := Miri.TreeBorrows.MachineMemoryHooks.beforeMemoryDeallocation
      ⟨(), .empty, false, #[]⟩ (hooksForChildProtected isProtected)
      alloc ptr retagTestAllocId (.concrete tag)
      (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.ONE .stack
    let out := treeBorrowNodeAccess .write rel perm isProtected
    res.outcome = .ok () ↔
      (treeBorrowTransitionIsUB out = false ∧ (isProtected = false ∨ perm = .cell)) :=
  @machineMemoryHooks_beforeMemoryDeallocation_simulation rel perm isProtected

open LeanMiriSpec.Correspondence in
example (descPerm ancPerm : TreeBorrowPerm)
    (h : treeBorrowsAncestorInv descPerm ancPerm = true) :
    treeBorrowsProtAncestorInv descPerm false ancPerm false = true :=
  @treeBorrowsAncestorInv_imp_prot_false descPerm ancPerm h

open LeanMiriSpec.Correspondence in
example (mode : AnnealRetagMode) (mutability : Mutability) (frozen : Bool)
    (ancPerm : TreeBorrowPerm) (ancProt : Bool)
    (hanc_ndis : ancPerm ≠ .disabled)
    (hanc_nim : ancProt = true → ancPerm ≠ .reservedIM)
    (hfrz_sh : ancPerm = .frozen → mutability = .not) :
    treeBorrowsProtAncestorInv
      (annealRetagPerm mode mutability frozen) (mode == .fnEntry)
      ancPerm ancProt = true :=
  @treeBorrowsProtAncestorInv_retag_init
    mode mutability frozen ancPerm ancProt hanc_ndis hanc_nim hfrz_sh

open LeanMiriSpec.Correspondence in
example (descPerm : TreeBorrowPerm) (descProt descProt' : Bool)
    (ancPerm : TreeBorrowPerm) (ancProt ancProt' : Bool)
    (hd : descProt' = true → descProt = true)
    (ha : ancProt' = true → ancProt = true)
    (hinv : treeBorrowsProtAncestorInv descPerm descProt ancPerm ancProt = true) :
    treeBorrowsProtAncestorInv descPerm descProt' ancPerm ancProt' = true :=
  @treeBorrowsProtAncestorInv_release_protectors
    descPerm descProt descProt' ancPerm ancProt ancProt' hd ha hinv

open LeanMiriSpec.Correspondence in
example (kind : TreeBorrowAccessKind) (g c r : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq_gc : g.tag ≠ c.tag) (hneq_gr : g.tag ≠ r.tag) (hneq_cr : c.tag ≠ r.tag)
    (hgpar : g.parentTag = some c.tag)
    (hcpar : c.parentTag = some r.tag)
    (hrpar : r.parentTag = none)
    (hgloc : g.targetLocal = targetLocal)
    (hcloc : c.targetLocal = targetLocal)
    (hrloc : r.targetLocal = targetLocal)
    (hgproj : g.targetProjection = .nil)
    (hcproj : c.targetProjection = .nil)
    (hrproj : r.targetProjection = .nil)
    (hinv : borrowListChain3ProtInv [g, c, r] activeProtectors = true) :
    let nres := (basedNormalTree [g, c, r] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [g, c, r] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [g, c, r] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed →
      TreeBorrowsRel borrows' activeProtectors nres.tree ∧
      borrowListChain3ProtInv borrows' activeProtectors = true) :=
  @basedNormalTree_performAccess_three_level_chain_prot_simulation
    kind g c r activeProtectors targetLocal start hneq_gc hneq_gr hneq_cr
    hgpar hcpar hrpar hgloc hcloc hrloc hgproj hcproj hrproj hinv

open LeanMiriSpec.Correspondence in
example (kind : TreeBorrowAccessKind) (c₀ c₁ p : BorrowEntry)
    (activeProtectors : List Nat) (targetLocal : Local) (start : Fin 4)
    (hneq₀₁ : c₀.tag ≠ c₁.tag) (hneq₀p : c₀.tag ≠ p.tag) (hneq₁p : c₁.tag ≠ p.tag)
    (hc₀par : c₀.parentTag = some p.tag)
    (hc₁par : c₁.parentTag = some p.tag)
    (hppar : p.parentTag = none)
    (hloc₀ : c₀.targetLocal = targetLocal)
    (hloc₁ : c₁.targetLocal = targetLocal)
    (hlocp : p.targetLocal = targetLocal)
    (hproj₀ : c₀.targetProjection = .nil)
    (hproj₁ : c₁.targetProjection = .nil)
    (hprojp : p.targetProjection = .nil)
    (hinv : borrowListBranch3ProtInv [c₀, c₁, p] activeProtectors = true) :
    let nres := (basedNormalTree [c₀, c₁, p] activeProtectors).performAccess start.val
      (annealAccessKindToMiri kind) .VisitChildrenOfAccessed
    let borrows' := annealTableAfterAccess kind [c₀, c₁, p] activeProtectors targetLocal start.val
    (nres.status = .Completed ↔
      annealTableAccessUB kind [c₀, c₁, p] activeProtectors targetLocal start.val = false) ∧
    (nres.status = .Completed →
      TreeBorrowsRel borrows' activeProtectors nres.tree ∧
      borrowListBranch3ProtInv borrows' activeProtectors = true) :=
  @basedNormalTree_performAccess_branching_children_prot_simulation
    kind c₀ c₁ p activeProtectors targetLocal start hneq₀₁ hneq₀p hneq₁p
    hc₀par hc₁par hppar hloc₀ hloc₁ hlocp hproj₀ hproj₁ hprojp hinv

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (rk : RetagKind) (mutability : Mutability) (pointee : RigidTy)
    (val : Value) (borrows : List BorrowEntry) (isProtected : Bool)
    (huninhab : rigidTyIsUninhabited 16 pointee = true) :
    stepMirFn (retagPointeeRefBody rk mutability pointee)
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_uninhabited_ref_ub_step
    rk mutability pointee val borrows isProtected huninhab

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (rk : RetagKind) (mutability : Mutability) (usePhantom : Bool) :
    let pointee : RigidTy :=
      if usePhantom then .adt "core::marker::PhantomData" [.never]
      else .array .never 0
    let childPerm := annealRetagPerm (retagKindToAnnealMode rk) mutability true
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    rigidTyIsUninhabited 16 pointee = false ∧
    rigidTyIsZeroSized 16 pointee = true ∧
    (∃ s' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability pointee) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) ∧
    (∃ s'' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability pointee) (retagZstScalarState true) =
        .step s'' ∧
      s''.memory = (retagZstScalarState true).memory ∧
      get? s''.frame.locals 2 = some (.init (.scalar ⟨8, 8⟩))) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_inhabited_never_container_zst_step
    rk mutability usePhantom

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    (∃ s₁ s₂ s₃ : MachineState,
      stepMirFn bodyLInhabited initLInhabited = .step s₁ ∧
      s₁.memory.borrows = [entry 1 .frozen] ∧
      stepMirFn bodyLInhabited s₁ = .step s₂ ∧
      s₂.memory.borrows = [entry 2 .frozen (some 1) (some 1), entry 1 .frozen] ∧
      s₂.memory.activeProtectors = [1] ∧
      stepMirFn bodyLInhabited s₂ = .step s₃ ∧
      s₃.memory = s₂.memory ∧
      TreeBorrowsRel s₃.memory.borrows s₃.memory.activeProtectors
        (basedNormalTree s₃.memory.borrows s₃.memory.activeProtectors)) ∧
    stepMirFn bodyLNever (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyLNever (initLUninhabited true) = .fail .ub ∧
    stepMirFn bodyLNeverArr1 (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyLNeverArr1 (initLUninhabited true) = .fail .ub :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_uninhabited_ref_retag_ub_vs_inhabited_never_zst_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    ∃ s₁ s₂ s₃ s₄ s₅ s₆ : MachineState,
      stepMirFn bodyM initM = .step s₁ ∧
      stepMirFn bodyM s₁ = .step s₂ ∧
      stepMirFn bodyM s₂ = .step s₃ ∧
      stepMirFn bodyM s₃ = .step s₄ ∧
      s₄.memory.borrows =
        [entry 3 .cell (some 2) (some 1), entry 2 .cell (some 1), entry 1 .unique] ∧
      s₄.memory.activeProtectors = [1] ∧
      borrowListChain3ProtInv s₄.memory.borrows [1] = true ∧
      stepMirFn bodyM s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 3 .cell (some 2) (some 1), entry 2 .cell (some 1), entry 1 .disabled] ∧
      treeBorrowsChain3Inv .cell .cell .disabled = false ∧
      borrowListChain3ProtInv s₅.memory.borrows [1] = true ∧
      ((basedNormalTree s₄.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₅.memory.borrows [1]
        ((basedNormalTree s₄.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).tree ∧
      stepMirFn bodyM s₅ = .step s₆ ∧
      s₆.memory.borrows = s₅.memory.borrows ∧
      ((basedNormalTree s₅.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).status = .Completed ∧
      TreeBorrowsRel s₆.memory.borrows [1]
        ((basedNormalTree s₅.memory.borrows [1]).performAccess 3 .Write
          .VisitChildrenOfAccessed).tree ∧
      stepMirFn bodyM s₆ = .fail .ub ∧
      ((basedNormalTree s₆.memory.borrows [1]).performAccess 0 .Read
          .VisitChildrenOfAccessed).status =
        .TransitionError 2 (.ChildAccessForbidden .Disabled) :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_protected_cell_chain_under_disabled_root_real_steps

open LeanMiriSpec.Correspondence.SimLM3_3 in
example
    (rk : RetagKind) (mutability : Mutability) (useMaybeUninit : Bool)
    (val : Value) (borrows : List BorrowEntry) (isProtected : Bool) :
    let zstPointee : RigidTy :=
      if useMaybeUninit then .adt "core::mem::MaybeUninit" [.never]
      else .adt "core::cell::UnsafeCell" [.tuple []]
    let childPerm :=
      annealRetagPerm (retagKindToAnnealMode rk) mutability useMaybeUninit
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    rigidTyIsUninhabited 16 zstPointee = false ∧
    rigidTyIsZeroSized 16 zstPointee = true ∧
    rigidTyIsFreeze 16 zstPointee = useMaybeUninit ∧
    rigidTyIsUninhabited 16 (.adt "core::cell::RefCell" [.tuple []]) = false ∧
    rigidTyIsZeroSized 16 (.adt "core::cell::RefCell" [.tuple []]) = false ∧
    rigidTyIsFreeze 16 (.adt "core::cell::RefCell" [.tuple []]) = false ∧
    (∃ s' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability zstPointee) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 childPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) ∧
    (∃ s'' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability zstPointee) (retagZstScalarState true) =
        .step s'' ∧
      s''.memory = (retagZstScalarState true).memory ∧
      get? s''.frame.locals 2 = some (.init (.scalar ⟨8, 8⟩))) ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::UnsafeCell" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::Cell" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::cell::RefCell" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub ∧
    stepMirFn (retagPointeeRefBody rk mutability (.adt "core::mem::ManuallyDrop" [.never]))
      (simState [.uninit, .init .unit, .init val] borrows isProtected) = .fail .ub :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_unsafecell_zst_vs_never_step
    rk mutability useMaybeUninit val borrows isProtected

open LeanMiriSpec.Correspondence.SimLM3_3 in
example (rk : RetagKind) (mutability : Mutability) :
    let phantomCellPt : RigidTy :=
      .adt "core::marker::PhantomData" [.adt "core::cell::UnsafeCell" [.uint .u64]]
    let cellU64Pt : RigidTy := .adt "core::cell::Cell" [.uint .u64]
    let mode := retagKindToAnnealMode rk
    let phPerm := annealRetagPerm mode mutability true
    let cellPerm := annealRetagPerm mode mutability false
    let childProt := match rk with | .fnEntry => some 2 | _ => none
    let activeProts := match rk with | .fnEntry => [2, 1] | _ => [1]
    rigidTyIsFreeze 16 phantomCellPt = true ∧
    rigidTyIsZeroSized 16 phantomCellPt = true ∧
    rigidTyIsFreeze 16 cellU64Pt = false ∧
    fnEntryRetagPerm mutability cellU64Pt = annealRetagPerm .fnEntry mutability false ∧
    retagPerm rk mutability cellU64Pt = cellPerm ∧
    (∃ s' : MachineState,
      stepMirFn (retagPointeeRefBody rk mutability phantomCellPt) retagZstRefState = .step s' ∧
      get? s'.frame.locals 2 = some (.init (.ptr ⟨3, 0⟩ 8)) ∧
      s'.memory.borrows =
        [entry 3 phPerm (some 1) childProt,
          entry 2 .unique none (some 1),
          entry 1 .unique] ∧
      s'.memory.activeProtectors = activeProts ∧
      TreeBorrowsRel s'.memory.borrows s'.memory.activeProtectors
        (basedNormalTree s'.memory.borrows s'.memory.activeProtectors)) :=
  @LeanMiriSpec.Correspondence.SimLM3_3.sim_lm3_3_retag_phantom_unsafecell_vs_cell_step
    rk mutability

open LeanMiriSpec.Correspondence.SimLM3_3 LeanMiriSpec.Correspondence.WitnessLM3_3 in
example :
    (∃ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : MachineState,
      stepMirFn bodyN initN = .step s₁ ∧
      stepMirFn bodyN s₁ = .step s₂ ∧
      stepMirFn bodyN s₂ = .step s₃ ∧
      s₃.memory.borrows = [entry 2 .unique (some 1) (some 1), entry 1 .unique] ∧
      stepMirFn bodyN s₃ = .step s₄ ∧
      stepMirFn bodyN s₄ = .step s₅ ∧
      s₅.memory.borrows =
        [entry 4 .reservedIM (some 3),
         entry 3 .reservedIM,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      stepMirFn bodyN s₅ = .step s₆ ∧
      stepMirFn bodyN s₆ = .step s₇ ∧
      stepMirFn bodyN s₇ = .step s₈ ∧
      s₈.memory.borrows =
        [{ tag := 6, targetLocal := 6, targetProjection := .nil, perm := .cell,
           protector := none, parentTag := none },
         { tag := 5, targetLocal := 4, targetProjection := .nil, perm := .frozen,
           protector := none, parentTag := none },
         entry 4 .reservedIM (some 3),
         entry 3 .reservedIM,
         entry 2 .unique (some 1) (some 1),
         entry 1 .unique] ∧
      TreeBorrowsRel s₈.memory.borrows s₈.memory.activeProtectors
        (basedNormalTree s₈.memory.borrows s₈.memory.activeProtectors)) ∧
    stepMirFn bodyNUnsafeCellNever (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyNUnsafeCellNever (initLUninhabited true) = .fail .ub ∧
    stepMirFn bodyNRefCellNever (initLUninhabited false) = .fail .ub ∧
    stepMirFn bodyNRefCellNever (initLUninhabited true) = .fail .ub :=
  @LeanMiriSpec.Correspondence.WitnessLM3_3.wit_lm3_3_wrapper_zst_freeze_and_uninhabited_cell_real_steps

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
  hooksAccessTag
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
  basedAccessTag
  annealTableAccessUB
  annealTableAfterAccess
  treeBorrowsAncestorInv
  treeBorrowsChain3Inv
  treeBorrowsBranch3Inv
  treeBorrowsProtAncestorInv
  treeBorrowsChain3ProtInv
  treeBorrowsBranch3ProtInv
  borrowListChain3ProtInv
  borrowListBranch3ProtInv
  SimLM3_3.stmt
  SimLM3_3.loc
  SimLM3_3.deref
  SimLM3_3.u64T
  SimLM3_3.u32T
  SimLM3_3.unsafeCellU32T
  SimLM3_3.declOf
  SimLM3_3.refMutDecl
  SimLM3_3.refDecl
  SimLM3_3.rawMutDecl
  SimLM3_3.cU64
  SimLM3_3.cU32
  SimLM3_3.scalarLayout
  SimLM3_3.witBody
  SimLM3_3.witInit
  SimLM3_3.entry
  SimLM3_3.StepTreeRel
  SimLM3_3.protOf
  SimLM3_3.activeOf
  SimLM3_3.simState
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
  SimLM3_3.childScalarRawState
  SimLM3_3.unitT
  SimLM3_3.retagZstRefBody
  SimLM3_3.retagZstRefState
  SimLM3_3.retagZstScalarState
  SimLM3_3.phantomU64T
  SimLM3_3.retagPhantomRefBody
  SimLM3_3.zstDerefReborrowBody
  SimLM3_3.zstDerefReborrowState
  SimLM3_3.retagPointeeRefBody
  WitnessLM3_3.bodyA
  WitnessLM3_3.initA
  WitnessLM3_3.bodyB
  WitnessLM3_3.initBC
  WitnessLM3_3.bodyC
  WitnessLM3_3.bodyD
  WitnessLM3_3.initD
  WitnessLM3_3.bodyE
  WitnessLM3_3.bodyF
  WitnessLM3_3.initF
  WitnessLM3_3.calleeG
  WitnessLM3_3.callerG
  WitnessLM3_3.initG
  WitnessLM3_3.bodyH
  WitnessLM3_3.initH
  WitnessLM3_3.bodyI
  WitnessLM3_3.initI
  WitnessLM3_3.initINullAt5
  WitnessLM3_3.tupleU64U64T
  WitnessLM3_3.fieldU64
  WitnessLM3_3.entryProj
  WitnessLM3_3.bodyJDisjoint
  WitnessLM3_3.bodyJOverlap
  WitnessLM3_3.initJ
  WitnessLM3_3.bodyK
  WitnessLM3_3.initK
  WitnessLM3_3.bodyLInhabited
  WitnessLM3_3.initLInhabited
  WitnessLM3_3.bodyLNever
  WitnessLM3_3.bodyLNeverArr1
  WitnessLM3_3.initLUninhabited
  WitnessLM3_3.bodyM
  WitnessLM3_3.initM
  WitnessLM3_3.unsafeCellUnitT
  WitnessLM3_3.phantomUnsafeCellU32T
  WitnessLM3_3.cellU32T
  WitnessLM3_3.bodyN
  WitnessLM3_3.initN
  WitnessLM3_3.bodyNUnsafeCellNever
  WitnessLM3_3.bodyNRefCellNever
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
  retagPointerValue_8byte_reference_simulation
  borrowTree_performNormalAccessAt_simulation
  borrowTree_performBorrowAccessRange_simulation
  machineMemoryHooks_fresh_root_write_simulation
  machineMemoryHooks_fresh_root_read_simulation
  machineMemoryHooks_beforeMemoryRead_simulation
  machineMemoryHooks_beforeMemoryWrite_simulation
  borrowTree_deallocateBorrowRange_simulation
  machineMemoryHooks_beforeMemoryDeallocation_simulation
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
  freezeTreeBorrowsOnReadAtProj_length
  invalidateTreeBorrowsAtProj_length
  treeBorrowNodeAccess_of_isUB_false
  freezeTreeBorrowsOnReadAtProj_locationState_simulation
  invalidateTreeBorrowsAtProj_locationState_simulation
  byteRangesOverlapBool_iff
  borrowEntryOverlapsWrite_iff
  borrowEntryReadUB_of_disjoint
  updateBorrowPermOnReadAtProj_of_disjoint
  updateBorrowPermTreeAtProj_of_foreign_disjoint
  hasTreeReadUB_of_all_disjoint
  hasTreeReadUB_disjoint_tail
  freezeTreeBorrowsOnReadAtProj_of_all_disjoint
  freezeTreeBorrowsOnReadAtProj_disjoint_tail
  hasProtectedTreeWriteConflict_of_all_disjoint
  invalidateTreeBorrowsAtProj_of_all_foreign_disjoint
  invalidateTreeBorrowsAtProj_disjoint_tail
  basedNormalTree_performAccess_singleton_simulation
  basedNormalTree_performAccess_parent_child_simulation
  basedNormalTree_performAccess_siblings_simulation
  basedNormalTree_performAccess_three_level_chain_simulation
  basedNormalTree_performAccess_branching_children_simulation
  treeBorrowsAncestorInv_imp_prot_false
  treeBorrowsProtAncestorInv_retag_init
  treeBorrowsProtAncestorInv_release_protectors
  basedNormalTree_performAccess_three_level_chain_prot_simulation
  basedNormalTree_performAccess_branching_children_prot_simulation
  rangedNormalTree_performAccessRange_simulation
  SimLM3_3.sim_lm3_3_child_write_step
  SimLM3_3.sim_lm3_3_child_read_step
  SimLM3_3.sim_lm3_3_foreign_write_step
  SimLM3_3.sim_lm3_3_foreign_read_step
  SimLM3_3.sim_lm3_3_reborrow_child_write_step
  SimLM3_3.sim_lm3_3_reborrow_parent_write_invalidates_child_step
  SimLM3_3.sim_lm3_3_retag_ref_step
  SimLM3_3.sim_lm3_3_retag_raw_step
  SimLM3_3.sim_lm3_3_retag_raw_scalar_step
  SimLM3_3.sim_lm3_3_retag_zst_ref_step
  SimLM3_3.sim_lm3_3_retag_zst_scalar_step
  SimLM3_3.sim_lm3_3_retag_phantom_ref_step
  SimLM3_3.sim_lm3_3_zst_deref_reborrow_step
  SimLM3_3.sim_lm3_3_retag_uninhabited_ref_ub_step
  SimLM3_3.sim_lm3_3_retag_inhabited_never_container_zst_step
  SimLM3_3.sim_lm3_3_retag_unsafecell_zst_vs_never_step
  SimLM3_3.sim_lm3_3_retag_phantom_unsafecell_vs_cell_step
  SimLM3_3.stateRelLM3_2Tree_treeBorrowsRel
  SimLM3_3.sim_lm3_3_interpreter_deref_read_step
  SimLM3_3.sim_lm3_3_interpreter_deref_write_step
  SimLM3_3.sim_lm3_3_interpreter_reborrow_step
  WitnessLM3_3.wit_lm3_3_reborrow_hierarchy_real_steps
  WitnessLM3_3.wit_lm3_3_protected_conflict_ub_real_steps
  WitnessLM3_3.wit_lm3_3_protected_unique_foreign_read_ub_real_steps
  WitnessLM3_3.wit_lm3_3_unsafe_cell_vs_freeze_real_steps
  WitnessLM3_3.wit_lm3_3_reservedIM_lifecycle_real_steps
  WitnessLM3_3.wit_lm3_3_cell_reborrow_preserves_unique_real_steps
  WitnessLM3_3.wit_lm3_3_protector_release_on_return_real_steps
  WitnessLM3_3.wit_lm3_3_non_fnEntry_retag_and_raw_retag_real_steps
  WitnessLM3_3.wit_lm3_3_zst_retag_skips_read_and_dangling_scalar_real_steps
  WitnessLM3_3.wit_lm3_3_subprojection_disjoint_vs_overlapping_real_steps
  WitnessLM3_3.wit_lm3_3_zst_deref_reborrow_and_phantom_retag_real_steps
  WitnessLM3_3.wit_lm3_3_uninhabited_ref_retag_ub_vs_inhabited_never_zst_real_steps
  WitnessLM3_3.wit_lm3_3_protected_cell_chain_under_disabled_root_real_steps
  WitnessLM3_3.wit_lm3_3_wrapper_zst_freeze_and_uninhabited_cell_real_steps

end StatementPins

-- Exhaustively verify standard axioms across all imported `LeanMiriSpec.*` and
-- `Miri.*` modules AND every constant elaborated in `LeanMiriSpec.Audit` itself.
#assert_all_leanmirispec_and_miri_standard_axioms

end LeanMiriSpec.Audit
