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
import LeanMiriSpec.Correspondence.UnionLM2_4
import LeanMiriSpec.Correspondence.SimLM2_4
import LeanMiriSpec.Correspondence.WitLM2_4

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
  that memory in lockstep;
* the `LM-2.2` theorems: `ValidStructLayout`, `writeField_preserves_other_fields_and_padding`,
  `writeScalarPairField_preserves_other_fields_and_padding`, `StructMemPlaceRel`
  (unpadded aggregates project to the unchanged base `MemPlaceRel` via
  `toMemPlaceRel`; padded ones are related only by `StateRelLM2_2`),
  `evalProjection_nested_field_read_simulation`,
  `evalOperand_nested_substruct_read_simulation`,
  `evalOperand_nested_scalar_wrap_read_simulation`,
  `evalRvalue_aggregate_tuple_struct_simulation`,
  `step_assign_nested_field_write_simulation`,
  `step_assign_nested_substruct_write_simulation`,
  `step_assign_nested_scalar_wrap_write_simulation`,
  `step_assign_use_struct_lm2_2_simulation`,
  `step_assign_use_memory_struct_lm2_2_simulation`,
  `step_stmt_lm2_2_simulation`, `step_terminator_goto_lm2_2_simulation`,
  `step_terminator_return_lm2_2_simulation`,
  `step_two_stmts_lm2_2_simulation`, and `step_stmts_lm2_2_simulation`, together
  with the fourteen `WitLM2_2` concrete execution witnesses.
* the `LM-2.4` theorems: the union aggregate, field read, and whole-union copy/move
  fresh and in-place overwrite steps (`step_union_aggregate_simulation`,
  `step_union_aggregate_overwrite_simulation`, `step_union_field_read_simulation`,
  `union_whole_copy_initMask_preservation_simulation`,
  `union_whole_move_initMask_preservation_simulation`,
  `step_union_whole_copy_or_move_overwrite_simulation`), the composed
  `union_field_write_read_same_field_simulation`, the uninitialized-byte read
  `union_uninit_bytes_read_ub_simulation`, the `I-11` mask and allocation copy
  certifications (`unionPrefixMask_vendoredCopy`, `union_copy_alloc_spec`,
  `union_copy_self_overlap_err`, `union_copy_uninit_alloc_spec`,
  `array_copy_alloc_spec`), the `Subslice` projections, operands, fresh/in-place
  assignments, and element writes (`evalProjection_subslice_simulation`,
  `evalProjection_nested_subslice_simulation`, `evalSubsliceOperand_simulation`,
  `step_subslice_assign_simulation`, `step_subslice_assign_overwrite_simulation`,
  `step_subslice_elem_write_characterization`), `Rvalue.Repeat` on union fields
  (`step_repeat_union_field_simulation`), `StorageLive`/`StorageDead` on
  `StateRelLM2_4` (`step_storageLive_LM2_4_simulation`,
  `step_storageDead_LM2_4_simulation`), the semantic boundaries
  (`evalProjection_subslice_inverted_divergence`,
  `evalProjection_subslice_fromEndFalse_oob_divergence`,
  `evalRvalue_union_aggregate_activeField_ignored`,
  `step_union_field_write_uninit_divergence`,
  `step_union_type_punning_read_divergence`,
  `step_union_nonzero_field_write_divergence`,
  `step_union_self_copy_overlap_divergence`,
  `step_union_copy_indirect_uninit_divergence`,
  `step_union_aggregate_smaller_overwrite_divergence`), the conservative
  extension `step_LM2_4_eq_of_bodyFree`, and the `WitLM2_4` witnesses.
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
  valueLeafBytes
  annealFieldLayout
  annealMutablePlaceHooks
  annealWriteProjectedLocalImmediate
  annealAggregateHooks
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
  evalRvalue_unionFieldRead
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
  evalRvalue_union_aggregate_activeField_ignored
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
  step_union_field_write_uninit_divergence
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
  Witness.lm24_field_write_uninit_divergence
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
  step_union_type_punning_read_divergence
  step_union_nonzero_field_write_divergence
  evalSubsliceOperand_zero_uninit_indirect_characterization
  annealMemCopyOp_freshArray
  step_subslice_assign_simulation
  Witness.lm24ConstU32
  Witness.lm24AggU32Stmt
  Witness.lm24Field1WriteU32Stmt
  Witness.lm24_constU32_wt
  Witness.lm24UU32Slot
  Witness.lm24_bb6_anneal₁
  Witness.lm24_type_punning_read_divergence
  Witness.lm24_bb7_anneal₁
  Witness.lm24_nonzero_field_write_divergence
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
  annealForceAllocation
  annealForceAllocation_of_ok
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
  annealForceAllocation_dead_err
  annealForceAllocation_indirect_eq
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
  step_subslice_elem_write_characterization
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
/-! ### LM-2.2 statement & witness pins -/

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
        annealReadImmediate) m) :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.machine
        decl.ty body.layouts fields paths rootVal mp ∧
      ∃ tf lay,
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m).1.stack.frames =
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m₀ =
          (m_err, .error (.undefinedBehavior msg))) ∨
    (∃ s₁ m₁,
      stepMirFn body s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m₀ =
        (m₁, .ok true) ∧
      StateRelLM2_2 body env stEnv₁ k₁ s₁ m₁ ∧
      StepRelLM2_2 body env stEnv₂ k₂ m₁
        (stepMirFn body s₁)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m₁)) :=
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
      (runMiriBounded Witness.lm22PairBody 12 Witness.lm22PairMiriInit) = some 0x99AABBCC :=
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
      (runMiriBounded Witness.lm22UnpaddedBody 6 Witness.lm22UnpaddedMiriInit) = some 77 :=
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
      (runMiriBounded Witness.lm22PaddedBody 9 Witness.lm22PaddedMiriInit) = some 99 :=
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
      (runMiriBounded Witness.lm22NestedBody 15 Witness.lm22NestedMiriInit) = some 0xBEEF) :=
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
    annealWriteImmediate val ⟨.local 0 dstIdx none id0, dstLay⟩ m =
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
        runMiriBounded body stmts.length m = .error m_err (.undefinedBehavior msg)) ∨
    (∃ s' m',
      runAnnealBounded body stmts.length s = .running s' ∧
      runMiriBounded body stmts.length m = .running m' ∧
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
      (runMiriBounded Witness.lm22ReassignBody 13 Witness.lm22ReassignMiriInit) =
        some 0xAABBCCDD :=
  Witness.lm22Reassign_full_trace_and_returns_agree

example :
    ∃ s' m',
      runAnnealBounded Witness.lm22ReassignBody 12
        (initMachineState Witness.lm22ReassignBody []) = .running s' ∧
      runMiriBounded Witness.lm22ReassignBody 12 Witness.lm22ReassignMiriInit = .running m' ∧
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
        annealReadImmediate) m) :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      (runMiriBounded Witness.lm22SubStructBody 15 Witness.lm22SubStructMiriInit) = some 0x7788 :=
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
      (runMiriBounded Witness.lm22LargeBody 6 Witness.lm22LargeMiriInit) = some 999) :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      (runMiriBounded Witness.lm22LiveRetBody 8 Witness.lm22LiveRetMiriInit) = some 99 :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
        annealReadImmediate) m) :=
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      (runMiriBounded Witness.lm22MemMoveBody 16 Witness.lm22MemMoveMiriInit) = some 0x3344 :=
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
      (runMiriBounded Witness.lm22ScalarWrapSubBody 16 Witness.lm22ScalarWrapSubMiriInit) =
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
      (runMiriBounded Witness.lm22Realistic80Body 10 Witness.lm22Realistic80MiriInit) =
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
      (runMiriBounded Witness.lm22PairWrapBody 14 Witness.lm22PairWrapMiriInit) =
        some 0x13579BDF :=
  Witness.lm22PairWrap_full_trace_and_returns_agree

example :
    runAnnealBounded Witness.lm22MemMoveUbBody 8
        (initMachineState Witness.lm22MemMoveUbBody []) = .faulted .ub ∧
    ∃ m_err msg,
      runMiriBounded Witness.lm22MemMoveUbBody 8 Witness.lm22MemMoveUbMiriInit =
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
      (annealStepHooks Witness.lm22SuperOuterBody.localDecls
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
      (runMiriBounded Witness.lm22SuperOuterBody 9
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
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
      runMiriBounded Witness.lm22StructRetBody 6 Witness.lm22StructRetMiriInit =
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
      (runMiriBounded Witness.lm22SelfMoveBody 9 Witness.lm22SelfMoveMiriInit) =
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
          (annealStepHooks Witness.lm22SelfCopyBody.localDecls
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

example
    (localDecls : List MirAst.LocalDecl)
    (layouts : LayoutTable)
    (mbody : Miri.MIR.Body)
    (hfree : BodyFreeOfLM2_4 localDecls layouts mbody)
    (m : AnnealStepState)
    (hbody : ∀ frame, m.stack.currentFrame? = some frame → frame.body = mbody) :
    Miri.Interpreter.Step.step (annealStepHooksLM2_4 localDecls layouts) () m =
      Miri.Interpreter.Step.step (annealStepHooks localDecls layouts) () m :=
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
    {op : MirAst.Operand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some 0)) [op]), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) 0 = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    {f0Ty : Ty}
    (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S) :
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
        get? s'.frame.locals u = some (.init (.aggregate 0 [.scalar sc])) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ j, j ≠ u →
          IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
        (∀ j, j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 1 (m', .ok true)) :=
  step_union_aggregate_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_u hwt hfl hfl_sized hu_uninit hu_imm hprim0 hop hf0_le

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
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r) :
    (j = 0 → fty = f0Ty →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m) ∧
      (∀ s', stepMirFn body s = .step s' →
        get? s'.frame.locals r = some (.init (.scalar sc))) ∧
      (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m).1.machine =
        m.machine) ∧
    (1 ≤ j → sc.sizeBytes < w → w ≤ S →
      stepMirFn body s = .fail .ub ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) :=
  step_union_field_read_simulation hstate hnodup hphase hbb hstmt hdecl_r hr_ty hdecl_u hprim hw hsz hwt hfields hj hu_slot hu_mls hmem hr_imm

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
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hj1 : 1 ≤ j)
    (hkw : sc.sizeBytes < w)
    (hwS : w ≤ S) :
    stepMirFn body s = .fail .ub ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) :=
  union_uninit_bytes_read_ub_simulation hstate hnodup hphase hbb hstmt hdecl_r hr_ty hdecl_u hprim hw hsz hwt hfields hj hu_slot hu_mls hmem hr_imm hj1 hkw hwS

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
    {op : MirAst.Operand}
    {isMove : Bool}
    {span₁ span₂ : String}
    {f0Ty : Ty}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt₁ : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some 0)) [op]), span₁⟩)
    (hstmt₂ : get? bb.statements (s.frame.stmtIdx + 1) =
      some ⟨.assign ⟨r, .nil⟩ (.use (unionFieldReadOperand isMove u 0 f0Ty)), span₂⟩)
    {uDecl rDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hdecl_r : get? body.localDecls r = some rDecl)
    (hr_ty : rDecl.ty = f0Ty)
    {S : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) 0 = some fl)
    (hfl_sized : fl.layout.isSized = true)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S) :
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
  union_field_write_read_same_field_simulation hstate hnodup hcanRes hphase hbb hstmt₁ hstmt₂ hdecl_u hdecl_r hr_ty hwt hfl hfl_sized hu_uninit hu_imm hr_imm hprim0 hop hf0_le

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
    {S : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
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
      get? s'.frame.locals w = some (.init (.aggregate 0 [.scalar sc])) ∧
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
  union_whole_copy_initMask_preservation_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_w hdecl_u hty hwt hu_slot hu_mls hmem hw_uninit hw_imm

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
    {S : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
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
      get? s'.frame.locals w = some (.init (.aggregate 0 [.scalar sc])) ∧
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
  union_whole_move_initMask_preservation_simulation hstate hnodup hcanRes hphase hbb hstmt hdecl_w hdecl_u hty hwt hu_slot hu_mls hmem hw_uninit hw_imm

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

example
    (locals : List LocalSlot)
    (mem : Memory)
    (localDecls : List MirAst.LocalDecl)
    (layouts : LayoutTable)
    (d : DefPath)
    (v f : Nat)
    (ops : List MirAst.Operand) :
    evalRvalue locals (.aggregate (.adt d v (some f)) ops) mem localDecls layouts =
      evalRvalue locals (.aggregate (.adt d v (some 0)) ops) mem localDecls layouts :=
  evalRvalue_union_aggregate_activeField_ignored locals mem localDecls layouts d v f ops

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
    {f0Ty : Ty}
    {op : MirAst.Operand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field 0 f0Ty]⟩ (.use op), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty) :
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
        get? s'.frame.locals u = some (.init (.aggregate 0 [.scalar sc'])) ∧
        (∀ j, j ≠ u → get? s'.frame.locals j = get? s.frame.locals j) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc' mp ∧
        LiveAllocsNodup m'.machine ∧
        (∀ tf, m.stack.frames = #[tf] → ∀ j,
          IsImmediateFrameLocal tf j → IsImmediateFrameLocal tf' j) ∧
        s'.frame.blockIdx = s.frame.blockIdx ∧ s'.frame.stmtIdx = s.frame.stmtIdx + 1 ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_union_field_write_simulation hstate hnodup hphase hbb hstmt hdecl_u hwt hu_slot hu_mls hmem hop

example
    {body : CapturedMir}
    {s : MachineState}
    {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hcanRes : CanReserveAllocId m.machine.memory)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    {u : Local}
    {f0Ty : Ty}
    {c : ConstOperand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field 0 f0Ty]⟩ (.use (.constant c)), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hu_uninit : get? s.frame.locals u = some .uninit)
    (hu_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame u)
    {sc : MirAst.ScalarInt}
    (hval : c.val = .scalar (.int sc))
    (hcty : c.ty = f0Ty)
    (hprim0 : IsPrimScalarTy f0Ty)
    (hsz : ValidScalarBytes sc.sizeBytes)
    (hcan : sc.bits < scalarModulus sc.sizeBytes)
    (hk_le : sc.sizeBytes ≤ S) :
    stepMirFn body s = .fail .ub ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv) (allocId : Miri.Memory.AllocId)
      (la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c', tf'.locals[u]? = some ⟨.live (.indirect mp), c'⟩) ∧
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId ∧
      (allocId, la) ∈ m'.machine.memory.live.toList ∧
      la.allocation.initializationMask = unionPrefixMask S sc.sizeBytes ∧
      (unionAllocRaw la.allocation).extract 0 sc.sizeBytes = allocLeBytes sc.bits sc.sizeBytes :=
  step_union_field_write_uninit_divergence hstate hcanRes hphase hbb hstmt hdecl_u hwt hu_uninit hu_imm hval hcty hprim0 hsz hcan hk_le

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
    stepMirFn Witness.lm24Body (Witness.lm24InitAnneal 4) = .fail .ub ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv) (allocId : Miri.Memory.AllocId)
      (la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 4) = (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c', tf'.locals[1]? = some ⟨.live (.indirect mp), c'⟩) ∧
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId ∧
      (allocId, la) ∈ m'.machine.memory.live.toList ∧
      la.allocation.initializationMask = unionPrefixMask 4 1 ∧
      (unionAllocRaw la.allocation).extract 0 1 = allocLeBytes 7 1 :=
  Witness.lm24_field_write_uninit_divergence

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
      evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub ∧
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
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil =
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
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub ∧
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
    (hdecl_u : get? body.localDecls u = some uDecl)
    (hprim : IsPrimScalarTy fty)
    {w : Nat}
    (hw : ValidScalarBytes w)
    (hsz : (translateTy fty body.layouts).layout.size = translateSizeBytes w)
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj : j < n)
    {f0Ty : Ty}
    {sc : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hr_live : get? s.frame.locals r ≠ some .dead)
    (hr_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame r)
    (hj1 : 1 ≤ j)
    (hw_le : w ≤ sc.sizeBytes) :
    stepMirFn body s = .fail .ub ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (msc_w : Miri.Memory.ScalarInt),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.machine = m.machine ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel ⟨sc.bits % scalarModulus w, w⟩ msc_w ∧
      ∃ c, tf'.locals[r]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc_w))), c⟩ :=
  step_union_type_punning_read_divergence hstate hnodup hphase hbb hstmt hdecl_r hdecl_u hprim hw
    hsz hwt hfields hj hu_slot hu_mls hmem hr_live hr_imm hj1 hw_le

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
    {c : ConstOperand}
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, [.field j fty]⟩ (.use (.constant c)), span⟩)
    {uDecl : MirAst.LocalDecl}
    (hdecl_u : get? body.localDecls u = some uDecl)
    {S n : Nat}
    (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n)
    (hj1 : 1 ≤ j)
    (hj : j < n)
    {f0Ty : Ty}
    {sc sc' : MirAst.ScalarInt}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c', topFrame.locals[u]? = some ⟨.live (.indirect mp), c'⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp)
    (hval : c.val = .scalar (.int sc'))
    (hcty : c.ty = fty)
    (hprim : IsPrimScalarTy fty)
    (hsz : ValidScalarBytes sc'.sizeBytes)
    (hcan : sc'.bits < scalarModulus sc'.sizeBytes)
    (hk'_le : sc'.sizeBytes ≤ S) :
    (∃ (s' : MachineState) (fields' : List Value),
      stepMirFn body s = .step s' ∧
      get? s'.frame.locals u = some (.init (.aggregate 0 fields')) ∧
      get? fields' 0 = some (.scalar sc) ∧
      get? fields' j = some (.scalar sc')) ∧
    ∃ (m' : AnnealStepState)
      (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (allocId : Miri.Memory.AllocId)
      (la' : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (∃ c', tf'.locals[u]? = some ⟨.live (.indirect mp), c'⟩) ∧
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId ∧
      (allocId, la') ∈ m'.machine.memory.live.toList ∧
      IsUnionPrefixMask S (max sc.sizeBytes sc'.sizeBytes) la'.allocation.initializationMask ∧
      (unionAllocRaw la'.allocation).extract 0 sc'.sizeBytes =
        allocLeBytes sc'.bits sc'.sizeBytes :=
  step_union_nonzero_field_write_divergence hstate hnodup hphase hbb hstmt hdecl_u hwt hfields hj1
    hj hu_slot hu_mls hmem hval hcty hprim hsz hcan hk'_le

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
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub ∧
          annealEvalOperandLM2_4 body.localDecls body.layouts (translateOperand op) known m =
            .error (.undefinedBehavior "access to uninitialized indirect place")
              { m with stack := ⟨#[topFrame']⟩ }) ∧
      (localAlloc.allocation.initializationMask =
          Miri.Memory.InitMask.new localAlloc.allocation.byteSize true →
        ∀ isMove fromEnd known,
          let op := subsliceReadOperand isMove arrIdx 0 0 fromEnd
          let arrLay := translateTy arrDecl.ty body.layouts
          let es := (translateTy { kind := elemKind, layoutIdx := 0 } body.layouts).layout.size
          evalOperand s.frame.locals op .nil s.memory.globals body.layouts .nil = .ub ∧
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
        (Witness.lm24AnnealState 6 1 [.uninit, Witness.lm24UU32Slot, .uninit, .uninit, .uninit]) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (∃ c, tf₂.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt msc_w))), c⟩) ∧
      msc_w.data = 0x04 ∧
      msc_w.size = Miri.ABI.Size.ofBytes 1 :=
  Witness.lm24_type_punning_read_divergence

example :
    ∃ (m₁ : AnnealStepState) (s₂ : MachineState) (fields' : List Value)
      (m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (mp : Miri.Interpreter.MemPlace AnnealProv) (allocId : Miri.Memory.AllocId)
      (la : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind),
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          (Witness.lm24InitMiri 7) = (m₁, .ok true) ∧
      StateRelLM2_4 Witness.lm24Body
        (Witness.lm24AnnealState 7 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) m₁ ∧
      stepMirFn Witness.lm24Body
        (Witness.lm24AnnealState 7 1 [.uninit, Witness.lm24USlot, .uninit, .uninit, .uninit]) = .step s₂ ∧
      get? s₂.frame.locals 1 = some (.init (.aggregate 0 fields')) ∧
      get? fields' 0 = some (.scalar ⟨5, 1⟩) ∧
      get? fields' 1 = some (.scalar ⟨0x01020304, 4⟩) ∧
      Miri.Interpreter.Step.step (annealStepHooksLM2_4 Witness.lm24Body.localDecls Witness.lm24Body.layouts) ()
          m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (∃ c, tf₂.locals[1]? = some ⟨.live (.indirect mp), c⟩) ∧
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some allocId ∧
      (allocId, la) ∈ m₂.machine.memory.live.toList ∧
      IsUnionPrefixMask 4 4 la.allocation.initializationMask ∧
      (unionAllocRaw la.allocation).extract 0 4 = allocLeBytes 0x01020304 4 :=
  Witness.lm24_nonzero_field_write_divergence

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
    annealForceAllocation localDecls layouts dest st = .ok forced st' :=
  annealForceAllocation_of_ok h

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
    annealForceAllocation body.localDecls body.layouts ⟨.local 0 idx none ident, lay⟩ m =
      .error (.undefinedBehavior "write to dead local") m :=
  annealForceAllocation_dead_err hframes hlt hdead ident lay

example
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} (hlt : idx < tf.locals.size)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hind : (tf.locals[idx]'hlt).value = .live (.indirect mp))
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout) :
    annealForceAllocation body.localDecls body.layouts ⟨.local 0 idx none ident, lay⟩ m =
      .ok ⟨mp, lay⟩ m :=
  annealForceAllocation_indirect_eq hframes hlt hind ident lay

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
    {S : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S) :
    ((get? s.frame.locals u = some .dead ∨
        (get? s.frame.locals u = some .uninit ∧
          ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf u)) →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ f0Ty sc mp_u,
      get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      get? s.frame.locals w = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ f0Ty sc mp_u f0Ty_old sc_old mp_w,
      w ≠ u →
      get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[u]? = some ⟨.live (.indirect mp_u), c⟩) →
      UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u →
      get? s.frame.locals w = some (.init (.aggregate 0 [.scalar sc_old])) →
      (∀ tf, m.stack.frames = #[tf] → ∃ c, tf.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) →
      UnionMemRel m.machine wDecl.ty body.layouts S f0Ty_old sc_old mp_w →
      ∃ (s' : MachineState) (m' : AnnealStepState)
        (tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
        stepMirFn body s = .step s' ∧
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        StateRelLM2_4 body s' m' ∧
        get? s'.frame.locals w = some (.init (.aggregate 0 [.scalar sc])) ∧
        get? s'.frame.locals u =
          (if isMove then some .uninit else some (.init (.aggregate 0 [.scalar sc]))) ∧
        m'.stack.frames = #[tf'] ∧
        (∃ c, tf'.locals[w]? = some ⟨.live (.indirect mp_w), c⟩) ∧
        UnionMemRel m'.machine wDecl.ty body.layouts S f0Ty sc mp_w ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_union_whole_copy_or_move_overwrite_simulation hstate hnodup hphase hbb hstmt hdecl_w hdecl_u
    hty hwt

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
    {S : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals u = some (.init (.aggregate 0 [.scalar sc]))) ∧
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
    (ident : Miri.Interpreter.LocalsIdentity) (lay : Miri.Interpreter.LocalLayout) :
    annealUnionAggregateField body.localDecls body.layouts ⟨.local 0 u none ident, lay⟩ 0 m =
      .error (.undefinedBehavior "write to dead local") m :=
  annealUnionAggregateField_dead_err hframes hlt hdead ident lay

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
      annealWriteImmediate (.scalar (.fromScalarInt msc')) ⟨.memory mp, destLay⟩
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
    {bb : BasicBlockData} {u : Local} {d : DefPath} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some 0)) [op]), span⟩)
    {uDecl : MirAst.LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) 0 = some fl)
    (hfl_sized : fl.layout.isSized = true)
    {f0Ty : Ty} (hprim0 : IsPrimScalarTy f0Ty)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op f0Ty)
    (hf0_le : (translateTy f0Ty body.layouts).layout.size.bytes.toNat ≤ S) :
    (get? s.frame.locals u = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (∀ f0Ty_old sc_old mp,
      get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc_old])) →
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
          get? s'.frame.locals u = some (.init (.aggregate 0 [.scalar sc])) ∧
          m'.stack.frames = #[tf'] ∧
          (∃ c, tf'.locals[u]? = some ⟨.live (.indirect mp), c⟩) ∧
          UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp ∧
          LiveAllocsNodup m'.machine ∧
          StepPreservesHighWater m 0 (m', .ok true))) :=
  step_union_aggregate_overwrite_simulation hstate hnodup hphase hbb hstmt hdecl_u hwt hfl
    hfl_sized hprim0 hop hf0_le

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRelLM2_4 body s m)
    (hnodup : LiveAllocsNodup m.machine)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {u : Local} {d : DefPath} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨u, .nil⟩ (.aggregate (.adt d 0 (some 0)) [op]), span⟩)
    {uDecl : MirAst.LocalDecl} (hdecl_u : get? body.localDecls u = some uDecl)
    {S : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    {fl : Miri.Interpreter.LocalLayout}
    (hfl : unionFieldLayoutOf body.layouts (translateTy uDecl.ty body.layouts) 0 = some fl)
    (hfl_sized : fl.layout.isSized = true)
    {f0Ty_old f0Ty : Ty} {sc_old : MirAst.ScalarInt} {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc_old])))
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
      .ok (.scalar sc) s.frame.locals) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals u = some (.init (.aggregate 0 [.scalar sc]))) ∧
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
  step_union_aggregate_smaller_overwrite_divergence hstate hnodup hphase hbb hstmt hdecl_u hwt hfl
    hfl_sized hu_slot hu_mls hprov hlive_old hmem_old hprim0 hop hlt_width hop_ok

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
      stepMirFn body s = .unsupported ∧
      ∃ (m' : AnnealStepState) (mp : Miri.Interpreter.MemPlace AnnealProv),
        Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        MemPlaceRel m'.machine arrDecl.ty body.layouts
          (some (.aggregate 0 (elems.set (fromIdx + off) (.scalar sc)))) mp ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 0 (m', .ok true)) :=
  step_subslice_elem_write_characterization hstate hnodup hphase hbb hstmt hdecl_arr hwf hcty hval
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
    {S n : Nat} (hwt : WellTypedUnionTy body.layouts uDecl.ty S)
    (hfields : (translateTy uDecl.ty body.layouts).layout.fields = .Union n) (hj : j < n)
    {f0Ty : Ty} {sc : MirAst.ScalarInt} {mp_u : Miri.Interpreter.MemPlace AnnealProv}
    (hu_slot : get? s.frame.locals u = some (.init (.aggregate 0 [.scalar sc])))
    (hu_mls : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∃ c, topFrame.locals[u]? = some ⟨.live (.indirect mp_u), c⟩)
    (hmem : UnionMemRel m.machine uDecl.ty body.layouts S f0Ty sc mp_u)
    (hf0_eq : f0Ty = { kind := elemKind, layoutIdx := 0 })
    (hbool : elemKind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : elemKind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    (1 ≤ j → sc.sizeBytes < w → w ≤ S →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (j = 0 → fty = f0Ty → get? s.frame.locals arrIdx = some .dead →
      StepRelLM2_4 body m (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooksLM2_4 body.localDecls body.layouts) () m)) ∧
    (j = 0 → fty = f0Ty →
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
        get? s'.frame.locals u = some (.init (.aggregate 0 [.scalar sc])) ∧
        m'.stack.frames = #[tf'] ∧
        MemPlaceRel m'.machine arrDecl.ty body.layouts
          (some (.aggregate 0 (List.replicate count (.scalar sc)))) mp_arr ∧
        UnionMemRel m'.machine uDecl.ty body.layouts S f0Ty sc mp_u ∧
        LiveAllocsNodup m'.machine ∧
        StepPreservesHighWater m 1 (m', .ok true)) :=
  step_repeat_union_field_simulation hstate hnodup hphase hbb hstmt hdecl_arr hdecl_u hwf hprim hw
    hsz hwt hfields hj hu_slot hu_mls hmem hf0_eq hbool hchar

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
      get? s₂.frame.locals 1 = some (.init (.aggregate 0 [.scalar ⟨0x77, 1⟩])) ∧
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
    ∃ (s_ovw : MachineState) (m_ovw m_elem : AnnealStepState)
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
        .unsupported ∧
      Miri.Interpreter.Step.step
          (annealStepHooksLM2_4 Witness.lm24A2SubsliceBody.localDecls
            Witness.lm24A2SubsliceBody.layouts) ()
          (Witness.lm24A2SubsliceMiri 2) = (m_elem, .ok true) ∧
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

end StatementPins

-- Exhaustively verify standard axioms across all imported `LeanMiriSpec.*` and
-- `Miri.*` modules AND every constant elaborated in `LeanMiriSpec.Audit` itself.
#assert_all_leanmirispec_and_miri_standard_axioms

end LeanMiriSpec.Audit
