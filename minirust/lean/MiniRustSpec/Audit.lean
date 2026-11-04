/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import MiniRustSpec.Anchors
import MiniRustSpec.Correspondence.Witness

/-!
# Axiom audit

`#assert_standard_axioms` fails the build unless each listed declaration
depends only on Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`); in particular on no `sorryAx` and no
`Lean.ofReduceBool` (which `native_decide` would introduce). It also logs the
axioms of each declaration, so `lake build MiniRustSpec.Audit` doubles as the
`#print axioms` receipt.

`#check_theorem_deps` (`checkTheoremDeps`) performs the same check on a group
of declarations and logs one summary line per group, tagged `[ANCHOR-AUDIT]`
(the anchors of the interpretation), `[SIMULATION-AUDIT]` (the
correspondence theorems and the lemmas they rest on), or `[WITNESS-AUDIT]`
(the concrete witnesses), ending in `sorry_free=true`. A group that depends on
`sorryAx` or on any other non-standard axiom fails the build instead.
-/

namespace MiniRustSpec.Audit

open Lean Elab Command

/-- Fail unless every listed declaration is distinct and depends only on the
standard axioms. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  let mut seen : Array Name := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if seen.contains n then
      throwError "duplicate declaration {n} in #assert_standard_axioms"
    seen := seen.push n
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    logInfo m!"{n} depends on axioms: {axs.toList}"

/-- `checkTheoremDeps`: fail unless every listed declaration is a distinct
`theorem` (`ConstantInfo.thmInfo`) that depends only on the standard axioms,
then log one line `<tag> decls=<n> axioms=<union> sorry_free=true`. -/
elab "#check_theorem_deps " tag:str ids:ident* : command => do
  let env ← getEnv
  let mut seen : Array Name := #[]
  let mut union : Array Name := #[]
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if seen.contains n then
      throwError "{tag.getString} duplicate declaration {n}"
    seen := seen.push n
    unless (env.find? n matches some (.thmInfo _)) do
      throwError "{tag.getString} {n} is not a theorem"
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      if a == ``sorryAx then
        throwError "{tag.getString} {n} depends on sorryAx"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{tag.getString} {n} depends on the non-standard axiom {a}"
      unless union.contains a do
        union := union.push a
  logInfo m!"{tag.getString} decls={ids.size} axioms={union.toList} sorry_free=true"

open MiniRustSpec.LibSpecr in
#assert_standard_axioms
  Nondet
  NdResult

#assert_standard_axioms MiniRustSpec.Gen.NdResult

open MiniRustSpec.Correspondence in
#assert_standard_axioms
  step_correspondence
  step_initBlock
  step_start
  initMachineState_startRel
  steps_ok_mono
  reaches_rel
  run_ret
  run_ret_from_start
  run_ub
  run_ub_from_start
  steps_error
  steps_error_from_start
  steps_outcome
  steps_outcome_from_start
  mirNoUB_safe
  mirNoUB_safe_from_start
  mirNoUB_progress
  mirNoUB_progress_from_start
  mirNoUB_diverges_steps_ok
  mirNoUB_diverges_from_start
  mirNoUB_diverges_rel_from_start
  mirCall_ret
  mirCall_ub
  mirCall_noUB
  mirCall_progress
  mirCall_diverges_steps_ok
  mirCall_diverges_rel
  mirCall_steps_error
  mirCall_outcome
  runA_sound
  runA_noUB
  faultsA_sound
  treeSafe_of_step_inv
  noRet_of_step_inv
  treeSafe_of_tau_inv
  noRet_of_tau_inv
  evalReturn_callee
  evalStatement_assign
  evalStatement_placeMention
  evalValue_operand
  evalValue_rvalue
  evalIntBinOp_spec
  evalIntBinOp_divExact
  evalUnOp_countOnes
  intBitAnd_one
  countOnesLoop_bounds
  evalStmt_assign
  evalStmt_placeMention
  evalOperand_frag
  evalRvalue_frag
  evalScalarBinOp_frag
  signedOverflowAdd_eq
  signedOverflowSub_eq
  signedOverflowMul_eq
  evalSignedDiv_spec
  evalSignedRem_spec
  shift_offset_eq
  unchecked_shift_oob_iff
  shiftLeftBits_intFromBits
  shiftRightUnsigned_intFromBits
  arithmeticShrBits_intFromBits
  bitwiseAndBits_intFromBits
  bitwiseOrBits_intFromBits
  bitwiseXorBits_intFromBits
  rvalueOk_binaryOp
  castBits_eq_toNat
  switch_lookup
  translateFn_spec
  translateFn_start
  evalValue_operandT
  evalValue_rvalueB
  evalStatement_assign_of
  evalStatement_assignB
  evalOperand_fragT
  evalRvalue_fragB
  evalStmt_assign_of
  evalStmt_assignB
  evalScalarBinOp_rel_int
  evalScalarBinOp_rel_bool
  signedLt_eq
  signedLe_eq
  evalUnaryNot_bool
  evalBinOp_rel_frag
  evalValue_boolNot
  evalValue_boolToU8
  evalValue_boolBitOp
  translateRvalue_cast_bool
  translateRvalue_boolBit
  evalScalarBinOp_boolBit
  switch_spec
  typedLoad_local_bool
  typedLoad_local_bool_uninit
  typedStore_local_bool
  typedStore_base_frag
  opBits_valid
  operandIsSigned_of_OperandOkT
  typedLoad_local_byte
  typedLoad_local_byte_uninit
  typedStore_local_byte
  typedStore_base_byte
  validBits_ordering
  decode_ordering
  checkValue_ordering
  encode_ordering
  evalUnOp_transmute_ordering
  evalBinOp_cmp_frag
  evalValue_translateCmp
  translateRvalue_cmp
  operandType_of_operandIsOrdering
  operandOkO_T
  evalValue_rvalueO
  evalStatement_assignO
  evalScalarBinOp_cmp_int
  evalScalarBinOp_cmp_bool
  evalRvalue_fragO
  evalStmt_assignO
  translateOperand_ordering_const
  scalarTypeOf_cases
  head_size_and_align_tuple
  layout_tuple
  withOverflow_eq
  checkValue_tuple
  encode_tuple
  decode_tuple
  decode_tuple_uninit
  typedLoad_local_tuple
  typedLoad_local_tuple_uninit
  typedStore_local_tuple
  typedLoad_local_localTy
  typedLoad_local_localTy_uninit
  evalPlace_field0
  evalPlace_field1
  typedLoad_local_tuple_field0
  typedLoad_local_tuple_field0_uninit
  typedLoad_local_tuple_field1
  typedLoad_local_tuple_field1_uninit
  evalBinOp_intWithOverflow
  translateRvalue_checked
  translateRvalue_tuple_agg
  evalValue_operandTuple
  evalValue_rvalueTuple
  evalStatement_assignTuple
  typedStore_base_tuple
  typedStore_base_localTy
  evalOperand_fragTuple
  evalScalarBinOp_checked
  evalRvalue_fragTuple
  evalStmt_assignTuple

open MiniRustSpec.Correspondence.Witness in
#assert_standard_axioms
  ctx0_ok1
  ctx0_ok2
  ctxI8_ok2
  ctx0_ok_u32_i8
  ctxI8_ok3
  ctxI8_ok_hetero
  spinLoop_step_self
  branchSpinLoop1_step_self
  sumTo_inFragment
  sumTo_translate
  sumTo_init_step
  sumTo_rel
  sumTo_anneal_ret
  sumTo_noUB
  sumTo_minirust_ret
  sumTo_minirust_direct
  sumTo_minirust_ret_from_start
  sumTo_minirust_direct_from_start
  retUninit_inFragment
  retUninit_translate
  retUninit_rel
  retUninit_anneal_ub
  retUninit_minirust_ub
  retUninit_minirust_direct
  retUninit_minirust_ub_from_start
  negMention_inFragment
  negMention_translate
  negMention5_startRel
  negMention5_anneal_ret
  negMention5_minirust_ret_from_start
  negMention5_minirust_direct
  negMention0_startRel
  negMention0_anneal_ub
  negMention0_minirust_ub_from_start
  negMention0_minirust_direct
  signedEdge_inFragment
  signedEdge_translate
  signedEdgeMin_anneal_ret
  signedEdgeMin_noUB
  signedEdgeMin_minirust_ret_from_start
  signedEdgeMin_minirust_noUB
  signedEdgeMin_minirust_direct
  signedEdgeOne_anneal_ret
  signedEdgeOne_minirust_ret_from_start
  signedEdgeOne_minirust_direct
  castBitNot_inFragment
  castBitNot_translate
  castBitNot4_anneal_ret
  castBitNot4_noUB
  castBitNot4_minirust_ret_from_start
  castBitNot4_minirust_direct
  spinLoop_inFragment
  spinLoop_translate
  spinLoop_noUB
  spinLoop_diverges
  spinLoop_minirust_steps_ok
  spinLoop_minirust_diverges_rel
  divRemI8_inFragment
  divRemI8_translate
  divRemNeg7_anneal_ret
  divRemNeg7_noUB
  divRemNeg7_minirust_ret_from_start
  divRemNeg7_minirust_direct
  divRemMinOne_anneal_ret
  divRemMinOne_minirust_ret_from_start
  divRemMinOne_minirust_direct
  divByZero_anneal_ub
  divByZero_minirust_ub_from_start
  divByZero_minirust_direct
  divByZero_converse_error
  divMinNeg1_anneal_ub
  divMinNeg1_minirust_ub_from_start
  divMinNeg1_minirust_direct
  remOnlyI8_inFragment
  remOnlyI8_translate
  remByZero_anneal_ub
  remByZero_minirust_ub_from_start
  remByZero_minirust_direct
  remMinNeg1_anneal_ub
  remMinNeg1_minirust_ub_from_start
  remMinNeg1_minirust_direct
  uncheckedArithI8_inFragment
  uncheckedArithI8_translate
  uncheckedOk_anneal_ret
  uncheckedOk_noUB
  uncheckedOk_minirust_ret_from_start
  uncheckedOk_minirust_direct
  uncheckedMulUb_anneal_ub
  uncheckedMulUb_minirust_ub_from_start
  uncheckedMulUb_minirust_direct
  uncheckedSubUb_anneal_ub
  uncheckedSubUb_minirust_ub_from_start
  uncheckedSubUb_minirust_direct
  uncheckedAddUb_anneal_ub
  uncheckedAddUb_minirust_ub_from_start
  uncheckedAddUb_minirust_direct
  uncheckedAddUb_outcome
  branchSpinLoop_inFragment
  branchSpinLoop_translate
  branchSpinLoop1_noUB
  branchSpinLoop1_diverges
  branchSpinLoop1_minirust_diverges_rel
  shiftI8_inFragment
  shiftI8_translate
  shiftOk_anneal_ret
  shiftOk_noUB
  shiftOk_minirust_ret_from_start
  shiftOk_minirust_direct
  shrUncheckedGe8Ub_anneal_ub
  shrUncheckedGe8Ub_minirust_ub_from_start
  shrUncheckedGe8Ub_minirust_direct
  shrUncheckedNegUb_anneal_ub
  shrUncheckedNegUb_minirust_ub_from_start
  shrUncheckedNegUb_minirust_direct
  shlUncheckedI8_inFragment
  shlUncheckedI8_translate
  shlUncheckedGe8Ub_anneal_ub
  shlUncheckedGe8Ub_minirust_ub_from_start
  shlUncheckedGe8Ub_minirust_direct
  shlUncheckedNegUb_anneal_ub
  shlUncheckedNegUb_minirust_ub_from_start
  shlUncheckedNegUb_minirust_direct
  bitwiseI8_inFragment
  bitwiseI8_translate
  bitwiseNeg_anneal_ret
  bitwiseNeg_noUB
  bitwiseNeg_minirust_ret_from_start
  bitwiseNeg_minirust_direct
  countOnes_neg86_i8
  countOnes_neg1_i8
  heteroShiftSwitch_inFragment
  heteroShiftSwitch_translate
  heteroShiftOk_anneal_ret
  heteroShiftOk_noUB
  heteroShiftOk_minirust_ret_from_start
  heteroShiftOk_minirust_direct
  heteroShrGe8Ub_anneal_ub
  heteroShrGe8Ub_minirust_ub_from_start
  heteroShrGe8Ub_minirust_direct
  heteroShrNegUb_anneal_ub
  heteroShrNegUb_minirust_ub_from_start
  heteroShrNegUb_minirust_direct
  divExact_ok_i8
  divExact_rem_ub_i8
  divExact_zero_ub_i8
  divExact_min_neg1_ub_i8
  uninitOperandUb_inFragment
  uninitOperandUb_translate
  uninitBinOpUb_anneal_ub
  uninitBinOpUb_minirust_ub_from_start
  uninitBinOpUb_minirust_direct
  uninitUnOpUb_anneal_ub
  uninitUnOpUb_minirust_ub_from_start
  uninitUnOpUb_minirust_direct
  uninitSwitchUb_anneal_ub
  uninitSwitchUb_minirust_ub_from_start
  uninitSwitchUb_minirust_direct
  uninitSwitchUb_converse_error
  ctxI8_ok_cmpNot
  cmpNotSwitch_inFragment
  cmpNotSwitch_translate
  cmpNotNeg1_anneal_ret
  cmpNotNeg1_noUB
  cmpNotNeg1_minirust_ret_from_start
  cmpNotNeg1_minirust_direct
  cmpNot3_anneal_ret
  cmpNot3_noUB
  cmpNot3_minirust_ret_from_start
  cmpNot3_minirust_direct
  ctxBool_ok
  ctxBool_ok1
  leNeGe_inFragment
  leNeGe_translate
  leNeGe250_anneal_ret
  leNeGe250_noUB
  leNeGe250_minirust_ret_from_start
  leNeGe250_minirust_direct
  leNeGe5_anneal_ret
  leNeGe5_noUB
  leNeGe5_minirust_ret_from_start
  leNeGe5_minirust_direct
  ctxI8_ok_boolCast
  boolCastI8_inFragment
  boolCastI8_translate
  boolCastInvalidArg_rejected
  boolCastTrue_anneal_ret
  boolCastTrue_noUB
  boolCastTrue_minirust_ret_from_start
  boolCastTrue_minirust_direct
  boolCastFalse_anneal_ret
  boolCastFalse_noUB
  boolCastFalse_minirust_ret_from_start
  boolCastFalse_minirust_direct
  uninitBool_inFragment
  uninitBool_translate
  uninitBool_anneal_ub
  uninitBool_minirust_ub_from_start
  uninitBool_minirust_direct
  uninitBoolNot_inFragment
  uninitBoolNot_translate
  uninitBoolNot_anneal_ub
  uninitBoolNot_minirust_ub_from_start
  uninitBoolNot_minirust_direct
  uninitBoolRel_inFragment
  uninitBoolRel_translate
  uninitBoolRel_anneal_ub
  uninitBoolRel_minirust_ub_from_start
  uninitBoolRel_minirust_direct
  ctxI8_ok_cmpSel
  cmpSel_inFragment
  cmpSel_translate
  cmpSelLess_anneal_ret
  cmpSelLess_noUB
  cmpSelLess_minirust_ret_from_start
  cmpSelLess_minirust_direct
  cmpSelEqual_anneal_ret
  cmpSelEqual_noUB
  cmpSelEqual_minirust_ret_from_start
  cmpSelEqual_minirust_direct
  cmpSelGreater_anneal_ret
  cmpSelGreater_noUB
  cmpSelGreater_minirust_ret_from_start
  cmpSelGreater_minirust_direct
  ctxBool_ok_ordering
  uninitOrdering_inFragment
  uninitOrdering_translate
  uninitOrdering_anneal_ub
  uninitOrdering_minirust_ub_from_start
  uninitOrdering_minirust_direct
  ctxI8_ok_boolBitOrdUse
  boolBitOrdUse_inFragment
  boolBitOrdUse_translate
  boolBitOrdInvalidTag_rejected
  boolBitOrdUseCmp_anneal_ret
  boolBitOrdUseCmp_noUB
  boolBitOrdUseCmp_minirust_ret_from_start
  boolBitOrdUseCmp_minirust_direct
  boolBitOrdUseCopy_anneal_ret
  boolBitOrdUseCopy_noUB
  boolBitOrdUseCopy_minirust_ret_from_start
  boolBitOrdUseCopy_minirust_direct
  uninitBoolBitAnd_inFragment
  uninitBoolBitAnd_translate
  uninitBoolBitAnd_anneal_ub
  uninitBoolBitAnd_minirust_ub_from_start
  uninitBoolBitAnd_minirust_direct
  uninitBoolBitOrRhs_inFragment
  uninitBoolBitOrRhs_translate
  uninitBoolBitOrRhs_anneal_ub
  uninitBoolBitOrRhs_minirust_ub_from_start
  uninitBoolBitOrRhs_minirust_direct
  relLt_signed
  relGt_unsigned
  relCmp_signed
  relCmp_unsigned
  relCmp_bool
  relLt_bool
  relGt_bool
  relLe_bool
  relGe_bool
  relEq_bool
  relNe_bool
  relGe_eq
  relNe_eq
  rel_mismatch
  transmute_bool_u8
  transmute_u8_bool
  transmute_u8_bool_invalid
  transmute_size_mismatch
  decode_bool_invalid
  bitNot_bool_panics
  ordering_validTags
  decode_ordering_less
  decode_ordering_invalid
  encode_ordering_greater
  checkValue_variant_invalid
  transmute_i8_ordering
  transmute_i8_ordering_invalid
  layout_paddedPair
  encode_paddedPair
  decode_paddedPair
  checkValue_tuple_arity
  decodeDiscriminant_short_circuits
  layout_slice
  layout_traitObject
  layout_unsizedTuple
  expectSize_unsized_panics
  expectAlign_traitObject_panics
  transmute_unsized_panics
  decode_unsized_panics
  encode_unsized_panics
  checkValue_unsized_panics
  layout_union
  decode_union
  encode_union
  checkValue_union_chunk_size
  checkValue_union_chunk_data
  transmute_union_paddedPair
  transmute_paddedPair_union
  transmute_union_paddedPair_uninit_ub
  ctxI8_ok_checkedArith
  checkedArithI8_inFragment
  checkedArithI8_translate
  checkedArithInvalidTupleArg_rejected
  checkedArithOk_anneal_ret
  checkedArithOk_noUB
  checkedArithOk_minirust_ret_from_start
  checkedArithOk_minirust_direct
  checkedArithAddOv_anneal_ret
  checkedArithAddOv_noUB
  checkedArithAddOv_minirust_ret_from_start
  checkedArithAddOv_minirust_direct
  checkedArithSubOv_anneal_ret
  checkedArithSubOv_noUB
  checkedArithSubOv_minirust_ret_from_start
  checkedArithSubOv_minirust_direct
  checkedArithMulOv_anneal_ret
  checkedArithMulOv_noUB
  checkedArithMulOv_minirust_ret_from_start
  checkedArithMulOv_minirust_direct
  ctxTupleU32_ok
  checkedTupleU32_inFragment
  checkedTupleU32_translate
  checkedTupleUnderAddOv_anneal_ret
  checkedTupleUnderAddOv_noUB
  checkedTupleUnderAddOv_minirust_ret_from_start
  checkedTupleUnderAddOv_minirust_direct
  checkedTupleMulOv_anneal_ret
  checkedTupleMulOv_noUB
  checkedTupleMulOv_minirust_ret_from_start
  checkedTupleMulOv_minirust_direct
  checkedTupleOk_anneal_ret
  checkedTupleOk_noUB
  checkedTupleOk_minirust_ret_from_start
  checkedTupleOk_minirust_direct
  ctxTupleU32_ok1
  uninitTupleField0_inFragment
  uninitTupleField0_translate
  uninitTupleField0_anneal_ub
  uninitTupleField0_minirust_ub_from_start
  uninitTupleField0_minirust_direct
  uninitTupleField1_inFragment
  uninitTupleField1_translate
  uninitTupleField1_anneal_ub
  uninitTupleField1_minirust_ub_from_start
  uninitTupleField1_minirust_direct
  withOverflow_i8_layout
  withOverflow_u32_layout
  tupleHeadLayout_full_sized_and_slice
  evalBinOp_addWithOverflow_i8_max
  evalBinOp_subWithOverflow_i8_min
  evalBinOp_addWithOverflow_u32_max
  evalBinOp_subWithOverflow_u32_zero
  evalBinOp_mulWithOverflow_i8_min
  evalBinOp_mulWithOverflow_u32
  ptrOffsetInbounds_ok_and_oob
  evalValue_tuple_and_evalPlace_field

#assert_standard_axioms
  MiniRustSpec.Anchors.anchors_ok
  MiniRustSpec.Anchors.anchors_nodup

#check_theorem_deps "[ANCHOR-AUDIT]"
  MiniRustSpec.Anchors.anchors_ok
  MiniRustSpec.Anchors.anchors_nodup

open MiniRustSpec.Correspondence in
#check_theorem_deps "[SIMULATION-AUDIT]"
  step_correspondence
  step_initBlock
  step_start
  initMachineState_startRel
  run_ret
  run_ret_from_start
  run_ub
  run_ub_from_start
  steps_error
  steps_error_from_start
  steps_outcome
  steps_outcome_from_start
  mirNoUB_safe
  mirNoUB_safe_from_start
  mirCall_ret
  mirCall_ub
  mirCall_noUB
  mirCall_progress
  mirCall_steps_error
  mirCall_outcome
  mirCall_diverges_steps_ok
  mirCall_diverges_rel
  evalValue_operandT
  evalValue_rvalueB
  evalStatement_assignB
  evalOperand_fragT
  evalRvalue_fragB
  evalStmt_assignB
  evalScalarBinOp_rel_int
  evalScalarBinOp_rel_bool
  evalScalarBinOp_boolBit
  evalUnaryNot_bool
  evalBinOp_rel_frag
  evalValue_boolNot
  evalValue_boolToU8
  evalValue_boolBitOp
  translateRvalue_cast_bool
  translateRvalue_boolBit
  switch_spec
  typedStore_base_frag
  operandType_of_operandIsOrdering
  operandOkO_T
  evalValue_rvalueO
  evalStatement_assignO
  evalRvalue_fragO
  evalStmt_assignO
  evalScalarBinOp_cmp_int
  evalScalarBinOp_cmp_bool
  evalValue_translateCmp
  validBits_ordering
  typedStore_base_byte
  head_size_and_align_tuple
  layout_tuple
  withOverflow_eq
  checkValue_tuple
  encode_tuple
  decode_tuple
  decode_tuple_uninit
  typedLoad_local_tuple
  typedLoad_local_tuple_uninit
  typedStore_local_tuple
  typedLoad_local_localTy
  typedLoad_local_localTy_uninit
  evalPlace_field0
  evalPlace_field1
  typedLoad_local_tuple_field0
  typedLoad_local_tuple_field0_uninit
  typedLoad_local_tuple_field1
  typedLoad_local_tuple_field1_uninit
  evalBinOp_intWithOverflow
  translateRvalue_checked
  translateRvalue_tuple_agg
  evalValue_operandTuple
  evalValue_rvalueTuple
  evalStatement_assignTuple
  typedStore_base_tuple
  typedStore_base_localTy
  evalOperand_fragTuple
  evalScalarBinOp_checked
  evalRvalue_fragTuple
  evalStmt_assignTuple

open MiniRustSpec.Correspondence.Witness in
#check_theorem_deps "[WITNESS-AUDIT]"
  cmpNotSwitch_inFragment
  cmpNotSwitch_translate
  cmpNotNeg1_anneal_ret
  cmpNotNeg1_noUB
  cmpNotNeg1_minirust_ret_from_start
  cmpNotNeg1_minirust_direct
  cmpNot3_anneal_ret
  cmpNot3_noUB
  cmpNot3_minirust_ret_from_start
  cmpNot3_minirust_direct
  leNeGe_inFragment
  leNeGe_translate
  leNeGe250_anneal_ret
  leNeGe250_noUB
  leNeGe250_minirust_ret_from_start
  leNeGe250_minirust_direct
  leNeGe5_anneal_ret
  leNeGe5_noUB
  leNeGe5_minirust_ret_from_start
  leNeGe5_minirust_direct
  boolCastI8_inFragment
  boolCastI8_translate
  boolCastInvalidArg_rejected
  boolCastTrue_anneal_ret
  boolCastTrue_noUB
  boolCastTrue_minirust_ret_from_start
  boolCastTrue_minirust_direct
  boolCastFalse_anneal_ret
  boolCastFalse_noUB
  boolCastFalse_minirust_ret_from_start
  boolCastFalse_minirust_direct
  uninitBool_inFragment
  uninitBool_translate
  uninitBool_anneal_ub
  uninitBool_minirust_ub_from_start
  uninitBool_minirust_direct
  uninitBoolNot_inFragment
  uninitBoolNot_translate
  uninitBoolNot_anneal_ub
  uninitBoolNot_minirust_ub_from_start
  uninitBoolNot_minirust_direct
  uninitBoolRel_inFragment
  uninitBoolRel_translate
  uninitBoolRel_anneal_ub
  uninitBoolRel_minirust_ub_from_start
  uninitBoolRel_minirust_direct
  ctxI8_ok_cmpSel
  cmpSel_inFragment
  cmpSel_translate
  cmpSelLess_anneal_ret
  cmpSelLess_noUB
  cmpSelLess_minirust_ret_from_start
  cmpSelLess_minirust_direct
  cmpSelEqual_anneal_ret
  cmpSelEqual_noUB
  cmpSelEqual_minirust_ret_from_start
  cmpSelEqual_minirust_direct
  cmpSelGreater_anneal_ret
  cmpSelGreater_noUB
  cmpSelGreater_minirust_ret_from_start
  cmpSelGreater_minirust_direct
  ctxBool_ok_ordering
  uninitOrdering_inFragment
  uninitOrdering_translate
  uninitOrdering_anneal_ub
  uninitOrdering_minirust_ub_from_start
  uninitOrdering_minirust_direct
  ctxI8_ok_boolBitOrdUse
  boolBitOrdUse_inFragment
  boolBitOrdUse_translate
  boolBitOrdInvalidTag_rejected
  boolBitOrdUseCmp_anneal_ret
  boolBitOrdUseCmp_noUB
  boolBitOrdUseCmp_minirust_ret_from_start
  boolBitOrdUseCmp_minirust_direct
  boolBitOrdUseCopy_anneal_ret
  boolBitOrdUseCopy_noUB
  boolBitOrdUseCopy_minirust_ret_from_start
  boolBitOrdUseCopy_minirust_direct
  uninitBoolBitAnd_inFragment
  uninitBoolBitAnd_translate
  uninitBoolBitAnd_anneal_ub
  uninitBoolBitAnd_minirust_ub_from_start
  uninitBoolBitAnd_minirust_direct
  uninitBoolBitOrRhs_inFragment
  uninitBoolBitOrRhs_translate
  uninitBoolBitOrRhs_anneal_ub
  uninitBoolBitOrRhs_minirust_ub_from_start
  uninitBoolBitOrRhs_minirust_direct
  relLt_signed
  relGt_unsigned
  relCmp_signed
  relCmp_unsigned
  relCmp_bool
  relLt_bool
  relGt_bool
  relLe_bool
  relGe_bool
  relEq_bool
  relNe_bool
  relGe_eq
  relNe_eq
  rel_mismatch
  transmute_bool_u8
  transmute_u8_bool
  transmute_u8_bool_invalid
  transmute_size_mismatch
  decode_bool_invalid
  bitNot_bool_panics
  ordering_validTags
  decode_ordering_less
  decode_ordering_invalid
  encode_ordering_greater
  checkValue_variant_invalid
  transmute_i8_ordering
  transmute_i8_ordering_invalid
  layout_paddedPair
  encode_paddedPair
  decode_paddedPair
  checkValue_tuple_arity
  decodeDiscriminant_short_circuits
  layout_slice
  layout_traitObject
  layout_unsizedTuple
  expectSize_unsized_panics
  expectAlign_traitObject_panics
  transmute_unsized_panics
  decode_unsized_panics
  encode_unsized_panics
  checkValue_unsized_panics
  layout_union
  decode_union
  encode_union
  checkValue_union_chunk_size
  checkValue_union_chunk_data
  transmute_union_paddedPair
  transmute_paddedPair_union
  transmute_union_paddedPair_uninit_ub
  ctxI8_ok_checkedArith
  checkedArithI8_inFragment
  checkedArithI8_translate
  checkedArithInvalidTupleArg_rejected
  checkedArithOk_anneal_ret
  checkedArithOk_noUB
  checkedArithOk_minirust_ret_from_start
  checkedArithOk_minirust_direct
  checkedArithAddOv_anneal_ret
  checkedArithAddOv_noUB
  checkedArithAddOv_minirust_ret_from_start
  checkedArithAddOv_minirust_direct
  checkedArithSubOv_anneal_ret
  checkedArithSubOv_noUB
  checkedArithSubOv_minirust_ret_from_start
  checkedArithSubOv_minirust_direct
  checkedArithMulOv_anneal_ret
  checkedArithMulOv_noUB
  checkedArithMulOv_minirust_ret_from_start
  checkedArithMulOv_minirust_direct
  ctxTupleU32_ok
  checkedTupleU32_inFragment
  checkedTupleU32_translate
  checkedTupleUnderAddOv_anneal_ret
  checkedTupleUnderAddOv_noUB
  checkedTupleUnderAddOv_minirust_ret_from_start
  checkedTupleUnderAddOv_minirust_direct
  checkedTupleMulOv_anneal_ret
  checkedTupleMulOv_noUB
  checkedTupleMulOv_minirust_ret_from_start
  checkedTupleMulOv_minirust_direct
  checkedTupleOk_anneal_ret
  checkedTupleOk_noUB
  checkedTupleOk_minirust_ret_from_start
  checkedTupleOk_minirust_direct
  ctxTupleU32_ok1
  uninitTupleField0_inFragment
  uninitTupleField0_translate
  uninitTupleField0_anneal_ub
  uninitTupleField0_minirust_ub_from_start
  uninitTupleField0_minirust_direct
  uninitTupleField1_inFragment
  uninitTupleField1_translate
  uninitTupleField1_anneal_ub
  uninitTupleField1_minirust_ub_from_start
  uninitTupleField1_minirust_direct
  withOverflow_i8_layout
  withOverflow_u32_layout
  tupleHeadLayout_full_sized_and_slice
  evalBinOp_addWithOverflow_i8_max
  evalBinOp_subWithOverflow_i8_min
  evalBinOp_addWithOverflow_u32_max
  evalBinOp_subWithOverflow_u32_zero
  evalBinOp_mulWithOverflow_i8_min
  evalBinOp_mulWithOverflow_u32
  ptrOffsetInbounds_ok_and_oob
  evalValue_tuple_and_evalPlace_field
  sumTo_minirust_ret_from_start
  castBitNot4_minirust_ret_from_start
  uninitSwitchUb_minirust_ub_from_start

/-- Exhaustively verify that every declaration across every imported
`MiniRustSpec.*` module in the environment depends only on Lean's standard
axioms (`propext`, `Quot.sound`, `Classical.choice`). -/
elab "#assert_all_minirustspec_standard_axioms" : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if (`MiniRustSpec).isPrefixOf modName then
      let modData := env.header.moduleData[i]!
      for c in modData.constNames do
        let axs ← liftCoreM <| Lean.collectAxioms c
        for a in axs do
          unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
            throwError "{c} (in {modName}) depends on the non-standard axiom {a}"
        checked := checked + 1
  logInfo m!"MiniRustSpec.Audit: exhaustively verified standard axioms for {checked} declarations across all MiniRustSpec.* modules"

#assert_all_minirustspec_standard_axioms

end MiniRustSpec.Audit
