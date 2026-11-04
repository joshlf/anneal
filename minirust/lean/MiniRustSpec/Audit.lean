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
-/

namespace MiniRustSpec.Audit

open Lean Elab Command

/-- Fail unless every listed declaration depends only on the standard axioms. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    logInfo m!"{n} depends on axioms: {axs.toList}"

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
  evalStatement_assign_array
  evalStatement_assign_index
  evalStatement_placeMention
  evalValue_operand
  evalValue_rvalue
  evalValue_arrayRvalue
  evalPlace_proj
  typedLoad_array_local
  typedLoad_array_elem
  typedStore_array_local
  typedStore_array_elem
  evalIntBinOp_spec
  evalIntBinOp_divExact
  evalUnOp_countOnes
  intBitAnd_one
  countOnesLoop_bounds
  evalStmt_assign
  evalStmt_assign_array
  evalStmt_assign_index
  evalStmt_placeMention
  evalOperand_frag
  evalRvalue_frag
  evalRvalue_array_frag
  readProjectedValue_proj
  writeProjectedValue_proj
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
  ctxI8_ok_arrayOps
  ctxI8_ok_arraySignedIdx
  ctxI8_ok_zeroArray
  arrayOpsI8_inFragment
  arrayOpsI8_translate
  arrayOpsOk_anneal_ret
  arrayOpsOk_noUB
  arrayOpsOk_minirust_ret_from_start
  arrayOpsOk_minirust_direct
  arrayOpsOob_anneal_ub
  arrayOpsOob_minirust_ub_from_start
  arrayOpsOob_minirust_direct
  arrayOpsOob_converse_error
  arraySignedIdxI8_inFragment
  arraySignedIdxI8_translate
  arraySignedIdxOk_anneal_ret
  arraySignedIdxOk_minirust_ret_from_start
  arraySignedIdxOk_minirust_direct
  arraySignedNegUb_anneal_ub
  arraySignedNegUb_minirust_ub_from_start
  arraySignedNegUb_minirust_direct
  arraySignedOobUb_anneal_ub
  arraySignedOobUb_minirust_ub_from_start
  arraySignedOobUb_minirust_direct
  zeroArrayI8_inFragment
  zeroArrayI8_translate
  zeroArrayOk_anneal_ret
  zeroArrayOk_noUB
  zeroArrayOk_minirust_ret_from_start
  zeroArrayOk_minirust_direct
  zeroArrayIdxUb_anneal_ub
  zeroArrayIdxUb_minirust_ub_from_start
  zeroArrayIdxUb_minirust_direct
  arrayOpsOk_minirust_inplace_bytes
  ctxI8_ok_arrayUninitIdx
  arrayUninitIdxI8_inFragment
  arrayUninitIdxI8_translate
  arrayUninitIdx_anneal_ub
  arrayUninitIdx_minirust_ub_from_start
  arrayUninitIdx_minirust_direct
  ctxU32_ok_arrayU32Idx
  arrayU32Idx_inFragment
  arrayU32Idx_translate
  arrayU32IdxOk_anneal_ret
  arrayU32IdxOk_noUB
  arrayU32IdxOk_minirust_ret_from_start
  arrayU32IdxOk_minirust_direct
  arrayU32IdxOk_minirust_inplace_bytes
  arrayU32IdxOob_anneal_ub
  arrayU32IdxOob_minirust_ub_from_start
  arrayU32IdxOob_minirust_direct
  arrayConstIdxOobI8_inFragment
  arrayConstIdxOobI8_translate
  arrayConstIdxOob_anneal_ub
  arrayConstIdxOob_minirust_ub_from_start
  arrayConstIdxOob_minirust_direct
  sizeMulInt_zero_neg
  array_encode_decode_edge_cases

#assert_standard_axioms
  MiniRustSpec.Anchors.anchors_ok
  MiniRustSpec.Anchors.anchors_nodup

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

/-- Audit a named group of theorems and log a receipt line computed from the
audit itself:
`[<tag>] decls=<n> theorems=<n> sorry_free=<b> standard_axioms_only=<b>`.
The command fails unless every listed name resolves to a theorem whose axiom
closure contains only the standard axioms (so in particular no `sorryAx`), so
the logged flags can only ever read `true`; `decls` counts the names actually
checked, so a receipt line cannot claim a theorem that is not in the group. -/
elab "#audit_group " tag:str ids:ident* : command => do
  let env ← getEnv
  let mut decls : Nat := 0
  let mut theorems : Nat := 0
  let mut sorryFree := true
  let mut standardOnly := true
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    decls := decls + 1
    match env.find? n with
    | some (.thmInfo _) => theorems := theorems + 1
    | _ => throwError "{n} is not a theorem"
    let axs ← liftCoreM <| Lean.collectAxioms n
    if axs.contains ``sorryAx then
      sorryFree := false
    unless axs.all (fun a => a == ``propext || a == ``Quot.sound || a == ``Classical.choice) do
      standardOnly := false
      logError m!"{n} depends on non-standard axioms: {axs.toList}"
  unless sorryFree && standardOnly do
    throwError "[{tag.getString}] audit failed"
  logInfo m!"[{tag.getString}] decls={decls} theorems={theorems} sorry_free={sorryFree} standard_axioms_only={standardOnly}"

#audit_group "ANCHOR-AUDIT"
  MiniRustSpec.Anchors.anchors_ok
  MiniRustSpec.Anchors.anchors_nodup

open MiniRustSpec.Correspondence in
#audit_group "SIMULATION-AUDIT"
  step_correspondence
  initMachineState_startRel
  mirCall_ret
  mirCall_ub
  mirCall_noUB
  mirCall_progress
  mirCall_steps_error
  mirCall_outcome
  evalPlace_proj
  evalStatement_assign_array
  evalStatement_assign_index
  evalValue_arrayRvalue
  typedLoad_array_local
  typedLoad_array_elem
  typedStore_array_local
  typedStore_array_elem
  evalStmt_assign_array
  evalStmt_assign_index
  evalRvalue_array_frag
  readProjectedValue_proj
  writeProjectedValue_proj

open MiniRustSpec.Correspondence.Witness in
#audit_group "WITNESS-AUDIT"
  arrayOpsI8_inFragment
  arrayOpsI8_translate
  arrayOpsOk_anneal_ret
  arrayOpsOk_noUB
  arrayOpsOk_minirust_ret_from_start
  arrayOpsOk_minirust_direct
  arrayOpsOk_minirust_inplace_bytes
  arrayOpsOob_anneal_ub
  arrayOpsOob_minirust_ub_from_start
  arrayOpsOob_minirust_direct
  arrayOpsOob_converse_error
  arraySignedIdxI8_inFragment
  arraySignedIdxI8_translate
  arraySignedIdxOk_anneal_ret
  arraySignedIdxOk_minirust_ret_from_start
  arraySignedIdxOk_minirust_direct
  arraySignedNegUb_anneal_ub
  arraySignedNegUb_minirust_ub_from_start
  arraySignedNegUb_minirust_direct
  arraySignedOobUb_anneal_ub
  arraySignedOobUb_minirust_ub_from_start
  arraySignedOobUb_minirust_direct
  arrayUninitIdxI8_inFragment
  arrayUninitIdxI8_translate
  arrayUninitIdx_anneal_ub
  arrayUninitIdx_minirust_ub_from_start
  arrayUninitIdx_minirust_direct
  arrayU32Idx_inFragment
  arrayU32Idx_translate
  arrayU32IdxOk_anneal_ret
  arrayU32IdxOk_noUB
  arrayU32IdxOk_minirust_ret_from_start
  arrayU32IdxOk_minirust_direct
  arrayU32IdxOk_minirust_inplace_bytes
  arrayU32IdxOob_anneal_ub
  arrayU32IdxOob_minirust_ub_from_start
  arrayU32IdxOob_minirust_direct
  arrayConstIdxOobI8_inFragment
  arrayConstIdxOobI8_translate
  arrayConstIdxOob_anneal_ub
  arrayConstIdxOob_minirust_ub_from_start
  arrayConstIdxOob_minirust_direct
  sizeMulInt_zero_neg
  array_encode_decode_edge_cases
  zeroArrayI8_inFragment
  zeroArrayI8_translate
  zeroArrayOk_anneal_ret
  zeroArrayOk_noUB
  zeroArrayOk_minirust_ret_from_start
  zeroArrayOk_minirust_direct
  zeroArrayIdxUb_anneal_ub
  zeroArrayIdxUb_minirust_ub_from_start
  zeroArrayIdxUb_minirust_direct

end MiniRustSpec.Audit
