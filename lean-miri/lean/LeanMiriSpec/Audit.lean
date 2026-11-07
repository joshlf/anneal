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
import LeanMiriSpec.Correspondence.PtrLM3_1
import LeanMiriSpec.Correspondence.SimLM3_1
import LeanMiriSpec.Correspondence.WitLM3_1

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
  AllocMapEntry
  lookupAllocMapByTag
  lookupAllocMapByLocal
  AllocMapRel
  PtrRel
  annealPointerArithmetic
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

end StatementPins

-- Exhaustively verify standard axioms across all imported `LeanMiriSpec.*` and
-- `Miri.*` modules AND every constant elaborated in `LeanMiriSpec.Audit` itself.
#assert_all_leanmirispec_and_miri_standard_axioms

end LeanMiriSpec.Audit
