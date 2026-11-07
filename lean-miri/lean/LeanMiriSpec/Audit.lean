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
  CanReserveAllocId
  evalProjection_index_simulation
  evalProjection_constantIndex_simulation
  evalRvalue_len_array_simulation
  evalRvalue_repeat_simulation
  evalRvalue_aggregate_array_simulation
  WellTypedArrayElemProj
  WellTypedArrayElemAssign
  step_assign_array_element_simulation
  WellTypedLM2_1Stmt
  step_stmt_lm2_1_simulation
  Witness.lm21Body
  Witness.lm21ArrAlloc
  Witness.lm21ArrElems
  Witness.lm21_wf_u16Arr3
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
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrLocal idxLocal : MirAst.Local} {arrDecl idxDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (harr_decl : get? body.localDecls arrLocal = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hmp : MemPlaceRel m.machine arrDecl.ty body.layouts (some (.aggregate 0 elems)) mp)
    (hidx_decl : get? body.localDecls idxLocal = some idxDecl)
    (hidx_ty : idxDecl.ty = { kind := .uint .usize, layoutIdx := 0 })
    (hidx_imm : IsImmediateFrameLocal topFrame idxLocal) :
    let cx := annealProjectionCx topFrame body.layouts
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩
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
  evalProjection_index_simulation hrel hframes hnodup harr_decl hwf hmp hidx_decl hidx_ty hidx_imm

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : StateRel body s m)
    (hframes : m.stack.frames = #[topFrame])
    (hnodup : LiveAllocsNodup m.machine)
    {arrLocal : MirAst.Local} {arrDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {elems : List Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (harr_decl : get? body.localDecls arrLocal = some arrDecl)
    (hwf : WellTypedArrayTy body.layouts arrDecl.ty elemKind count)
    (hmp : MemPlaceRel m.machine arrDecl.ty body.layouts (some (.aggregate 0 elems)) mp)
    (offset minLength : Nat) (fromEnd : Bool)
    (hoff_bound : offset < 2 ^ 64)
    (hmin_bound : minLength < 2 ^ 64)
    (hwf_const :
      (fromEnd = false → offset < minLength) ∧
      (fromEnd = true → 0 < offset ∧ offset ≤ minLength)) :
    let cx := annealProjectionCx topFrame body.layouts
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect mp, translateTy arrDecl.ty body.layouts⟩
    let elemTy : MirAst.Ty := { kind := elemKind, layoutIdx := 0 }
    let elemLay := (translateTy elemTy body.layouts).layout
    let idx := if fromEnd then count - offset else offset
    (minLength ≤ count →
      ∃ elemVal sc msc,
        get? elems idx = some elemVal ∧
        elemVal = .scalar sc ∧
        readProjectedValue s.frame.locals (.aggregate 0 elems)
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
      readProjectedValue s.frame.locals (.aggregate 0 elems)
        [.constantIndex offset minLength fromEnd] = .ub ∧
      (∀ v,
        writeProjectedValue s.frame.locals (.aggregate 0 elems)
          [.constantIndex offset minLength fromEnd] v = .ub) ∧
      ∃ msg,
        (annealProjectList cx base [.ConstantIndex offset minLength fromEnd]).mapError
          annealLiftProjectionError = .error (.undefinedBehavior msg)) :=
  evalProjection_constantIndex_simulation hrel hframes hnodup harr_decl hwf hmp
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
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_len_array_simulation hstate hnodup hphase hbb hstmt
    hdecl_arr hwf hdecl_dst hdst_ty hdst_imm harr_slot

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {bb : MirAst.BasicBlockData} {dstIdx : MirAst.Local} {dstDecl : MirAst.LocalDecl}
    {elemKind : MirAst.RigidTy} {count : Nat} {op : MirAst.Operand} {span : String}
    (hrel : StateRel body s m)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hdst_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hcan_res : CanReserveAllocId m.machine.memory) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.repeat op count), span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_repeat_simulation hrel hbb hstmt hdecl_dst hwf hdst_imm hop hprim hcan_res

example
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {bb : MirAst.BasicBlockData} {dstIdx : MirAst.Local} {dstDecl : MirAst.LocalDecl}
    {elemTy : MirAst.Ty} {elemKind : MirAst.RigidTy} {count : Nat}
    {ops : List MirAst.Operand} {span : String}
    (hrel : StateRel body s m)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hwf : WellTypedArrayTy body.layouts dstDecl.ty elemKind count)
    (hlen_ops : ops.length = count)
    (hdst_imm : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    (hops : ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ op ∈ ops, WellTypedScalarOperand body topFrame op { kind := elemKind, layoutIdx := 0 })
    (hprim : IsPrimScalarTy { kind := elemKind, layoutIdx := 0 })
    (hcan_res : CanReserveAllocId m.machine.memory) :
    StepRel body m
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.aggregate (.array elemTy) ops), span⟩
        body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  evalRvalue_aggregate_array_simulation hrel hbb hstmt hdecl_dst hwf hlen_ops hdst_imm hops
    hprim hcan_res

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
      WellTypedLM2_1Stmt body s m topFrame stmt) :
    StepRel body m
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_stmt_lm2_1_simulation hstate hnodup hphase hbb hstmt hwt

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
          Witness.lm21Body.layouts)
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
        (annealProjectionCx (Witness.lm21ArrMiriFrame 7 .uninit) Witness.lm21Body.layouts)
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

end StatementPins

-- Exhaustively verify standard axioms across all imported `LeanMiriSpec.*` and
-- `Miri.*` modules AND every constant elaborated in `LeanMiriSpec.Audit` itself.
#assert_all_leanmirispec_and_miri_standard_axioms

end LeanMiriSpec.Audit
