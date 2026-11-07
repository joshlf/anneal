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
import LeanMiriSpec.Correspondence.Witness
import LeanMiriSpec.Correspondence.AllocLM1_4
import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.WitLM1_4

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

end StatementPins

-- Exhaustively verify standard axioms across all imported `LeanMiriSpec.*` and
-- `Miri.*` modules AND every constant elaborated in `LeanMiriSpec.Audit` itself.
#assert_all_leanmirispec_and_miri_standard_axioms

end LeanMiriSpec.Audit
