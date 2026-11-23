-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.ParametricCore.LoopInv
import Anneal.ParametricCore.BlockTree
import Anneal.ParametricCore.StageCut
import Anneal.ParametricCore.ByteSubLens
import Anneal.MirFuelFree
import Anneal.MirLoops
import Anneal.PureMirExec
import Anneal.SepLogicLenses
import Anneal.PureLift.V2026_06_01Bridge

/-!
# `ParametricCore` ↔ `Trusted.Rustc.V2026_06_01` Operational Bridge

Instantiates Episode 1's zero-TCB parametric core (`LoopInv`, `BlockTree`,
`StageCut`, `ByteSubLens`) directly on the unmodified trusted
`Trusted.Rustc.V2026_06_01.MirSemantics` operational semantics (`MachineState`,
`stepMirFn`, `stepMirState`, `Memory`, `CapturedAllocation`, `AbstractByte`),
`Anneal.PureMirExec` (`mirStep`, `stepCfgState`), `Anneal.MirFuelFree`
(`MirWpConverges`, `MirStepsConverges`, `dwp_of_mirWpConverges`,
`verify*Mir*_of_wpConverges`), `Anneal.SepLogicLenses` (`ByteLensCodec`,
`TypedAt`, `SliceTypedAt`), `Anneal.Memory` (Tree Borrows `ByteRangePerm`),
and `Anneal.PureLift.V2026_06_01Bridge` (`StepPath`, `mirOperationalAdapter`,
`mir_pure_lift_sound`, `MirTypedByteCodec`), with zero shadow operational
semantics.
-/

namespace Anneal.ParametricCore.V2026Bridge

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.VerificationResult
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.ParametricCore

/-! ## 1. Deterministic Live-Step `MirWpOps` (`mirDetWpOps` & `mirCfgWpOps`) -/

/-- Map a deterministic `Anneal.PureMirExec.Step` result into `StepOutcome`. -/
@[reducible] def toStepOutcome
    (r : Anneal.PureMirExec.Step MachineState MirOutcome) :
    StepOutcome MachineState MirOutcome Unit :=
  match r with
  | .cont s' => .step s'
  | .done o => .done o
  | .fault => .fault ()

/-- Deterministic live single-step transition of `body` wrapping
`Anneal.PureMirExec.mirStep body` directly. -/
@[reducible] def mirDetStep (body : CapturedMir) (ms : MachineState) :
    StepOutcome MachineState MirOutcome Unit :=
  toStepOutcome (Anneal.PureMirExec.mirStep body ms)

/-- Deterministic `MirWpOps` interface for `body : CapturedMir`, exposing
`ms.frame.blockIdx` as `blockTag?`. -/
@[reducible] def mirDetWpOps (body : CapturedMir) :
    MirWpOps MachineState MirOutcome Unit :=
  MirWpOps.ofDetStep (mirDetStep body) (fun ms => some ms.frame.blockIdx)

/-- Fault-forbidding deterministic `MirWpOps` interface over `PureMirExec.mirStep`:
agrees with `mirDetWpOps` on all fault-free weakest preconditions and refines
every coalgebraic `EffectWP` interface. -/
@[reducible] def mirStrictDetWpOps (body : CapturedMir) :
    MirWpOps MachineState MirOutcome Unit where
  stepWp ms P Q _ :=
    match Anneal.PureMirExec.mirStep body ms with
    | .cont s' => P s'
    | .done o => Q o
    | .fault => False
  stepWp_mono := by
    intro ms P₁ P₂ Q₁ Q₂ _ _ hP hQ _ h
    cases hStep : Anneal.PureMirExec.mirStep body ms with
    | cont s' => rw [hStep] at h; exact hP s' h
    | done o => rw [hStep] at h; exact hQ o h
    | fault => rw [hStep] at h; exact False.elim h
  blockTag? ms := some ms.frame.blockIdx

theorem toStepOutcome_step_iff {r : Anneal.PureMirExec.Step MachineState MirOutcome}
    {s' : MachineState} :
    toStepOutcome r = .step s' ↔ r = .cont s' := by
  cases r with
  | cont s₁ =>
    constructor
    · intro h; exact congrArg _ (StepOutcome.step.inj h)
    · intro h; injection h with hEq; rw [hEq]
  | done _ => constructor <;> (intro h; cases h)
  | fault => constructor <;> (intro h; cases h)

theorem toStepOutcome_done_iff {r : Anneal.PureMirExec.Step MachineState MirOutcome}
    {o : MirOutcome} :
    toStepOutcome r = .done o ↔ r = .done o := by
  cases r with
  | cont _ => constructor <;> (intro h; cases h)
  | done o₁ =>
    constructor
    · intro h; exact congrArg _ (StepOutcome.done.inj h)
    · intro h; injection h with hEq; rw [hEq]
  | fault => constructor <;> (intro h; cases h)

theorem toStepOutcome_fault_iff {r : Anneal.PureMirExec.Step MachineState MirOutcome} :
    toStepOutcome r = .fault () ↔ r = .fault := by
  cases r with
  | cont _ => constructor <;> (intro h; cases h)
  | done _ => constructor <;> (intro h; cases h)
  | fault => exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem mirDetStep_step_iff {body : CapturedMir} {ms ms' : MachineState} :
    mirDetStep body ms = .step ms' ↔ Anneal.PureMirExec.mirStep body ms = .cont ms' :=
  toStepOutcome_step_iff

theorem mirDetStep_done_iff {body : CapturedMir} {ms : MachineState}
    {out : MirOutcome} :
    mirDetStep body ms = .done out ↔ Anneal.PureMirExec.mirStep body ms = .done out :=
  toStepOutcome_done_iff

theorem mirDetWpOps_conjunctive (body : CapturedMir) :
    (mirDetWpOps body).Conjunctive :=
  MirWpOps.ofDetStep_conjunctive _ _

theorem mirDetWpOps_fuelContinuous (body : CapturedMir) :
    (mirDetWpOps body).FuelContinuous :=
  MirWpOps.ofDetStep_fuelContinuous _ _

theorem mirDetWpOps_strict (body : CapturedMir) :
    (mirDetWpOps body).Strict :=
  MirWpOps.ofDetStep_strict _ _

theorem mirDetWpOps_atBlock_iff (body : CapturedMir) (bb : Nat) (ms : MachineState) :
    (mirDetWpOps body).atBlock bb ms ↔ ms.frame.blockIdx = bb := by
  constructor
  · intro h; exact Option.some.inj h
  · intro h; exact congrArg some h

theorem mirStrictDetWpOps_refines_mirDetWpOps (body : CapturedMir) :
    (mirStrictDetWpOps body).Refines (mirDetWpOps body) := by
  intro ms P Q R h
  change (mirDetStep body ms).wp P Q R
  unfold mirDetStep
  cases hStep : Anneal.PureMirExec.mirStep body ms with
  | cont s' =>
    change (match Anneal.PureMirExec.mirStep body ms with
      | .cont s' => P s' | .done o => Q o | .fault => False) at h
    rw [hStep] at h; exact h
  | done o =>
    change (match Anneal.PureMirExec.mirStep body ms with
      | .cont s' => P s' | .done o => Q o | .fault => False) at h
    rw [hStep] at h; exact h
  | fault =>
    change (match Anneal.PureMirExec.mirStep body ms with
      | .cont s' => P s' | .done o => Q o | .fault => False) at h
    rw [hStep] at h; exact False.elim h

theorem wpUntilOk_mirDet_iff_strictDet {body : CapturedMir}
    {stop : MachineState → Prop} {post : MirOutcome → Prop} {ms : MachineState} :
    wpUntilOk (ops := mirDetWpOps body) stop post ms ↔
      wpUntilOk (ops := mirStrictDetWpOps body) stop post ms := by
  constructor
  · intro h
    refine wpUntil_det_induction
      (C := fun s => wpUntilOk (ops := mirStrictDetWpOps body) stop post s)
      (fun _ hs => wpUntil_here (ops := mirStrictDetWpOps body) hs)
      (fun s s' hStep ih => by
        refine wpUntil_step (ops := mirStrictDetWpOps body) ?_
        change match Anneal.PureMirExec.mirStep body s with
          | .cont s₁ => wpUntilOk (ops := mirStrictDetWpOps body) stop post s₁
          | .done o => post o | .fault => False
        rw [mirDetStep_step_iff.mp hStep]; exact ih)
      (fun s out hDone hPost => by
        refine wpUntil_step (ops := mirStrictDetWpOps body) ?_
        change match Anneal.PureMirExec.mirStep body s with
          | .cont s₁ => wpUntilOk (ops := mirStrictDetWpOps body) stop post s₁
          | .done o => post o | .fault => False
        rw [mirDetStep_done_iff.mp hDone]; exact hPost)
      (fun _ _ _ hF => False.elim hF) h
  · exact wpUntil_of_refines (mirStrictDetWpOps_refines_mirDetWpOps body)

theorem wpStateOk_mirDet_iff_strictDet {body : CapturedMir}
    {post : MirOutcome → Prop} {ms : MachineState} :
    wpStateOk (ops := mirDetWpOps body) post ms ↔
      wpStateOk (ops := mirStrictDetWpOps body) post ms :=
  wpUntilOk_mirDet_iff_strictDet

/-- Soundness transport from `wpUntilOk` over `mirDetWpOps body` into
`Anneal.MirFuelFree.MirStepsConverges`, via `wpUntil_det_induction`. -/
theorem mirStepsConverges_of_wpUntilOk {body : CapturedMir} {ms : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : wpUntilOk (ops := mirDetWpOps body) mid post ms) :
    MirStepsConverges body ms mid post :=
  wpUntil_det_induction
    (C := fun s => MirStepsConverges body s mid post)
    (fun _ hMid => MirStepsConverges.refl hMid)
    (fun _ _ hStep ih =>
      Anneal.PureMirExec.mirStepsConverges_of_mirStep_cont
        (mirDetStep_step_iff.mp hStep) ih)
    (fun _ _ hDone hPost =>
      MirStepsConverges.ret_of_step
        (Anneal.PureMirExec.stepMirFn_of_mirStep_done (mirDetStep_done_iff.mp hDone))
        hPost)
    (fun _ _ _ hF => False.elim hF) h

/-- Soundness transport from `wpReach` over `mirDetWpOps body` into
`Anneal.MirFuelFree.MirStepsConverges`. -/
theorem mirStepsConverges_of_wpReach {body : CapturedMir} {ms : MachineState}
    {mid : MachineState → Prop}
    (h : wpReach (ops := mirDetWpOps body) mid ms) :
    MirStepsConverges body ms mid (fun _ => False) :=
  mirStepsConverges_of_wpUntilOk h

/-- Soundness transport from `wpReach` over `mirDetWpOps body` into
`Anneal.MirFuelFree.MirReachState`. -/
theorem mirReachState_of_wpReach {body : CapturedMir} {ms ms' : MachineState}
    (h : wpReach (ops := mirDetWpOps body) (· = ms') ms) :
    MirReachState body ms ms' :=
  mirStepsConverges_of_wpReach h

/-- Soundness transport from `wpStateOk` over `mirDetWpOps body` into
`Anneal.MirFuelFree.MirWpConverges`, via `wpOutcome_det_induction`. -/
theorem mirWpConverges_of_wpStateOk {body : CapturedMir} {ms : MachineState}
    {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirDetWpOps body) post ms) :
    MirWpConverges body ms post :=
  wpOutcome_det_induction
    (C := fun s => MirWpConverges body s post)
    (fun _ _ hStep ih =>
      Anneal.PureMirExec.mirWpConverges_of_mirStep_cont
        (mirDetStep_step_iff.mp hStep) ih)
    (fun _ _ hDone hPost =>
      MirWpConverges.ret_of_step
        (Anneal.PureMirExec.stepMirFn_of_mirStep_done (mirDetStep_done_iff.mp hDone))
        hPost)
    (fun _ _ _ hF => False.elim hF) h

/-- Call-forbidding soundness transport from `wpStateOk` over `mirDetWpOps body`
into `Anneal.MirFuelFree.MirNoCallWpConverges`. -/
theorem mirNoCallWpConverges_of_wpStateOk {body : CapturedMir} {ms : MachineState}
    {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirDetWpOps body) post ms) :
    MirNoCallWpConverges body ms post :=
  wpOutcome_det_induction
    (C := fun s => MirNoCallWpConverges body s post)
    (fun _ _ hStep ih =>
      Anneal.PureMirExec.mirNoCallWpConverges_of_mirStep_cont
        (mirDetStep_step_iff.mp hStep) ih)
    (fun _ _ hDone hPost =>
      Anneal.PureMirExec.mirNoCallWpConverges_of_mirStep_done
        (mirDetStep_done_iff.mp hDone) hPost)
    (fun _ _ _ hF => False.elim hF) h

/-- Total-correctness `DWP` soundness from `wpStateOk (ops := mirDetWpOps body)`. -/
theorem dwp_of_wpStateOk {body : CapturedMir} {ms : MachineState}
    {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirDetWpOps body) post ms) :
    DWP mirDefaultWP (mirTree body ms) (fun out _ => post out) PUnit.unit :=
  dwp_of_mirWpConverges (mirWpConverges_of_wpStateOk h)

/-- Partial-correctness `DWLP` soundness from `wpStateOk (ops := mirDetWpOps body)`. -/
theorem dwlp_of_wpStateOk {body : CapturedMir} {ms : MachineState}
    {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirDetWpOps body) post ms) :
    DWLP mirDefaultWP (mirTree body ms) (fun out _ => post out) PUnit.unit :=
  dwlp_of_mirWpConverges (mirWpConverges_of_wpStateOk h)

/-- Discharge stateless `VerificationResult c` from `wpStateOk (ops := mirDetWpOps c.body)`
(`mirSafePost`). -/
theorem verifyMir_of_wpStateOk (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      wpStateOk (ops := mirDetWpOps c.body)
        (mirSafePost (fun retVal _ => c.post args retVal))
        (initMachineStateWithCallees c.body args c.callees)) :
    VerificationResult c :=
  verifyMir_of_wpConverges c (fun args hPre => mirWpConverges_of_wpStateOk (h args hPre))

/-- Discharge stateless `VerificationResult c` from panic-forbidding
`wpStateOk (ops := mirDetWpOps c.body)` (`mirNormalPost`). -/
theorem verifyMirNoPanic_of_wpStateOk (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      wpStateOk (ops := mirDetWpOps c.body)
        (mirNormalPost (fun retVal _ => c.post args retVal))
        (initMachineStateWithCallees c.body args c.callees)) :
    VerificationResult c :=
  verifyMirNoPanic_of_wpConverges c (fun args hPre => mirWpConverges_of_wpStateOk (h args hPre))

/-- Discharge stateful `StatefulVerificationResult c` from
`wpStateOk (ops := mirDetWpOps c.body)` (`mirSafePost`). -/
theorem verifyStatefulMir_of_wpStateOk (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      wpStateOk (ops := mirDetWpOps c.body)
        (mirSafePost (c.post args mem))
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees)) :
    StatefulVerificationResult c :=
  verifyStatefulMir_of_wpConverges c
    (fun args mem hPre => mirWpConverges_of_wpStateOk (h args mem hPre))

/-- Discharge stateful `StatefulVerificationResult c` from panic-forbidding
`wpStateOk (ops := mirDetWpOps c.body)` (`mirNormalPost`). -/
theorem verifyStatefulMirNoPanic_of_wpStateOk (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      wpStateOk (ops := mirDetWpOps c.body)
        (mirNormalPost (c.post args mem))
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees)) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_wpConverges c
    (fun args mem hPre => mirWpConverges_of_wpStateOk (h args mem hPre))

/-- Discharge total-correctness `TotalVerificationResult c` from
`wpStateOk (ops := mirDetWpOps c.body)` (`mirNormalPost`). -/
theorem verifyTotalMir_of_wpStateOk (c : TotalClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      wpStateOk (ops := mirDetWpOps c.body)
        (mirNormalPost (c.post args mem))
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees)) :
    TotalVerificationResult c :=
  verifyTotalMir_of_wpConverges c
    (fun args mem hPre => mirWpConverges_of_wpStateOk (h args mem hPre))

/-! ### Deterministic `stepCfgState` `MirWpOps` (`mirCfgWpOps`) -/

/-- Deterministic step outcome wrapping `Anneal.PureMirExec.stepCfgState body`. -/
@[reducible] def mirCfgStep (body : CapturedMir)
    (cfg : Anneal.PureMirExec.CfgExecState) :
    StepOutcome Anneal.PureMirExec.CfgExecState MirOutcome Unit :=
  match cfg with
  | .halted true out => .done out
  | .halted false _ => .fault ()
  | .faulted => .fault ()
  | .running false _ _ => .fault ()
  | .running true _ _ => .step (Anneal.PureMirExec.stepCfgState body cfg)

/-- Deterministic `MirWpOps` interface over `Anneal.PureMirExec.stepCfgState body`. -/
@[reducible] def mirCfgWpOps (body : CapturedMir) :
    MirWpOps Anneal.PureMirExec.CfgExecState MirOutcome Unit :=
  MirWpOps.ofDetStep (mirCfgStep body)
    (fun cfg => match cfg with
      | .running _ _ ms => some ms.frame.blockIdx
      | _ => none)

theorem exists_cfgStateWP_runCfgSteps_of_wpStateOk {body : CapturedMir}
    {cfg : Anneal.PureMirExec.CfgExecState} {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirCfgWpOps body) post cfg) :
    ∃ fuel, Anneal.PureMirExec.cfgStateWP post
      (Anneal.PureMirExec.runCfgSteps body cfg fuel) :=
  wpOutcome_det_induction
    (C := fun c => ∃ fuel, Anneal.PureMirExec.cfgStateWP post
      (Anneal.PureMirExec.runCfgSteps body c fuel))
    (fun c c' hStep ih => by
      cases c with
      | halted ok out =>
        cases ok <;> cases hStep
      | faulted => cases hStep
      | running ok cur ms =>
        cases ok with
        | false => cases hStep
        | true =>
          injection hStep with hEq
          subst hEq
          rcases ih with ⟨fuel, hFuel⟩
          exact ⟨fuel + 1, by
            rw [Anneal.PureMirExec.runCfgSteps_step]
            exact hFuel⟩)
    (fun c out hDone hPost => by
      cases c with
      | halted ok out₀ =>
        cases ok with
        | false => cases hDone
        | true =>
          injection hDone with hEq
          subst hEq
          exact ⟨0, ⟨rfl, hPost⟩⟩
      | faulted => cases hDone
      | running ok _ _ => cases ok <;> cases hDone)
    (fun _ _ _ hF => False.elim hF) h

/-- Soundness transport from `wpStateOk (ops := mirCfgWpOps body)` into
`MirNoCallWpConverges` for `.runtimeOptimized` bodies. -/
theorem mirNoCallWpConverges_of_cfgWpStateOk {body : CapturedMir}
    (hPhase : body.phase = .runtimeOptimized)
    {cfg : Anneal.PureMirExec.CfgExecState} {ms : MachineState}
    {post : MirOutcome → Prop}
    (hValid : Anneal.PureMirExec.CfgValid body cfg (.running ms))
    (h : wpStateOk (ops := mirCfgWpOps body) post cfg) :
    MirNoCallWpConverges body ms post := by
  rcases exists_cfgStateWP_runCfgSteps_of_wpStateOk h with ⟨fuel, hCfg⟩
  refine ⟨fuel + 1, ?_⟩
  rw [wpMirNoCallSym_eq_wpMirNoCallBounded]
  exact Anneal.PureMirExec.wpCoalBounded_of_runCfgSteps body post hPhase
    fuel cfg (.running ms) hValid hCfg

/-- Soundness transport from `wpStateOk (ops := mirCfgWpOps body)` into
`MirWpConverges` for `.runtimeOptimized` bodies. -/
theorem mirWpConverges_of_cfgWpStateOk {body : CapturedMir}
    (hPhase : body.phase = .runtimeOptimized)
    {cfg : Anneal.PureMirExec.CfgExecState} {ms : MachineState}
    {post : MirOutcome → Prop}
    (hValid : Anneal.PureMirExec.CfgValid body cfg (.running ms))
    (h : wpStateOk (ops := mirCfgWpOps body) post cfg) :
    MirWpConverges body ms post :=
  MirWpConverges.of_noCall (mirNoCallWpConverges_of_cfgWpStateOk hPhase hValid h)

/-! ## 2. Coalgebraic `stepMirState` / `StateEffectWP` Interfaces & `Refines` -/

/-- Lift continuation, terminal, and fault predicates to `MirExecState`. -/
@[reducible] def liftExecCont
    (P : MachineState → Prop) (Q : MirOutcome → Prop) (R : Unit → Prop) :
    MirExecState → Prop
  | .running s => P s
  | .halted out => Q out
  | .faulted _ => R ()

/-- Exact fault classification for a `stepMirState` transition. -/
inductive MirStepFault : Type where
  | fail (kind : FailureKind) : MirStepFault
  | extCall : MirStepFault
  deriving DecidableEq, Repr

/-- Lift continuation, terminal, and `FailureKind`-indexed fault predicates to
`MirExecState`. -/
@[reducible] def liftExecContFail
    (P : MachineState → Prop) (Q : MirOutcome → Prop) (R : FailureKind → Prop) :
    MirExecState → Prop
  | .running s => P s
  | .halted out => Q out
  | .faulted fk => R fk

theorem liftExecContFail_mono
    {P₁ P₂ : MachineState → Prop} {Q₁ Q₂ : MirOutcome → Prop}
    {R₁ R₂ : FailureKind → Prop}
    (hP : ∀ s, P₁ s → P₂ s) (hQ : ∀ o, Q₁ o → Q₂ o) (hR : ∀ f, R₁ f → R₂ f) :
    ∀ st, liftExecContFail P₁ Q₁ R₁ st → liftExecContFail P₂ Q₂ R₂ st
  | .running s, h => hP s h
  | .halted o, h => hQ o h
  | .faulted fk, h => hR fk h

/-- Coalgebraic `MirWpOps` interface directly over
`Trusted.Rustc.V2026_06_01.MirSemantics.stepMirState body` and any stateless
`EffectWP MirEffect` (`StateEffectWP PUnit MirEffect`). -/
@[reducible] def mirEffectWpOps (ewp : EffectWP MirEffect) (body : CapturedMir) :
    MirWpOps MachineState MirOutcome Unit where
  stepWp ms P Q R :=
    match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecCont P Q R st'
    | .vis i k => ewp.wp i (fun o _ => liftExecCont P Q R (k o)) PUnit.unit
  stepWp_mono := by
    intro ms P₁ P₂ Q₁ Q₂ R₁ R₂ hP hQ hR h
    cases hStep : stepMirState body (.running ms) with
    | ret out => rw [hStep] at h; exact hQ out h
    | tau st' =>
      rw [hStep] at h
      cases st' with
      | running s' => exact hP s' h
      | halted o => exact hQ o h
      | faulted _ => exact hR () h
    | vis i k =>
      rw [hStep] at h
      refine ewp.mono (fun o _ ho => ?_) h
      cases hK : k o with
      | running s' => rw [hK] at ho; exact hP s' ho
      | halted out => rw [hK] at ho; exact hQ out ho
      | faulted _ => rw [hK] at ho; exact hR () ho
  blockTag? ms := some ms.frame.blockIdx

/-- Call-free coalgebraic `MirWpOps` interface (`mirNoCallWP` over `stepMirState`). -/
@[reducible] def mirNoCallCoalWpOps (body : CapturedMir) :
    MirWpOps MachineState MirOutcome Unit :=
  mirEffectWpOps mirNoCallWP body

/-- Full coalgebraic `MirWpOps` interface (`mirDefaultWP` over `stepMirState`,
supporting demonic external calls). -/
@[reducible] def mirCoalWpOps (body : CapturedMir) :
    MirWpOps MachineState MirOutcome Unit :=
  mirEffectWpOps mirDefaultWP body

/-- Symbolic-tree call-free coalgebraic `MirWpOps` over `stepMirSymTree` /
`evalSymNodeTreeNoCall`. -/
@[reducible] def mirSymNoCallCoalWpOps (body : CapturedMir) :
    MirWpOps MachineState MirOutcome FailureKind where
  stepWp ms P Q R :=
    evalSymNodeTreeNoCall (liftExecContFail P Q R) Q (stepMirSymTree body ms)
  stepWp_mono := fun hP hQ hR h =>
    evalSymNodeTreeNoCall_mono (liftExecContFail_mono hP hQ hR) hQ h
  blockTag? ms := some ms.frame.blockIdx

/-- Deterministic call-free step extracted directly from `stepMirState body`. -/
def mirNoCallStep (body : CapturedMir) (ms : MachineState) :
    StepOutcome MachineState MirOutcome MirStepFault :=
  match stepMirState body (.running ms) with
  | .ret out => .done out
  | .tau (.running s') => .step s'
  | .tau (.halted out) => .done out
  | .tau (.faulted fk) => .fault (.fail fk)
  | .vis (.inl (.fail fk)) _ => .fault (.fail fk)
  | .vis (.inr (.inl _)) k =>
    match k PUnit.unit with
    | .running s' => .step s'
    | .halted out => .done out
    | .faulted fk => .fault (.fail fk)
  | .vis (.inr (.inr _)) _ => .fault .extCall

/-- Deterministic `MirWpOps` over `mirNoCallStep body` with exact `MirStepFault`. -/
@[reducible] def mirNoCallDetWpOps (body : CapturedMir) :
    MirWpOps MachineState MirOutcome MirStepFault :=
  MirWpOps.ofDetStep (mirNoCallStep body) (fun ms => some ms.frame.blockIdx)

/-- Fault-tracking coalgebraic `MirWpOps` over `stepMirState body`: admits
explicit fault predicates on `MirStepFault` and agrees with `mirCoalWpOps` on
all fault-free proofs (`onFault := fun _ => False`). -/
@[reducible] def mirCoalFaultWpOps (body : CapturedMir) :
    MirWpOps MachineState MirOutcome MirStepFault where
  stepWp ms P Q R :=
    match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecContFail P Q (fun fk => R (.fail fk)) st'
    | .vis (.inl (.fail fk)) _ => R (.fail fk)
    | .vis (.inr (.inl _)) k =>
      liftExecContFail P Q (fun fk => R (.fail fk)) (k PUnit.unit)
    | .vis (.inr (.inr _)) k =>
      R .extCall ∨
        ∀ ans : MirCallAns,
          liftExecContFail P Q (fun fk => R (.fail fk)) (k ans)
  stepWp_mono := by
    intro ms P₁ P₂ Q₁ Q₂ R₁ R₂ hP hQ hR h
    cases hStep : stepMirState body (.running ms) with
    | ret out => rw [hStep] at h; exact hQ out h
    | tau st' =>
      rw [hStep] at h
      exact liftExecContFail_mono hP hQ (fun fk hf => hR (.fail fk) hf) st' h
    | vis i k =>
      rw [hStep] at h
      rcases i with f | (e | c)
      · cases f; exact hR _ h
      · cases e
        exact liftExecContFail_mono hP hQ (fun fk hf => hR (.fail fk) hf)
          (k PUnit.unit) h
      · cases c
        cases h with
        | inl hCall => exact Or.inl (hR .extCall hCall)
        | inr hAll =>
          exact Or.inr (fun ans =>
            liftExecContFail_mono hP hQ (fun fk hf => hR (.fail fk) hf)
              (k ans) (hAll ans))
  blockTag? ms := some ms.frame.blockIdx

/-- Exact `MirWpOps.Refines` from fault-forbidding deterministic `PureMirExec.mirStep`
to call-free coalgebraic `mirNoCallCoalWpOps`. -/
theorem mirStrictDetWpOps_refines_mirNoCallCoalWpOps (body : CapturedMir) :
    (mirStrictDetWpOps body).Refines (mirNoCallCoalWpOps body) := by
  intro ms P Q R h
  change (match Anneal.PureMirExec.mirStep body ms with
    | .cont s' => P s' | .done o => Q o | .fault => False) at h
  change match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecCont P Q R st'
    | .vis i k => mirNoCallWP.wp i (fun o _ => liftExecCont P Q R (k o)) PUnit.unit
  cases hStep : Anneal.PureMirExec.mirStep body ms with
  | fault => rw [hStep] at h; exact False.elim h
  | done out =>
    rw [hStep] at h
    have hRet := Anneal.PureMirExec.stepMirFn_of_mirStep_done hStep
    dsimp only [stepMirState]
    rw [hRet]
    exact h
  | cont s' =>
    rw [hStep] at h
    dsimp only [stepMirState]
    rcases Anneal.PureMirExec.stepMirFn_of_mirStep_cont hStep with hTau | ⟨obs, k, hVis, hK⟩
    · rw [hTau]; exact h
    · rw [hVis]
      change liftExecCont P Q R (k PUnit.unit)
      rw [hK]
      exact h

/-- Exact `MirWpOps.Refines` from call-free coalgebraic `mirNoCallCoalWpOps`
to full coalgebraic `mirCoalWpOps` (`mirDefaultWP`). -/
theorem mirNoCallCoalWpOps_refines_mirCoalWpOps (body : CapturedMir) :
    (mirNoCallCoalWpOps body).Refines (mirCoalWpOps body) := by
  intro ms P Q R h
  change match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecCont P Q R st'
    | .vis i k => mirNoCallWP.wp i (fun o _ => liftExecCont P Q R (k o)) PUnit.unit at h
  change match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecCont P Q R st'
    | .vis i k => mirDefaultWP.wp i (fun o _ => liftExecCont P Q R (k o)) PUnit.unit
  cases hStep : stepMirState body (.running ms) with
  | ret out => rw [hStep] at h; exact h
  | tau st' => rw [hStep] at h; exact h
  | vis i k =>
    rw [hStep] at h
    rcases i with f | (e | c)
    · cases f; exact False.elim h
    · cases e; exact h
    · cases c; exact False.elim h

/-- Exact `MirWpOps.Refines` from fault-forbidding deterministic `PureMirExec.mirStep`
to full coalgebraic `mirCoalWpOps`. -/
theorem mirStrictDetWpOps_refines_mirCoalWpOps (body : CapturedMir) :
    (mirStrictDetWpOps body).Refines (mirCoalWpOps body) :=
  (mirStrictDetWpOps_refines_mirNoCallCoalWpOps body).trans
    (mirNoCallCoalWpOps_refines_mirCoalWpOps body)

/-- Exact `MirWpOps.Refines` from deterministic `mirNoCallDetWpOps` (over
`MirWpOps.ofDetStep`) to coalgebraic `mirCoalFaultWpOps`. -/
theorem mirNoCallDetWpOps_refines_mirCoalFaultWpOps (body : CapturedMir) :
    (mirNoCallDetWpOps body).Refines (mirCoalFaultWpOps body) := by
  intro ms P Q R h
  change (mirNoCallStep body ms).wp P Q R at h
  unfold mirNoCallStep at h
  change match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecContFail P Q (fun fk => R (.fail fk)) st'
    | .vis (.inl (.fail fk)) _ => R (.fail fk)
    | .vis (.inr (.inl _)) k =>
      liftExecContFail P Q (fun fk => R (.fail fk)) (k PUnit.unit)
    | .vis (.inr (.inr _)) k =>
      R .extCall ∨
        ∀ ans : MirCallAns,
          liftExecContFail P Q (fun fk => R (.fail fk)) (k ans)
  cases hStep : stepMirState body (.running ms) with
  | ret out => rw [hStep] at h; exact h
  | tau st' =>
    rw [hStep] at h
    cases st' with
    | running s' => exact h
    | halted out => exact h
    | faulted fk => exact h
  | vis i k =>
    rw [hStep] at h
    rcases i with f | (e | c)
    · cases f; exact h
    · cases e
      dsimp only at h ⊢
      cases hK : k PUnit.unit with
      | running s' => rw [hK] at h; exact h
      | halted out => rw [hK] at h; exact h
      | faulted fk => rw [hK] at h; exact h
    · cases c; exact Or.inl h

/-- Agreement between `mirNoCallCoalWpOps` (`stepMirState` + `mirNoCallWP`) and
`mirSymNoCallCoalWpOps` (`stepMirSymTree` + `evalSymNodeTreeNoCall`) on all
fault-free obligations. -/
theorem mirNoCallCoalWpOps_stepWp_iff_sym (body : CapturedMir)
    (ms : MachineState) (P : MachineState → Prop) (Q : MirOutcome → Prop) :
    (mirNoCallCoalWpOps body).stepWp ms P Q (fun _ => False) ↔
      (mirSymNoCallCoalWpOps body).stepWp ms P Q (fun _ => False) := by
  change (match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecCont P Q (fun _ => False) st'
    | .vis i k =>
      mirNoCallWP.wp i (fun o _ => liftExecCont P Q (fun _ => False) (k o)) PUnit.unit) ↔
    evalSymNodeTreeNoCall (liftExecContFail P Q (fun _ => False)) Q
      (stepMirSymTree body ms)
  rw [evalSymNodeTreeNoCall_eq, stepMirSymTree_eval, evalNodeNoCallWP_eq]
  have hLift : ∀ st, liftExecCont P Q (fun _ => False) st ↔
      liftExecContFail P Q (fun _ => False) st := by
    intro st
    cases st <;> exact Iff.rfl
  dsimp only [stepMirState]
  cases stepMirFn body ms with
  | ret out => exact Iff.rfl
  | tau st' => exact hLift st'
  | vis i k =>
    rcases i with f | (e | c)
    · cases f; exact Iff.rfl
    · cases e; exact hLift (k PUnit.unit)
    · cases c; exact Iff.rfl

/-- Agreement between `mirCoalFaultWpOps` and `mirCoalWpOps` on all fault-free
obligations (`onFault := fun _ => False`). -/
theorem mirCoalFaultWpOps_stepWp_iff_coal (body : CapturedMir)
    (ms : MachineState) (P : MachineState → Prop) (Q : MirOutcome → Prop) :
    (mirCoalFaultWpOps body).stepWp ms P Q (fun _ => False) ↔
      (mirCoalWpOps body).stepWp ms P Q (fun _ => False) := by
  have hLift : ∀ st, liftExecContFail P Q (fun _ => False) st ↔
      liftExecCont P Q (fun _ => False) st := by
    intro st
    cases st <;> exact Iff.rfl
  change (match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecContFail P Q (fun _ => False) st'
    | .vis (.inl (.fail _)) _ => False
    | .vis (.inr (.inl _)) k =>
      liftExecContFail P Q (fun _ => False) (k PUnit.unit)
    | .vis (.inr (.inr _)) k =>
      False ∨ ∀ ans : MirCallAns,
        liftExecContFail P Q (fun _ => False) (k ans)) ↔
    (match stepMirState body (.running ms) with
    | .ret out => Q out
    | .tau st' => liftExecCont P Q (fun _ => False) st'
    | .vis i k =>
      mirDefaultWP.wp i (fun o _ => liftExecCont P Q (fun _ => False) (k o)) PUnit.unit)
  cases stepMirState body (.running ms) with
  | ret _ => exact Iff.rfl
  | tau st' => exact hLift st'
  | vis i k =>
    rcases i with f | (e | c)
    · cases f; exact Iff.rfl
    · cases e; exact hLift (k PUnit.unit)
    · cases c
      exact ⟨fun h => by
        cases h with
        | inl hf => exact False.elim hf
        | inr hAll => exact fun ans => (hLift (k ans)).mp (hAll ans),
       fun hAll => Or.inr (fun ans => (hLift (k ans)).mpr (hAll ans))⟩

theorem wpUntilOk_mirCoalFault_iff_coal {body : CapturedMir}
    {stop : MachineState → Prop} {post : MirOutcome → Prop} {ms : MachineState} :
    wpUntilOk (ops := mirCoalFaultWpOps body) stop post ms ↔
      wpUntilOk (ops := mirCoalWpOps body) stop post ms := by
  constructor
  · intro h
    refine wpUntil_induction (ops := mirCoalFaultWpOps body)
      (fun _ hs => wpUntil_here (ops := mirCoalWpOps body) hs)
      (fun s hs => wpUntil_step (ops := mirCoalWpOps body)
        ((mirCoalFaultWpOps_stepWp_iff_coal body s _ _).mp hs)) h
  · intro h
    refine wpUntil_induction (ops := mirCoalWpOps body)
      (fun _ hs => wpUntil_here (ops := mirCoalFaultWpOps body) hs)
      (fun s hs => wpUntil_step (ops := mirCoalFaultWpOps body)
        ((mirCoalFaultWpOps_stepWp_iff_coal body s _ _).mpr hs)) h

/-- **General coalgebraic total-correctness soundness (`DWP`)**: for any
`ewp : EffectWP MirEffect`, `wpStateOk` over `mirEffectWpOps ewp body` implies
`DWP ewp (mirTree body ms) (fun out _ => post out) PUnit.unit`. -/
theorem dwp_of_effectWpStateOk {ewp : EffectWP MirEffect} {body : CapturedMir}
    {ms : MachineState} {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirEffectWpOps ewp body) post ms) :
    DWP ewp (mirTree body ms) (fun out _ => post out) PUnit.unit := by
  have hExec : ∀ st : MirExecState,
      liftExecCont (fun s => DWP ewp (mirTree body s) (fun out _ => post out) PUnit.unit)
        post (fun _ => False) st →
      DWP ewp (ITree.cofix (stepMirState body) st) (fun out _ => post out) PUnit.unit := by
    intro st hst
    cases st with
    | running s => exact hst
    | halted out =>
      rw [DWP.unfold_eq, ITree.observe_cofix]
      exact hst
    | faulted _ => exact False.elim hst
  refine wpOutcome_induction (ops := mirEffectWpOps ewp body)
    (C := fun s => DWP ewp (mirTree body s) (fun out _ => post out) PUnit.unit) ?_ h
  intro s hs
  unfold mirTree
  rw [DWP.unfold_eq, ITree.observe_cofix]
  change match stepMirState body (.running s) with
    | .ret out => post out
    | .tau st' =>
      liftExecCont (fun s' => DWP ewp (mirTree body s') (fun out _ => post out) PUnit.unit)
        post (fun _ => False) st'
    | .vis i k =>
      ewp.wp i (fun o _ =>
        liftExecCont (fun s' => DWP ewp (mirTree body s') (fun out _ => post out) PUnit.unit)
          post (fun _ => False) (k o)) PUnit.unit at hs
  cases hStep : stepMirState body (.running s) with
  | ret out =>
    rw [hStep] at hs
    exact hs
  | tau st' =>
    rw [hStep] at hs
    exact hExec st' hs
  | vis i k =>
    rw [hStep] at hs
    exact ewp.mono (fun o _ ho => hExec (k o) ho) hs

/-- **General coalgebraic partial-correctness soundness (`DWLP`)**: for any
`ewp : EffectWP MirEffect`, `wlpOutcome` over `mirEffectWpOps ewp body` implies
`DWLP ewp (mirTree body ms) (fun out _ => post out) PUnit.unit`. -/
theorem dwlp_of_effectWlpOutcome {ewp : EffectWP MirEffect} {body : CapturedMir}
    {ms : MachineState} {post : MirOutcome → Prop}
    (h : wlpOutcome (ops := mirEffectWpOps ewp body) post (fun _ => False) ms) :
    DWLP ewp (mirTree body ms) (fun out _ => post out) PUnit.unit := by
  let Inv : ITree MirEffect MirOutcome → PUnit → Prop := fun t _ =>
    ∃ st : MirExecState,
      t = ITree.cofix (stepMirState body) st ∧
      liftExecCont
        (fun s => wlpOutcome (ops := mirEffectWpOps ewp body) post (fun _ => False) s)
        post (fun _ => False) st
  refine DWLP.coinduct Inv ?_ ⟨.running ms, rfl, h⟩
  intro t _ ⟨st, hEq, hSt⟩
  subst hEq
  rw [ITree.observe_cofix]
  cases st with
  | halted out => exact hSt
  | faulted _ => exact False.elim hSt
  | running s =>
    have hUnf := (wlpOutcome_unfold_iff (ops := mirEffectWpOps ewp body)).mp hSt
    change match stepMirState body (.running s) with
      | .ret out => post out
      | .tau st' =>
        liftExecCont
          (fun s' => wlpOutcome (ops := mirEffectWpOps ewp body) post (fun _ => False) s')
          post (fun _ => False) st'
      | .vis i k =>
        ewp.wp i (fun o _ =>
          liftExecCont
            (fun s' => wlpOutcome (ops := mirEffectWpOps ewp body) post (fun _ => False) s')
            post (fun _ => False) (k o)) PUnit.unit at hUnf
    cases hStep : stepMirState body (.running s) with
    | ret out => rw [hStep] at hUnf; exact hUnf
    | tau st' => rw [hStep] at hUnf; exact ⟨st', rfl, hUnf⟩
    | vis i k =>
      rw [hStep] at hUnf
      exact ewp.mono (fun o _ ho => ⟨k o, rfl, ho⟩) hUnf

/-- Soundness of full coalgebraic `mirCoalWpOps` into `DWP mirDefaultWP`. -/
theorem dwp_of_coalWpStateOk {body : CapturedMir} {ms : MachineState}
    {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirCoalWpOps body) post ms) :
    DWP mirDefaultWP (mirTree body ms) (fun out _ => post out) PUnit.unit :=
  dwp_of_effectWpStateOk h

/-- Soundness of `mirCoalWpOps` partial correctness into `DWLP mirDefaultWP`. -/
theorem dwlp_of_coalWlpOutcome {body : CapturedMir} {ms : MachineState}
    {post : MirOutcome → Prop}
    (h : wlpOutcome (ops := mirCoalWpOps body) post (fun _ => False) ms) :
    DWLP mirDefaultWP (mirTree body ms) (fun out _ => post out) PUnit.unit :=
  dwlp_of_effectWlpOutcome h

/-- Soundness of `mirCoalFaultWpOps` into `DWP mirDefaultWP`. -/
theorem dwp_of_coalFaultWpStateOk {body : CapturedMir} {ms : MachineState}
    {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirCoalFaultWpOps body) post ms) :
    DWP mirDefaultWP (mirTree body ms) (fun out _ => post out) PUnit.unit :=
  dwp_of_coalWpStateOk (wpUntilOk_mirCoalFault_iff_coal.mp h)

/-- Soundness of symbolic call-free coalgebraic `mirSymNoCallCoalWpOps` into
`MirWpConverges`. -/
theorem mirWpConverges_of_symNoCallCoalWpStateOk {body : CapturedMir}
    {ms : MachineState} {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirSymNoCallCoalWpOps body) post ms) :
    MirWpConverges body ms post :=
  wpOutcome_induction (ops := mirSymNoCallCoalWpOps body)
    (C := fun s => MirWpConverges body s post)
    (fun _ hStep =>
      MirWpConverges.step
        (evalSymNodeTreeNoCall_mono
          (fun st' h' => by
            cases st' with
            | running s' => exact h'
            | halted o => exact MirExecWpConverges.halted h'
            | faulted _ => exact False.elim h')
          (fun _ hq => hq) hStep))
    h

/-- Soundness of call-free coalgebraic `mirNoCallCoalWpOps` into
`MirWpConverges`. -/
theorem mirWpConverges_of_noCallCoalWpStateOk {body : CapturedMir}
    {ms : MachineState} {post : MirOutcome → Prop}
    (h : wpStateOk (ops := mirNoCallCoalWpOps body) post ms) :
    MirWpConverges body ms post :=
  mirWpConverges_of_symNoCallCoalWpStateOk
    (wpOutcome_induction (ops := mirNoCallCoalWpOps body)
      (C := fun s => wpStateOk (ops := mirSymNoCallCoalWpOps body) post s)
      (fun s hStep =>
        wpOutcome_step (ops := mirSymNoCallCoalWpOps body)
          ((mirNoCallCoalWpOps_stepWp_iff_sym body s _ _).mp hStep))
      h)

/-- Soundness of call-free coalgebraic `mirNoCallCoalWpOps` `wpUntilOk` into
`MirStepsConverges`. -/
theorem mirStepsConverges_of_noCallCoalWpUntilOk {body : CapturedMir}
    {ms : MachineState} {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : wpUntilOk (ops := mirNoCallCoalWpOps body) mid post ms) :
    MirStepsConverges body ms mid post :=
  wpUntil_induction (ops := mirNoCallCoalWpOps body)
    (C := fun s => MirStepsConverges body s mid post)
    (fun _ hMid => MirStepsConverges.refl hMid)
    (fun s hStep => by
      have hSym := (mirNoCallCoalWpOps_stepWp_iff_sym body s _ _).mp hStep
      exact MirStepsConverges.step
        (evalSymNodeTreeNoCall_mono
          (fun st' h' => by
            cases st' with
            | running s' => exact h'
            | halted o => exact h'
            | faulted _ => exact False.elim h')
          (fun _ hq => hq) hSym))
    h

/-- Bounded coalgebraic `wpOutcomeFuel` over full `mirCoalWpOps` (including
external calls) directly implies `wpMirSym` at `fuel + 1` steps. -/
theorem wpMirSym_of_coalWpOutcomeFuel {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {fuel : Nat} {ms : MachineState},
      wpOutcomeFuel (ops := mirCoalWpOps body) post (fun _ => False) fuel ms →
      wpMirSym (fuel + 1) body ms post
  | 0, _, h => False.elim h
  | fuel + 1, ms, h => by
    unfold wpMirSym wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    have hUnf := (wpOutcomeFuel_succ_iff (ops := mirCoalWpOps body)).mp h
    change match stepMirState body (.running ms) with
      | .ret out => post out
      | .tau st' =>
        liftExecCont
          (wpOutcomeFuel (ops := mirCoalWpOps body) post (fun _ => False) fuel)
          post (fun _ => False) st'
      | .vis i k =>
        mirDefaultWP.wp i (fun o _ =>
          liftExecCont
            (wpOutcomeFuel (ops := mirCoalWpOps body) post (fun _ => False) fuel)
            post (fun _ => False) (k o)) PUnit.unit at hUnf
    have hLift : ∀ st,
        liftExecCont
          (wpOutcomeFuel (ops := mirCoalWpOps body) post (fun _ => False) fuel)
          post (fun _ => False) st →
        wpMirExecSym (fuel + 1) body st post := by
      intro st hst
      cases st with
      | running s' => exact wpMirSym_of_coalWpOutcomeFuel hst
      | halted out => exact hst
      | faulted _ => exact False.elim hst
    cases hStep : stepMirState body (.running ms) with
    | ret out => rw [hStep] at hUnf; exact hUnf
    | tau st' => rw [hStep] at hUnf; exact hLift st' hUnf
    | vis i k =>
      rw [hStep] at hUnf
      exact mirDefaultWP.mono (fun o _ ho => hLift (k o) ho) hUnf

/-- Bounded coalgebraic `wpOutcomeFuel` over full `mirCoalWpOps` yields
fuel-free `MirWpConverges`. -/
theorem mirWpConverges_of_coalWpOutcomeFuel {body : CapturedMir}
    {fuel : Nat} {ms : MachineState} {post : MirOutcome → Prop}
    (h : wpOutcomeFuel (ops := mirCoalWpOps body) post (fun _ => False) fuel ms) :
    MirWpConverges body ms post :=
  ⟨fuel + 1, wpMirSym_of_coalWpOutcomeFuel h⟩

/-! ## 3. `BlockTree` & `Chunk8BlockTree` Operational Bridges -/

/-- Exact identification of `Trusted.Sequence.get?` with
`Anneal.ParametricCore.listGet?`, via `listGet?_eq_of_rec`. -/
theorem sequenceGet?_eq_listGet? {α : Type u} (xs : List α) (idx : Nat) :
    Trusted.Sequence.get? xs idx = listGet? xs idx :=
  listGet?_eq_of_rec Trusted.Sequence.get?
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) xs idx

/-- `BlockTree.ofList body.basicBlocks` is a valid block tree for `body`. -/
theorem validBlockTree_basicBlocks (body : CapturedMir) :
    ValidBlockTree body.basicBlocks (BlockTree.ofList body.basicBlocks) :=
  valid_blockTree_ofList body.basicBlocks

/-- `Chunk8BlockTree.ofList body.basicBlocks` is a valid chunk-8 block tree for
`body`. -/
theorem validChunk8BlockTree_basicBlocks (body : CapturedMir) :
    ValidChunk8BlockTree body.basicBlocks (Chunk8BlockTree.ofList body.basicBlocks) :=
  valid_chunk8BlockTree_ofList body.basicBlocks

/-- Any `ValidBlockTree` over `body.basicBlocks` matches `Trusted.Sequence.get?`
for every in-bounds and out-of-bounds block index. -/
theorem validBlockTree_lookup_eq_sequenceGet? {body : CapturedMir}
    {bt : BlockTree BasicBlockData}
    (hValid : ValidBlockTree body.basicBlocks bt) (idx : Nat) :
    bt.lookup? idx = Trusted.Sequence.get? body.basicBlocks idx :=
  (BlockTree.lookup_eq_getElem? hValid idx).trans (sequenceGet?_eq_listGet? _ _).symm

/-- Any `ValidChunk8BlockTree` over `body.basicBlocks` matches
`Trusted.Sequence.get?` for every in-bounds and out-of-bounds block index. -/
theorem validChunk8BlockTree_lookup_eq_sequenceGet? {body : CapturedMir}
    {cbt : Chunk8BlockTree BasicBlockData}
    (hValid : ValidChunk8BlockTree body.basicBlocks cbt) (idx : Nat) :
    cbt.lookup? idx = Trusted.Sequence.get? body.basicBlocks idx :=
  (hValid.2 idx).trans (sequenceGet?_eq_listGet? _ _).symm

/-- `BlockTree.ofList body.basicBlocks` accelerates `V2026_06_01` basic-block
lookup unconditionally across all block indices. -/
theorem blockTree_ofList_basicBlocks_lookup? (body : CapturedMir) (idx : Nat) :
    (BlockTree.ofList body.basicBlocks).lookup? idx =
      Trusted.Sequence.get? body.basicBlocks idx :=
  validBlockTree_lookup_eq_sequenceGet? (validBlockTree_basicBlocks body) idx

/-- `Chunk8BlockTree.ofList body.basicBlocks` accelerates `V2026_06_01`
basic-block lookup unconditionally across all block indices. -/
theorem chunk8BlockTree_ofList_basicBlocks_lookup? (body : CapturedMir) (idx : Nat) :
    (Chunk8BlockTree.ofList body.basicBlocks).lookup? idx =
      Trusted.Sequence.get? body.basicBlocks idx :=
  validChunk8BlockTree_lookup_eq_sequenceGet? (validChunk8BlockTree_basicBlocks body) idx

/-- Parameterized root-body block-lookup wrapper around trusted `stepMirFn`:
when executing `body` itself (`activeCallee = none`), fetches the basic block
through `look s.frame.blockIdx`; when inside an active callee, delegates
directly to `stepMirFn body s`. Zero shadow operational semantics. -/
def stepMirFnWith (body : CapturedMir) (look : Nat → Option BasicBlockData)
    (s : MachineState) : MirStepNode :=
  match s.memory.activeCallee with
  | some _ => stepMirFn body s
  | none =>
    match body.phase with
    | .other _ => MirStepNode.unsupported
    | _ =>
      match look s.frame.blockIdx with
      | none => MirStepNode.fail .ub
      | some bb =>
        match get? bb.statements s.frame.stmtIdx with
        | some stmt => evalStmt s stmt body.localDecls body.layouts
        | none =>
          if s.frame.stmtIdx == length bb.statements then
            evalTerminator s bb.terminator (some body)
          else
            MirStepNode.fail .ub

theorem stepMirFnWith_pointwise (body : CapturedMir)
    (f g : Nat → Option BasicBlockData) (s : MachineState)
    (hEq : f s.frame.blockIdx = g s.frame.blockIdx) :
    stepMirFnWith body f s = stepMirFnWith body g s := by
  unfold stepMirFnWith
  cases s.memory.activeCallee with
  | some _ => rfl
  | none =>
    cases body.phase <;> simp only [hEq]

theorem stepMirFnWith_eq_stepMirFn (body : CapturedMir)
    (look : Nat → Option BasicBlockData) (s : MachineState)
    (hLook : look s.frame.blockIdx = Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx) :
    stepMirFnWith body look s = stepMirFn body s := by
  unfold stepMirFnWith stepMirFn
  cases hAc : s.memory.activeCallee with
  | some _ => rfl
  | none =>
    dsimp only [Option.getD]
    cases body.phase with
    | other _ => rfl
    | runtimePostCleanup => dsimp only; rw [hLook]; rfl
    | runtimeOptimized => dsimp only; rw [hLook]; rfl

/-- Deterministic live step of `body` with root basic-block lookup delegated
to `look`. -/
def mirDetStepWith (body : CapturedMir) (look : Nat → Option BasicBlockData)
    (s : MachineState) : StepOutcome MachineState MirOutcome Unit :=
  match stepMirFnWith body look s with
  | .tau (.running s') => .step s'
  | .vis (.inr (.inl (.emit _))) k =>
    match k PUnit.unit with
    | .running s' => .step s'
    | _ => .fault ()
  | .ret out => .done out
  | _ => .fault ()

theorem mirDetStepWith_pointwise (body : CapturedMir)
    (f g : Nat → Option BasicBlockData) (s : MachineState)
    (hEq : f s.frame.blockIdx = g s.frame.blockIdx) :
    mirDetStepWith body f s = mirDetStepWith body g s := by
  unfold mirDetStepWith
  rw [stepMirFnWith_pointwise body f g s hEq]

theorem mirDetStepWith_eq_mirDetStep_at (body : CapturedMir)
    (look : Nat → Option BasicBlockData) (s : MachineState)
    (hLook : look s.frame.blockIdx = Trusted.Sequence.get? body.basicBlocks s.frame.blockIdx) :
    mirDetStepWith body look s = mirDetStep body s := by
  unfold mirDetStepWith mirDetStep toStepOutcome Anneal.PureMirExec.mirStep
  rw [stepMirFnWith_eq_stepMirFn body look s hLook]
  cases stepMirFn body s with
  | ret out => rfl
  | tau st' => cases st' <;> rfl
  | vis i k =>
    rcases i with f | (e | c)
    · rfl
    · cases e
      dsimp only
      cases k PUnit.unit <;> rfl
    · rfl

theorem mirDetStepWith_listGet?_eq (body : CapturedMir) (s : MachineState) :
    mirDetStepWith body (listGet? body.basicBlocks) s = mirDetStep body s :=
  mirDetStepWith_eq_mirDetStep_at body (listGet? body.basicBlocks) s
    (sequenceGet?_eq_listGet? body.basicBlocks s.frame.blockIdx).symm

theorem mirDetStepWith_validBlockTree_eq {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    (s : MachineState) :
    mirDetStepWith body bt.lookup? s = mirDetStep body s :=
  mirDetStepWith_eq_mirDetStep_at body bt.lookup? s
    (validBlockTree_lookup_eq_sequenceGet? hValid s.frame.blockIdx)

theorem mirDetStepWith_validChunk8BlockTree_eq {body : CapturedMir}
    {cbt : Chunk8BlockTree BasicBlockData}
    (hValid : ValidChunk8BlockTree body.basicBlocks cbt) (s : MachineState) :
    mirDetStepWith body cbt.lookup? s = mirDetStep body s :=
  mirDetStepWith_eq_mirDetStep_at body cbt.lookup? s
    (validChunk8BlockTree_lookup_eq_sequenceGet? hValid s.frame.blockIdx)

/-- Build a `StepStageCut` for live `mirDetStep body` directly by evaluating
`evalBlockTreeToCut` on any `ValidBlockTree body.basicBlocks bt`. -/
theorem stepStageCut_of_validBlockTreeToCut {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : MachineState}
    (hEval : evalBlockTreeToCut bt (mirDetStepWith body) StepOutcome.next?
      (fun ms => ms.frame.blockIdx) cuts fuel s₀ = .cut s₁) :
    StepStageCut (mirDetStep body) fuel s₀ s₁ := by
  have hCut : StepStageCut (mirDetStepWith body (listGet? body.basicBlocks)) fuel s₀ s₁ :=
    stageCut_of_validBlockTreeToCut_of_pointwise hValid (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx))
      hEval
  exact (StepStageCut.congr_step (mirDetStepWith_listGet?_eq body)).mp hCut

/-- Build a `StepStageCut` for live `mirDetStep body` directly by evaluating
`evalBlockTreeFromCut` (taking at least one step past a starting cutpoint). -/
theorem stepStageCut_of_validBlockTreeFromCut {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : MachineState}
    (hEval : evalBlockTreeFromCut bt (mirDetStepWith body) StepOutcome.next?
      (fun ms => ms.frame.blockIdx) cuts fuel s₀ = .cut s₁) :
    StepStageCut (mirDetStep body) (fuel + 1) s₀ s₁ := by
  have hCut : StepStageCut (mirDetStepWith body (listGet? body.basicBlocks))
      (fuel + 1) s₀ s₁ :=
    stageCut_of_validBlockTreeFromCut_of_pointwise hValid (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx))
      hEval
  exact (StepStageCut.congr_step (mirDetStepWith_listGet?_eq body)).mp hCut

/-- Build a `StepStageCut` for live `mirDetStep body` using a `ValidChunk8BlockTree`. -/
theorem stepStageCut_of_validChunk8BlockTreeToCut {body : CapturedMir}
    {cbt : Chunk8BlockTree BasicBlockData}
    (hValid : ValidChunk8BlockTree body.basicBlocks cbt)
    {cuts : MaskTree} {fuel : Nat} {s₀ s₁ : MachineState}
    (hEval : evalChunk8BlockTreeToCut cbt (mirDetStepWith body) StepOutcome.next?
      (fun ms => ms.frame.blockIdx) cuts fuel s₀ = .cut s₁) :
    StepStageCut (mirDetStep body) fuel s₀ s₁ := by
  have hCut : StepStageCut (mirDetStepWith body (listGet? body.basicBlocks)) fuel s₀ s₁ :=
    stageCut_of_validChunk8BlockTreeToCut_of_pointwise hValid (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx))
      hEval
  exact (StepStageCut.congr_step (mirDetStepWith_listGet?_eq body)).mp hCut

/-- Region-guarded `wpReach` for live `(mirDetWpOps body).within (fun s => region s = true)`
directly from `evalBlockTreeToCut` on a `ValidBlockTree`. -/
theorem wpReach_within_of_validBlockTreeToCut {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    {region : MachineState → Bool} {cuts : MaskTree} {fuel : Nat}
    {s₀ s₁ : MachineState}
    (hEval : evalBlockTreeToCut bt
      (fun look => guardStep region (mirDetStepWith body look))
      guardNext? (fun ms => ms.frame.blockIdx) cuts fuel s₀ = .cut s₁) :
    wpReach (ops := (mirDetWpOps body).within (fun s => region s = true))
      (fun s => s = s₁) s₀ := by
  have hW : wpReach
      (ops := (MirWpOps.ofDetStep (mirDetStepWith body (listGet? body.basicBlocks))
        (fun ms => some ms.frame.blockIdx)).within (fun s => region s = true))
      (fun s => s = s₁) s₀ :=
    wpReach_within_of_validBlockTreeToCut_of_pointwise hValid (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx))
      hEval
  refine wpUntil_of_refines ?_ hW
  intro s P Q R ⟨hReg, hStep⟩
  refine ⟨hReg, ?_⟩
  change (mirDetStep body s).wp P Q R
  rw [← mirDetStepWith_listGet?_eq body s]
  exact hStep

/-- Region-guarded `wpReach` from a starting cutpoint via `evalBlockTreeFromCut`. -/
theorem wpReach_within_of_validBlockTreeFromCut {body : CapturedMir}
    {bt : BlockTree BasicBlockData} (hValid : ValidBlockTree body.basicBlocks bt)
    {region : MachineState → Bool} {cuts : MaskTree} {fuel : Nat}
    {s₀ s₁ : MachineState}
    (hEval : evalBlockTreeFromCut bt
      (fun look => guardStep region (mirDetStepWith body look))
      guardNext? (fun ms => ms.frame.blockIdx) cuts fuel s₀ = .cut s₁) :
    wpReach (ops := (mirDetWpOps body).within (fun s => region s = true))
      (fun s => s = s₁) s₀ := by
  have hW : wpReach
      (ops := (MirWpOps.ofDetStep (mirDetStepWith body (listGet? body.basicBlocks))
        (fun ms => some ms.frame.blockIdx)).within (fun s => region s = true))
      (fun s => s = s₁) s₀ :=
    wpReach_within_of_validBlockTreeFromCut_of_pointwise hValid (mirDetStepWith body)
      (fun f g s hEq => mirDetStepWith_pointwise body f g s (hEq s.frame.blockIdx))
      hEval
  refine wpUntil_of_refines ?_ hW
  intro s P Q R ⟨hReg, hStep⟩
  refine ⟨hReg, ?_⟩
  change (mirDetStep body s).wp P Q R
  rw [← mirDetStepWith_listGet?_eq body s]
  exact hStep

/-! ## 4. `StageCut` / `StepStageCut` / `DetStageCut` ↔ `MirWpConverges` & `PureLift` -/

/-- A sealed `StepStageCut` on `mirDetStep body` establishes `MirReachState`. -/
theorem mirReachState_of_stepStageCut {body : CapturedMir} {fuel : Nat}
    {s₀ s₁ : MachineState} (hCut : StepStageCut (mirDetStep body) fuel s₀ s₁) :
    MirReachState body s₀ s₁ :=
  mirReachState_of_wpReach (StepStageCut.to_wpReach hCut)

/-- Prepend a sealed `StepStageCut` onto a `MirWpConverges` continuation. -/
theorem mirWpConverges_of_stepStageCut {body : CapturedMir} {fuel : Nat}
    {s₀ s₁ : MachineState} {post : MirOutcome → Prop}
    (hCut : StepStageCut (mirDetStep body) fuel s₀ s₁)
    (hCont : MirWpConverges body s₁ post) :
    MirWpConverges body s₀ post :=
  MirWpConverges.bind_reachState (mirReachState_of_stepStageCut hCut) hCont

/-- A sealed fuel-free `DetStageCut` on `mirDetStep body` establishes
`MirReachState`. -/
theorem mirReachState_of_detStageCut {body : CapturedMir} {s₀ s₁ : MachineState}
    (hCut : DetStageCut (mirDetStep body) s₀ s₁) :
    MirReachState body s₀ s₁ :=
  mirReachState_of_wpReach (detStageCut_iff_wpReach.mp hCut)

/-- Prepend a sealed fuel-free `DetStageCut` onto a `MirWpConverges`
continuation. -/
theorem mirWpConverges_of_detStageCut {body : CapturedMir} {s₀ s₁ : MachineState}
    {post : MirOutcome → Prop}
    (hCut : DetStageCut (mirDetStep body) s₀ s₁)
    (hCont : MirWpConverges body s₁ post) :
    MirWpConverges body s₀ post :=
  MirWpConverges.bind_reachState (mirReachState_of_detStageCut hCut) hCont

/-- Transport a sealed `StageCut` on `mirDetWpOps body` into `MirStepsConverges`. -/
theorem mirStepsConverges_of_stageCut {body : CapturedMir}
    {entry cut : MachineState → Prop} {post : MirOutcome → Prop}
    (hCut : StageCut (ops := mirDetWpOps body) entry cut post (fun _ => False))
    {s : MachineState} (hEntry : entry s) :
    MirStepsConverges body s cut post :=
  mirStepsConverges_of_wpUntilOk (StageCut.elim (ops := mirDetWpOps body) hCut hEntry)

/-- Transport a sealed `StageCut` plus cutpoint continuation into
`MirWpConverges`. -/
theorem mirWpConverges_of_stageCut {body : CapturedMir}
    {entry cut : MachineState → Prop} {post : MirOutcome → Prop}
    (hCut : StageCut (ops := mirDetWpOps body) entry cut post (fun _ => False))
    (hCont : ∀ s', cut s' → MirWpConverges body s' post)
    {s : MachineState} (hEntry : entry s) :
    MirWpConverges body s post :=
  MirWpConverges.bind (mirStepsConverges_of_stageCut hCut hEntry) hCont

/-- Transport a sealed `StageCut` on `mirNoCallCoalWpOps body` into
`MirWpConverges`. -/
theorem mirWpConverges_of_coalStageCut {body : CapturedMir}
    {entry cut : MachineState → Prop} {post : MirOutcome → Prop}
    (hCut : StageCut (ops := mirNoCallCoalWpOps body) entry cut post (fun _ => False))
    (hCont : ∀ s', cut s' → MirWpConverges body s' post)
    {s : MachineState} (hEntry : entry s) :
    MirWpConverges body s post :=
  MirWpConverges.bind
    (mirStepsConverges_of_noCallCoalWpUntilOk
      (StageCut.elim (ops := mirNoCallCoalWpOps body) hCut hEntry)) hCont

/-- **Step-counted `StepStageCut` → `PureLift.MirLiftCoreInterop.StepPath`**:
transports a sealed `StepStageCut` into an exact-length `StepPath` over
`PureMirExec.mirStep body` via `StepStageCut.induction`, without unsealing. -/
theorem stepPath_of_stepStageCut {body : CapturedMir} {fuel : Nat}
    {s₀ s₁ : MachineState} (hCut : StepStageCut (mirDetStep body) fuel s₀ s₁) :
    ∃ k, k ≤ fuel ∧
      Anneal.PureLift.MirLiftCoreInterop.StepPath
        (Anneal.PureMirExec.mirStep body) s₀ k s₁ :=
  StepStageCut.induction
    (R := Anneal.PureLift.MirLiftCoreInterop.StepPath (Anneal.PureMirExec.mirStep body))
    (fun s => .refl s)
    (fun _ _ _ _ hStep hRest => .cons (mirDetStep_step_iff.mp hStep) hRest)
    hCut

/-- Converse: every `PureLift` `StepPath` over `PureMirExec.mirStep body` seals
into a `StepStageCut` at the exact step count `k`. -/
theorem stepStageCut_of_stepPath {body : CapturedMir} {k : Nat}
    {s₀ s₁ : MachineState}
    (hPath : Anneal.PureLift.MirLiftCoreInterop.StepPath
      (Anneal.PureMirExec.mirStep body) s₀ k s₁) :
    StepStageCut (mirDetStep body) k s₀ s₁ := by
  induction hPath with
  | refl s => exact StepStageCut.refl (mirDetStep body) 0 s
  | cons hStep _ ih =>
    exact StepStageCut.step (mirDetStep_step_iff.mpr hStep) ih

/-- **Fuel-free `DetStageCut` → `PureLift.MirLiftCoreInterop.StepPath`**:
extracts an exact `StepPath` witness via `DetStageCut.exists_fuel` and
`StepStageCut.induction`. -/
theorem stepPath_of_detStageCut {body : CapturedMir} {s₀ s₁ : MachineState}
    (hCut : DetStageCut (mirDetStep body) s₀ s₁) :
    ∃ k, Anneal.PureLift.MirLiftCoreInterop.StepPath
      (Anneal.PureMirExec.mirStep body) s₀ k s₁ := by
  rcases DetStageCut.exists_fuel hCut with ⟨_, hStep⟩
  rcases stepPath_of_stepStageCut hStep with ⟨k, _, hPath⟩
  exact ⟨k, hPath⟩

/-- Every `PureLift` `StepPath` seals into a fuel-free `DetStageCut`. -/
theorem detStageCut_of_stepPath {body : CapturedMir} {k : Nat}
    {s₀ s₁ : MachineState}
    (hPath : Anneal.PureLift.MirLiftCoreInterop.StepPath
      (Anneal.PureMirExec.mirStep body) s₀ k s₁) :
    DetStageCut (mirDetStep body) s₀ s₁ :=
  DetStageCut.of_stepStageCut (stepStageCut_of_stepPath hPath)

/-- Exact equivalence between fuel-free `DetStageCut` and existential
`PureLift.MirLiftCoreInterop.StepPath`. -/
theorem detStageCut_iff_exists_stepPath {body : CapturedMir}
    {s₀ s₁ : MachineState} :
    DetStageCut (mirDetStep body) s₀ s₁ ↔
      ∃ k, Anneal.PureLift.MirLiftCoreInterop.StepPath
        (Anneal.PureMirExec.mirStep body) s₀ k s₁ :=
  ⟨stepPath_of_detStageCut, fun ⟨_, hPath⟩ => detStageCut_of_stepPath hPath⟩

/-- **`mirOperationalAdapter` `ExecutesTo` from `StepStageCut`**: a sealed
`StepStageCut` supplies the `ExecutesTo` step-path witness of
`Anneal.PureLift.V2026_06_01Bridge.mirOperationalAdapter`. -/
theorem mirOperationalAdapter_executesTo_of_stepStageCut
    (tagOf : Anneal.PureLift.LoanId → Nat) (body : CapturedMir)
    (bindings : List (Anneal.PureLift.LoanId × Local × Anneal.PureLift.SubPath))
    (rootAddrs : List (Anneal.PureLift.LoanId × Local × Anneal.PureLift.SubPath) := [])
    {fuel : Nat} {s₀ s₁ : MachineState}
    (hCut : StepStageCut (mirDetStep body) fuel s₀ s₁) :
    ∃ k, k ≤ fuel ∧
      (Anneal.PureLift.V2026_06_01Bridge.mirOperationalAdapter tagOf body bindings
        rootAddrs).ExecutesTo s₀ k s₁ :=
  stepPath_of_stepStageCut hCut

/-- **`mir_pure_lift_sound` via `StepStageCut`**: discharges `mir_pure_lift_sound`
when the live simulation supplies a sealed `StepStageCut` instead of raw
`StepPath` steps. -/
theorem mir_pure_lift_sound_of_stepStageCut
    (tagOf : Anneal.PureLift.LoanId → Nat) (body : CapturedMir)
    (bindings : List (Anneal.PureLift.LoanId × Local × Anneal.PureLift.SubPath))
    (params : List (Anneal.PureLift.ParamInput Anneal.PureLift.StdVal))
    (plan : Anneal.PureLift.FlowPlan Anneal.PureLift.StdVal)
    (retExpr : Anneal.PureLift.RvalOp Anneal.PureLift.StdVal)
    (post : Anneal.PureLift.FuncOut Anneal.PureLift.StdVal → Prop)
    (m0 : MachineState)
    (rootAddrs : List (Anneal.PureLift.LoanId × Local × Anneal.PureLift.SubPath) := [])
    (hInit : ∃ st0,
      Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st0 ∧
      Anneal.PureLift.V2026_06_01Bridge.mirStateRel tagOf bindings st0 m0)
    (hSpec : Anneal.PureLift.HoldsFnSpec
      (Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params plan retExpr) post)
    (hSim : ∀ st0 out,
      Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st0 →
      Anneal.PureLift.V2026_06_01Bridge.mirStateRel tagOf bindings st0 m0 →
      Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params plan retExpr = .ok out →
      ∃ fuel mFinal,
        StepStageCut (mirDetStep body) fuel m0 mFinal ∧
        Anneal.PureLift.V2026_06_01Bridge.MirReturnRel tagOf body out mFinal rootAddrs) :
    MirWpConverges body m0
      (fun o => Anneal.PureLift.V2026_06_01Bridge.LiftedMirPost tagOf post o rootAddrs) := by
  refine Anneal.PureLift.V2026_06_01Bridge.mir_pure_lift_sound tagOf body bindings
    params plan retExpr post m0 rootAddrs hInit hSpec ?_
  intro st0 out hSt0 hRel hEval
  rcases hSim st0 out hSt0 hRel hEval with ⟨fuel, mFinal, hCut, hRet⟩
  rcases stepPath_of_stepStageCut hCut with ⟨k, _, hPath⟩
  exact ⟨k, mFinal, hPath, hRet⟩

/-- **Seamless `ParametricCore.StageCut` + `PureLift` composition**: prepend a
`ParametricCore.StageCut` (possibly composed via `stageCut_compose` and framed
via `stageCut_frame` / `stageCut_frame_within`) onto a `PureLift`-certified
continuation (`mir_pure_lift_sound`), yielding end-to-end `MirWpConverges`. -/
theorem mirWpConverges_stageCut_then_pureLift
    (tagOf : Anneal.PureLift.LoanId → Nat) (body : CapturedMir)
    (bindings : List (Anneal.PureLift.LoanId × Local × Anneal.PureLift.SubPath))
    (params : List (Anneal.PureLift.ParamInput Anneal.PureLift.StdVal))
    (plan : Anneal.PureLift.FlowPlan Anneal.PureLift.StdVal)
    (retExpr : Anneal.PureLift.RvalOp Anneal.PureLift.StdVal)
    (post : Anneal.PureLift.FuncOut Anneal.PureLift.StdVal → Prop)
    (entry cut : MachineState → Prop)
    (rootAddrs : List (Anneal.PureLift.LoanId × Local × Anneal.PureLift.SubPath) := [])
    (hStage : StageCut (ops := mirDetWpOps body) entry cut
      (fun o => Anneal.PureLift.V2026_06_01Bridge.LiftedMirPost tagOf post o rootAddrs)
      (fun _ => False))
    (hSpec : Anneal.PureLift.HoldsFnSpec
      (Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params plan retExpr) post)
    (hCutInit : ∀ mc, cut mc →
      ∃ st0,
        Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st0 ∧
        Anneal.PureLift.V2026_06_01Bridge.mirStateRel tagOf bindings st0 mc)
    (hCutSim : ∀ mc st0 out, cut mc →
      Anneal.PureLift.initFnState Anneal.PureLift.stdValAlg params = .ok st0 →
      Anneal.PureLift.V2026_06_01Bridge.mirStateRel tagOf bindings st0 mc →
      Anneal.PureLift.evalFnValue Anneal.PureLift.stdValAlg params plan retExpr = .ok out →
      ∃ mFinal,
        DetStageCut (mirDetStep body) mc mFinal ∧
        Anneal.PureLift.V2026_06_01Bridge.MirReturnRel tagOf body out mFinal rootAddrs)
    {m0 : MachineState} (hEntry : entry m0) :
    MirWpConverges body m0
      (fun o => Anneal.PureLift.V2026_06_01Bridge.LiftedMirPost tagOf post o rootAddrs) := by
  refine mirWpConverges_of_stageCut hStage (fun mc hCut => ?_) hEntry
  refine Anneal.PureLift.V2026_06_01Bridge.mir_pure_lift_sound tagOf body bindings
    params plan retExpr post mc rootAddrs (hCutInit mc hCut) hSpec ?_
  intro st0 out hSt0 hRel hEval
  rcases hCutSim mc st0 out hCut hSt0 hRel hEval with ⟨mFinal, hDet, hRet⟩
  rcases stepPath_of_detStageCut hDet with ⟨k, hPath⟩
  exact ⟨k, mFinal, hPath, hRet⟩

/-! ## 5. `ByteStoreOps` for `V2026_06_01` `Memory` & `SepLogicLenses.ByteMem` -/

/-! ### 5A. `Memory.globals : List CapturedAllocation` (`Option UInt8`) -/

/-- `AllocView` of a `V2026_06_01` `CapturedAllocation`: writable iff
`mutability = .mut` (failing closed on immutable `static` allocations). -/
def capturedAllocView : AllocView CapturedAllocation (Option UInt8) where
  allocId a := a.allocId
  bytes a := a.bytes
  setBytes a bs := { a with bytes := bs }
  writable a := match a.mutability with | .mut => true | .not => false

theorem capturedAllocView_lawful : capturedAllocView.Lawful where
  allocId_setBytes _ _ := rfl
  bytes_setBytes _ _ := rfl
  writable_setBytes _ _ := rfl
  setBytes_bytes _ := rfl
  setBytes_setBytes _ _ _ := rfl

/-- Canonical `ByteStoreOps` instance over `Memory.globals`
(`List CapturedAllocation`). -/
instance memGlobalsByteStoreOps : ByteStoreOps Memory Nat (Option UInt8) :=
  ByteStoreOps.ofTable capturedAllocView
    (fun m => m.globals) (fun m g => { m with globals := g })

/-- Lawfulness of `memGlobalsByteStoreOps` via `LawfulByteStoreOps.ofTable`. -/
instance memGlobalsLawfulByteStoreOps :
    LawfulByteStoreOps Memory Nat (Option UInt8) :=
  LawfulByteStoreOps.ofTable capturedAllocView_lawful
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)

/-- Exact identification of trusted `lookupGlobalAlloc` with `tableFind` via
`tableFind_eq_of_rec`. -/
theorem lookupGlobalAlloc_eq_tableFind (g : List CapturedAllocation) (id : Nat) :
    lookupGlobalAlloc g id = tableFind capturedAllocView id g :=
  tableFind_eq_of_rec (view := capturedAllocView) lookupGlobalAlloc
    (fun _ => rfl) (fun _ _ _ => rfl) g id

/-- Direct recursive global-allocation replacement matching `tableReplace`. -/
def replaceGlobalAlloc (aNew : CapturedAllocation) :
    List CapturedAllocation → List CapturedAllocation
  | [] => []
  | a :: rest =>
    match Nat.beq a.allocId aNew.allocId with
    | true => aNew :: rest
    | false => a :: replaceGlobalAlloc aNew rest

/-- Exact identification of `replaceGlobalAlloc` with `tableReplace` via
`tableReplace_eq_of_rec`. -/
theorem replaceGlobalAlloc_eq_tableReplace (aNew : CapturedAllocation)
    (g : List CapturedAllocation) :
    replaceGlobalAlloc aNew g = tableReplace capturedAllocView aNew g :=
  tableReplace_eq_of_rec (view := capturedAllocView) replaceGlobalAlloc
    (fun _ => rfl) (fun _ _ _ => rfl) aNew g

/-- Fail-closed rejection: an immutable `CapturedAllocation` (`mutability = .not`)
cannot be accessed or written through a `ByteSubLens`. -/
theorem memGlobals_get_none_of_immutable {m : Memory} {L : ByteSubLens Nat}
    {alloc : CapturedAllocation}
    (hFind : lookupGlobalAlloc m.globals L.addr = some alloc)
    (hImm : alloc.mutability = .not) :
    L.get m = none := by
  unfold ByteSubLens.get
  cases Nat.blt 0 L.len with
  | false => rfl
  | true =>
    change tableRead capturedAllocView m.globals L.addr L.offset L.len = none
    rw [lookupGlobalAlloc_eq_tableFind] at hFind
    exact tableRead_none_of_not_writable L.offset L.len hFind
      (by dsimp [capturedAllocView]; rw [hImm])

theorem memGlobals_set_none_of_immutable {m : Memory} {L : ByteSubLens Nat}
    {bs : List (Option UInt8)} {alloc : CapturedAllocation}
    (hFind : lookupGlobalAlloc m.globals L.addr = some alloc)
    (hImm : alloc.mutability = .not) :
    L.set m bs = none := by
  unfold ByteSubLens.set
  cases Nat.blt 0 L.len with
  | false => rfl
  | true =>
    cases Nat.beq bs.length L.len with
    | false => rfl
    | true =>
      dsimp only [ByteStoreOps.writeBytes?, ByteStoreOps.ofTable]
      rw [lookupGlobalAlloc_eq_tableFind] at hFind
      rw [tableWrite_none_of_not_writable L.offset bs hFind
        (by dsimp [capturedAllocView]; rw [hImm])]
      rfl

/-- Canonical alignment oracle on `Memory.globals` built via `tableAlignedAt`,
reading `CapturedAllocation.align.bytes`. -/
def memGlobalsAlignedAt (m : Memory) (id off k : Nat) : Bool :=
  tableAlignedAt capturedAllocView (fun m => m.globals) (fun a => a.align.bytes) m id off k

/-- `memGlobalsAlignedAt` is write-invariant across all `memGlobalsByteStoreOps`
writes, via `ByteStoreOps.ofTable_writePreserves_tableAlignedAt`. -/
theorem memGlobals_writePreserves_alignedAt (id off k : Nat) :
    memGlobalsByteStoreOps.WritePreserves (fun m => memGlobalsAlignedAt m id off k) :=
  ByteStoreOps.ofTable_writePreserves_tableAlignedAt capturedAllocView_lawful
    (fun m : Memory => m.globals) (fun m g => { m with globals := g })
    (fun _ _ => rfl) (fun a => a.align.bytes) (fun _ _ => rfl) id off k

/-- `WritePreserves` invariance of every non-byte field of `Memory` across
`ByteSubLens.set`, `AlignedSubLens.set`, `execMutSummary`, and
`execMutSummaryChain`. -/
theorem memGlobals_writePreserves_borrows :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.borrows) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_nextAllocId :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.nextAllocId) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_nextTag :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.nextTag) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_callees :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.callees) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_callStack :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.callStack) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_activeCallee :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.activeCallee) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_traitImpls :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.traitImpls) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_activeProtectors :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.activeProtectors) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

theorem memGlobals_writePreserves_callerLocals :
    memGlobalsByteStoreOps.WritePreserves (fun m : Memory => m.callerLocals) :=
  ByteStoreOps.ofTable_writePreserves _ _ _ _ (fun _ _ => rfl)

/-- Allocation alignment metadata is preserved across all global-byte writes
via `ByteStoreOps.ofTable_writePreserves_find`. -/
theorem memGlobals_writePreserves_align (id : Nat) :
    memGlobalsByteStoreOps.WritePreserves
      (fun m : Memory => (lookupGlobalAlloc m.globals id).map (fun a => a.align)) := by
  have h := ByteStoreOps.ofTable_writePreserves_find capturedAllocView_lawful
    (fun m : Memory => m.globals) (fun m g => { m with globals := g })
    (fun _ _ => rfl) (fun a => a.align) (fun _ _ => rfl) id
  intro m m' addr off bs hW
  have hEq := h m m' addr off bs hW
  dsimp only at hEq ⊢
  rw [lookupGlobalAlloc_eq_tableFind, lookupGlobalAlloc_eq_tableFind]
  exact hEq

/-- Allocation mutability metadata is preserved across all global-byte writes
via `ByteStoreOps.ofTable_writePreserves_find`. -/
theorem memGlobals_writePreserves_mutability (id : Nat) :
    memGlobalsByteStoreOps.WritePreserves
      (fun m : Memory => (lookupGlobalAlloc m.globals id).map (fun a => a.mutability)) := by
  have h := ByteStoreOps.ofTable_writePreserves_find capturedAllocView_lawful
    (fun m : Memory => m.globals) (fun m g => { m with globals := g })
    (fun _ _ => rfl) (fun a => a.mutability) (fun _ _ => rfl) id
  intro m m' addr off bs hW
  have hEq := h m m' addr off bs hW
  dsimp only at hEq ⊢
  rw [lookupGlobalAlloc_eq_tableFind, lookupGlobalAlloc_eq_tableFind]
  exact hEq

/-- Allocation relocation metadata is preserved across all global-byte writes. -/
theorem memGlobals_writePreserves_relocations (id : Nat) :
    memGlobalsByteStoreOps.WritePreserves
      (fun m : Memory => (lookupGlobalAlloc m.globals id).map (fun a => a.relocations)) := by
  have h := ByteStoreOps.ofTable_writePreserves_find capturedAllocView_lawful
    (fun m : Memory => m.globals) (fun m g => { m with globals := g })
    (fun _ _ => rfl) (fun a => a.relocations) (fun _ _ => rfl) id
  intro m m' addr off bs hW
  have hEq := h m m' addr off bs hW
  dsimp only at hEq ⊢
  rw [lookupGlobalAlloc_eq_tableFind, lookupGlobalAlloc_eq_tableFind]
  exact hEq

/-- `AlignedSubLens.set` preserves any `WritePreserves` projection `proj`. -/
theorem alignedSubLens_set_preserves {Mem Addr Byte : Type}
    [ops : ByteStoreOps Mem Addr Byte] {V : Sort u} {proj : Mem → V}
    (hPres : ops.WritePreserves proj)
    {alignedAt : Mem → Addr → Nat → Nat → Bool} {A : AlignedSubLens Addr}
    {m m' : Mem} {bs : List Byte}
    (hSet : A.set alignedAt m bs = some m') :
    proj m' = proj m :=
  ByteSubLens.set_preserves hPres (AlignedSubLens.set_inv hSet).2

/-! ### 5B. Tree Borrows Disjoint `ByteRangePerm` Non-Interference -/

/-- Lens corresponding to a `ByteRangePerm`'s allocation and byte range. -/
def byteRangePermLens (entry : Anneal.Memory.ByteRangePerm) : ByteSubLens Nat where
  addr := entry.allocId
  offset := entry.offset
  len := entry.len

/-- Separated byte sub-lenses have zero Tree Borrows overlap
(`Anneal.Memory.byteRangeOverlapsWrite = false`). -/
theorem byteRangeOverlapsWrite_false_of_separated
    (entry : Anneal.Memory.ByteRangePerm) (writeLens : ByteSubLens Nat)
    (hSep : (byteRangePermLens entry).Separated writeLens) :
    Anneal.Memory.byteRangeOverlapsWrite entry
      writeLens.addr writeLens.offset writeLens.len = false := by
  unfold Anneal.Memory.byteRangeOverlapsWrite byteRangesOverlapBool
  cases hSep with
  | inl hNe =>
    have hBeq : Nat.beq entry.allocId writeLens.addr = false :=
      natBeq_false_of_not_eq hNe
    rw [hBeq]
    rfl
  | inr hDisj =>
    cases hBeq : Nat.beq entry.allocId writeLens.addr with
    | false => rfl
    | true =>
      cases hDisj with
      | inl hLe =>
        dsimp only [byteRangePermLens] at hLe
        have hNotLt : Nat.ble writeLens.offset.succ (Nat.add entry.offset entry.len) = false := by
          cases hB : Nat.ble writeLens.offset.succ (Nat.add entry.offset entry.len) with
          | false => rfl
          | true =>
            have hLt : writeLens.offset + 1 ≤ entry.offset + entry.len :=
              Nat.le_of_ble_eq_true hB
            omega
        rw [hNotLt]
        cases Nat.beq entry.len 0 <;> cases Nat.beq writeLens.len 0 <;>
          cases Nat.ble entry.offset.succ (Nat.add writeLens.offset writeLens.len) <;> rfl
      | inr hLe =>
        dsimp only [byteRangePermLens] at hLe
        have hNotLt : Nat.ble entry.offset.succ (Nat.add writeLens.offset writeLens.len) = false := by
          cases hB : Nat.ble entry.offset.succ (Nat.add writeLens.offset writeLens.len) with
          | false => rfl
          | true =>
            have hLt : entry.offset + 1 ≤ writeLens.offset + writeLens.len :=
              Nat.le_of_ble_eq_true hB
            omega
        rw [hNotLt]
        cases Nat.beq entry.len 0 <;> cases Nat.beq writeLens.len 0 <;>
          cases Nat.ble writeLens.offset.succ (Nat.add entry.offset entry.len) <;> rfl

/-- Separated write leaves any Tree Borrows `ByteRangePerm` untouched under
`stepForeignWriteByteRange`. -/
theorem stepForeignWriteByteRange_unchanged_of_separated
    (ps : Anneal.Memory.ProtectorSet) (entry : Anneal.Memory.ByteRangePerm)
    (writeLens : ByteSubLens Nat)
    (hSep : (byteRangePermLens entry).Separated writeLens) :
    Anneal.Memory.stepForeignWriteByteRange ps entry
      writeLens.addr writeLens.offset writeLens.len = some entry :=
  Anneal.Memory.disjoint_byte_range_non_interference ps entry
    writeLens.addr writeLens.offset writeLens.len
    (byteRangeOverlapsWrite_false_of_separated entry writeLens hSep)

/-- Operational Tree Borrows non-interference on a live `BorrowEntry`: a write
to a separated `ByteSubLens` leaves both the abstract `stepForeignWriteByteRange`
and the trusted `updateBorrowPermAtProj` unchanged. -/
theorem borrowEntry_operational_non_interference_of_separated
    (entry : BorrowEntry) (activeProtectors : List Nat)
    (writeLens : ByteSubLens Nat) (writeProj : List ProjectionElem)
    (hEntryLen : Nat.beq entry.rangeLen 0 = false)
    (hWriteLen : Nat.beq writeLens.len 0 = false)
    (hSep : (byteRangePermLens (Anneal.Memory.BorrowEntry.toByteRangePerm entry)).Separated
      writeLens) :
    Anneal.Memory.stepForeignWriteByteRange { activeLifetimes := activeProtectors }
      (Anneal.Memory.BorrowEntry.toByteRangePerm entry)
      writeLens.addr writeLens.offset writeLens.len =
      some (Anneal.Memory.BorrowEntry.toByteRangePerm entry) ∧
    updateBorrowPermAtProj entry writeLens.addr none writeProj
      writeLens.offset writeLens.len entry.targetFrameDepth = entry :=
  Anneal.Memory.disjoint_byte_range_operational_non_interference entry activeProtectors
    writeLens.addr writeProj writeLens.offset writeLens.len hEntryLen hWriteLen
    (byteRangeOverlapsWrite_false_of_separated _ writeLens hSep)

/-! ### 5C. `ByteMem` Store & `SliceCodec` ↔ `ByteLensCodec` / `TypedAt` / `MirTypedByteCodec` -/

/-- `ByteCodec` for `Option UInt8` (`CapturedAllocation` bytes). -/
abbrev optUInt8ByteCodec : ByteCodec (Option UInt8) :=
  ByteCodec.option ByteCodec.uint8

theorem optUInt8ByteCodec_exact : optUInt8ByteCodec.Exact :=
  ByteCodec.option_exact ByteCodec.uint8_exact

/-- `ByteCodec` for provenance-free initialized `AbstractByte`s. -/
def abstractByteCodec : ByteCodec AbstractByte where
  enc b := .init (UInt8.ofBitVec b) none
  dec
    | .uninit => none
    | .init u _ => some u.toBitVec
  dec_enc b := by
    show some (UInt8.ofBitVec b).toBitVec = some b
    rfl

/-- Lift any `Anneal.SepLogicLenses.ByteLensCodec α n` into a `ParametricCore`
`SliceCodec AbstractByte α n` via `SliceCodec.ofGuarded`, with zero extra
proof obligations. -/
def sliceCodecOfByteLensCodec {α : Type} {n : Nat}
    (c : Anneal.SepLogicLenses.ByteLensCodec α n) :
    SliceCodec AbstractByte α n :=
  SliceCodec.ofGuarded n c.encode c.decode c.encode_len c.decode_encode

theorem sliceCodecOfByteLensCodec_dec_of_length {α : Type} {n : Nat}
    (c : Anneal.SepLogicLenses.ByteLensCodec α n)
    {bs : List AbstractByte} (hLen : bs.length = n) :
    (sliceCodecOfByteLensCodec c).dec bs = c.decode bs :=
  SliceCodec.ofGuarded_dec_of_length hLen

/-- Lift any `PureLift.V2026_06_01Bridge.MirTypedByteCodec` into a
`ParametricCore` `SliceCodec AbstractByte α n`. -/
def sliceCodecOfMirTypedByteCodec {layouts : LayoutTable} {ty : Ty}
    {α : Type} {n : Nat}
    (m : Anneal.PureLift.V2026_06_01Bridge.MirTypedByteCodec layouts ty α n) :
    SliceCodec AbstractByte α n :=
  sliceCodecOfByteLensCodec m.codec

theorem sliceCodecOfMirTypedByteCodec_enc_eq {layouts : LayoutTable} {ty : Ty}
    {α : Type} {n : Nat}
    (m : Anneal.PureLift.V2026_06_01Bridge.MirTypedByteCodec layouts ty α n)
    (x : α) :
    encodeValueToBytes defaultCodecFuel layouts ty (m.toValue x) =
      some ((sliceCodecOfMirTypedByteCodec m).enc x) :=
  m.encode_toValue x

theorem sliceCodecOfMirTypedByteCodec_decode_eq {layouts : LayoutTable} {ty : Ty}
    {α : Type} {n : Nat}
    (m : Anneal.PureLift.V2026_06_01Bridge.MirTypedByteCodec layouts ty α n)
    {bs : List AbstractByte} (hLen : bs.length = n) :
    decodeValueFromBytes defaultCodecFuel layouts ty bs =
      ((sliceCodecOfMirTypedByteCodec m).dec bs).map m.toValue := by
  rw [m.decode_eq_map bs, sliceCodecOfMirTypedByteCodec,
    sliceCodecOfByteLensCodec_dec_of_length m.codec hLen]

/-- `ByteStoreOps` on a single `Anneal.SepLogicLenses.ByteMem` (`List AbstractByte`),
backed directly by `sliceAbstractBytes` / `writeAbstractBytesAt`. -/
instance byteMemByteStoreOps :
    ByteStoreOps Anneal.SepLogicLenses.ByteMem Unit AbstractByte where
  readBytes? bm _ off len :=
    match Nat.ble (off + len) bm.length with
    | true => some ((bm.drop off).take len)
    | false => none
  writeBytes? bm _ off bs :=
    match Nat.ble (off + bs.length) bm.length with
    | true => some (listSplice bm off bs)
    | false => none
  addrDisjoint _ off₁ len₁ _ off₂ len₂ :=
    off₁ + len₁ ≤ off₂ ∨ off₂ + len₂ ≤ off₁

instance byteMemLawfulByteStoreOps :
    LawfulByteStoreOps Anneal.SepLogicLenses.ByteMem Unit AbstractByte where
  read_len := by
    intro bm _ off len bs h
    dsimp [ByteStoreOps.readBytes?] at h
    cases hB : Nat.ble (off + len) bm.length with
    | false => rw [hB] at h; cases h
    | true =>
      rw [hB] at h
      injection h with hEq
      subst hEq
      exact listSlice_length bm off len (Nat.le_of_ble_eq_true hB)
  read_sub := by
    intro bm _ off len rel k bs h hLe
    dsimp [ByteStoreOps.readBytes?] at h ⊢
    cases hB : Nat.ble (off + len) bm.length with
    | false => rw [hB] at h; cases h
    | true =>
      rw [hB] at h
      injection h with hEq
      subst hEq
      have hBound : off + len ≤ bm.length := Nat.le_of_ble_eq_true hB
      have hSub : off + rel + k ≤ bm.length := by omega
      rw [Nat.ble_eq_true_of_le hSub]
      exact congrArg some (listSlice_slice bm off len rel k hLe).symm
  write_sub := by
    intro bm _ off len rel old sub hRead hLe
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hRead ⊢
    cases hB : Nat.ble (off + len) bm.length with
    | false => rw [hB] at hRead; cases hRead
    | true =>
      rw [hB] at hRead
      injection hRead with hOld
      subst hOld
      have hBound : off + len ≤ bm.length := Nat.le_of_ble_eq_true hB
      have hSub : off + rel + sub.length ≤ bm.length := by omega
      have hSpLen : (listSplice ((bm.drop off).take len) rel sub).length = len :=
        (listSplice_length _ rel sub
          (by rw [listSlice_length bm off len hBound]; exact hLe)).trans
          (listSlice_length bm off len hBound)
      rw [Nat.ble_eq_true_of_le hSub, hSpLen, Nat.ble_eq_true_of_le hBound]
      exact congrArg some (listSplice_sub bm off len rel sub hBound hLe)
  read_write_same := by
    intro bm bm' _ off bs hW
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hW ⊢
    cases hB : Nat.ble (off + bs.length) bm.length with
    | false => rw [hB] at hW; cases hW
    | true =>
      rw [hB] at hW
      injection hW with hEq
      subst hEq
      have hBound : off + bs.length ≤ bm.length := Nat.le_of_ble_eq_true hB
      rw [listSplice_length bm off bs hBound, Nat.ble_eq_true_of_le hBound]
      exact congrArg some (listSplice_read_same bm off bs hBound)
  write_read_same := by
    intro bm _ off len bs hR
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hR ⊢
    cases hB : Nat.ble (off + len) bm.length with
    | false => rw [hB] at hR; cases hR
    | true =>
      rw [hB] at hR
      injection hR with hEq
      subst hEq
      have hBound : off + len ≤ bm.length := Nat.le_of_ble_eq_true hB
      rw [listSlice_length bm off len hBound, Nat.ble_eq_true_of_le hBound]
      exact congrArg some (listSplice_self bm off len hBound)
  write_of_read := by
    intro bm _ off len old bs hR hLen
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hR ⊢
    cases hB : Nat.ble (off + len) bm.length with
    | false => rw [hB] at hR; cases hR
    | true =>
      rw [hLen, hB]
      exact ⟨_, rfl⟩
  write_write_same := by
    intro bm bm₁ _ off bs₁ bs₂ hW hLen
    dsimp [ByteStoreOps.writeBytes?] at hW ⊢
    cases hB : Nat.ble (off + bs₁.length) bm.length with
    | false => rw [hB] at hW; cases hW
    | true =>
      rw [hB] at hW
      injection hW with hEq
      subst hEq
      have hBound : off + bs₁.length ≤ bm.length := Nat.le_of_ble_eq_true hB
      rw [listSplice_length bm off bs₁ hBound, hLen, Nat.ble_eq_true_of_le hBound]
      exact congrArg some (listSplice_overwrite bm off bs₁ bs₂ hBound hLen)
  read_write_disjoint := by
    intro bm bm' _ off₁ bs₁ _ off₂ len₂ hDisj hW
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hW ⊢
    cases hB : Nat.ble (off₁ + bs₁.length) bm.length with
    | false => rw [hB] at hW; cases hW
    | true =>
      rw [hB] at hW
      injection hW with hEq
      subst hEq
      have hBound : off₁ + bs₁.length ≤ bm.length := Nat.le_of_ble_eq_true hB
      rw [listSplice_length bm off₁ bs₁ hBound]
      cases hB2 : Nat.ble (off₂ + len₂) bm.length with
      | false => rfl
      | true =>
        exact congrArg some (listSplice_read_disjoint bm off₁ bs₁ off₂ len₂ hBound hDisj)
  write_write_comm := by
    intro bm bm₁ bm₂ _ off₁ bs₁ _ off₂ bs₂ hDisj hW₁ hW₂
    dsimp [ByteStoreOps.writeBytes?] at hW₁ hW₂ ⊢
    cases hB₁ : Nat.ble (off₁ + bs₁.length) bm.length with
    | false => rw [hB₁] at hW₁; cases hW₁
    | true =>
      rw [hB₁] at hW₁; injection hW₁ with hEq₁; subst hEq₁
      cases hB₂ : Nat.ble (off₂ + bs₂.length) bm.length with
      | false => rw [hB₂] at hW₂; cases hW₂
      | true =>
        rw [hB₂] at hW₂; injection hW₂ with hEq₂; subst hEq₂
        have hb₁ := Nat.le_of_ble_eq_true hB₁
        have hb₂ := Nat.le_of_ble_eq_true hB₂
        rw [listSplice_length bm off₁ bs₁ hb₁, listSplice_length bm off₂ bs₂ hb₂,
          hB₁, hB₂]
        refine ⟨listSplice (listSplice bm off₁ bs₁) off₂ bs₂, rfl, congrArg some ?_⟩
        cases hDisj with
        | inl hSep => exact (listSplice_comm bm off₁ bs₁ off₂ bs₂ hSep (by omega)).symm
        | inr hSep => exact listSplice_comm bm off₂ bs₂ off₁ bs₁ hSep (by omega)
  addrDisjoint_of_separated := by
    intro a₁ a₂ o₁ l₁ o₂ l₂ h
    cases a₁; cases a₂
    rcases h with hNe | hR
    · exact False.elim (hNe rfl)
    · exact hR
  addrDisjoint_symm := fun h => h.symm
  addrDisjoint_mono_sub := by
    intro _ _ o₁ l₁ o₂ l₂ o₁' l₁' o₂' l₂' h1 h2 h3 h4 hD
    cases hD with
    | inl h => exact Or.inl (by omega)
    | inr h => exact Or.inr (by omega)

/-- `ByteSubLens.get` on `ByteMem` agrees with trusted `sliceAbstractBytes`
for every positive-length lens. -/
theorem byteMem_get_eq_sliceAbstractBytes (bm : Anneal.SepLogicLenses.ByteMem)
    (L : ByteSubLens Unit) (hPos : 0 < L.len) :
    L.get bm = sliceAbstractBytes bm L.offset L.len := by
  rw [ByteSubLens.get_of_pos bm hPos, Anneal.SepLogicLenses.sliceAbstractBytes_eq]
  change (match Nat.ble (L.offset + L.len) bm.length with
    | true => some ((bm.drop L.offset).take L.len)
    | false => none) =
    if L.offset + L.len ≤ bm.length then some ((bm.drop L.offset).take L.len) else none
  by_cases h : L.offset + L.len ≤ bm.length
  · rw [Nat.ble_eq_true_of_le h, ite_eq_left h]
  · rw [natBle_false_of_not_le h, ite_eq_right h]

/-- `ByteSubLens.set` on `ByteMem` agrees with trusted `writeAbstractBytesAt`
for every positive-length lens and matching-length byte patch. -/
theorem byteMem_set_eq_writeAbstractBytesAt (bm : Anneal.SepLogicLenses.ByteMem)
    (L : ByteSubLens Unit) (bs : List AbstractByte) (hPos : 0 < L.len)
    (hLen : bs.length = L.len) :
    L.set bm bs = writeAbstractBytesAt bm L.offset bs := by
  rw [ByteSubLens.set_of_pos bm hPos hLen]
  change (match Nat.ble (L.offset + bs.length) bm.length with
    | true => some (listSplice bm L.offset bs)
    | false => none) = writeAbstractBytesAt bm L.offset bs
  by_cases h : L.offset + bs.length ≤ bm.length
  · rw [Nat.ble_eq_true_of_le h,
      Anneal.SepLogicLenses.writeAbstractBytesAt_eq_splice h]
    rfl
  · rw [natBle_false_of_not_le h]
    cases hW : writeAbstractBytesAt bm L.offset bs with
    | none => rfl
    | some bm' =>
      rcases Anneal.SepLogicLenses.writeAbstractBytesAt_some_inv hW with
        ⟨hNil, _⟩ | ⟨hLe, _⟩
      · rw [hNil] at hLen; omega
      · exact False.elim (h hLe)

/-- **`ByteSubLens.getVal` ↔ `SepLogicLenses.TypedAt`**: reading through
`sliceCodecOfByteLensCodec c` on a `ByteSubLens Unit` of length `n > 0`
succeeds with `v` iff `TypedAt c L.offset v bm`. -/
theorem byteMem_getVal_iff_typedAt {α : Type} {n : Nat}
    (c : Anneal.SepLogicLenses.ByteLensCodec α n) (hPos : 0 < n)
    (bm : Anneal.SepLogicLenses.ByteMem) (L : ByteSubLens Unit)
    (hLen : L.len = n) (v : α) :
    L.getVal (sliceCodecOfByteLensCodec c) bm = some v ↔
      Anneal.SepLogicLenses.TypedAt c L.offset v bm := by
  rw [Anneal.SepLogicLenses.typedAt_iff]
  constructor
  · intro hGet
    rcases ByteSubLens.getVal_inv hGet with ⟨_, bs, hR, hDec⟩
    have hBsLen : bs.length = n := (ByteSubLens.get_len hR).trans hLen
    rw [byteMem_get_eq_sliceAbstractBytes bm L (by omega),
      Anneal.SepLogicLenses.sliceAbstractBytes_eq] at hR
    by_cases hB : L.offset + L.len ≤ bm.length
    · rw [ite_eq_left hB] at hR
      injection hR with hEq
      subst hEq
      rw [sliceCodecOfByteLensCodec_dec_of_length c hBsLen] at hDec
      rw [hLen] at hB hDec
      exact ⟨hB, hDec⟩
    · rw [ite_eq_right hB] at hR; cases hR
  · rintro ⟨hB, hDec⟩
    have hR : L.get bm = some ((bm.drop L.offset).take n) := by
      rw [byteMem_get_eq_sliceAbstractBytes bm L (by omega),
        Anneal.SepLogicLenses.sliceAbstractBytes_eq, hLen, ite_eq_left hB]
    have hBsLen : ((bm.drop L.offset).take n).length = n :=
      listSlice_length bm L.offset n hB
    exact ByteSubLens.getVal_of hLen hR
      ((sliceCodecOfByteLensCodec_dec_of_length c hBsLen).trans hDec)

/-- **`ByteSubLens.getVal` from `SepLogicLenses.SliceTypedAt`**: zooming a
slice-wide lens to element `i < wide.2` decodes element `xs[i]`. -/
theorem byteMem_getVal_of_sliceTypedAt {α : Type} {n : Nat}
    {c : Anneal.SepLogicLenses.ByteLensCodec α n} (hPos : 0 < n)
    {wide : Anneal.SepLogicLenses.WidePtrVal} {xs : List α}
    {bm : Anneal.SepLogicLenses.ByteMem}
    (hSlice : Anneal.SepLogicLenses.SliceTypedAt c wide xs bm)
    {i : Nat} (hi : i < xs.length) :
    ((ByteSubLens.mk () wide.1.offsetBytes (wide.2 * n)).zoom (i * n) n).getVal
      (sliceCodecOfByteLensCodec c) bm = some xs[i] :=
  (byteMem_getVal_iff_typedAt c hPos bm _ rfl xs[i]).mpr (hSlice.getElem_typedAt' hi)

/-- **`ByteSubLens.getVal` ↔ trusted `decodeValueFromBytes` via
`PureLift.V2026_06_01Bridge.MirTypedByteCodec`**. -/
theorem byteMem_getVal_mirTypedByteCodec_iff_decode {layouts : LayoutTable}
    {ty : Ty} {α : Type} {n : Nat}
    (m : Anneal.PureLift.V2026_06_01Bridge.MirTypedByteCodec layouts ty α n)
    (bm : Anneal.SepLogicLenses.ByteMem) (L : ByteSubLens Unit)
    (hLen : L.len = n) (x : α) :
    L.getVal (sliceCodecOfMirTypedByteCodec m) bm = some x ↔
      ∃ bs, L.get bm = some bs ∧
        decodeValueFromBytes defaultCodecFuel layouts ty bs = some (m.toValue x) := by
  constructor
  · intro hGet
    rcases ByteSubLens.getVal_inv hGet with ⟨_, bs, hR, hDec⟩
    have hBsLen : bs.length = n := (ByteSubLens.get_len hR).trans hLen
    refine ⟨bs, hR, ?_⟩
    rw [sliceCodecOfMirTypedByteCodec_decode_eq m hBsLen, hDec]
    rfl
  · rintro ⟨bs, hR, hDec⟩
    have hBsLen : bs.length = n := (ByteSubLens.get_len hR).trans hLen
    rw [sliceCodecOfMirTypedByteCodec_decode_eq m hBsLen] at hDec
    cases hC : (sliceCodecOfMirTypedByteCodec m).dec bs with
    | none => rw [hC] at hDec; cases hDec
    | some y =>
      rw [hC] at hDec
      injection hDec with hVal
      have hEq : y = x := m.toValue_injective hVal
      subst hEq
      exact ByteSubLens.getVal_of hLen hR hC

/-! ### Global `CapturedAllocation` ↔ `AbstractByte` & `decodeValueFromBytes` -/

/-- Convert a provenance-free `Option UInt8` byte to an `AbstractByte`. -/
@[reducible] def optUInt8ToAbstractByte : Option UInt8 → AbstractByte
  | none => .uninit
  | some b => .init b none

theorem globalAllocBytesAux_noRelocs (bytes : List (Option UInt8)) :
    ∀ (rem off : Nat), off + rem ≤ bytes.length →
      globalAllocBytesAux bytes [] off rem =
        some (((bytes.drop off).take rem).map optUInt8ToAbstractByte)
  | 0, off, _ => rfl
  | rem + 1, off, hLe => by
    unfold globalAllocBytesAux
    have hLt : off < bytes.length := by omega
    have hGet : Trusted.Sequence.get? bytes off = some bytes[off] := by
      unfold Trusted.Sequence.get?
      exact List.getElem?_eq_getElem hLt
    rw [hGet]
    dsimp only
    rw [globalAllocBytesAux_noRelocs bytes rem (off + 1) (by omega)]
    have hSlice : (bytes.drop off).take (rem + 1) =
        bytes[off] :: (bytes.drop (off + 1)).take rem := by
      rw [List.drop_eq_getElem_cons hLt, List.take_succ_cons]
    rw [hSlice, List.map_cons]
    cases bytes[off] <;> rfl

/-- For a provenance-free mutable `CapturedAllocation`, `ByteSubLens.get` on
`memGlobalsByteStoreOps` agrees directly with trusted
`globalAllocSliceToAbstractBytes` (mapped through `optUInt8ToAbstractByte`). -/
theorem memGlobals_get_eq_globalAllocSliceToAbstractBytes {m : Memory}
    {L : ByteSubLens Nat} {alloc : CapturedAllocation} {bs : List (Option UInt8)}
    (hFind : lookupGlobalAlloc m.globals L.addr = some alloc)
    (hRelocs : alloc.relocations = [])
    (hGet : L.get m = some bs) :
    globalAllocSliceToAbstractBytes alloc L.offset L.len =
      some (bs.map optUInt8ToAbstractByte) := by
  rcases ByteSubLens.get_inv hGet with ⟨_, hRead⟩
  change tableRead capturedAllocView m.globals L.addr L.offset L.len = some bs at hRead
  rw [lookupGlobalAlloc_eq_tableFind] at hFind
  rcases tableRead_inv hRead with ⟨a', hFind', _, hBound, hSlice⟩
  rw [hFind] at hFind'
  injection hFind' with hA
  subst hA
  subst hSlice
  dsimp only [capturedAllocView] at hBound ⊢
  unfold globalAllocSliceToAbstractBytes
  have hOff : L.offset ≤ alloc.bytes.length := by omega
  change (match Nat.ble L.offset alloc.bytes.length with
    | false => none
    | true => globalAllocBytesAux alloc.bytes alloc.relocations L.offset L.len) = _
  rw [Nat.ble_eq_true_of_le hOff, hRelocs]
  exact globalAllocBytesAux_noRelocs alloc.bytes L.len L.offset hBound

/-- `encodeLittleEndianBytes` matches `encodeBytes` over `toLeBytesAux` mapped
through `optUInt8ToAbstractByte`. -/
private theorem toLeBytesAux_eq_encodeLittleEndianBytes :
    ∀ (n v : Nat),
      (encodeBytes optUInt8ByteCodec (Anneal.LeBytes.toLeBytesAux n v)).map
          optUInt8ToAbstractByte =
        encodeLittleEndianBytes v n none
  | 0, _ => rfl
  | n + 1, v => by
    show .init (UInt8.ofBitVec (BitVec.ofNat 8 v)) none ::
      (encodeBytes optUInt8ByteCodec (Anneal.LeBytes.toLeBytesAux n (v / 256))).map
        optUInt8ToAbstractByte =
      .init (UInt8.ofNat v) none :: encodeLittleEndianBytes (Nat.div v 256) n none
    rw [toLeBytesAux_eq_encodeLittleEndianBytes n (v / 256)]
    rfl

/-- `SliceCodec.uint32 optUInt8ByteCodec` agrees with trusted `encodeLittleEndianBytes`
at `u32`. -/
theorem sliceCodec_uint32_optUInt8_encode_eq (v : UInt32) :
    ((SliceCodec.uint32 optUInt8ByteCodec).enc v).map optUInt8ToAbstractByte =
      encodeLittleEndianBytes v.toNat 4 none :=
  toLeBytesAux_eq_encodeLittleEndianBytes 4 v.toNat

/-- Decoding the `AbstractByte` image of `SliceCodec.uint32 optUInt8ByteCodec`
through trusted `decodeValueFromBytes` recovers `Value.scalar ⟨v.toNat, 4⟩`. -/
theorem decodeValueFromBytes_u32_of_getVal {m : Memory} {L : ByteSubLens Nat}
    {alloc : CapturedAllocation} {v : UInt32} (layouts : LayoutTable)
    (hFind : lookupGlobalAlloc m.globals L.addr = some alloc)
    (hRelocs : alloc.relocations = [])
    (hVal : L.getVal (SliceCodec.uint32 optUInt8ByteCodec) m = some v) :
    ∃ bs, globalAllocSliceToAbstractBytes alloc L.offset L.len = some bs ∧
      decodeValueFromBytes defaultCodecFuel layouts { kind := .uint .u32, layoutIdx := 0 } bs =
        some (.scalar ⟨v.toNat, 4⟩) := by
  rcases ByteSubLens.getVal_inv hVal with ⟨_, raw, hGet, hDec⟩
  have hRaw : raw = (SliceCodec.uint32 optUInt8ByteCodec).enc v :=
    ((SliceCodec.uint32_exact optUInt8ByteCodec_exact) raw v hDec).symm
  have hGlob := memGlobals_get_eq_globalAllocSliceToAbstractBytes hFind hRelocs hGet
  refine ⟨raw.map optUInt8ToAbstractByte, hGlob, ?_⟩
  rw [hRaw, sliceCodec_uint32_optUInt8_encode_eq v]
  let x : {n : Nat // n < 256 ^ 4} := ⟨v.toNat, v.toBitVec.isLt⟩
  exact Anneal.SepLogicLenses.decodeValueFromBytes_uintLE_chunk .u32 4 15 layouts rfl
    (by omega) _ x ((Anneal.SepLogicLenses.ByteLensCodec.uintLE 4).encode_len x)
    ((Anneal.SepLogicLenses.ByteLensCodec.uintLE 4).decode_encode x)

/-- Decoding the `AbstractByte` image of `SliceCodec.bool optUInt8ByteCodec`
through trusted `decodeValueFromBytes` recovers `Value.scalar ⟨if b then 1 else 0, 1⟩`. -/
theorem decodeValueFromBytes_bool_of_getVal {m : Memory} {L : ByteSubLens Nat}
    {alloc : CapturedAllocation} {b : Bool} (layouts : LayoutTable)
    (hFind : lookupGlobalAlloc m.globals L.addr = some alloc)
    (hRelocs : alloc.relocations = [])
    (hVal : L.getVal (SliceCodec.bool optUInt8ByteCodec) m = some b) :
    ∃ bs, globalAllocSliceToAbstractBytes alloc L.offset L.len = some bs ∧
      decodeValueFromBytes defaultCodecFuel layouts { kind := .bool, layoutIdx := 0 } bs =
        some (.scalar ⟨if b then 1 else 0, 1⟩) := by
  rcases ByteSubLens.getVal_inv hVal with ⟨_, raw, hGet, hDec⟩
  have hRaw : raw = (SliceCodec.bool optUInt8ByteCodec).enc b :=
    ((SliceCodec.bool_exact optUInt8ByteCodec_exact) raw b hDec).symm
  have hGlob := memGlobals_get_eq_globalAllocSliceToAbstractBytes hFind hRelocs hGet
  refine ⟨raw.map optUInt8ToAbstractByte, hGlob, ?_⟩
  rw [hRaw]
  cases b <;> rfl

/-- `SliceCodec.uint16 optUInt8ByteCodec` agrees with trusted `decodeValueFromBytes`
at `u16`. -/
theorem decodeValueFromBytes_u16_of_getVal {m : Memory} {L : ByteSubLens Nat}
    {alloc : CapturedAllocation} {v : UInt16} (layouts : LayoutTable)
    (hFind : lookupGlobalAlloc m.globals L.addr = some alloc)
    (hRelocs : alloc.relocations = [])
    (hVal : L.getVal (SliceCodec.uint16 optUInt8ByteCodec) m = some v) :
    ∃ bs, globalAllocSliceToAbstractBytes alloc L.offset L.len = some bs ∧
      decodeValueFromBytes defaultCodecFuel layouts { kind := .uint .u16, layoutIdx := 0 } bs =
        some (.scalar ⟨v.toNat, 2⟩) := by
  rcases ByteSubLens.getVal_inv hVal with ⟨_, raw, hGet, hDec⟩
  have hRaw : raw = (SliceCodec.uint16 optUInt8ByteCodec).enc v :=
    ((SliceCodec.uint16_exact optUInt8ByteCodec_exact) raw v hDec).symm
  have hGlob := memGlobals_get_eq_globalAllocSliceToAbstractBytes hFind hRelocs hGet
  refine ⟨raw.map optUInt8ToAbstractByte, hGlob, ?_⟩
  have hEnc : raw.map optUInt8ToAbstractByte = encodeLittleEndianBytes v.toNat 2 none := by
    rw [hRaw]
    exact toLeBytesAux_eq_encodeLittleEndianBytes 2 v.toNat
  rw [hEnc]
  let x : {n : Nat // n < 256 ^ 2} := ⟨v.toNat, v.toBitVec.isLt⟩
  exact Anneal.SepLogicLenses.decodeValueFromBytes_uintLE_chunk .u16 2 15 layouts rfl
    (by omega) _ x ((Anneal.SepLogicLenses.ByteLensCodec.uintLE 2).encode_len x)
    ((Anneal.SepLogicLenses.ByteLensCodec.uintLE 2).decode_encode x)

/-- `SliceCodec.uint64 optUInt8ByteCodec` agrees with trusted `decodeValueFromBytes`
at `u64`. -/
theorem decodeValueFromBytes_u64_of_getVal {m : Memory} {L : ByteSubLens Nat}
    {alloc : CapturedAllocation} {v : UInt64} (layouts : LayoutTable)
    (hFind : lookupGlobalAlloc m.globals L.addr = some alloc)
    (hRelocs : alloc.relocations = [])
    (hVal : L.getVal (SliceCodec.uint64 optUInt8ByteCodec) m = some v) :
    ∃ bs, globalAllocSliceToAbstractBytes alloc L.offset L.len = some bs ∧
      decodeValueFromBytes defaultCodecFuel layouts { kind := .uint .u64, layoutIdx := 0 } bs =
        some (.scalar ⟨v.toNat, 8⟩) := by
  rcases ByteSubLens.getVal_inv hVal with ⟨_, raw, hGet, hDec⟩
  have hRaw : raw = (SliceCodec.uint64 optUInt8ByteCodec).enc v :=
    ((SliceCodec.uint64_exact optUInt8ByteCodec_exact) raw v hDec).symm
  have hGlob := memGlobals_get_eq_globalAllocSliceToAbstractBytes hFind hRelocs hGet
  refine ⟨raw.map optUInt8ToAbstractByte, hGlob, ?_⟩
  have hEnc : raw.map optUInt8ToAbstractByte = encodeLittleEndianBytes v.toNat 8 none := by
    rw [hRaw]
    exact toLeBytesAux_eq_encodeLittleEndianBytes 8 v.toNat
  rw [hEnc]
  let x : {n : Nat // n < 256 ^ 8} := ⟨v.toNat, v.toBitVec.isLt⟩
  exact Anneal.SepLogicLenses.decodeValueFromBytes_uintLE_chunk .u64 8 15 layouts rfl
    (by omega) _ x ((Anneal.SepLogicLenses.ByteLensCodec.uintLE 8).encode_len x)
    ((Anneal.SepLogicLenses.ByteLensCodec.uintLE 8).decode_encode x)

/-! ### 5D. `Memory.callerLocals` Byte-Array Store (`CallerLocalAddr`) -/

/-- Address of a caller-owned `[u8; N]` referent slot in `Memory.callerLocals`,
backing real `&mut [u8]` slice mutations in `V2026_06_01` callee MIR bodies. -/
structure CallerLocalAddr : Type where
  localIdx : Nat
  deriving DecidableEq, Repr

/-- Extract a `List UInt8` from a `Value` list of canonical `u8` scalars
(`.scalar ⟨b, 1⟩` with `b < 256`). -/
def valuesAsU8Bytes? : List Value → Option (List UInt8)
  | [] => some []
  | .scalar ⟨bits, 1⟩ :: rest =>
    if Nat.blt bits 256 then
      match valuesAsU8Bytes? rest with
      | some bs => some (UInt8.ofNat bits :: bs)
      | none => none
    else none
  | _ :: _ => none

/-- Encode a `List UInt8` as a canonical `V2026_06_01` `[u8; N]` aggregate
element list. -/
def u8BytesToValues : List UInt8 → List Value
  | [] => []
  | b :: rest => .scalar ⟨b.toNat, 1⟩ :: u8BytesToValues rest

theorem valuesAsU8Bytes?_u8BytesToValues :
    ∀ bs : List UInt8, valuesAsU8Bytes? (u8BytesToValues bs) = some bs
  | [] => rfl
  | b :: rest => by
    simp only [u8BytesToValues, valuesAsU8Bytes?]
    have hLt : Nat.blt b.toNat 256 = true :=
      Nat.ble_eq_true_of_le (Nat.succ_le_of_lt b.toBitVec.isLt)
    rw [hLt]
    simp only [ite_true]
    rw [valuesAsU8Bytes?_u8BytesToValues rest]
    have hOf : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
    rw [hOf]

theorem u8BytesToValues_of_valuesAsU8Bytes? :
    ∀ {vs : List Value} {bs : List UInt8},
      valuesAsU8Bytes? vs = some bs → u8BytesToValues bs = vs
  | [], bs, h => by injection h with hEq; subst hEq; rfl
  | v :: rest, bs, h => by
    cases v with
    | scalar sc =>
      rcases sc with ⟨bits, sz⟩
      cases sz with
      | zero => cases h
      | succ sz' =>
        cases sz' with
        | succ _ => cases h
        | zero =>
          change valuesAsU8Bytes? (.scalar ⟨bits, 1⟩ :: rest) = some bs at h
          simp only [valuesAsU8Bytes?] at h
          cases hLt : Nat.blt bits 256 with
          | false => rw [hLt] at h; cases h
          | true =>
            rw [hLt] at h
            simp only [ite_true] at h
            cases hR : valuesAsU8Bytes? rest with
            | none => rw [hR] at h; cases h
            | some bs' =>
              rw [hR] at h
              injection h with hEq
              subst hEq
              have hNat : (UInt8.ofNat bits).toNat = bits := by
                have hB : bits < 256 := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hLt)
                exact Nat.mod_eq_of_lt hB
              show .scalar ⟨(UInt8.ofNat bits).toNat, 1⟩ :: u8BytesToValues bs' =
                .scalar ⟨bits, 1⟩ :: rest
              rw [hNat, u8BytesToValues_of_valuesAsU8Bytes? hR]
    | unit | ptr _ _ | aggregate _ _ | uninit => cases h

/-- Extract a `[u8; N]` byte buffer from a `LocalSlot`. -/
def slotAsU8Bytes? : LocalSlot → Option (List UInt8)
  | .init (.aggregate 0 vs) => valuesAsU8Bytes? vs
  | _ => none

/-- Package a `List UInt8` as a live `[u8; N]` `LocalSlot`. -/
def u8BytesToSlot (bs : List UInt8) : LocalSlot :=
  .init (.aggregate 0 (u8BytesToValues bs))

theorem slotAsU8Bytes?_u8BytesToSlot (bs : List UInt8) :
    slotAsU8Bytes? (u8BytesToSlot bs) = some bs :=
  valuesAsU8Bytes?_u8BytesToValues bs

theorem u8BytesToSlot_of_slotAsU8Bytes? {slot : LocalSlot} {bs : List UInt8}
    (h : slotAsU8Bytes? slot = some bs) :
    u8BytesToSlot bs = slot := by
  cases slot with
  | uninit | dead => cases h
  | init v =>
    cases v with
    | unit | scalar _ | ptr _ _ | uninit => cases h
    | aggregate var vs =>
      cases var with
      | succ _ => cases h
      | zero =>
        unfold u8BytesToSlot
        rw [u8BytesToValues_of_valuesAsU8Bytes? h]

/-- `ByteStoreOps` instance for caller-owned `[u8; N]` buffers in
`Memory.callerLocals`. -/
instance memCallerByteStoreOps : ByteStoreOps Memory CallerLocalAddr UInt8 where
  readBytes? m a off len :=
    match listGet? m.callerLocals a.localIdx with
    | none => none
    | some slot =>
      match slotAsU8Bytes? slot with
      | none => none
      | some bytes =>
        match Nat.ble (off + len) bytes.length with
        | true => some ((bytes.drop off).take len)
        | false => none
  writeBytes? m a off bs :=
    match listGet? m.callerLocals a.localIdx with
    | none => none
    | some slot =>
      match slotAsU8Bytes? slot with
      | none => none
      | some bytes =>
        match Nat.ble (off + bs.length) bytes.length with
        | true =>
          match listSet? m.callerLocals a.localIdx
              (u8BytesToSlot (listSplice bytes off bs)) with
          | some cl' => some { m with callerLocals := cl' }
          | none => none
        | false => none
  addrDisjoint a₁ off₁ len₁ a₂ off₂ len₂ :=
    a₁ ≠ a₂ ∨ off₁ + len₁ ≤ off₂ ∨ off₂ + len₂ ≤ off₁

private theorem memCaller_write_inv {m m' : Memory} {a : CallerLocalAddr}
    {off : Nat} {bs : List UInt8}
    (hW : memCallerByteStoreOps.writeBytes? m a off bs = some m') :
    ∃ slot bytes cl',
      listGet? m.callerLocals a.localIdx = some slot ∧
      slotAsU8Bytes? slot = some bytes ∧
      off + bs.length ≤ bytes.length ∧
      listSet? m.callerLocals a.localIdx (u8BytesToSlot (listSplice bytes off bs)) = some cl' ∧
      m' = { m with callerLocals := cl' } := by
  dsimp [ByteStoreOps.writeBytes?] at hW
  cases hG : listGet? m.callerLocals a.localIdx with
  | none => simp only [hG] at hW; cases hW
  | some slot =>
    simp only [hG] at hW
    cases hS : slotAsU8Bytes? slot with
    | none => simp only [hS] at hW; cases hW
    | some bytes =>
      simp only [hS] at hW
      cases hB : Nat.ble (off + bs.length) bytes.length with
      | false => simp only [hB] at hW; cases hW
      | true =>
        simp only [hB] at hW
        cases hSet : listSet? m.callerLocals a.localIdx
            (u8BytesToSlot (listSplice bytes off bs)) with
        | none => simp only [hSet] at hW; cases hW
        | some cl' =>
          simp only [hSet] at hW
          injection hW with hEq
          exact ⟨slot, bytes, cl', rfl, hS, Nat.le_of_ble_eq_true hB, hSet, hEq.symm⟩

instance memCallerLawfulByteStoreOps :
    LawfulByteStoreOps Memory CallerLocalAddr UInt8 where
  read_len := by
    intro m a off len bs h
    dsimp [ByteStoreOps.readBytes?] at h
    cases hG : listGet? m.callerLocals a.localIdx with
    | none => simp only [hG] at h; cases h
    | some slot =>
      simp only [hG] at h
      cases hS : slotAsU8Bytes? slot with
      | none => simp only [hS] at h; cases h
      | some bytes =>
        simp only [hS] at h
        cases hB : Nat.ble (off + len) bytes.length with
        | false => simp only [hB] at h; cases h
        | true =>
          simp only [hB] at h; injection h with hEq; subst hEq
          exact listSlice_length bytes off len (Nat.le_of_ble_eq_true hB)
  read_sub := by
    intro m a off len rel k bs h hLe
    dsimp [ByteStoreOps.readBytes?] at h ⊢
    cases hG : listGet? m.callerLocals a.localIdx with
    | none => simp only [hG] at h; cases h
    | some slot =>
      simp only [hG] at h ⊢
      cases hS : slotAsU8Bytes? slot with
      | none => simp only [hS] at h; cases h
      | some bytes =>
        simp only [hS] at h ⊢
        cases hB : Nat.ble (off + len) bytes.length with
        | false => simp only [hB] at h; cases h
        | true =>
          simp only [hB] at h; injection h with hEq; subst hEq
          have hBound := Nat.le_of_ble_eq_true hB
          rw [Nat.ble_eq_true_of_le (by omega)]
          exact congrArg some (listSlice_slice bytes off len rel k hLe).symm
  write_sub := by
    intro m a off len rel old sub hR hLe
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hR ⊢
    cases hG : listGet? m.callerLocals a.localIdx with
    | none => simp only [hG] at hR; cases hR
    | some slot =>
      simp only [hG] at hR ⊢
      cases hS : slotAsU8Bytes? slot with
      | none => simp only [hS] at hR; cases hR
      | some bytes =>
        simp only [hS] at hR ⊢
        cases hB : Nat.ble (off + len) bytes.length with
        | false => simp only [hB] at hR; cases hR
        | true =>
          simp only [hB] at hR; injection hR with hOld; subst hOld
          have hBound := Nat.le_of_ble_eq_true hB
          have hSpLen : (listSplice ((bytes.drop off).take len) rel sub).length = len :=
            (listSplice_length _ rel sub
              (by rw [listSlice_length bytes off len hBound]; exact hLe)).trans
              (listSlice_length bytes off len hBound)
          rw [Nat.ble_eq_true_of_le (by omega), hSpLen, Nat.ble_eq_true_of_le hBound,
            listSplice_sub bytes off len rel sub hBound hLe]
  read_write_same := by
    intro m m' a off bs hW
    rcases memCaller_write_inv hW with ⟨slot, bytes, cl', _, _, hBound, hSet, hM'⟩
    subst hM'
    dsimp [ByteStoreOps.readBytes?]
    rw [listGet?_listSet?_same hSet]; dsimp only
    rw [slotAsU8Bytes?_u8BytesToSlot]; dsimp only
    rw [listSplice_length bytes off bs hBound, Nat.ble_eq_true_of_le hBound]
    exact congrArg some (listSplice_read_same bytes off bs hBound)
  write_read_same := by
    intro m a off len bs hR
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hR ⊢
    cases hG : listGet? m.callerLocals a.localIdx with
    | none => simp only [hG] at hR; cases hR
    | some slot =>
      simp only [hG] at hR ⊢
      cases hS : slotAsU8Bytes? slot with
      | none => simp only [hS] at hR; cases hR
      | some bytes =>
        simp only [hS] at hR ⊢
        cases hB : Nat.ble (off + len) bytes.length with
        | false => simp only [hB] at hR; cases hR
        | true =>
          simp only [hB] at hR; injection hR with hEq; subst hEq
          have hBound := Nat.le_of_ble_eq_true hB
          have hLt := listGet?_lt_of_eq_some hG
          rw [listSlice_length bytes off len hBound, Nat.ble_eq_true_of_le hBound,
            listSplice_self bytes off len hBound, u8BytesToSlot_of_slotAsU8Bytes? hS,
            listSet?_of_lt slot hLt]
          dsimp only
          have hSetEq : m.callerLocals.set a.localIdx slot = m.callerLocals := by
            apply List.ext_getElem
            · simp
            · intro j hj₁ hj₂
              by_cases hJ : j = a.localIdx
              · subst hJ
                rw [List.getElem_set_self]
                have hG' : m.callerLocals[a.localIdx]? = some slot :=
                  (listGet?_eq_getElem? m.callerLocals a.localIdx).symm.trans hG
                rw [List.getElem?_eq_getElem hj₂] at hG'
                exact (Option.some.inj hG').symm
              · rw [List.getElem_set_ne (Ne.symm hJ)]
          rw [hSetEq]
  write_of_read := by
    intro m a off len old bs hR hLen
    dsimp [ByteStoreOps.readBytes?, ByteStoreOps.writeBytes?] at hR ⊢
    cases hG : listGet? m.callerLocals a.localIdx with
    | none => simp only [hG] at hR; cases hR
    | some slot =>
      simp only [hG] at hR ⊢
      cases hS : slotAsU8Bytes? slot with
      | none => simp only [hS] at hR; cases hR
      | some bytes =>
        simp only [hS] at hR ⊢
        cases hB : Nat.ble (off + len) bytes.length with
        | false => simp only [hB] at hR; cases hR
        | true =>
          have hLt := listGet?_lt_of_eq_some hG
          rw [hLen, hB]; dsimp only
          rw [listSet?_of_lt _ hLt]
          exact ⟨_, rfl⟩
  write_write_same := by
    intro m m₁ a off bs₁ bs₂ hW hLen
    rcases memCaller_write_inv hW with ⟨slot, bytes, cl', hG, hS, hBound, hSet, hM₁⟩
    subst hM₁
    dsimp [ByteStoreOps.writeBytes?]
    rw [listGet?_listSet?_same hSet]
    dsimp only
    rw [slotAsU8Bytes?_u8BytesToSlot]
    dsimp only
    rw [listSplice_length bytes off bs₁ hBound, hLen, Nat.ble_eq_true_of_le hBound,
      listSplice_overwrite bytes off bs₁ bs₂ hBound hLen]
    rw [hG]; dsimp only
    rw [hS]; dsimp only
    rw [Nat.ble_eq_true_of_le hBound]
    dsimp only
    rcases listSet?_lt_and_eq hSet with ⟨hLt, hCl'⟩
    have hLt' : a.localIdx < cl'.length := by
      rw [(listSet?_lt_and_length hSet).2]; exact hLt
    rw [listSet?_of_lt _ hLt', listSet?_of_lt _ hLt]
    dsimp only
    have hSetSet : cl'.set a.localIdx (u8BytesToSlot (listSplice bytes off bs₂)) =
        m.callerLocals.set a.localIdx (u8BytesToSlot (listSplice bytes off bs₂)) := by
      rw [hCl', List.set_set]
    rw [hSetSet]
  read_write_disjoint := by
    intro m m' a₁ off₁ bs₁ a₂ off₂ len₂ hDisj hW
    rcases memCaller_write_inv hW with ⟨slot₁, bytes₁, cl', hG₁, hS₁, hBound₁, hSet, hM'⟩
    subst hM'
    dsimp [ByteStoreOps.readBytes?]
    by_cases hEq : a₁ = a₂
    · subst hEq
      have hRange : off₁ + bs₁.length ≤ off₂ ∨ off₂ + len₂ ≤ off₁ :=
        hDisj.resolve_left (fun h => h rfl)
      rw [listGet?_listSet?_same hSet]; dsimp only
      rw [slotAsU8Bytes?_u8BytesToSlot]; dsimp only
      rw [hG₁]; dsimp only
      rw [hS₁]; dsimp only
      rw [listSplice_length bytes₁ off₁ bs₁ hBound₁]
      cases hB₂ : Nat.ble (off₂ + len₂) bytes₁.length with
      | false => rfl
      | true =>
        exact congrArg some
          (listSplice_read_disjoint bytes₁ off₁ bs₁ off₂ len₂ hBound₁ hRange)
    · have hIdxNe : a₂.localIdx ≠ a₁.localIdx := by
        intro hI; apply hEq; cases a₁; cases a₂; simp at hI; subst hI; rfl
      rw [listGet?_listSet?_ne hIdxNe hSet]
  write_write_comm := by
    intro m m₁ m₂ a₁ off₁ bs₁ a₂ off₂ bs₂ hDisj hW₁ hW₂
    rcases memCaller_write_inv hW₁ with ⟨s₁, b₁, cl₁, hG₁, hS₁, hB₁, hSet₁, hM₁⟩
    rcases memCaller_write_inv hW₂ with ⟨s₂, b₂, cl₂, hG₂, hS₂, hB₂, hSet₂, hM₂⟩
    subst hM₁ hM₂
    dsimp [ByteStoreOps.writeBytes?]
    by_cases hEq : a₁ = a₂
    · subst hEq
      have hRange : off₁ + bs₁.length ≤ off₂ ∨ off₂ + bs₂.length ≤ off₁ :=
        hDisj.resolve_left (fun h => h rfl)
      rw [hG₁] at hG₂; injection hG₂ with hSEq; subst hSEq
      rw [hS₁] at hS₂; injection hS₂ with hBEq; subst hBEq
      rw [listGet?_listSet?_same hSet₁, listGet?_listSet?_same hSet₂]; dsimp only
      rw [slotAsU8Bytes?_u8BytesToSlot, slotAsU8Bytes?_u8BytesToSlot]; dsimp only
      rw [listSplice_length b₁ off₁ bs₁ hB₁, listSplice_length b₁ off₂ bs₂ hB₂,
        Nat.ble_eq_true_of_le hB₁, Nat.ble_eq_true_of_le hB₂]; dsimp only
      rcases listSet?_lt_and_eq hSet₁ with ⟨hLt, hCl₁⟩
      rcases listSet?_lt_and_eq hSet₂ with ⟨_, hCl₂⟩
      have hLt₁ : a₁.localIdx < cl₁.length := by
        rw [(listSet?_lt_and_length hSet₁).2]; exact hLt
      have hLt₂ : a₁.localIdx < cl₂.length := by
        rw [(listSet?_lt_and_length hSet₂).2]; exact hLt
      rw [listSet?_of_lt _ hLt₁, listSet?_of_lt _ hLt₂]; dsimp only
      let cl₃ := cl₁.set a₁.localIdx
        (u8BytesToSlot (listSplice (listSplice b₁ off₁ bs₁) off₂ bs₂))
      refine ⟨{ m with callerLocals := cl₃ }, rfl, ?_⟩
      congr 1; congr 1
      dsimp only [cl₃]
      rw [hCl₁, hCl₂, List.set_set, List.set_set]
      cases hRange with
      | inl hSep =>
        rw [listSplice_comm b₁ off₁ bs₁ off₂ bs₂ hSep (by omega)]
      | inr hSep =>
        rw [(listSplice_comm b₁ off₂ bs₂ off₁ bs₁ hSep (by omega)).symm]
    · have hIdxNe : a₂.localIdx ≠ a₁.localIdx := by
        intro hI; apply hEq; cases a₁; cases a₂; simp at hI; subst hI; rfl
      rw [listGet?_listSet?_ne hIdxNe hSet₁, hG₂]; dsimp only
      rw [hS₂]; dsimp only
      rw [Nat.ble_eq_true_of_le hB₂]; dsimp only
      rw [listGet?_listSet?_ne (Ne.symm hIdxNe) hSet₂, hG₁]; dsimp only
      rw [hS₁]; dsimp only
      rw [Nat.ble_eq_true_of_le hB₁]; dsimp only
      rcases listSet?_lt_and_eq hSet₁ with ⟨hLt₁, hCl₁⟩
      rcases listSet?_lt_and_eq hSet₂ with ⟨hLt₂, hCl₂⟩
      have hLt₂' : a₂.localIdx < cl₁.length := by
        rw [(listSet?_lt_and_length hSet₁).2]; exact hLt₂
      have hLt₁' : a₁.localIdx < cl₂.length := by
        rw [(listSet?_lt_and_length hSet₂).2]; exact hLt₁
      rw [listSet?_of_lt _ hLt₂', listSet?_of_lt _ hLt₁']; dsimp only
      let cl₃ := cl₁.set a₂.localIdx (u8BytesToSlot (listSplice b₂ off₂ bs₂))
      refine ⟨{ m with callerLocals := cl₃ }, rfl, ?_⟩
      congr 1; congr 1
      dsimp only [cl₃]
      rw [hCl₁, hCl₂, List.set_comm _ _ (Ne.symm hIdxNe)]
  addrDisjoint_of_separated := fun h => h
  addrDisjoint_symm := by
    intro a₁ a₂ o₁ l₁ o₂ l₂ h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  addrDisjoint_mono_sub := by
    intro a₁ a₂ o₁ l₁ o₂ l₂ o₁' l₁' o₂' l₂' h1 h2 h3 h4 hD
    rcases hD with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

theorem memCaller_writePreserves_borrows :
    memCallerByteStoreOps.WritePreserves (fun m : Memory => m.borrows) := by
  intro m m' _ _ _ hW; rcases memCaller_write_inv hW with ⟨_, _, _, _, _, _, _, rfl⟩; rfl

theorem memCaller_writePreserves_globals :
    memCallerByteStoreOps.WritePreserves (fun m : Memory => m.globals) := by
  intro m m' _ _ _ hW; rcases memCaller_write_inv hW with ⟨_, _, _, _, _, _, _, rfl⟩; rfl

theorem memCaller_writePreserves_nextTag :
    memCallerByteStoreOps.WritePreserves (fun m : Memory => m.nextTag) := by
  intro m m' _ _ _ hW; rcases memCaller_write_inv hW with ⟨_, _, _, _, _, _, _, rfl⟩; rfl

theorem memCaller_writePreserves_activeProtectors :
    memCallerByteStoreOps.WritePreserves (fun m : Memory => m.activeProtectors) := by
  intro m m' _ _ _ hW; rcases memCaller_write_inv hW with ⟨_, _, _, _, _, _, _, rfl⟩; rfl

/-! ## 6. `MutSummaryCut` & `MutSummaryOutcomeCut` Operational Bridges -/

/-- Partial `MirOutcome` extractor matching only normal returns
`.normal (retVal, mem')` whose return value parses via `ofVal`, and rejecting
`.panic` and `.abort` (returning `none`). -/
@[reducible] def mirNormalOutcomeExtract {Ret : Type} (ofVal : Value → Option Ret) :
    MirOutcome → Option (Memory × Ret)
  | .normal (retVal, mem') => (ofVal retVal).map (fun r => (mem', r))
  | .panic => none
  | .abort => none

theorem mirNormalOutcomeExtract_panic_none {Ret : Type} (ofVal : Value → Option Ret) :
    mirNormalOutcomeExtract ofVal .panic = none := rfl

theorem mirNormalOutcomeExtract_abort_none {Ret : Type} (ofVal : Value → Option Ret) :
    mirNormalOutcomeExtract ofVal .abort = none := rfl

theorem mirNormalOutcomeExtract_eq_some_iff {Ret : Type}
    {ofVal : Value → Option Ret} {out : MirOutcome} {m' : Memory} {ret : Ret} :
    mirNormalOutcomeExtract ofVal out = some (m', ret) ↔
      ∃ v : Value, out = .normal (v, m') ∧ ofVal v = some ret := by
  cases out with
  | panic => exact ⟨(fun h => nomatch h), (fun ⟨_, hEq, _⟩ => nomatch hEq)⟩
  | abort => exact ⟨(fun h => nomatch h), (fun ⟨_, hEq, _⟩ => nomatch hEq)⟩
  | normal p =>
    rcases p with ⟨v, mem'⟩
    constructor
    · intro h
      dsimp [mirNormalOutcomeExtract] at h
      cases hV : ofVal v with
      | none => rw [hV] at h; cases h
      | some r =>
        rw [hV] at h
        injection h with hPair
        injection hPair with hM hR
        subst hM hR
        exact ⟨v, rfl, hV⟩
    · rintro ⟨v', hEq, hV⟩
      injection hEq with hPair
      injection hPair with hV' hM'
      subst hV' hM'
      dsimp [mirNormalOutcomeExtract]
      rw [hV]
      rfl

/-- **Operational `MutSummaryOutcomeCut` → `MirWpConverges` bridge**: applying a
sealed `MutSummaryOutcomeCut` on a `V2026_06_01` callee `CapturedMir` body
delivers fuel-free `MirWpConverges` (with `mirNormalPost`, rejecting `.panic`
and `.abort`), exact target post-bytes, and universal framing of every disjoint
`ByteSubLens`. -/
theorem mirWpConverges_of_mutSummaryOutcomeCut {Addr Byte Arg Ret : Type}
    [ops : ByteStoreOps Memory Addr Byte] [LawfulByteStoreOps Memory Addr Byte]
    {body : CapturedMir} {entry : ByteSubLens Addr → Memory → Arg → MachineState}
    {ofVal : Value → Option Ret} {sum : MutSummary Byte Arg Ret}
    (hCut : MutSummaryOutcomeCut (wops := mirDetWpOps body) entry
      (mirNormalOutcomeExtract ofVal) sum)
    {L : ByteSubLens Addr} {arg : Arg} {m m' : Memory} {ret : Ret}
    (hExec : execMutSummary sum L m arg = some (m', ret)) :
    MirWpConverges body (entry L m arg)
      (mirNormalPost (fun v mem' => ofVal v = some ret ∧ mem' = m')) ∧
    (∀ other : ByteSubLens Addr, ByteSubLens.Disjoint Memory L other →
      other.get m' = other.get m) := by
  rcases apply_mutSummaryOutcomeCut_sound (wops := mirDetWpOps body) hCut hExec with
    ⟨hWp, _, hFrame⟩
  refine ⟨?_, hFrame⟩
  refine MirWpConverges.mono (fun out hOut => ?_) (mirWpConverges_of_wpStateOk hWp)
  rcases mirNormalOutcomeExtract_eq_some_iff.mp hOut with ⟨v, rfl, hV⟩
  exact ⟨hV, rfl⟩

/-- Typed (`MutSummary.ofSliceCodec`) operational `MutSummaryOutcomeCut` →
`MirWpConverges` bridge with zero raw byte lists in the caller proof. -/
theorem mirWpConverges_of_mutSummaryOutcomeCut_ofSliceCodec
    {Addr Byte Arg Ret α : Type} {n : Nat}
    [ops : ByteStoreOps Memory Addr Byte] [LawfulByteStoreOps Memory Addr Byte]
    {body : CapturedMir} {entry : ByteSubLens Addr → Memory → Arg → MachineState}
    {ofVal : Value → Option Ret} {sc : SliceCodec Byte α n}
    {fn : α → Arg → Option (α × Ret)}
    (hCut : MutSummaryOutcomeCut (wops := mirDetWpOps body) entry
      (mirNormalOutcomeExtract ofVal) (MutSummary.ofSliceCodec sc fn))
    {L : ByteSubLens Addr} {arg : Arg} {m : Memory} {v v' : α} {ret : Ret}
    (hGet : L.getVal sc m = some v) (hFn : fn v arg = some (v', ret)) :
    ∃ m',
      MirWpConverges body (entry L m arg)
        (mirNormalPost (fun rv mem' => ofVal rv = some ret ∧ mem' = m')) ∧
      L.setVal sc m v' = some m' ∧
      L.getVal sc m' = some v' ∧
      (∀ other : ByteSubLens Addr, ByteSubLens.Disjoint Memory L other →
        other.get m' = other.get m) := by
  rcases apply_mutSummaryOutcomeCut_ofSliceCodec (wops := mirDetWpOps body) hCut hGet hFn with
    ⟨m', hWp, hSet, hPost, hFrame⟩
  refine ⟨m', ?_, hSet, hPost, hFrame⟩
  refine MirWpConverges.mono (fun out hOut => ?_) (mirWpConverges_of_wpStateOk hWp)
  rcases mirNormalOutcomeExtract_eq_some_iff.mp hOut with ⟨rv, rfl, hV⟩
  exact ⟨hV, rfl⟩

/-- **Operational `MutSummaryCut` → `MirStepsConverges` / `MirWpConverges` bridge**:
applies a relational `MutSummaryCut` sealed over `mirDetWpOps body`. -/
theorem mirStepsConverges_of_mutSummaryCut {Addr Byte Arg Ret : Type}
    [ops : ByteStoreOps Memory Addr Byte] [LawfulByteStoreOps Memory Addr Byte]
    {body : CapturedMir}
    {atEntry : ByteSubLens Addr → Arg → MachineState → Prop}
    {atExit : Ret → MachineState → MachineState → Prop}
    {sum : MutSummary Byte Arg Ret}
    (hCut : MutSummaryCut (wops := mirDetWpOps body)
      (fun ms => ms.memory) atEntry atExit sum)
    {L : ByteSubLens Addr} {arg : Arg} {s : MachineState} {m' : Memory} {ret : Ret}
    (hEntry : atEntry L arg s)
    (hExec : execMutSummary sum L s.memory arg = some (m', ret)) :
    MirStepsConverges body s (fun s' => s'.memory = m' ∧ atExit ret s s')
      (fun _ => False) ∧
    (∀ other : ByteSubLens Addr, ByteSubLens.Disjoint Memory L other →
      other.get m' = other.get s.memory) := by
  rcases apply_mutSummaryCut_sound (wops := mirDetWpOps body) hCut hEntry hExec with
    ⟨hReach, _, hFrame⟩
  exact ⟨mirStepsConverges_of_wpReach hReach, hFrame⟩

/-- Fail-closed rejection: if a callee terminates with `.panic` (or `.abort`)
from `entry L m arg` when the summary applies, it cannot satisfy
`MutSummaryOutcomeCut` under `mirNormalOutcomeExtract`. -/
theorem not_mutSummaryOutcomeCut_of_nonNormal {Addr Byte Arg Ret : Type}
    [ops : ByteStoreOps Memory Addr Byte] [LawfulByteStoreOps Memory Addr Byte]
    {body : CapturedMir} {entry : ByteSubLens Addr → Memory → Arg → MachineState}
    {ofVal : Value → Option Ret} {sum : MutSummary Byte Arg Ret}
    {L : ByteSubLens Addr} {m m' : Memory} {arg : Arg} {ret : Ret} {out : MirOutcome}
    (hExec : execMutSummary sum L m arg = some (m', ret))
    (hNonNorm : mirNormalOutcomeExtract ofVal out = none)
    (hRun : wpStateOk (ops := mirDetWpOps body) (· = out) (entry L m arg)) :
    ¬ MutSummaryOutcomeCut (wops := mirDetWpOps body) entry
      (mirNormalOutcomeExtract ofVal) sum := by
  intro hCut
  have hWp := (apply_mutSummaryOutcomeCut_sound (wops := mirDetWpOps body) hCut hExec).1
  have hBoth := wpOutcome_conj (ops := mirDetWpOps body) (mirDetWpOps_conjunctive body)
    hWp hRun
  have hFalse : wpOutcome (ops := mirDetWpOps body) (fun _ => False) (fun _ => False)
      (entry L m arg) := by
    refine wpOutcome_mono (ops := mirDetWpOps body) ?_ (fun _ hf => hf.1) hBoth
    intro o h
    rcases h with ⟨hEx, hEq⟩
    subst hEq
    rw [hNonNorm] at hEx
    cases hEx
  exact wpOutcome_not_false (ops := mirDetWpOps body) (mirDetWpOps_strict body) hFalse

/-- Every step in a certified `MutSummaryOutcomeChainRunsTo` over `V2026_06_01`
bodies lifts directly to `MirWpConverges` (using `mirNormalOutcomeExtract`). -/
inductive MirOutcomeChainConverges {Addr Byte Arg Ret : Type}
    (ofVal : Value → Option Ret) :
    List (CapturedMir × (ByteSubLens Addr → Memory → Arg → MachineState) ×
      MutSummaryCall Byte Addr Arg Ret) →
    Memory → Memory → List Ret → Prop where
  | nil (m : Memory) : MirOutcomeChainConverges ofVal [] m m []
  | cons {body : CapturedMir}
      {entry : ByteSubLens Addr → Memory → Arg → MachineState}
      {c : MutSummaryCall Byte Addr Arg Ret}
      {rest : List (CapturedMir × (ByteSubLens Addr → Memory → Arg → MachineState) ×
        MutSummaryCall Byte Addr Arg Ret)}
      {m m₁ m₂ : Memory} {r : Ret} {rs : List Ret}
      (hConv : MirWpConverges body (entry c.lens m c.arg)
        (mirNormalPost (fun v mem' => ofVal v = some r ∧ mem' = m₁)))
      (hRest : MirOutcomeChainConverges ofVal rest m₁ m₂ rs) :
      MirOutcomeChainConverges ofVal ((body, entry, c) :: rest) m m₂ (r :: rs)

/-- Lift a certified `execMutSummaryChain` of sealed `V2026_06_01` callee
`MutSummaryOutcomeCut`s into `MirOutcomeChainConverges` plus universal
disjoint-lens framing. -/
theorem mirOutcomeChainConverges_of_execMutSummaryChain {Addr Byte Arg Ret : Type}
    [ops : ByteStoreOps Memory Addr Byte] [LawfulByteStoreOps Memory Addr Byte]
    {ofVal : Value → Option Ret} :
    ∀ (specs : List (CapturedMir × (ByteSubLens Addr → Memory → Arg → MachineState) ×
        MutSummaryCall Byte Addr Arg Ret))
      {m m' : Memory} {rets : List Ret},
      (∀ item, item ∈ specs →
        MutSummaryOutcomeCut (wops := mirDetWpOps item.1) item.2.1
          (mirNormalOutcomeExtract ofVal) item.2.2.sum) →
      execMutSummaryChain (specs.map (fun s => s.2.2)) m = some (m', rets) →
      MirOutcomeChainConverges ofVal specs m m' rets ∧
      (∀ other : ByteSubLens Addr,
        AllCallsDisjoint Memory other (specs.map (fun s => s.2.2)) →
        other.get m' = other.get m)
  | [], m, m', rets, _, hChain => by
    rw [List.map_nil, execMutSummaryChain_nil] at hChain
    injection hChain with hPair
    injection hPair with hM hR
    subst hM hR
    exact ⟨.nil m, fun _ _ => rfl⟩
  | (body, entry, c) :: rest, m, m', rets, hCuts, hChain => by
    rw [List.map_cons] at hChain
    rcases execMutSummaryChain_cons_inv hChain with ⟨m₁, r, rs, hExec, hRest, hRets⟩
    subst hRets
    have hCutHead := hCuts (body, entry, c) (List.Mem.head _)
    have hHead := (mirWpConverges_of_mutSummaryOutcomeCut hCutHead hExec).1
    have hTail := mirOutcomeChainConverges_of_execMutSummaryChain rest
      (fun item hMem => hCuts item (List.Mem.tail _ hMem)) hRest
    refine ⟨.cons hHead hTail.1, ?_⟩
    intro other hDisj
    rw [List.map_cons] at hDisj
    exact execMutSummaryChain_frame_disjoint other
      (c :: rest.map (fun s => s.2.2)) hDisj (execMutSummaryChain_cons_of hExec hRest)

end Anneal.ParametricCore.V2026Bridge
