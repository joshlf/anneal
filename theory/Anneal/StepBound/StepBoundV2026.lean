-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.Framework.StepWp
import Anneal.CnfOrd.Ord
import Anneal.CnfOrd.Worklist
import Anneal.ConjunctiveWp.WlpV2026
import Anneal.ParametricCore.LoopInv
import Anneal.ParametricCore.StageCut
import Anneal.ParametricCore.V2026Bridge
import Anneal.InitLemmas
import Anneal.MirFuelFree
import Trusted

/-!
# Quantitative Step Bounds & `< ω^ω` Bridges over `V2026_06_01` (`Anneal.StepBound.StepBoundV2026`)

Converges `#4400` (`Anneal.StepBound.{Core, CnfOrdBridge, V2Loop}`) directly
onto unmodified `Trusted.Rustc.V2026_06_01.MirSemantics` via `v2026Step`,
`Anneal.Framework.StepWp`, `Anneal.CnfOrd.Worklist`, and
`Anneal.ParametricCore.{LoopInv, StageCut, V2026Bridge}`:

1. **Quantitative Step-Bound Core (`ReachesDoneWithinV2026`,
   `ExecWithinStepsV2026`, `ExecStatefulWithinStepsV2026`):** `@Nat.rec`
   step-bounded execution predicates proved equivalent to
   `execStepOutcome (v2026Step body) post (fun _ => False) bound s`, with direct
   adequacy into `MirWpConverges`, `MirNoUBTree`, `¬ DivergesV2026`,
   `VerificationResult`, `StatefulVerificationResult`, and
   `TotalVerificationResult`.
2. **Exact & Upper-Bounded Sequential Composition + `ParametricCore`
   Integration (`StepsToV2026`, `BoundedReachV2026`):** Exact `k`-step and
   upper-bounded `≤ bound` reachability relations with bidirectional bridges to
   BOTH `Anneal.Framework.StepWp.StepStageCut` AND
   `Anneal.ParametricCore.StepStageCut` / `wpReach` / `wpUntilOk` / `wpStateOk`
   over `V2026Bridge.mirDetStep` / `mirDetWpOps`.
3. **Acyclic, Cutpoint, & Loop Step-Bound Rules + `CnfOrd` Bridge:**
   Countdown (`v2026_loop_countdown`), rank-bounded with early exit
   (`v2026_loop_nat_bounded`), progress-weighted byte-credit
   (`v2026_loop_byte_credit`), two-tier bounded-reset ordinal ceiling
   (`cnfLex2`, `lex2Bound`, `v2026_loop_lex2_bounded_reset`), constructive
   `< ω^ω` budget extraction (`v2026_loop_cnfOrd_exists`,
   `execWithinStepsV2026_of_cnfOrd`), worklist-to-MIR bridges
   (`v2026_steps_of_cnfStepConverges`, `v2026_steps_of_worklist_terminates`),
   and reactive per-frame contracts (`ReactiveStepContractV2026`).
4. **Tight-Budget & Non-Vacuity Refutation Lemmas:** Refutation of
   `ReachesDoneWithinV2026` on diverging traces, under-budget bounds
   (`bound ≤ k`), postcondition failures, and fault trajectories, exercised on
   concrete `CapturedMir` witnesses.
-/

namespace Anneal.StepBound

open Trusted.Effect
open Trusted.VerificationResult
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.InitLemmas
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.Framework.StepWp
open Anneal.CnfOrd
open Anneal.ConjunctiveWp

/-! ## Part I: Quantitative Step-Bound Core over `V2026_06_01` -/

/-- State `s` reaches `.done out` under `v2026Step body` within at most `bound`
MIR steps with `post out` (never faulting or exceeding `bound`). Defined via
`@Nat.rec` to stay free of equation-compiler recursion. -/
def ReachesDoneWithinV2026 (body : CapturedMir) (post : MirOutcome → Prop) :
    Nat → MachineState → Prop :=
  @Nat.rec (fun _ => MachineState → Prop)
    (fun _ => False)
    (fun _ ih s =>
      (∃ out : MirOutcome, v2026Step body s = .done out ∧ post out) ∨
      (∃ s' : MachineState, v2026Step body s = .step s' ∧ ih s'))

/-- Whole-function stateless execution of `body` on `args` with linked `callees`
reaches `.done out` satisfying `post out` within at most `bound` MIR steps. -/
def ExecWithinStepsV2026 (body : CapturedMir) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop)
    (bound : Nat) : Prop :=
  ReachesDoneWithinV2026 body post bound
    (initMachineStateWithCallees body args callees)

/-- Whole-function stateful execution of `body` on `(args, mem, callees)`
reaches `.done out` satisfying `post out` within at most `bound` MIR steps. -/
def ExecStatefulWithinStepsV2026 (body : CapturedMir) (args : List Value)
    (mem : Memory) (callees : List CapturedMir) (post : MirOutcome → Prop)
    (bound : Nat) : Prop :=
  ReachesDoneWithinV2026 body post bound
    (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
      body args mem callees)

/-- Zero step budget is uninhabited. -/
theorem reachesDoneWithinV2026_zero_iff (body : CapturedMir)
    (post : MirOutcome → Prop) (s : MachineState) :
    ReachesDoneWithinV2026 body post 0 s ↔ False :=
  Iff.rfl

/-- Successor unfolding for `ReachesDoneWithinV2026`. -/
theorem reachesDoneWithinV2026_succ_iff (body : CapturedMir)
    (post : MirOutcome → Prop) (b : Nat) (s : MachineState) :
    ReachesDoneWithinV2026 body post (b + 1) s ↔
      (∃ out : MirOutcome, v2026Step body s = .done out ∧ post out) ∨
      (∃ s' : MachineState, v2026Step body s = .step s' ∧
        ReachesDoneWithinV2026 body post b s') :=
  Iff.rfl

/-- Direct base introduction on a `.done` transition. -/
theorem reachesDoneWithinV2026_of_done {body : CapturedMir}
    {post : MirOutcome → Prop} {s : MachineState} {out : MirOutcome}
    (hDone : v2026Step body s = .done out) (hPost : post out) :
    ReachesDoneWithinV2026 body post 1 s :=
  Or.inl ⟨out, hDone, hPost⟩

/-- Direct step introduction on a `.step` transition. -/
theorem reachesDoneWithinV2026_of_step {body : CapturedMir}
    {post : MirOutcome → Prop} {b : Nat} {s s' : MachineState}
    (hStep : v2026Step body s = .step s')
    (hRest : ReachesDoneWithinV2026 body post b s') :
    ReachesDoneWithinV2026 body post (b + 1) s :=
  Or.inr ⟨s', hStep, hRest⟩

/-- Monotonicity of `ReachesDoneWithinV2026` in the step budget (`b₁ ≤ b₂`). -/
theorem ReachesDoneWithinV2026.mono {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {b₁ b₂ : Nat} {s : MachineState},
      b₁ ≤ b₂ →
      ReachesDoneWithinV2026 body post b₁ s →
      ReachesDoneWithinV2026 body post b₂ s
  | 0, _, _, _, h => False.elim h
  | _ + 1, b₂, _, hLe, h => by
    cases b₂ with
    | zero => cases hLe
    | succ _ =>
      cases h with
      | inl hDone => exact Or.inl hDone
      | inr hStep =>
        let ⟨s', hs, hRest⟩ := hStep
        exact Or.inr ⟨s', hs,
          ReachesDoneWithinV2026.mono (Nat.le_of_succ_le_succ hLe) hRest⟩

/-- Postcondition weakening for `ReachesDoneWithinV2026`. -/
theorem ReachesDoneWithinV2026.weaken {body : CapturedMir}
    {post₁ post₂ : MirOutcome → Prop}
    (hImp : ∀ out, post₁ out → post₂ out) :
    ∀ {b : Nat} {s : MachineState},
      ReachesDoneWithinV2026 body post₁ b s →
      ReachesDoneWithinV2026 body post₂ b s
  | 0, _, h => False.elim h
  | _ + 1, _, h => by
    cases h with
    | inl hDone =>
      let ⟨out, hs, hp⟩ := hDone
      exact Or.inl ⟨out, hs, hImp out hp⟩
    | inr hStep =>
      let ⟨s', hs, hRest⟩ := hStep
      exact Or.inr ⟨s', hs, ReachesDoneWithinV2026.weaken hImp hRest⟩

/-- Step-budget monotonicity for `ExecWithinStepsV2026`. -/
theorem ExecWithinStepsV2026.mono {body : CapturedMir} {args : List Value}
    {callees : List CapturedMir} {post : MirOutcome → Prop} {b₁ b₂ : Nat}
    (hLe : b₁ ≤ b₂) (h : ExecWithinStepsV2026 body args callees post b₁) :
    ExecWithinStepsV2026 body args callees post b₂ :=
  ReachesDoneWithinV2026.mono hLe h

/-- Postcondition weakening for `ExecWithinStepsV2026`. -/
theorem ExecWithinStepsV2026.weaken {body : CapturedMir} {args : List Value}
    {callees : List CapturedMir} {post₁ post₂ : MirOutcome → Prop} {b : Nat}
    (hImp : ∀ out, post₁ out → post₂ out)
    (h : ExecWithinStepsV2026 body args callees post₁ b) :
    ExecWithinStepsV2026 body args callees post₂ b :=
  ReachesDoneWithinV2026.weaken hImp h

/-- Exact equivalence between `ReachesDoneWithinV2026` and
`execStepOutcome (v2026Step body) post (fun _ => False)`. -/
theorem reachesDoneWithinV2026_iff_execStepOutcome {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {bound : Nat} {s : MachineState},
      ReachesDoneWithinV2026 body post bound s ↔
        execStepOutcome (v2026Step body) post (fun _ => False) bound s
  | 0, _ => Iff.rfl
  | b + 1, s => by
    constructor
    · intro h
      dsimp only [execStepOutcome]
      rw [execStepPred_succ_iff]
      cases h with
      | inl hDone =>
        let ⟨out, hEq, hPost⟩ := hDone
        rw [hEq]
        exact hPost
      | inr hStep =>
        let ⟨s', hEq, hRest⟩ := hStep
        rw [hEq]
        exact reachesDoneWithinV2026_iff_execStepOutcome.mp hRest
    · intro h
      dsimp only [execStepOutcome] at h
      rw [execStepPred_succ_iff] at h
      cases hEv : v2026Step body s with
      | step s' =>
        rw [hEv] at h
        exact Or.inr ⟨s', hEv, reachesDoneWithinV2026_iff_execStepOutcome.mpr h⟩
      | done out =>
        rw [hEv] at h
        exact Or.inl ⟨out, hEv, h⟩
      | fault _ =>
        rw [hEv] at h
        exact False.elim h

/-- Adequacy: `ReachesDoneWithinV2026` implies unmodified
`Anneal.MirFuelFree.MirWpConverges`. -/
theorem mirWpConverges_of_reachesDoneWithinV2026 {body : CapturedMir}
    {post : MirOutcome → Prop} {bound : Nat} {s : MachineState}
    (h : ReachesDoneWithinV2026 body post bound s) :
    MirWpConverges body s post :=
  mirWpConverges_of_v2026Exec (reachesDoneWithinV2026_iff_execStepOutcome.mp h)

/-- Call-free adequacy: `ReachesDoneWithinV2026` implies
`Anneal.MirFuelFree.MirNoCallWpConverges`. -/
theorem mirNoCallWpConverges_of_reachesDoneWithinV2026 {body : CapturedMir}
    {post : MirOutcome → Prop} {bound : Nat} {s : MachineState}
    (h : ReachesDoneWithinV2026 body post bound s) :
    MirNoCallWpConverges body s post :=
  mirNoCallWpConverges_of_v2026Exec
    (reachesDoneWithinV2026_iff_execStepOutcome.mp h)

/-- Exact fuel-free characterization: call-free MIR convergence holds iff a
finite quantitative step bound `ReachesDoneWithinV2026` exists. -/
theorem mirNoCallWpConverges_iff_exists_reachesDoneWithinV2026
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop} :
    MirNoCallWpConverges body s post ↔
      ∃ bound : Nat, ReachesDoneWithinV2026 body post bound s :=
  Iff.trans mirNoCallWpConverges_iff_exists_v2026Exec
    ⟨fun ⟨b, h⟩ => ⟨b, reachesDoneWithinV2026_iff_execStepOutcome.mpr h⟩,
     fun ⟨b, h⟩ => ⟨b, reachesDoneWithinV2026_iff_execStepOutcome.mp h⟩⟩

/-- Adequacy: `ReachesDoneWithinV2026` implies all-prefix UB-freedom
`MirNoUBTree (mirTree body s)`. -/
theorem mirNoUBTree_of_reachesDoneWithinV2026 {body : CapturedMir}
    {post : MirOutcome → Prop} {bound : Nat} {s : MachineState}
    (h : ReachesDoneWithinV2026 body post bound s) :
    MirNoUBTree (mirTree body s) :=
  mirNoUBTree_of_v2026Exec (reachesDoneWithinV2026_iff_execStepOutcome.mp h)

/-- Any `ReachesDoneWithinV2026` derivation rules out `DivergesV2026`. -/
theorem not_divergesV2026_of_reachesDoneWithinV2026 {body : CapturedMir}
    {post : MirOutcome → Prop} {bound : Nat} {s : MachineState}
    (h : ReachesDoneWithinV2026 body post bound s) :
    ¬ DivergesV2026 body s :=
  fun hDiv =>
    not_execStepOutcome_of_divergesV2026 hDiv post (fun _ => False) bound
      (reachesDoneWithinV2026_iff_execStepOutcome.mp h)

/-- Whole-function stateless `VerificationResult` (`mirSafePost`) from
`ExecWithinStepsV2026`. -/
theorem verifyMirSafe_of_execWithinStepsV2026 (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ bound : Nat,
        ExecWithinStepsV2026 c.body args c.callees
          (mirSafePost (fun retVal _ => c.post args retVal)) bound) :
    VerificationResult c :=
  verifyMirSafe_of_wpConverges c (fun args hPre => by
    let ⟨_, hExec⟩ := h args hPre
    exact mirWpConverges_of_reachesDoneWithinV2026 hExec)

/-- Whole-function panic-forbidding stateless `VerificationResult`
(`mirNormalPost`) from `ExecWithinStepsV2026`. -/
theorem verifyMirNoPanic_of_execWithinStepsV2026 (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ bound : Nat,
        ExecWithinStepsV2026 c.body args c.callees
          (mirNormalPost (fun retVal _ => c.post args retVal)) bound) :
    VerificationResult c :=
  verifyMirNoPanic_of_wpConverges c (fun args hPre => by
    let ⟨_, hExec⟩ := h args hPre
    exact mirWpConverges_of_reachesDoneWithinV2026 hExec)

/-- Whole-function stateful `StatefulVerificationResult` (`mirSafePost`) from
`ExecStatefulWithinStepsV2026`. -/
theorem verifyStatefulMirSafe_of_execWithinStepsV2026 (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ bound : Nat,
        ExecStatefulWithinStepsV2026 c.body args mem c.callees
          (mirSafePost (c.post args mem)) bound) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_wpConverges c (fun args mem hPre => by
    let ⟨_, hExec⟩ := h args mem hPre
    exact mirWpConverges_of_reachesDoneWithinV2026 hExec)

/-- Whole-function panic-forbidding stateful `StatefulVerificationResult`
(`mirNormalPost`) from `ExecStatefulWithinStepsV2026`. -/
theorem verifyStatefulMirNoPanic_of_execWithinStepsV2026 (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ bound : Nat,
        ExecStatefulWithinStepsV2026 c.body args mem c.callees
          (mirNormalPost (c.post args mem)) bound) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_wpConverges c (fun args mem hPre => by
    let ⟨_, hExec⟩ := h args mem hPre
    exact mirWpConverges_of_reachesDoneWithinV2026 hExec)

/-- Whole-function total-correctness `TotalVerificationResult`
(`mirNormalPost`) from `ExecStatefulWithinStepsV2026`. -/
theorem verifyTotalMir_of_execWithinStepsV2026 (c : TotalClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ bound : Nat,
        ExecStatefulWithinStepsV2026 c.body args mem c.callees
          (mirNormalPost (c.post args mem)) bound) :
    TotalVerificationResult c :=
  verifyTotalMir_of_wpConverges c (fun args mem hPre => by
    let ⟨_, hExec⟩ := h args mem hPre
    exact mirWpConverges_of_reachesDoneWithinV2026 hExec)

/-! ## Part II: Exact & Upper-Bounded Sequential Composition + `ParametricCore` Integration -/

/-- Exact `n`-step `v2026Step` transition sequence `s₁ →^n s₂`. -/
inductive StepsToV2026 (body : CapturedMir) :
    Nat → MachineState → MachineState → Prop where
  | refl (s : MachineState) : StepsToV2026 body 0 s s
  | step {n : Nat} {s s' s'' : MachineState} :
      v2026Step body s = .step s' →
      StepsToV2026 body n s' s'' →
      StepsToV2026 body (n + 1) s s''

/-- Single `.step` lifting for `StepsToV2026`. -/
theorem StepsToV2026.single {body : CapturedMir} {s s' : MachineState}
    (hStep : v2026Step body s = .step s') : StepsToV2026 body 1 s s' :=
  StepsToV2026.step hStep (StepsToV2026.refl s')

/-- Alias of `StepsToV2026.single` for `v2026Step` equality witnesses. -/
theorem StepsToV2026.of_v2026Step {body : CapturedMir} {s s' : MachineState}
    (hStep : v2026Step body s = .step s') : StepsToV2026 body 1 s s' :=
  StepsToV2026.single hStep

/-- Single-step lifting from a silent `stepMirFn body s = .tau (.running s')`. -/
theorem StepsToV2026.of_stepMirFn_tau {body : CapturedMir} {s s' : MachineState}
    (hStep : stepMirFn body s = .tau (.running s')) :
    StepsToV2026 body 1 s s' :=
  StepsToV2026.single (v2026Step_step_iff.mpr (Or.inl hStep))

/-- Single-step lifting from an observable `MirStepNode.emitStep obs s'`. -/
theorem StepsToV2026.of_stepMirFn_emit {body : CapturedMir} {s s' : MachineState}
    {obs : MirObs} (hStep : stepMirFn body s = MirStepNode.emitStep obs s') :
    StepsToV2026 body 1 s s' := by
  refine StepsToV2026.single ?_
  unfold v2026Step
  rw [hStep]
  exact ofV2026MirStepNode_emitStep obs s'

/-- Exact `k₁ + k₂` sequential composition for `StepsToV2026`. -/
theorem StepsToV2026.trans {body : CapturedMir} {k₁ k₂ : Nat}
    {s₀ s₁ s₂ : MachineState}
    (h₁ : StepsToV2026 body k₁ s₀ s₁) (h₂ : StepsToV2026 body k₂ s₁ s₂) :
    StepsToV2026 body (k₁ + k₂) s₀ s₂ := by
  induction h₁ with
  | refl _ =>
    rw [Nat.zero_add]
    exact h₂
  | @step n _ _ _ hs _ ih =>
    rw [Nat.succ_add n k₂]
    exact StepsToV2026.step hs (ih h₂)

/-- `StepsToV2026` is deterministic: exact `k`-step endpoints are unique. -/
theorem StepsToV2026.deterministic {body : CapturedMir} :
    ∀ {k : Nat} {s s₁ s₂ : MachineState},
      StepsToV2026 body k s s₁ → StepsToV2026 body k s s₂ → s₁ = s₂
  | 0, _, _, _, h₁, h₂ => by
    cases h₁
    cases h₂
    rfl
  | _ + 1, _, _, _, h₁, h₂ => by
    cases h₁ with
    | step hs₁ hTail₁ =>
      cases h₂ with
      | step hs₂ hTail₂ =>
        rw [hs₁] at hs₂
        injection hs₂ with hEq
        subst hEq
        exact StepsToV2026.deterministic hTail₁ hTail₂

/-- Lift an exact `StepsToV2026` chain to
`Anneal.Framework.StepWp.StepStageCut (v2026Step body)`. -/
theorem StepsToV2026.to_stepStageCut {body : CapturedMir} {k : Nat}
    {s₀ s₁ : MachineState} (h : StepsToV2026 body k s₀ s₁) :
    Anneal.Framework.StepWp.StepStageCut (v2026Step body) k s₀ s₁ := by
  induction h with
  | refl s => exact Anneal.Framework.StepWp.StepStageCut.refl (v2026Step body) 0 s
  | step hs _ ih => exact Anneal.Framework.StepWp.StepStageCut.step hs ih

/-- Lift an exact `StepsToV2026` chain directly to
`Anneal.ParametricCore.StepStageCut (V2026Bridge.mirDetStep body)`. -/
theorem StepsToV2026.to_parametricStepStageCut {body : CapturedMir} {k : Nat}
    {s₀ s₁ : MachineState} (h : StepsToV2026 body k s₀ s₁) :
    Anneal.ParametricCore.StepStageCut
      (Anneal.ParametricCore.V2026Bridge.mirDetStep body) k s₀ s₁ := by
  induction h with
  | refl s =>
    exact Anneal.ParametricCore.StepStageCut.refl
      (Anneal.ParametricCore.V2026Bridge.mirDetStep body) 0 s
  | step hs _ ih =>
    exact Anneal.ParametricCore.StepStageCut.step
      (v2026Step_step_iff_mirDetStep_step.mp hs) ih

/-- Prepending a `StepsToV2026` trace onto `ReachesDoneWithinV2026`. -/
theorem reachesDoneWithinV2026_of_stepsTo {body : CapturedMir}
    {post : MirOutcome → Prop} {k₁ k₂ : Nat} {s₀ s₁ : MachineState}
    (hPrefix : StepsToV2026 body k₁ s₀ s₁)
    (hRest : ReachesDoneWithinV2026 body post k₂ s₁) :
    ReachesDoneWithinV2026 body post (k₁ + k₂) s₀ := by
  induction hPrefix with
  | refl _ =>
    rw [Nat.zero_add]
    exact hRest
  | step hs _ ih =>
    rw [Nat.succ_add]
    exact reachesDoneWithinV2026_of_step hs (ih hRest)

/-- Upper-bounded `V2026_06_01` multi-step reachability (`∃ k ≤ bound`). -/
def BoundedReachV2026 (body : CapturedMir) (stopPred : MachineState → Prop)
    (bound : Nat) (s : MachineState) : Prop :=
  ∃ k : Nat, ∃ s' : MachineState,
    k ≤ bound ∧ StepsToV2026 body k s s' ∧ stopPred s'

/-- Zero-step reflexivity for `BoundedReachV2026`. -/
theorem BoundedReachV2026.refl {body : CapturedMir}
    {stopPred : MachineState → Prop} (bound : Nat) {s : MachineState}
    (hP : stopPred s) :
    BoundedReachV2026 body stopPred bound s :=
  ⟨0, s, Nat.zero_le bound, StepsToV2026.refl s, hP⟩

/-- Exact `StepsToV2026` introduction into `BoundedReachV2026`. -/
theorem BoundedReachV2026.of_exact {body : CapturedMir}
    {stopPred : MachineState → Prop} {k bound : Nat} {s s' : MachineState}
    (hk : k ≤ bound) (hSteps : StepsToV2026 body k s s') (hP : stopPred s') :
    BoundedReachV2026 body stopPred bound s :=
  ⟨k, s', hk, hSteps, hP⟩

/-- Step-prefix introduction into `BoundedReachV2026`. -/
theorem BoundedReachV2026.step {body : CapturedMir}
    {stopPred : MachineState → Prop} {b : Nat} {s s' : MachineState}
    (hStep : v2026Step body s = .step s')
    (hRest : BoundedReachV2026 body stopPred b s') :
    BoundedReachV2026 body stopPred (b + 1) s := by
  let ⟨k, s'', hk, hSteps, hP⟩ := hRest
  exact ⟨k + 1, s'', Nat.succ_le_succ hk, StepsToV2026.step hStep hSteps, hP⟩

/-- Budget monotonicity for `BoundedReachV2026`. -/
theorem BoundedReachV2026.mono {body : CapturedMir}
    {stopPred : MachineState → Prop} {b₁ b₂ : Nat} {s : MachineState}
    (hLe : b₁ ≤ b₂) (h : BoundedReachV2026 body stopPred b₁ s) :
    BoundedReachV2026 body stopPred b₂ s := by
  let ⟨k, s', hk, hSteps, hP⟩ := h
  exact ⟨k, s', Nat.le_trans hk hLe, hSteps, hP⟩

/-- Postcondition weakening for `BoundedReachV2026`. -/
theorem BoundedReachV2026.weaken {body : CapturedMir}
    {P Q : MachineState → Prop} {b : Nat} {s : MachineState}
    (hImp : ∀ s', P s' → Q s') (h : BoundedReachV2026 body P b s) :
    BoundedReachV2026 body Q b s := by
  let ⟨k, s', hk, hSteps, hP⟩ := h
  exact ⟨k, s', hk, hSteps, hImp s' hP⟩

/-- Sequential composition (`b₁ + b₂`) for `BoundedReachV2026`. -/
theorem BoundedReachV2026.trans {body : CapturedMir}
    {P Q : MachineState → Prop} {b₁ b₂ : Nat} {s₀ : MachineState}
    (h₁ : BoundedReachV2026 body P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → BoundedReachV2026 body Q b₂ s₁) :
    BoundedReachV2026 body Q (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hk₁, hSteps₁, hP⟩ := h₁
  let ⟨k₂, s₂, hk₂, hSteps₂, hQ⟩ := h₂ s₁ hP
  exact ⟨k₁ + k₂, s₂, Nat.add_le_add hk₁ hk₂,
    StepsToV2026.trans hSteps₁ hSteps₂, hQ⟩

/-- Bind a `BoundedReachV2026` prefix with a `ReachesDoneWithinV2026` suffix
(`b₁ + b₂`). -/
theorem BoundedReachV2026.bind_done {body : CapturedMir}
    {P : MachineState → Prop} {post : MirOutcome → Prop}
    {b₁ b₂ : Nat} {s₀ : MachineState}
    (h₁ : BoundedReachV2026 body P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → ReachesDoneWithinV2026 body post b₂ s₁) :
    ReachesDoneWithinV2026 body post (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hk₁, hSteps₁, hP⟩ := h₁
  exact ReachesDoneWithinV2026.mono (Nat.add_le_add_right hk₁ b₂)
    (reachesDoneWithinV2026_of_stepsTo hSteps₁ (h₂ s₁ hP))

/-- Bind a `BoundedReachV2026` prefix with an `execStepOutcome` suffix
(`b₁ + b₂`). -/
theorem BoundedReachV2026.bind_exec {body : CapturedMir}
    {P : MachineState → Prop} {post : MirOutcome → Prop}
    {b₁ b₂ : Nat} {s₀ : MachineState}
    (h₁ : BoundedReachV2026 body P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ →
      execStepOutcome (v2026Step body) post (fun _ => False) b₂ s₁) :
    execStepOutcome (v2026Step body) post (fun _ => False) (b₁ + b₂) s₀ :=
  reachesDoneWithinV2026_iff_execStepOutcome.mp
    (BoundedReachV2026.bind_done h₁
      (fun s₁ hP => reachesDoneWithinV2026_iff_execStepOutcome.mpr (h₂ s₁ hP)))

/-! ### Bidirectional Bridges with `Framework.StepWp.StepStageCut` & `ParametricCore` -/

/-- Exact equivalence between `Framework.StepWp.StepStageCut (v2026Step body)`
and `ParametricCore.StepStageCut (V2026Bridge.mirDetStep body)` (`0` unsealing
of either `@[irreducible]` barrier). -/
theorem stepStageCut_v2026_iff_parametric {body : CapturedMir} {fuel : Nat}
    {s₀ s₁ : MachineState} :
    Anneal.Framework.StepWp.StepStageCut (v2026Step body) fuel s₀ s₁ ↔
      Anneal.ParametricCore.StepStageCut
        (Anneal.ParametricCore.V2026Bridge.mirDetStep body) fuel s₀ s₁ := by
  constructor
  · intro hCut
    let ⟨k, hk, hSteps⟩ :=
      Anneal.Framework.StepWp.StepStageCut.induction
        (R := StepsToV2026 body)
        StepsToV2026.refl
        (fun _ _ _ _ hs hTail => StepsToV2026.step hs hTail) hCut
    exact Anneal.ParametricCore.StepStageCut.fuel_mono hk
      (StepsToV2026.to_parametricStepStageCut hSteps)
  · intro hCut
    let ⟨k, hk, hSteps⟩ :=
      Anneal.ParametricCore.StepStageCut.induction
        (R := fun s k t => StepsToV2026 body k s t)
        StepsToV2026.refl
        (fun _ _ _ _ hs hTail =>
          StepsToV2026.step (v2026Step_step_iff_mirDetStep_step.mpr hs) hTail)
        hCut
    exact Anneal.Framework.StepWp.StepStageCut.fuel_mono hk
      (StepsToV2026.to_stepStageCut hSteps)

/-- Prepend a `Framework.StepWp.StepStageCut (v2026Step body)` onto
`ReachesDoneWithinV2026`. -/
theorem reachesDoneWithinV2026_of_stepStageCut {body : CapturedMir}
    {post : MirOutcome → Prop} {f₁ f₂ : Nat} {s₀ s₁ : MachineState}
    (hCut : Anneal.Framework.StepWp.StepStageCut (v2026Step body) f₁ s₀ s₁)
    (hCont : ReachesDoneWithinV2026 body post f₂ s₁) :
    ReachesDoneWithinV2026 body post (f₁ + f₂) s₀ :=
  reachesDoneWithinV2026_iff_execStepOutcome.mpr
    (execStepPred_of_stepStageCut hCut
      (reachesDoneWithinV2026_iff_execStepOutcome.mp hCont))

/-- Prepend a `ParametricCore.StepStageCut (V2026Bridge.mirDetStep body)` onto
`ReachesDoneWithinV2026`. -/
theorem reachesDoneWithinV2026_of_parametricStepStageCut {body : CapturedMir}
    {post : MirOutcome → Prop} {f₁ f₂ : Nat} {s₀ s₁ : MachineState}
    (hCut : Anneal.ParametricCore.StepStageCut
      (Anneal.ParametricCore.V2026Bridge.mirDetStep body) f₁ s₀ s₁)
    (hCont : ReachesDoneWithinV2026 body post f₂ s₁) :
    ReachesDoneWithinV2026 body post (f₁ + f₂) s₀ :=
  reachesDoneWithinV2026_of_stepStageCut
    (stepStageCut_v2026_iff_parametric.mpr hCut) hCont

/-- Extract a `BoundedReachV2026` witness from a
`Framework.StepWp.StepStageCut`. -/
theorem boundedReachV2026_of_stepStageCut {body : CapturedMir}
    {stopPred : MachineState → Prop} {fuel : Nat} {s₀ s₁ : MachineState}
    (hCut : Anneal.Framework.StepWp.StepStageCut (v2026Step body) fuel s₀ s₁)
    (hStop : stopPred s₁) :
    BoundedReachV2026 body stopPred fuel s₀ := by
  let ⟨k, hk, hSteps⟩ :=
    Anneal.Framework.StepWp.StepStageCut.induction
      (R := StepsToV2026 body)
      StepsToV2026.refl
      (fun _ _ _ _ hs hTail => StepsToV2026.step hs hTail) hCut
  exact ⟨k, s₁, hk, hSteps, hStop⟩

/-- Extract a `BoundedReachV2026` witness from a
`ParametricCore.StepStageCut (V2026Bridge.mirDetStep body)`. -/
theorem boundedReachV2026_of_parametricStepStageCut {body : CapturedMir}
    {stopPred : MachineState → Prop} {fuel : Nat} {s₀ s₁ : MachineState}
    (hCut : Anneal.ParametricCore.StepStageCut
      (Anneal.ParametricCore.V2026Bridge.mirDetStep body) fuel s₀ s₁)
    (hStop : stopPred s₁) :
    BoundedReachV2026 body stopPred fuel s₀ :=
  boundedReachV2026_of_stepStageCut
    (stepStageCut_v2026_iff_parametric.mpr hCut) hStop

/-- Lift `BoundedReachV2026` directly into `ParametricCore.wpReach` over
`V2026Bridge.mirDetWpOps body`. -/
theorem wpReach_mirDet_of_boundedReachV2026 {body : CapturedMir}
    {stopPred : MachineState → Prop} {bound : Nat} {s₀ : MachineState}
    (h : BoundedReachV2026 body stopPred bound s₀) :
    Anneal.ParametricCore.wpReach
      (ops := Anneal.ParametricCore.V2026Bridge.mirDetWpOps body)
      stopPred s₀ := by
  let ⟨_, s₁, _, hSteps, hStop⟩ := h
  exact Anneal.ParametricCore.wpUntil_mono_stop
    (ops := Anneal.ParametricCore.V2026Bridge.mirDetWpOps body)
    (fun _ hEq => by subst hEq; exact hStop)
    (Anneal.ParametricCore.StepStageCut.to_wpReach
      (StepsToV2026.to_parametricStepStageCut hSteps))

/-- Lift `BoundedReachV2026` directly into `ParametricCore.wpUntilOk` over
`V2026Bridge.mirDetWpOps body`. -/
theorem wpUntilOk_mirDet_of_boundedReachV2026 {body : CapturedMir}
    {stopPred : MachineState → Prop} {post : MirOutcome → Prop}
    {bound : Nat} {s₀ : MachineState}
    (h : BoundedReachV2026 body stopPred bound s₀) :
    Anneal.ParametricCore.wpUntilOk
      (ops := Anneal.ParametricCore.V2026Bridge.mirDetWpOps body)
      stopPred post s₀ :=
  Anneal.ParametricCore.wpUntil_mono
    (ops := Anneal.ParametricCore.V2026Bridge.mirDetWpOps body)
    (fun _ hs => hs) (fun _ hf => False.elim hf) (fun _ hf => hf)
    (wpReach_mirDet_of_boundedReachV2026 h)

/-- Lift `BoundedReachV2026` directly into `Anneal.MirFuelFree.MirStepsConverges`. -/
theorem mirStepsConverges_of_boundedReachV2026 {body : CapturedMir}
    {stopPred : MachineState → Prop} {post : MirOutcome → Prop}
    {bound : Nat} {s₀ : MachineState}
    (h : BoundedReachV2026 body stopPred bound s₀) :
    MirStepsConverges body s₀ stopPred post :=
  Anneal.ParametricCore.V2026Bridge.mirStepsConverges_of_wpUntilOk
    (wpUntilOk_mirDet_of_boundedReachV2026 h)

/-- Extract a finite quantitative step bound `∃ B, ReachesDoneWithinV2026`
from a fuel-free `ParametricCore.wpUntilOk` over `V2026Bridge.mirDetWpOps body`
paired with bounded continuations at `stop`. -/
theorem reachesDoneWithinV2026_of_wpUntilOk_mirDet {body : CapturedMir}
    {stop : MachineState → Prop} {post : MirOutcome → Prop} {s₀ : MachineState}
    (h : Anneal.ParametricCore.wpUntilOk
      (ops := Anneal.ParametricCore.V2026Bridge.mirDetWpOps body) stop post s₀)
    (hCont : ∀ s', stop s' → ∃ b, ReachesDoneWithinV2026 body post b s') :
    ∃ B : Nat, ReachesDoneWithinV2026 body post B s₀ :=
  Anneal.ParametricCore.wpUntil_det_induction
    (C := fun s => ∃ B : Nat, ReachesDoneWithinV2026 body post B s)
    hCont
    (fun _ _ hStep ih => by
      let ⟨B, hB⟩ := ih
      exact ⟨B + 1, reachesDoneWithinV2026_of_step
        (v2026Step_step_iff_mirDetStep_step.mpr hStep) hB⟩)
    (fun _ _ hDone hPost =>
      ⟨1, reachesDoneWithinV2026_of_done
        (v2026Step_done_of_mirDetStep_done hDone) hPost⟩)
    (fun _ _ _ hF => False.elim hF) h

/-- Extract a finite quantitative step bound `∃ B, ReachesDoneWithinV2026`
from a fuel-free `ParametricCore.wpStateOk` over
`V2026Bridge.mirDetWpOps body`. -/
theorem reachesDoneWithinV2026_of_wpStateOk_mirDet {body : CapturedMir}
    {post : MirOutcome → Prop} {s₀ : MachineState}
    (h : Anneal.ParametricCore.wpStateOk
      (ops := Anneal.ParametricCore.V2026Bridge.mirDetWpOps body) post s₀) :
    ∃ B : Nat, ReachesDoneWithinV2026 body post B s₀ :=
  reachesDoneWithinV2026_of_wpUntilOk_mirDet h (fun _ hf => False.elim hf)

/-! ## Part III: Acyclic, Cutpoint, & Loop Step-Bound Rules + `CnfOrd` Bridge -/

/-- Two-stage sequential composition (`b₁ + b₂`) for `BoundedReachV2026`. -/
theorem v2026_sequential_compose {body : CapturedMir}
    {P Q R : MachineState → Prop} {b₁ b₂ : Nat} {s₀ : MachineState}
    (hStage₁ : BoundedReachV2026 body P b₁ s₀)
    (hStage₂ : ∀ s₁, P s₁ → BoundedReachV2026 body Q b₂ s₁)
    (hPost : ∀ s₂, Q s₂ → R s₂) :
    BoundedReachV2026 body R (b₁ + b₂) s₀ :=
  BoundedReachV2026.weaken hPost (BoundedReachV2026.trans hStage₁ hStage₂)

/-- Bind a `BoundedReachV2026` stage (`≤ b₁`) with a terminating
`ReachesDoneWithinV2026` continuation (`≤ b₂`) into total bound `b₁ + b₂`. -/
theorem v2026_sequential_done {body : CapturedMir}
    {P : MachineState → Prop} {post : MirOutcome → Prop}
    {b₁ b₂ : Nat} {s₀ : MachineState}
    (hStage : BoundedReachV2026 body P b₁ s₀)
    (hDone : ∀ s₁, P s₁ → ReachesDoneWithinV2026 body post b₂ s₁) :
    ReachesDoneWithinV2026 body post (b₁ + b₂) s₀ :=
  BoundedReachV2026.bind_done hStage hDone

/-- Bind a `BoundedReachV2026` stage (`≤ b₁`) with an `execStepOutcome`
continuation (`≤ b₂`) into total bound `b₁ + b₂`. -/
theorem v2026_sequential_exec {body : CapturedMir}
    {P : MachineState → Prop} {post : MirOutcome → Prop}
    {b₁ b₂ : Nat} {s₀ : MachineState}
    (hStage : BoundedReachV2026 body P b₁ s₀)
    (hDone : ∀ s₁, P s₁ →
      execStepOutcome (v2026Step body) post (fun _ => False) b₂ s₁) :
    execStepOutcome (v2026Step body) post (fun _ => False) (b₁ + b₂) s₀ :=
  BoundedReachV2026.bind_exec hStage hDone

/-- Bounded countdown loop rule (allowing early exit at `n + 1`): `n`
iterations each taking `≤ bodyBound` steps plus exit cost `exitBound` yield
`n * bodyBound + exitBound` total `V2026_06_01` MIR steps. -/
theorem v2026_loop_countdown {body : CapturedMir} {post : MirOutcome → Prop}
    (Inv : Nat → MachineState → Prop) (bodyBound exitBound : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2026 body post exitBound s)
    (hStep : ∀ n s, Inv (n + 1) s →
      ReachesDoneWithinV2026 body post exitBound s ∨
      BoundedReachV2026 body (Inv n) bodyBound s) :
    ∀ (n : Nat) (s : MachineState),
      Inv n s → ReachesDoneWithinV2026 body post (n * bodyBound + exitBound) s
  | 0, s, hInv => by
    rw [Nat.zero_mul, Nat.zero_add]
    exact hExit s hInv
  | n + 1, s, hInv => by
    cases hStep n s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2026.mono
        (Nat.le_add_left exitBound ((n + 1) * bodyBound)) hEarly
    | inr hNext =>
      have hJoin :
          ReachesDoneWithinV2026 body post
            (bodyBound + (n * bodyBound + exitBound)) s :=
        BoundedReachV2026.bind_done hNext
          (fun s' hs' =>
            v2026_loop_countdown Inv bodyBound exitBound hExit hStep n s' hs')
      have hArith :
          bodyBound + (n * bodyBound + exitBound) =
            (n + 1) * bodyBound + exitBound := by
        rw [Nat.succ_mul, Nat.add_comm (n * bodyBound) bodyBound, Nat.add_assoc]
      rw [hArith] at hJoin
      exact hJoin

/-- Strict no-early-exit countdown loop alias matching `#4400` `V2Loop.lean`. -/
theorem v2026_loop_const_bound {body : CapturedMir} {post : MirOutcome → Prop}
    (Inv : Nat → MachineState → Prop) (bodyBound exitBound : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2026 body post exitBound s)
    (hStep : ∀ n s, Inv (n + 1) s →
      BoundedReachV2026 body (Inv n) bodyBound s) :
    ∀ (n : Nat) (s : MachineState),
      Inv n s → ReachesDoneWithinV2026 body post (n * bodyBound + exitBound) s :=
  v2026_loop_countdown Inv bodyBound exitBound hExit
    (fun n s h => Or.inr (hStep n s h))

private theorem v2026_loop_nat_cap_aux {body : CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : MachineState → Prop) (rank : MachineState → Nat)
    (bodyBound exitBound : Nat)
    (hStep : ∀ s, Inv s →
      ReachesDoneWithinV2026 body post exitBound s ∨
      BoundedReachV2026 body (fun s' => Inv s' ∧ rank s' < rank s) bodyBound s) :
    ∀ (cap : Nat) (s : MachineState),
      Inv s → rank s ≤ cap →
      ReachesDoneWithinV2026 body post (cap * bodyBound + exitBound) s
  | 0, s, hInv, hRank => by
    cases hStep s hInv with
    | inl hEarly =>
      rw [Nat.zero_mul, Nat.zero_add]
      exact hEarly
    | inr hNext =>
      let ⟨_, _, _, _, _, hLt⟩ := hNext
      exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hLt hRank))
  | cap + 1, s, hInv, hRank => by
    cases hStep s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2026.mono
        (Nat.le_add_left exitBound ((cap + 1) * bodyBound)) hEarly
    | inr hNext =>
      have hJoin :
          ReachesDoneWithinV2026 body post
            (bodyBound + (cap * bodyBound + exitBound)) s := by
        refine BoundedReachV2026.bind_done hNext (fun s' hAnd => ?_)
        have hLe : rank s' ≤ cap :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hAnd.2 hRank)
        exact v2026_loop_nat_cap_aux Inv rank bodyBound exitBound hStep
          cap s' hAnd.1 hLe
      have hArith :
          bodyBound + (cap * bodyBound + exitBound) =
            (cap + 1) * bodyBound + exitBound := by
        rw [Nat.succ_mul, Nat.add_comm (cap * bodyBound) bodyBound, Nat.add_assoc]
      rw [hArith] at hJoin
      exact hJoin

/-- General bounded `Nat`-measure loop rule with early exit: if every `Inv s`
state either finishes in `≤ exitBound` steps or reaches `Inv s'` with
`rank s' < rank s` in `≤ bodyBound` steps, then
`ReachesDoneWithinV2026 body post (rank s * bodyBound + exitBound) s`. -/
theorem v2026_loop_nat_bounded {body : CapturedMir} {post : MirOutcome → Prop}
    (Inv : MachineState → Prop) (rank : MachineState → Nat)
    (bodyBound exitBound : Nat)
    (hStep : ∀ s, Inv s →
      ReachesDoneWithinV2026 body post exitBound s ∨
      BoundedReachV2026 body (fun s' => Inv s' ∧ rank s' < rank s) bodyBound s) :
    ∀ s : MachineState, Inv s →
      ReachesDoneWithinV2026 body post (rank s * bodyBound + exitBound) s :=
  fun s hInv =>
    v2026_loop_nat_cap_aux Inv rank bodyBound exitBound hStep (rank s) s hInv
      (Nat.le_refl (rank s))

private theorem byte_credit_step_le (k m m' K C : Nat)
    (hm : m' < m) (hk : k ≤ K * (m - m')) :
    k + (K * m' + C) ≤ K * m + C := by
  have h1 : k + (K * m' + C) ≤ K * (m - m') + (K * m' + C) :=
    Nat.add_le_add_right hk (K * m' + C)
  have h2 : K * (m - m') + (K * m' + C) = (K * (m - m') + K * m') + C := by
    rw [Nat.add_assoc]
  have h3 : K * (m - m') + K * m' = K * ((m - m') + m') := by
    rw [← Nat.mul_add]
  have h4 : (m - m') + m' = m := Nat.sub_add_cancel (Nat.le_of_lt hm)
  rw [h2, h3, h4] at h1
  exact h1

private theorem v2026_loop_byte_credit_cap_aux {body : CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : Nat → MachineState → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2026 body post C s)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ReachesDoneWithinV2026 body post C s ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2026 body k s s' ∧
        Inv m' s') :
    ∀ (cap m : Nat) (s : MachineState),
      m ≤ cap → Inv m s → ReachesDoneWithinV2026 body post (K * m + C) s
  | 0, m, s, hLe, hInv => by
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hLe
    rw [hm0, Nat.mul_zero, Nat.zero_add]
    rw [hm0] at hInv
    exact hExit s hInv
  | cap + 1, m, s, hLe, hInv => by
    cases m with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add]
      exact hExit s hInv
    | succ mPrev =>
      cases hStep (mPrev + 1) s (Nat.succ_pos mPrev) hInv with
      | inl hEarly =>
        exact ReachesDoneWithinV2026.mono
          (Nat.le_add_left C (K * (mPrev + 1))) hEarly
      | inr hNext =>
        let ⟨m', k, s', hLt, hk, hSteps, hInv'⟩ := hNext
        have hCap : m' ≤ cap :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hLt hLe)
        have hSub : ReachesDoneWithinV2026 body post (K * m' + C) s' :=
          v2026_loop_byte_credit_cap_aux Inv K C hExit hStep cap m' s' hCap hInv'
        have hSum : ReachesDoneWithinV2026 body post (k + (K * m' + C)) s :=
          reachesDoneWithinV2026_of_stepsTo hSteps hSub
        exact ReachesDoneWithinV2026.mono
          (byte_credit_step_le k (mPrev + 1) m' K C hLt hk) hSum

/-- Progress-weighted (`ByteCredit`) linear loop combinator over
`ReachesDoneWithinV2026`: iterations consuming `(m - m') ≥ 1` credit in
`k ≤ K * (m - m')` steps yield total step bound `K * m + C`. -/
theorem v2026_loop_byte_credit {body : CapturedMir} {post : MirOutcome → Prop}
    (Inv : Nat → MachineState → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2026 body post C s)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ReachesDoneWithinV2026 body post C s ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2026 body k s s' ∧
        Inv m' s') :
    ∀ (m : Nat) (s : MachineState),
      Inv m s → ReachesDoneWithinV2026 body post (K * m + C) s :=
  fun m s hInv =>
    v2026_loop_byte_credit_cap_aux Inv K C hExit hStep m m s
      (Nat.le_refl m) hInv

/-- End-to-end setup + countdown loop wrapper yielding `ExecWithinStepsV2026`,
`MirWpConverges`, `MirNoUBTree`, and `¬ DivergesV2026`. -/
theorem execWithinStepsV2026_of_setup_loop {body : CapturedMir}
    {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop} (Inv : Nat → MachineState → Prop)
    (setupBound bodyBound exitBound n : Nat)
    (hSetup : BoundedReachV2026 body (Inv n) setupBound
      (initMachineStateWithCallees body args callees))
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2026 body post exitBound s)
    (hStep : ∀ k s, Inv (k + 1) s →
      ReachesDoneWithinV2026 body post exitBound s ∨
      BoundedReachV2026 body (Inv k) bodyBound s) :
    ExecWithinStepsV2026 body args callees post
      (setupBound + (n * bodyBound + exitBound)) ∧
    MirWpConverges body (initMachineStateWithCallees body args callees) post ∧
    MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) ∧
    ¬ DivergesV2026 body (initMachineStateWithCallees body args callees) := by
  have hLoop := v2026_loop_countdown Inv bodyBound exitBound hExit hStep
  have hReach :
      ExecWithinStepsV2026 body args callees post
        (setupBound + (n * bodyBound + exitBound)) :=
    BoundedReachV2026.bind_done hSetup (fun s₁ hInv => hLoop n s₁ hInv)
  exact ⟨hReach,
    mirWpConverges_of_reachesDoneWithinV2026 hReach,
    mirNoUBTree_of_reachesDoneWithinV2026 hReach,
    not_divergesV2026_of_reachesDoneWithinV2026 hReach⟩

/-- `execStateV2026` interface for the countdown loop rule (matches `#4400`
`v2_loop_const_exec`). -/
theorem v2026_loop_const_exec {body : CapturedMir} {post : MirOutcome → Prop}
    (Inv : Nat → MachineState → Prop) (bodyBound exitBound : Nat)
    (hExit : ∀ s, Inv 0 s → execStateV2026 body exitBound s post)
    (hStep : ∀ n s, Inv (n + 1) s →
      execStateV2026 body exitBound s post ∨
      BoundedReachV2026 body (Inv n) bodyBound s) :
    ∀ (n : Nat) (s : MachineState),
      Inv n s → execStateV2026 body (n * bodyBound + exitBound) s post :=
  fun n s hInv =>
    reachesDoneWithinV2026_iff_execStepOutcome.mp
      (v2026_loop_countdown Inv bodyBound exitBound
        (fun st h0 => reachesDoneWithinV2026_iff_execStepOutcome.mpr (hExit st h0))
        (fun k st hk =>
          match hStep k st hk with
          | .inl hE => .inl (reachesDoneWithinV2026_iff_execStepOutcome.mpr hE)
          | .inr hB => .inr hB)
        n s hInv)

/-- `execStateV2026` interface for the byte-credit loop rule (matches `#4400`
`v2_loop_byte_credit_exec`). -/
theorem v2026_loop_byte_credit_exec {body : CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : Nat → MachineState → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → execStateV2026 body C s post)
    (hStep : ∀ m s, 0 < m → Inv m s →
      execStateV2026 body C s post ∨
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2026 body k s s' ∧
        Inv m' s') :
    ∀ (m : Nat) (s : MachineState),
      Inv m s → execStateV2026 body (K * m + C) s post :=
  fun m s hInv =>
    reachesDoneWithinV2026_iff_execStepOutcome.mp
      (v2026_loop_byte_credit Inv K C
        (fun st h0 => reachesDoneWithinV2026_iff_execStepOutcome.mpr (hExit st h0))
        (fun m' st hm hI =>
          match hStep m' st hm hI with
          | .inl hE => .inl (reachesDoneWithinV2026_iff_execStepOutcome.mpr hE)
          | .inr hN => .inr hN)
        m s hInv)

/-- Strict (no early exit) byte-credit loop rule (matches `#4400`
`v2_loop_byte_credit_strict`). -/
theorem v2026_loop_byte_credit_strict {body : CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : Nat → MachineState → Prop) (K C : Nat)
    (hExit : ∀ s, Inv 0 s → execStateV2026 body C s post)
    (hStep : ∀ m s, 0 < m → Inv m s →
      ∃ m' k s', m' < m ∧ k ≤ K * (m - m') ∧ StepsToV2026 body k s s' ∧
        Inv m' s') :
    ∀ (m : Nat) (s : MachineState),
      Inv m s → execStateV2026 body (K * m + C) s post :=
  v2026_loop_byte_credit_exec Inv K C hExit
    (fun m s hm hInv => .inr (hStep m s hm hInv))

/-- End-to-end setup + byte-credit loop wrapper yielding
`ExecWithinStepsV2026`, `MirWpConverges`, `MirNoCallWpConverges`,
`MirNoUBTree`, and `¬ DivergesV2026` (matches `#4400`
`execWithinStepsV2_of_setup_byte_credit`). -/
theorem execWithinStepsV2026_of_setup_byte_credit {body : CapturedMir}
    {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop} (Inv : Nat → MachineState → Prop)
    (setupBound K C m : Nat)
    (hSetup : BoundedReachV2026 body (Inv m) setupBound
      (initMachineStateWithCallees body args callees))
    (hExit : ∀ s, Inv 0 s → ReachesDoneWithinV2026 body post C s)
    (hStep : ∀ cur s, 0 < cur → Inv cur s →
      ReachesDoneWithinV2026 body post C s ∨
      ∃ cur' k s', cur' < cur ∧ k ≤ K * (cur - cur') ∧
        StepsToV2026 body k s s' ∧ Inv cur' s') :
    ExecWithinStepsV2026 body args callees post (setupBound + (K * m + C)) ∧
    MirWpConverges body (initMachineStateWithCallees body args callees) post ∧
    MirNoCallWpConverges body (initMachineStateWithCallees body args callees) post ∧
    MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) ∧
    ¬ DivergesV2026 body (initMachineStateWithCallees body args callees) := by
  have hReach :
      ExecWithinStepsV2026 body args callees post (setupBound + (K * m + C)) :=
    BoundedReachV2026.bind_done hSetup
      (fun s₁ hInv => v2026_loop_byte_credit Inv K C hExit hStep m s₁ hInv)
  exact ⟨hReach,
    mirWpConverges_of_reachesDoneWithinV2026 hReach,
    mirNoCallWpConverges_of_reachesDoneWithinV2026 hReach,
    mirNoUBTree_of_reachesDoneWithinV2026 hReach,
    not_divergesV2026_of_reachesDoneWithinV2026 hReach⟩

/-! ### Canonical Two-Term Ordinals (`cnfLex2`) & Bounded-Reset Ceiling (`lex2Bound`) -/

/-- Canonical `CnfOrd` encoding `ω^1 * outer + ω^0 * inner`. -/
def cnfLex2 (outer inner : Nat) : CnfOrd :=
  cnfNorm [(1, outer), (0, inner)]

/-- `cnfLex2 outer inner` is always canonical. -/
theorem cnfLex2_canonical (outer inner : Nat) :
    isCanonicalCnf (cnfLex2 outer inner) = true :=
  isCanonicalCnf_cnfNorm [(1, outer), (0, inner)]

/-- Coefficient at degree `0` of `cnfLex2 outer inner` is `inner`. -/
theorem cnfCoeffAt_cnfLex2_zero (outer inner : Nat) :
    cnfCoeffAt 0 (cnfLex2 outer inner) = inner := by
  unfold cnfLex2
  rw [cnfCoeffAt_cnfNorm]
  rfl

/-- Coefficient at degree `1` of `cnfLex2 outer inner` is `outer`. -/
theorem cnfCoeffAt_cnfLex2_one (outer inner : Nat) :
    cnfCoeffAt 1 (cnfLex2 outer inner) = outer := by
  unfold cnfLex2
  rw [cnfCoeffAt_cnfNorm]
  rfl

/-- All coefficients above degree `1` in `cnfLex2 outer inner` vanish. -/
theorem cnfCoeffAt_cnfLex2_gt_one (outer inner q : Nat)
    (hGt : natLt 1 q = true) :
    cnfCoeffAt q (cnfLex2 outer inner) = 0 := by
  unfold cnfLex2
  rw [cnfCoeffAt_cnfNorm]
  cases q with
  | zero => cases hGt
  | succ q₁ =>
    cases q₁ with
    | zero => cases hGt
    | succ _ => rfl

/-- Inner counter decrement strictly drops `cnfLex2 o i < cnfLex2 o (i + 1)`. -/
theorem cnfLex2_drop_inner (o i : Nat) :
    cnfLt (cnfLex2 o i) (cnfLex2 o (i + 1)) = true := by
  refine cnfLt_of_coeff_drop (cnfLex2 o i) (cnfLex2 o (i + 1))
    (cnfLex2_canonical o i) (cnfLex2_canonical o (i + 1)) 0 ?_ ?_
  · rw [cnfCoeffAt_cnfLex2_zero, cnfCoeffAt_cnfLex2_zero]
    exact (nat_ble_iff (i + 1) (i + 1)).mpr (Nat.le_refl (i + 1))
  · intro q hGt
    cases q with
    | zero => cases hGt
    | succ q₁ =>
      cases q₁ with
      | zero => rw [cnfCoeffAt_cnfLex2_one, cnfCoeffAt_cnfLex2_one]
      | succ q₂ =>
        have hGt₁ : natLt 1 (q₂ + 2) = true :=
          (nat_ble_iff 2 (q₂ + 2)).mpr
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le q₂)))
        rw [cnfCoeffAt_cnfLex2_gt_one o i (q₂ + 2) hGt₁,
          cnfCoeffAt_cnfLex2_gt_one o (i + 1) (q₂ + 2) hGt₁]

/-- Outer counter decrement drops `cnfLex2 o i' < cnfLex2 (o + 1) i` regardless
of arbitrary finite inner reset `i'`. -/
theorem cnfLex2_drop_outer (o i i' : Nat) :
    cnfLt (cnfLex2 o i') (cnfLex2 (o + 1) i) = true := by
  refine cnfLt_of_coeff_drop (cnfLex2 o i') (cnfLex2 (o + 1) i)
    (cnfLex2_canonical o i') (cnfLex2_canonical (o + 1) i) 1 ?_ ?_
  · rw [cnfCoeffAt_cnfLex2_one, cnfCoeffAt_cnfLex2_one]
    exact (nat_ble_iff (o + 1) (o + 1)).mpr (Nat.le_refl (o + 1))
  · intro q hGt
    rw [cnfCoeffAt_cnfLex2_gt_one o i' q hGt,
      cnfCoeffAt_cnfLex2_gt_one (o + 1) i q hGt]

/-- Exact closed-form step budget for an `ω^1 * outer + ω^0 * inner` nested
loop whose outer back-edges reset the inner counter to at most `resetCap`:
`outer * (resetCap * kInner + kOuter) + inner * kInner + kExit`. -/
def lex2Bound (resetCap kInner kOuter kExit outer inner : Nat) : Nat :=
  outer * (resetCap * kInner + kOuter) + inner * kInner + kExit

private theorem lex2Bound_inner_step (resetCap kInner kOuter kExit o i : Nat) :
    kInner + lex2Bound resetCap kInner kOuter kExit o i =
      lex2Bound resetCap kInner kOuter kExit o (i + 1) := by
  unfold lex2Bound
  rw [Nat.succ_mul]
  rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) (i * kInner) kExit]
  rw [← Nat.add_assoc kInner (o * (resetCap * kInner + kOuter))
    (i * kInner + kExit)]
  rw [Nat.add_comm kInner (o * (resetCap * kInner + kOuter))]
  rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) kInner (i * kInner + kExit)]
  rw [← Nat.add_assoc kInner (i * kInner) kExit]
  rw [Nat.add_comm kInner (i * kInner)]
  rw [← Nat.add_assoc (o * (resetCap * kInner + kOuter))
    (i * kInner + kInner) kExit]

private theorem lex2Bound_outer_step
    (resetCap kInner kOuter kExit o i' : Nat) (hi : i' ≤ resetCap) :
    kOuter + lex2Bound resetCap kInner kOuter kExit o i' ≤
      lex2Bound resetCap kInner kOuter kExit (o + 1) 0 := by
  unfold lex2Bound
  have hMul : i' * kInner ≤ resetCap * kInner :=
    Nat.mul_le_mul_right kInner hi
  have hInnerLe :
      kOuter + (o * (resetCap * kInner + kOuter) + i' * kInner + kExit) ≤
        kOuter +
          (o * (resetCap * kInner + kOuter) + resetCap * kInner + kExit) :=
    Nat.add_le_add_left
      (Nat.add_le_add_right
        (Nat.add_le_add_left hMul (o * (resetCap * kInner + kOuter))) kExit)
      kOuter
  have hEq :
      kOuter +
          (o * (resetCap * kInner + kOuter) + resetCap * kInner + kExit) =
        (o + 1) * (resetCap * kInner + kOuter) + 0 * kInner + kExit := by
    rw [Nat.zero_mul, Nat.add_zero]
    rw [Nat.succ_mul]
    rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) (resetCap * kInner) kExit]
    rw [← Nat.add_assoc kOuter (o * (resetCap * kInner + kOuter))
      (resetCap * kInner + kExit)]
    rw [Nat.add_comm kOuter (o * (resetCap * kInner + kOuter))]
    rw [Nat.add_assoc (o * (resetCap * kInner + kOuter)) kOuter
      (resetCap * kInner + kExit)]
    rw [← Nat.add_assoc kOuter (resetCap * kInner) kExit]
    rw [Nat.add_comm kOuter (resetCap * kInner)]
    rw [← Nat.add_assoc (o * (resetCap * kInner + kOuter))
      (resetCap * kInner + kOuter) kExit]
  rw [hEq] at hInnerLe
  exact hInnerLe

private theorem lex2_kExit_le_bound (resetCap kInner kOuter kExit o i : Nat) :
    kExit ≤ lex2Bound resetCap kInner kOuter kExit o i := by
  unfold lex2Bound
  exact Nat.le_add_left kExit
    (o * (resetCap * kInner + kOuter) + i * kInner)

private theorem v2026_loop_lex2_zero_aux {body : CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : Nat → Nat → MachineState → Prop)
    (resetCap kInner kOuter kExit : Nat)
    (hBase : ∀ s, Inv 0 0 s → ReachesDoneWithinV2026 body post kExit s)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2026 body post kExit s ∨
      BoundedReachV2026 body (Inv o i) kInner s) :
    ∀ (i : Nat) (s : MachineState),
      Inv 0 i s →
      ReachesDoneWithinV2026 body post
        (lex2Bound resetCap kInner kOuter kExit 0 i) s
  | 0, s, hInv => by
    unfold lex2Bound
    rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add]
    exact hBase s hInv
  | i + 1, s, hInv => by
    cases hInner 0 i s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2026.mono
        (lex2_kExit_le_bound resetCap kInner kOuter kExit 0 (i + 1)) hEarly
    | inr hStep =>
      have hJoin :
          ReachesDoneWithinV2026 body post
            (kInner + lex2Bound resetCap kInner kOuter kExit 0 i) s :=
        BoundedReachV2026.bind_done hStep (fun s' hs' =>
          v2026_loop_lex2_zero_aux Inv resetCap kInner kOuter kExit hBase hInner
            i s' hs')
      rw [lex2Bound_inner_step] at hJoin
      exact hJoin

private theorem v2026_loop_lex2_succ_aux {body : CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : Nat → Nat → MachineState → Prop)
    (resetCap kInner kOuter kExit oPrev : Nat)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2026 body post kExit s ∨
      BoundedReachV2026 body (Inv o i) kInner s)
    (hOuter : ∀ o s, Inv (o + 1) 0 s →
      ReachesDoneWithinV2026 body post kExit s ∨
      ∃ i', i' ≤ resetCap ∧ BoundedReachV2026 body (Inv o i') kOuter s)
    (hPrev : ∀ i' s, i' ≤ resetCap → Inv oPrev i' s →
      ReachesDoneWithinV2026 body post
        (lex2Bound resetCap kInner kOuter kExit oPrev i') s) :
    ∀ (i : Nat) (s : MachineState),
      Inv (oPrev + 1) i s →
      ReachesDoneWithinV2026 body post
        (lex2Bound resetCap kInner kOuter kExit (oPrev + 1) i) s
  | 0, s, hInv => by
    cases hOuter oPrev s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2026.mono
        (lex2_kExit_le_bound resetCap kInner kOuter kExit (oPrev + 1) 0) hEarly
    | inr hNext =>
      let ⟨i', hi', hStep⟩ := hNext
      have hJoin :
          ReachesDoneWithinV2026 body post
            (kOuter + lex2Bound resetCap kInner kOuter kExit oPrev i') s :=
        BoundedReachV2026.bind_done hStep (fun s' hs' => hPrev i' s' hi' hs')
      exact ReachesDoneWithinV2026.mono
        (lex2Bound_outer_step resetCap kInner kOuter kExit oPrev i' hi') hJoin
  | i + 1, s, hInv => by
    cases hInner (oPrev + 1) i s hInv with
    | inl hEarly =>
      exact ReachesDoneWithinV2026.mono
        (lex2_kExit_le_bound resetCap kInner kOuter kExit (oPrev + 1) (i + 1))
        hEarly
    | inr hStep =>
      have hJoin :
          ReachesDoneWithinV2026 body post
            (kInner +
              lex2Bound resetCap kInner kOuter kExit (oPrev + 1) i) s :=
        BoundedReachV2026.bind_done hStep (fun s' hs' =>
          v2026_loop_lex2_succ_aux Inv resetCap kInner kOuter kExit oPrev
            hInner hOuter hPrev i s' hs')
      rw [lex2Bound_inner_step] at hJoin
      exact hJoin

/-- Nested bounded-reset loop combinator for `(outer, inner)` with ordinal rank
`cnfLex2 outer inner`: proves exact explicit `Nat` step bound
`lex2Bound resetCap kInner kOuter kExit outer inner`. -/
theorem v2026_loop_lex2_bounded_reset {body : CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : Nat → Nat → MachineState → Prop)
    (resetCap kInner kOuter kExit : Nat)
    (hBase : ∀ s, Inv 0 0 s → ReachesDoneWithinV2026 body post kExit s)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2026 body post kExit s ∨
      BoundedReachV2026 body (Inv o i) kInner s)
    (hOuter : ∀ o s, Inv (o + 1) 0 s →
      ReachesDoneWithinV2026 body post kExit s ∨
      ∃ i', i' ≤ resetCap ∧ BoundedReachV2026 body (Inv o i') kOuter s) :
    ∀ (o i : Nat) (s : MachineState),
      Inv o i s →
      ReachesDoneWithinV2026 body post
        (lex2Bound resetCap kInner kOuter kExit o i) s := by
  intro o
  induction o with
  | zero =>
    intro i s hInv
    exact v2026_loop_lex2_zero_aux Inv resetCap kInner kOuter kExit hBase hInner
      i s hInv
  | succ oPrev ih =>
    intro i s hInv
    exact v2026_loop_lex2_succ_aux Inv resetCap kInner kOuter kExit oPrev
      hInner hOuter (fun i' st _ hSt => ih i' st hSt) i s hInv

/-- End-to-end wrapper combining setup prefix `setupBound` and closed-form
`lex2Bound`. -/
theorem execWithinStepsV2026_of_lex2_bounded_reset {body : CapturedMir}
    {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop}
    (Inv : Nat → Nat → MachineState → Prop)
    (setupBound resetCap kInner kOuter kExit outer inner : Nat)
    (hSetup : BoundedReachV2026 body (Inv outer inner) setupBound
      (initMachineStateWithCallees body args callees))
    (hBase : ∀ s, Inv 0 0 s → ReachesDoneWithinV2026 body post kExit s)
    (hInner : ∀ o i s, Inv o (i + 1) s →
      ReachesDoneWithinV2026 body post kExit s ∨
      BoundedReachV2026 body (Inv o i) kInner s)
    (hOuter : ∀ o s, Inv (o + 1) 0 s →
      ReachesDoneWithinV2026 body post kExit s ∨
      ∃ i', i' ≤ resetCap ∧ BoundedReachV2026 body (Inv o i') kOuter s) :
    ExecWithinStepsV2026 body args callees post
      (setupBound + lex2Bound resetCap kInner kOuter kExit outer inner) ∧
    MirWpConverges body (initMachineStateWithCallees body args callees) post ∧
    MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) ∧
    ¬ DivergesV2026 body (initMachineStateWithCallees body args callees) := by
  have hLoop := v2026_loop_lex2_bounded_reset Inv resetCap kInner kOuter kExit
    hBase hInner hOuter outer inner
  have hReach :
      ExecWithinStepsV2026 body args callees post
        (setupBound + lex2Bound resetCap kInner kOuter kExit outer inner) :=
    BoundedReachV2026.bind_done hSetup (fun s₁ hInv => hLoop s₁ hInv)
  exact ⟨hReach,
    mirWpConverges_of_reachesDoneWithinV2026 hReach,
    mirNoUBTree_of_reachesDoneWithinV2026 hReach,
    not_divergesV2026_of_reachesDoneWithinV2026 hReach⟩

/-! ### Constructive `< ω^ω` Step-Budget Extraction via `CnfOrd.Worklist` / `CnfAcc` -/

/-- Well-founded `< ω^ω` descent extraction over `ReachesDoneWithinV2026`:
if every `Inv s` state either exits within `exitBound` steps or advances in
`BoundedReachV2026` (`≤ iterBound`) to `s'` strictly lowering
`cnfNorm (measure s')`, then `ReachesDoneWithinV2026 body post B s` holds for
an extracted finite bound `B : Nat`. -/
theorem v2026_loop_cnfOrd_exists {body : CapturedMir} {post : MirOutcome → Prop}
    (Inv : MachineState → Prop) (measure : MachineState → CnfOrd)
    (iterBound exitBound : Nat)
    (hStep : ∀ s : MachineState, Inv s →
      ReachesDoneWithinV2026 body post exitBound s ∨
      BoundedReachV2026 body
        (fun s' =>
          Inv s' ∧ cnfLt (cnfNorm (measure s')) (cnfNorm (measure s)) = true)
        iterBound s) :
    ∀ s : MachineState, Inv s →
      ∃ B : Nat, ReachesDoneWithinV2026 body post B s := by
  have hAux :
      ∀ (ord : CnfOrd), CnfAcc ord →
      ∀ s : MachineState, Inv s → cnfNorm (measure s) = ord →
        ∃ B : Nat, ReachesDoneWithinV2026 body post B s := by
    intro ord hAcc
    induction hAcc with
    | intro x _ ih =>
      intro s hInv hOrd
      cases hStep s hInv with
      | inl hDone => exact ⟨exitBound, hDone⟩
      | inr hNext =>
        let ⟨k, s', _, hSteps, hInv', hLt⟩ := hNext
        rw [hOrd] at hLt
        let ⟨B', hSub⟩ := ih (cnfNorm (measure s'))
          (isCanonicalCnf_cnfNorm _) hLt s' hInv' rfl
        exact ⟨k + B', reachesDoneWithinV2026_of_stepsTo hSteps hSub⟩
  intro s hInv
  exact hAux (cnfNorm (measure s))
    (cnfAcc_all (cnfNorm (measure s)) (isCanonicalCnf_cnfNorm _))
    s hInv rfl

/-- Constructive `< ω^ω` step-budget extraction driven directly through
`Anneal.CnfOrd.execLoop_cnfNorm_exists` (`CnfOrd/Worklist.lean`). -/
theorem v2026_loop_cnfOrd_of_execUntil {body : CapturedMir}
    {Inv Exit : MachineState → Prop} {post : MirOutcome → Prop}
    {rawRank : MachineState → CnfOrd}
    (hStep : ∀ s, Inv s →
      Exit s ∨ (∃ f,
        execUntil (v2026Step body)
          (fun s' =>
            (Inv s' ∧ cnfLt (cnfNorm (rawRank s')) (cnfNorm (rawRank s)) = true)
            ∨ Exit s')
          post (fun _ => False) f s))
    (hExit : ∀ s, Exit s → ReachesDoneWithinV2026 body post exitBound s)
    (s : MachineState) (hInv : Inv s) :
    ∃ B : Nat, ReachesDoneWithinV2026 body post B s := by
  let ⟨fLoop, hLoop⟩ :=
    execLoop_cnfNorm_exists (rawRank := rawRank) hStep s hInv
  refine ⟨fLoop + exitBound, reachesDoneWithinV2026_iff_execStepOutcome.mpr ?_⟩
  exact execUntilPred_to_execStepPred hLoop (fun s' hEx =>
    reachesDoneWithinV2026_iff_execStepOutcome.mp (hExit s' hEx))

/-- End-to-end `V2026_06_01` adequacy from an arbitrary `< ω^ω` ranking measure:
extracts a finite `Nat` step bound `B` yielding `ExecWithinStepsV2026`,
`MirWpConverges`, `MirNoUBTree`, and `¬ DivergesV2026`. -/
theorem execWithinStepsV2026_of_cnfOrd {body : CapturedMir}
    {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop} (Inv : MachineState → Prop)
    (measure : MachineState → CnfOrd) (setupBound iterBound exitBound : Nat)
    (hSetup : BoundedReachV2026 body Inv setupBound
      (initMachineStateWithCallees body args callees))
    (hStep : ∀ s : MachineState, Inv s →
      ReachesDoneWithinV2026 body post exitBound s ∨
      BoundedReachV2026 body
        (fun s' =>
          Inv s' ∧ cnfLt (cnfNorm (measure s')) (cnfNorm (measure s)) = true)
        iterBound s) :
    ∃ B : Nat,
      ExecWithinStepsV2026 body args callees post B ∧
      MirWpConverges body (initMachineStateWithCallees body args callees) post ∧
      MirNoUBTree (mirTree body (initMachineStateWithCallees body args callees)) ∧
      ¬ DivergesV2026 body (initMachineStateWithCallees body args callees) := by
  let ⟨kSetup, s₁, _, hSetupSteps, hInv₁⟩ := hSetup
  let ⟨B', hLoop⟩ := v2026_loop_cnfOrd_exists Inv measure iterBound exitBound
    hStep s₁ hInv₁
  have hReach :
      ExecWithinStepsV2026 body args callees post (kSetup + B') :=
    reachesDoneWithinV2026_of_stepsTo hSetupSteps hLoop
  exact ⟨kSetup + B', hReach,
    mirWpConverges_of_reachesDoneWithinV2026 hReach,
    mirNoUBTree_of_reachesDoneWithinV2026 hReach,
    not_divergesV2026_of_reachesDoneWithinV2026 hReach⟩

/-! ### `CnfStepConverges` & `WorklistPool` MIR Simulation Bridges -/

/-- Lift a `CnfStepConverges` abstract termination derivation under simulation
`sim` into a `V2026_06_01` MIR step budget `steps * iterBound + exitBound`. -/
theorem v2026_steps_of_cnfStepConverges {α : Type} {body : CapturedMir}
    {post : MirOutcome → Prop}
    (stepAbs : α → Option α) (measure : α → CnfOrd)
    (sim : α → MachineState → Prop) (iterBound exitBound : Nat)
    (hDone : ∀ a s, stepAbs a = none → sim a s →
      ReachesDoneWithinV2026 body post exitBound s)
    (hStep : ∀ a a' s, stepAbs a = some a' → sim a s →
      BoundedReachV2026 body (sim a') iterBound s)
    {a₀ aFinal : α}
    (hConv : CnfStepConverges stepAbs measure a₀ aFinal) :
    ∀ s₀ : MachineState, sim a₀ s₀ →
      ∃ steps : Nat,
        ReachesDoneWithinV2026 body post (steps * iterBound + exitBound) s₀ := by
  induction hConv with
  | quiescent a hNone =>
    intro s₀ hSim
    refine ⟨0, ?_⟩
    rw [Nat.zero_mul, Nat.zero_add]
    exact hDone a s₀ hNone hSim
  | step a a' _ hSome _ _ ih =>
    intro s₀ hSim
    have hReach : BoundedReachV2026 body (sim a') iterBound s₀ :=
      hStep a a' s₀ hSome hSim
    let ⟨k, s₁, hk, hSteps, hSim'⟩ := hReach
    let ⟨steps, hRest⟩ := ih s₁ hSim'
    refine ⟨steps + 1, ?_⟩
    have hJoin :
        ReachesDoneWithinV2026 body post (k + (steps * iterBound + exitBound)) s₀ :=
      reachesDoneWithinV2026_of_stepsTo hSteps hRest
    have hMono := ReachesDoneWithinV2026.mono
      (Nat.add_le_add_right hk (steps * iterBound + exitBound)) hJoin
    have hArith :
        iterBound + (steps * iterBound + exitBound) =
          (steps + 1) * iterBound + exitBound := by
      rw [Nat.succ_mul, Nat.add_comm (steps * iterBound) iterBound, Nat.add_assoc]
    rw [hArith] at hMono
    exact hMono

/-- Lift any `< ω^ω`-ranked `stepAbs : α → Option α` via
`cnfStep_terminates_all` and simulation `sim` into a `V2026_06_01` step
bound. -/
theorem v2026_steps_of_cnfStep_terminates {α : Type} {body : CapturedMir}
    {post : MirOutcome → Prop}
    (stepAbs : α → Option α) (measure : α → CnfOrd)
    (InvAbs : α → Prop) (sim : α → MachineState → Prop)
    (iterBound exitBound : Nat)
    (hDesc : ∀ (a a' : α), InvAbs a → stepAbs a = some a' →
      InvAbs a' ∧ cnfLt (cnfNorm (measure a')) (cnfNorm (measure a)) = true)
    (hDone : ∀ a s, stepAbs a = none → sim a s →
      ReachesDoneWithinV2026 body post exitBound s)
    (hStep : ∀ a a' s, stepAbs a = some a' → sim a s →
      BoundedReachV2026 body (sim a') iterBound s)
    {a₀ : α} {s₀ : MachineState} (hInv₀ : InvAbs a₀) (hSim₀ : sim a₀ s₀) :
    ∃ steps : Nat,
      ReachesDoneWithinV2026 body post (steps * iterBound + exitBound) s₀ := by
  let ⟨_, _, hConv, _, _⟩ := cnfStep_terminates_all stepAbs measure InvAbs hDesc
    a₀ hInv₀
  exact v2026_steps_of_cnfStepConverges stepAbs measure sim iterBound exitBound
    hDone hStep hConv s₀ hSim₀

/-- Lift a `WorklistConverges` proof into a `V2026_06_01` MIR step budget
`steps * iterBound + exitBound`. -/
theorem v2026_steps_of_worklist_converges {body : CapturedMir}
    {post : MirOutcome → Prop}
    (pol : SpawnPolicy) (sim : WorklistPool → MachineState → Prop)
    (iterBound exitBound : Nat)
    (hDone : ∀ w s, poolIsNonEmpty w = false → sim w s →
      ReachesDoneWithinV2026 body post exitBound s)
    (hStep : ∀ w w' s, poolIsNonEmpty w = true →
      worklistStep pol w = .returned w' → sim w s →
      BoundedReachV2026 body (sim w') iterBound s)
    {w₀ wFinal : WorklistPool}
    (hConv : WorklistConverges pol w₀ wFinal) :
    ∀ s₀ : MachineState, sim w₀ s₀ →
      ∃ steps : Nat,
        ReachesDoneWithinV2026 body post (steps * iterBound + exitBound) s₀ := by
  induction hConv with
  | quiescent w hEmp =>
    intro s₀ hSim
    refine ⟨0, ?_⟩
    rw [Nat.zero_mul, Nat.zero_add]
    exact hDone w s₀ hEmp hSim
  | step w wNext _ hNonEmp hWork _ _ ih =>
    intro s₀ hSim
    have hReach : BoundedReachV2026 body (sim wNext) iterBound s₀ :=
      hStep w wNext s₀ hNonEmp hWork hSim
    let ⟨k, s₁, hk, hSteps, hSim'⟩ := hReach
    let ⟨steps, hRest⟩ := ih s₁ hSim'
    refine ⟨steps + 1, ?_⟩
    have hJoin :
        ReachesDoneWithinV2026 body post (k + (steps * iterBound + exitBound)) s₀ :=
      reachesDoneWithinV2026_of_stepsTo hSteps hRest
    have hMono := ReachesDoneWithinV2026.mono
      (Nat.add_le_add_right hk (steps * iterBound + exitBound)) hJoin
    have hArith :
        iterBound + (steps * iterBound + exitBound) =
          (steps + 1) * iterBound + exitBound := by
      rw [Nat.succ_mul, Nat.add_comm (steps * iterBound) iterBound, Nat.add_assoc]
    rw [hArith] at hMono
    exact hMono

/-- Lift any `PolicyAdmissible` worklist simulator (such as
`towerLookupNext_admissible`) via `worklist_terminates_all` into a `V2026_06_01`
MIR step bound. -/
theorem v2026_steps_of_worklist_terminates {body : CapturedMir}
    {post : MirOutcome → Prop}
    (pol : SpawnPolicy) (hPol : PolicyAdmissible pol)
    (sim : WorklistPool → MachineState → Prop) (iterBound exitBound : Nat)
    (hDone : ∀ w s, poolIsNonEmpty w = false → sim w s →
      ReachesDoneWithinV2026 body post exitBound s)
    (hStep : ∀ w w' s, poolIsNonEmpty w = true →
      worklistStep pol w = .returned w' → sim w s →
      BoundedReachV2026 body (sim w') iterBound s)
    (w₀ : WorklistPool) (s₀ : MachineState) (hSim₀ : sim w₀ s₀) :
    ∃ steps : Nat,
      ReachesDoneWithinV2026 body post (steps * iterBound + exitBound) s₀ := by
  let ⟨_, hConv, _, _, _, _⟩ := worklist_terminates_all pol hPol w₀
  exact v2026_steps_of_worklist_converges pol sim iterBound exitBound hDone hStep
    hConv s₀ hSim₀

/-! ### Step-Bounded Reactive Per-Frame / Per-Event Contracts (`ReactiveStepContractV2026`) -/

/-- Non-stuttering bounded `V2026_06_01` reachability (`1 ≤ k ≤ bound`):
requires at least one real MIR `.step` transition before reaching
`stopPred`. -/
def StrictBoundedReachV2026 (body : CapturedMir) (stopPred : MachineState → Prop)
    (bound : Nat) (s : MachineState) : Prop :=
  ∃ k : Nat, ∃ s' : MachineState,
    1 ≤ k ∧ k ≤ bound ∧ StepsToV2026 body k s s' ∧ stopPred s'

/-- Sequential composition (`b₁ + b₂`) for `StrictBoundedReachV2026`. -/
theorem StrictBoundedReachV2026.trans {body : CapturedMir}
    {P Q : MachineState → Prop} {b₁ b₂ : Nat} {s₀ : MachineState}
    (h₁ : StrictBoundedReachV2026 body P b₁ s₀)
    (h₂ : ∀ s₁, P s₁ → StrictBoundedReachV2026 body Q b₂ s₁) :
    StrictBoundedReachV2026 body Q (b₁ + b₂) s₀ := by
  let ⟨k₁, s₁, hPos₁, hk₁, hSteps₁, hP⟩ := h₁
  let ⟨k₂, s₂, _, hk₂, hSteps₂, hQ⟩ := h₂ s₁ hP
  exact ⟨k₁ + k₂, s₂, Nat.le_trans hPos₁ (Nat.le_add_right k₁ k₂),
    Nat.add_le_add hk₁ hk₂, StepsToV2026.trans hSteps₁ hSteps₂, hQ⟩

/-- Budget monotonicity for `StrictBoundedReachV2026`. -/
theorem StrictBoundedReachV2026.mono {body : CapturedMir}
    {stopPred : MachineState → Prop} {b₁ b₂ : Nat} {s : MachineState}
    (hLe : b₁ ≤ b₂) (h : StrictBoundedReachV2026 body stopPred b₁ s) :
    StrictBoundedReachV2026 body stopPred b₂ s := by
  let ⟨k, s', hPos, hk, hSteps, hP⟩ := h
  exact ⟨k, s', hPos, Nat.le_trans hk hLe, hSteps, hP⟩

/-- Per-frame / per-event reactive `V2026_06_01` latency contract: from any
`inv s`, execution within `frameBound` MIR steps either finishes cleanly in
`post` or advances strictly (`1 ≤ k ≤ frameBound` steps) to the next `yieldPred`
checkpoint preserving `inv`. -/
def ReactiveStepContractV2026 (body : CapturedMir)
    (inv yieldPred : MachineState → Prop) (post : MirOutcome → Prop)
    (frameBound : Nat) : Prop :=
  ∀ s : MachineState, inv s →
    ReachesDoneWithinV2026 body post frameBound s ∨
    StrictBoundedReachV2026 body (fun s' => inv s' ∧ yieldPred s') frameBound s

/-- Iterate a `ReactiveStepContractV2026` over any finite prefix of `frames`
ticks: within at most `frames * frameBound` MIR steps, execution either
finishes cleanly in `post` or completes `frames` non-stuttering checkpoints
(`frames ≤ k` steps). -/
theorem ReactiveStepContractV2026.iterate_prefix {body : CapturedMir}
    {inv yieldPred : MachineState → Prop} {post : MirOutcome → Prop}
    {frameBound : Nat}
    (hContract : ReactiveStepContractV2026 body inv yieldPred post frameBound) :
    ∀ (frames : Nat) (s₀ : MachineState), inv s₀ →
      ReachesDoneWithinV2026 body post (frames * frameBound) s₀ ∨
      ∃ (k : Nat) (s' : MachineState),
        frames ≤ k ∧ k ≤ frames * frameBound ∧ StepsToV2026 body k s₀ s' ∧
          inv s' ∧ (0 < frames → yieldPred s')
  | 0, s₀, hInv => by
    rw [Nat.zero_mul]
    refine Or.inr ⟨0, s₀, Nat.le_refl 0, Nat.le_refl 0, StepsToV2026.refl s₀,
      hInv, fun hLt => False.elim (Nat.not_lt_zero 0 hLt)⟩
  | n + 1, s₀, hInv => by
    have hPrev := ReactiveStepContractV2026.iterate_prefix hContract n s₀ hInv
    have hArith : n * frameBound + frameBound = (n + 1) * frameBound := by
      rw [Nat.succ_mul]
    cases hPrev with
    | inl hDone =>
      have hLe : n * frameBound ≤ (n + 1) * frameBound := by
        rw [Nat.succ_mul]
        exact Nat.le_add_right _ _
      exact Or.inl (ReachesDoneWithinV2026.mono hLe hDone)
    | inr hPrefix =>
      let ⟨k, s₁, hMin, hk, hSteps, hInv₁, _⟩ := hPrefix
      cases hContract s₁ hInv₁ with
      | inl hDoneNext =>
        have hTotal :
            ReachesDoneWithinV2026 body post (k + frameBound) s₀ :=
          reachesDoneWithinV2026_of_stepsTo hSteps hDoneNext
        have hLe : k + frameBound ≤ (n + 1) * frameBound := by
          rw [← hArith]
          exact Nat.add_le_add_right hk frameBound
        exact Or.inl (ReachesDoneWithinV2026.mono hLe hTotal)
      | inr hTick =>
        let ⟨kTick, s₂, hkMin, hkMax, hStepsTick, hInv₂, hYield₂⟩ := hTick
        refine Or.inr ⟨k + kTick, s₂, ?_, ?_,
          StepsToV2026.trans hSteps hStepsTick, hInv₂, fun _ => hYield₂⟩
        · exact Nat.add_le_add hMin hkMin
        · rw [← hArith]
          exact Nat.add_le_add hk hkMax

/-! ## Part IV: Tight-Budget & Non-Vacuity Refutation Lemmas -/

/-- Divergence (`DivergesV2026 body s`) refutes `ReachesDoneWithinV2026` at
every finite step budget and postcondition. -/
theorem not_reachesDoneWithinV2026_of_divergesV2026 {body : CapturedMir}
    {s : MachineState} (hDiv : DivergesV2026 body s)
    (bound : Nat) (post : MirOutcome → Prop) :
    ¬ ReachesDoneWithinV2026 body post bound s :=
  fun hReach => not_divergesV2026_of_reachesDoneWithinV2026 hReach hDiv

/-- Infinite `.step` traces refute `ReachesDoneWithinV2026` at every budget. -/
theorem not_reachesDoneWithinV2026_of_infinite_trace {body : CapturedMir}
    {post : MirOutcome → Prop} (trace : Nat → MachineState)
    (hSteps : ∀ n : Nat, v2026Step body (trace n) = .step (trace (n + 1)))
    (bound : Nat) :
    ¬ ReachesDoneWithinV2026 body post bound (trace 0) :=
  not_reachesDoneWithinV2026_of_divergesV2026 ⟨trace, rfl, hSteps⟩ bound post

/-- Whole-function divergence refutes `ExecWithinStepsV2026` at every budget. -/
theorem not_execWithinStepsV2026_of_divergesV2026 {body : CapturedMir}
    {args : List Value} {callees : List CapturedMir}
    (hDiv : DivergesV2026 body (initMachineStateWithCallees body args callees))
    (post : MirOutcome → Prop) (bound : Nat) :
    ¬ ExecWithinStepsV2026 body args callees post bound :=
  not_reachesDoneWithinV2026_of_divergesV2026 hDiv bound post

/-- Any `bound ≤ k` is strictly insufficient when deterministic `v2026Step`
execution takes `k` `.step` transitions via `StepsToV2026 body k s s'`. -/
theorem not_reachesDoneWithinV2026_of_stepsTo_ge {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {k bound : Nat} {s s' : MachineState},
      StepsToV2026 body k s s' →
      bound ≤ k →
      ¬ ReachesDoneWithinV2026 body post bound s
  | _, 0, _, _, _, _, h => False.elim h
  | 0, _ + 1, _, _, _, hLe, _ => by cases hLe
  | _ + 1, _ + 1, _, _, hSteps, hLe, hReach => by
    cases hSteps with
    | step hStepS hTail =>
      cases hReach with
      | inl hDone =>
        let ⟨_, hD, _⟩ := hDone
        rw [hStepS] at hD
        cases hD
      | inr hNext =>
        let ⟨_, hS₁, hRest⟩ := hNext
        rw [hStepS] at hS₁
        injection hS₁ with hEq
        subst hEq
        exact not_reachesDoneWithinV2026_of_stepsTo_ge hTail
          (Nat.le_of_succ_le_succ hLe) hRest

/-- If `s` reaches `s'` in `k` `.step` transitions and `s'` steps to
`.done out` where `¬ post out`, then `ReachesDoneWithinV2026 body post bound s`
fails for all `bound`. -/
theorem not_reachesDoneWithinV2026_of_stepsTo_done_fail {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {k bound : Nat} {s s' : MachineState} {out : MirOutcome},
      StepsToV2026 body k s s' →
      v2026Step body s' = .done out →
      ¬ post out →
      ¬ ReachesDoneWithinV2026 body post bound s
  | _, 0, _, _, _, _, _, _, h => False.elim h
  | 0, _ + 1, _, _, _, hSteps, hDoneEnd, hNotPost, hReach => by
    cases hSteps with
    | refl _ =>
      cases hReach with
      | inl hD =>
        let ⟨_, hD', hP⟩ := hD
        rw [hDoneEnd] at hD'
        injection hD' with hEq
        subst hEq
        exact hNotPost hP
      | inr hS =>
        let ⟨_, hS', _⟩ := hS
        rw [hDoneEnd] at hS'
        cases hS'
  | _ + 1, _ + 1, _, _, _, hSteps, hDoneEnd, hNotPost, hReach => by
    cases hSteps with
    | step hStepS hTail =>
      cases hReach with
      | inl hD =>
        let ⟨_, hD', _⟩ := hD
        rw [hStepS] at hD'
        cases hD'
      | inr hNext =>
        let ⟨_, hS₁, hRest⟩ := hNext
        rw [hStepS] at hS₁
        injection hS₁ with hEq
        subst hEq
        exact not_reachesDoneWithinV2026_of_stepsTo_done_fail hTail hDoneEnd
          hNotPost hRest

/-- If `s` reaches `s'` in `k` `.step` transitions and `s'` faults, then
`ReachesDoneWithinV2026 body post bound s` fails for all `bound`. -/
theorem not_reachesDoneWithinV2026_of_stepsTo_fault {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {k bound : Nat} {s s' : MachineState} {f : V2026StepFault},
      StepsToV2026 body k s s' →
      v2026Step body s' = .fault f →
      ¬ ReachesDoneWithinV2026 body post bound s
  | _, 0, _, _, _, _, _, h => False.elim h
  | 0, _ + 1, _, _, _, hSteps, hFault, hReach => by
    cases hSteps with
    | refl _ =>
      cases hReach with
      | inl hD =>
        let ⟨_, hD', _⟩ := hD
        rw [hFault] at hD'
        cases hD'
      | inr hS =>
        let ⟨_, hS', _⟩ := hS
        rw [hFault] at hS'
        cases hS'
  | _ + 1, _ + 1, _, _, _, hSteps, hFault, hReach => by
    cases hSteps with
    | step hStepS hTail =>
      cases hReach with
      | inl hD =>
        let ⟨_, hD', _⟩ := hD
        rw [hStepS] at hD'
        cases hD'
      | inr hNext =>
        let ⟨_, hS₁, hRest⟩ := hNext
        rw [hStepS] at hS₁
        injection hS₁ with hEq
        subst hEq
        exact not_reachesDoneWithinV2026_of_stepsTo_fault hTail hFault hRest

/-! ## Part V: Concrete `V2026_06_01` Tight-Budget & Refutation Canaries -/

/-- Minimal 1-block `CapturedMir` whose `bb0` faults immediately with
`TerminatorKind.unreachable` (UB). -/
def canaryFaultingMirBody : CapturedMir :=
  { defPath := "Anneal::StepBound::canaryFaulting"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := [{ mutability := .mut, ty := u32Ty, debugName := some "_0" }]
    basicBlocks :=
      [ { statements := []
          terminator := { kind := .unreachable, span := "StepBoundV2026.lean:fault:bb0" }
          isCleanup := false } ]
    fnAbi :=
      { args := []
        ret := { layout := u32Layout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts :=
      { pointerBits := 64
        isLittleEndian := true
        entries := [u32Layout] }
    allocations := [] }

/-- Concrete tight-budget & refutation canary over real `CapturedMir` bodies:
1. `branchingTracePipelineBody` (with live `switchInt` observation emission)
   takes exactly `3` `.step` transitions plus `1` `.done` transition:
   succeeds at `bound = 4`, is refuted at `bound = 3` (under-budget), and is
   refuted for a wrong postcondition at every `bound`.
2. `canaryFaultingMirBody` (`.unreachable`) is refuted at every `bound`.
3. `canaryDivergingMirBody` (`goto 0`) is refuted at every `bound`. -/
theorem canary_stepBoundV2026_tight_and_refutations (bound : Nat) :
    let s0 := initMachineState branchingTracePipelineBody
      [.scalar { bits := 9, sizeBytes := 4 }]
    let okPost : MirOutcome → Prop :=
      fun out => out = .normal
        (.scalar { bits := 9, sizeBytes := 4 }, s0.memory)
    let badPost : MirOutcome → Prop :=
      fun out => out = .normal
        (.scalar { bits := 10, sizeBytes := 4 }, s0.memory)
    ReachesDoneWithinV2026 branchingTracePipelineBody okPost 4 s0 ∧
    ¬ ReachesDoneWithinV2026 branchingTracePipelineBody okPost 3 s0 ∧
    ¬ ReachesDoneWithinV2026 branchingTracePipelineBody badPost bound s0 ∧
    ¬ ReachesDoneWithinV2026 canaryFaultingMirBody (fun _ => True) bound
        (initMachineState canaryFaultingMirBody []) ∧
    ¬ ReachesDoneWithinV2026 canaryDivergingMirBody (fun _ => True) bound
        (initMachineState canaryDivergingMirBody []) := by
  dsimp only
  let s0 := initMachineState branchingTracePipelineBody
    [.scalar { bits := 9, sizeBytes := 4 }]
  let okPost : MirOutcome → Prop :=
    fun out => out = .normal
      (.scalar { bits := 9, sizeBytes := 4 }, s0.memory)
  let badPost : MirOutcome → Prop :=
    fun out => out = .normal
      (.scalar { bits := 10, sizeBytes := 4 }, s0.memory)
  have hOk : ReachesDoneWithinV2026 branchingTracePipelineBody okPost 4 s0 :=
    reachesDoneWithinV2026_iff_execStepOutcome.mpr rfl
  let s1 := branchingTraceMidState 9 s0.memory
  let s2 : MachineState :=
    { frame :=
        { blockIdx := 1
          stmtIdx := 1
          locals := [.init (.scalar { bits := 9, sizeBytes := 4 }), .uninit] }
      memory := s0.memory }
  let s3 : MachineState :=
    { frame :=
        { blockIdx := 2
          stmtIdx := 0
          locals := [.init (.scalar { bits := 9, sizeBytes := 4 }), .uninit] }
      memory := s0.memory }
  have hSteps3 : StepsToV2026 branchingTracePipelineBody 3 s0 s3 :=
    StepsToV2026.step (s' := s1) rfl
      (StepsToV2026.step (s' := s2) rfl
        (StepsToV2026.single (s' := s3) rfl))
  have hDone3 :
      v2026Step branchingTracePipelineBody s3 =
        .done (.normal (.scalar { bits := 9, sizeBytes := 4 }, s0.memory)) :=
    rfl
  have hNot3 : ¬ ReachesDoneWithinV2026 branchingTracePipelineBody okPost 3 s0 :=
    not_reachesDoneWithinV2026_of_stepsTo_ge hSteps3 (Nat.le_refl 3)
  have hBadPost : ¬ badPost (.normal (.scalar { bits := 9, sizeBytes := 4 }, s0.memory)) := by
    intro hEq
    cases hEq
  have hNotBad :
      ¬ ReachesDoneWithinV2026 branchingTracePipelineBody badPost bound s0 :=
    not_reachesDoneWithinV2026_of_stepsTo_done_fail hSteps3 hDone3 hBadPost
  have hFault :
      v2026Step canaryFaultingMirBody
        (initMachineState canaryFaultingMirBody []) = .fault (.fail .ub) :=
    rfl
  have hNotFault :
      ¬ ReachesDoneWithinV2026 canaryFaultingMirBody (fun _ => True) bound
        (initMachineState canaryFaultingMirBody []) :=
    not_reachesDoneWithinV2026_of_stepsTo_fault (StepsToV2026.refl _) hFault
  have hDiv := (canary_v2026_diverging_witness 0 (fun _ => True)).1
  have hNotDiv :
      ¬ ReachesDoneWithinV2026 canaryDivergingMirBody (fun _ => True) bound
        (initMachineState canaryDivergingMirBody []) :=
    not_reachesDoneWithinV2026_of_divergesV2026 hDiv bound (fun _ => True)
  exact ⟨hOk, hNot3, hNotBad, hNotFault, hNotDiv⟩

end Anneal.StepBound
