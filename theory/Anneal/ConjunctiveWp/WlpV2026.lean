-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.Framework.StepWp
import Anneal.Firewall
import Anneal.MirFuelFree
import Anneal.PureMirExec
import Anneal.ParametricCore.V2026Bridge
import Anneal.ParametricCore.StageCut
import Trusted

/-!
# `V2026_06_01` Conjunctive WP, Anti-Monotonic `wlp`, Divergence & Doubling Fuel

Converges `#4239` (`Anneal.ConjunctiveWp.Wlp`) directly onto unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics` (`stepMirFn`, `stepMirState`,
`MirStepNode`, `mirTree`, `mirCallTree`, `MirNoUBTree`, `VerificationResult`,
`StatefulVerificationResult`) via the MIR-agnostic `Anneal.Framework.StepWp`
unification seam:

1. **Lossless `V2026_06_01` Adapter (`V2026StepFault`, `ofV2026MirStepNode`,
   `v2026Step`):** Maps every `MirStepNode` constructor — including silent
   `.tau (.running / .halted / .faulted)`, root `.ret`, fault `.vis (.inl _)`,
   observable `.vis (.inr (.inl (.emit _))) k` (such as `switchInt` branch
   events), and external calls `.vis (.inr (.inr (.call _)))` — into
   `Framework.StepWp.StepResult MachineState MirOutcome V2026StepFault`, with
   exact correspondence lemmas against `stepMirFn`, `stepMirState`,
   `PureMirExec.mirStep`, `ParametricCore.V2026Bridge.mirDetStep`, and
   `ParametricCore.V2026Bridge.mirNoCallStep`, exact one-step `wpMirSym`
   unfolding rules, and adequacy bridges into `MirWpConverges`, `MirNoUBTree`,
   `ReachesRet`, `Productive`, `VerificationResult`,
   `StatefulVerificationResult`, and `TotalVerificationResult`. The adapter is
   proved *exactly complete* for call-free semantics
   (`v2026Exec_of_wpMirNoCallSym`, `mirNoCallWpConverges_iff_exists_v2026Exec`,
   `wpStateOk_mirNoCallDet_iff_exists_v2026Exec`), and `MirNoUBTree`,
   `ReachesRet`, `Productive`, `VerificationResult`, and
   `StatefulVerificationResult` adequacy are all proved directly against
   `Trusted.ITree.Reaches` / `TreeSafe` using only `{propext, Quot.sound}` —
   zero `Classical.choice`.
2. **Deterministic `execWlp*`, Anti-Monotonicity, & Asymmetric Two-Pass Rules:**
   `wlpOutcomeV2026`, `wlpStateV2026`, `wlpProgV2026`, `wlpProgStrictV2026`,
   `execWlpOutcomeV2026`, `execWlpStateV2026`, `execWlpProgV2026`,
   `execWlpProgStrictV2026`, fuel anti-monotonicity (`wlpOutcomeV2026_fuel_anti`),
   and asymmetric-fuel splitting (`fuelSafe ≤ fuelWlp`) into `MirWpConverges`,
   `MirNoUBTree`, and `VerificationResult`.
3. **Minimum-Budget Conjunctive Composition (`compNatMin`):** Combines
   independent `wlpOutcomeV2026`, `wpOutcomeV2026`, `execStepOutcome`,
   `wpProgV2026`, and `wpUntil` derivations at budgets `n₁`, `n₂` into
   `compNatMin n₁ n₂`.
4. **Productive State-Transition Divergence Certificates (`DivergesV2026`,
   `ProductiveStepWitness`, `divergesV2026_of_productiveWitness`):** Constructive
   `@Nat.rec` infinite `.step` trace witnesses proved to refute both
   `execStepOutcome` and `MirWpConverges` for every finite fuel budget.
5. **Logarithmic Binary-Doubling Fuel (`pow2Fuel`, `wpPow2Cont`,
   `execPow2Cont`):** Composes up to `2^k` `V2026_06_01` steps in recursion
   depth `k` with $O(k)$ invariant lifting (`wpPow2Cont_inv`), exact equivalence
   to `execStepOutcome` at `pow2Fuel k`, and direct adequacy into
   `MirWpConverges`, `MirNoUBTree`, and `VerificationResult`.
-/

namespace Anneal.ConjunctiveWp

open Trusted.Effect
open Trusted.ITree
open Trusted.VerificationResult
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.Framework.StepWp

/-! ## Part I: Lossless `V2026_06_01` Adapter & Soundness Bridges -/

/-- Lossless fault classification for single-step `V2026_06_01` MIR execution. -/
inductive V2026StepFault where
  | fail (kind : FailureKind)
  | extCall (req : MirCallReq)
  | stuck

/-- Lossless translation from a trusted `V2026_06_01` `MirStepNode` into
`Framework.StepWp.StepResult MachineState MirOutcome V2026StepFault`.
Handles both silent `.tau` transitions and observable `MirObsE` emissions
(`.vis (.inr (.inl (.emit _))) k`). -/
def ofV2026MirStepNode (n : MirStepNode) :
    StepResult MachineState MirOutcome V2026StepFault :=
  match n with
  | .tau (.running s') => .step s'
  | .tau (.halted out) => .done out
  | .tau (.faulted fk) => .fault (.fail fk)
  | .ret out => .done out
  | .vis (.inl (.fail fk)) _ => .fault (.fail fk)
  | .vis (.inr (.inl (.emit _))) k =>
    match k PUnit.unit with
    | .running s' => .step s'
    | .halted out => .done out
    | .faulted fk => .fault (.fail fk)
  | .vis (.inr (.inr (.call req))) _ => .fault (.extCall req)

/-- Single-step `V2026_06_01` transition function over unmodified trusted
`stepMirFn`. -/
def v2026Step (body : CapturedMir) (s : MachineState) :
    StepResult MachineState MirOutcome V2026StepFault :=
  ofV2026MirStepNode (stepMirFn body s)

/-- `v2026Step` agrees definitionally with `ofV2026MirStepNode` applied to
`stepMirState body (.running s)`. -/
theorem v2026Step_eq_ofV2026MirStepNode_stepMirState
    (body : CapturedMir) (s : MachineState) :
    v2026Step body s = ofV2026MirStepNode (stepMirState body (.running s)) :=
  rfl

/-- `ofV2026MirStepNode` maps `MirStepNode.emitStep obs s'` to `.step s'` for
both `.silent` and `.event tag`. -/
theorem ofV2026MirStepNode_emitStep (obs : MirObs) (s' : MachineState) :
    ofV2026MirStepNode (MirStepNode.emitStep obs s') = .step s' := by
  cases obs <;> rfl

/-- Exact characterization of `.step s'` under `v2026Step`: either a silent
`.tau (.running s')` step or an observable `.vis (.inr (.inl (.emit obs))) k`
step whose continuation yields `.running s'`. -/
theorem v2026Step_step_iff {body : CapturedMir} {s s' : MachineState} :
    v2026Step body s = .step s' ↔
      stepMirFn body s = .tau (.running s') ∨
      ∃ obs k, stepMirFn body s = .vis (.inr (.inl (.emit obs))) k ∧
        k PUnit.unit = .running s' := by
  unfold v2026Step ofV2026MirStepNode
  cases h : stepMirFn body s with
  | ret out =>
    constructor
    · intro he; cases he
    · intro hDisj
      cases hDisj with
      | inl hT => cases hT
      | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
  | tau st =>
    cases st with
    | running s₁ =>
      constructor
      · intro he; injection he with hEq; subst hEq; exact Or.inl rfl
      · intro hDisj
        cases hDisj with
        | inl hT => injection hT with hR; injection hR with hEq; subst hEq; rfl
        | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | halted out =>
      constructor
      · intro he; cases he
      · intro hDisj
        cases hDisj with
        | inl hT => cases hT
        | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | faulted fk =>
      constructor
      · intro he; cases he
      · intro hDisj
        cases hDisj with
        | inl hT => cases hT
        | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail fk =>
        constructor
        · intro he; cases he
        · intro hDisj
          cases hDisj with
          | inl hT => cases hT
          | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | inr i2 =>
      cases i2 with
      | inl e =>
        cases e with
        | emit obs =>
          dsimp only
          cases hk : k PUnit.unit with
          | running s₁ =>
            constructor
            · intro he
              injection he with hEq
              subst hEq
              exact Or.inr ⟨obs, k, rfl, hk⟩
            · intro hDisj
              cases hDisj with
              | inl hT => cases hT
              | inr hV =>
                let ⟨obs', k', hv, hk'⟩ := hV
                cases hv
                rw [hk] at hk'
                injection hk' with hEq
                subst hEq
                rfl
          | halted out =>
            constructor
            · intro he; cases he
            · intro hDisj
              cases hDisj with
              | inl hT => cases hT
              | inr hV =>
                let ⟨_, _, hv, hk'⟩ := hV
                cases hv
                rw [hk] at hk'
                cases hk'
          | faulted fk =>
            constructor
            · intro he; cases he
            · intro hDisj
              cases hDisj with
              | inl hT => cases hT
              | inr hV =>
                let ⟨_, _, hv, hk'⟩ := hV
                cases hv
                rw [hk] at hk'
                cases hk'
      | inr c =>
        cases c with
        | call req =>
          constructor
          · intro he; cases he
          · intro hDisj
            cases hDisj with
            | inl hT => cases hT
            | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv

/-- Exact characterization of `.done out` under `v2026Step`. -/
theorem v2026Step_done_iff {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} :
    v2026Step body s = .done out ↔
      stepMirFn body s = .ret out ∨
      stepMirFn body s = .tau (.halted out) ∨
      ∃ obs k, stepMirFn body s = .vis (.inr (.inl (.emit obs))) k ∧
        k PUnit.unit = .halted out := by
  unfold v2026Step ofV2026MirStepNode
  cases h : stepMirFn body s with
  | ret o =>
    constructor
    · intro he; injection he with hEq; subst hEq; exact Or.inl rfl
    · intro hD
      cases hD with
      | inl hR => injection hR with hEq; subst hEq; rfl
      | inr hRest =>
        cases hRest with
        | inl hT => cases hT
        | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
  | tau st =>
    cases st with
    | running _ =>
      constructor
      · intro he; cases he
      · intro hD
        cases hD with
        | inl hR => cases hR
        | inr hRest =>
          cases hRest with
          | inl hT => cases hT
          | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | halted o =>
      constructor
      · intro he; injection he with hEq; subst hEq; exact Or.inr (Or.inl rfl)
      · intro hD
        cases hD with
        | inl hR => cases hR
        | inr hRest =>
          cases hRest with
          | inl hT => injection hT with hH; injection hH with hEq; subst hEq; rfl
          | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | faulted _ =>
      constructor
      · intro he; cases he
      · intro hD
        cases hD with
        | inl hR => cases hR
        | inr hRest =>
          cases hRest with
          | inl hT => cases hT
          | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail _ =>
        constructor
        · intro he; cases he
        · intro hD
          cases hD with
          | inl hR => cases hR
          | inr hRest =>
            cases hRest with
            | inl hT => cases hT
            | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | inr i2 =>
      cases i2 with
      | inl e =>
        cases e with
        | emit obs =>
          dsimp only
          cases hk : k PUnit.unit with
          | running _ =>
            constructor
            · intro he; cases he
            · intro hD
              cases hD with
              | inl hR => cases hR
              | inr hRest =>
                cases hRest with
                | inl hT => cases hT
                | inr hV =>
                  let ⟨_, _, hv, hk'⟩ := hV
                  cases hv
                  rw [hk] at hk'
                  cases hk'
          | halted o =>
            constructor
            · intro he
              injection he with hEq
              subst hEq
              exact Or.inr (Or.inr ⟨obs, k, rfl, hk⟩)
            · intro hD
              cases hD with
              | inl hR => cases hR
              | inr hRest =>
                cases hRest with
                | inl hT => cases hT
                | inr hV =>
                  let ⟨_, _, hv, hk'⟩ := hV
                  cases hv
                  rw [hk] at hk'
                  injection hk' with hEq
                  subst hEq
                  rfl
          | faulted _ =>
            constructor
            · intro he; cases he
            · intro hD
              cases hD with
              | inl hR => cases hR
              | inr hRest =>
                cases hRest with
                | inl hT => cases hT
                | inr hV =>
                  let ⟨_, _, hv, hk'⟩ := hV
                  cases hv
                  rw [hk] at hk'
                  cases hk'
      | inr c =>
        cases c with
        | call _ =>
          constructor
          · intro he; cases he
          · intro hD
            cases hD with
            | inl hR => cases hR
            | inr hRest =>
              cases hRest with
              | inl hT => cases hT
              | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv

/-- Exact characterization of `.fault (.fail fk)` under `v2026Step`. -/
theorem v2026Step_fault_fail_iff {body : CapturedMir} {s : MachineState}
    {fk : FailureKind} :
    v2026Step body s = .fault (.fail fk) ↔
      stepMirFn body s = .tau (.faulted fk) ∨
      (∃ k, stepMirFn body s = .vis (.inl (.fail fk)) k) ∨
      (∃ obs k, stepMirFn body s = .vis (.inr (.inl (.emit obs))) k ∧
        k PUnit.unit = .faulted fk) := by
  unfold v2026Step ofV2026MirStepNode
  cases h : stepMirFn body s with
  | ret _ =>
    constructor
    · intro he; cases he
    · intro hD
      cases hD with
      | inl hT => cases hT
      | inr hRest =>
        cases hRest with
        | inl hF => let ⟨_, hf⟩ := hF; cases hf
        | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
  | tau st =>
    cases st with
    | running _ =>
      constructor
      · intro he; cases he
      · intro hD
        cases hD with
        | inl hT => cases hT
        | inr hRest =>
          cases hRest with
          | inl hF => let ⟨_, hf⟩ := hF; cases hf
          | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | halted _ =>
      constructor
      · intro he; cases he
      · intro hD
        cases hD with
        | inl hT => cases hT
        | inr hRest =>
          cases hRest with
          | inl hF => let ⟨_, hf⟩ := hF; cases hf
          | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | faulted fk' =>
      constructor
      · intro he; injection he with hF; injection hF with hEq; subst hEq; exact Or.inl rfl
      · intro hD
        cases hD with
        | inl hT => injection hT with hF; injection hF with hEq; subst hEq; rfl
        | inr hRest =>
          cases hRest with
          | inl hF => let ⟨_, hf⟩ := hF; cases hf
          | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
  | vis i k =>
    cases i with
    | inl f =>
      cases f with
      | fail fk' =>
        constructor
        · intro he; injection he with hF; injection hF with hEq; subst hEq
          exact Or.inr (Or.inl ⟨k, rfl⟩)
        · intro hD
          cases hD with
          | inl hT => cases hT
          | inr hRest =>
            cases hRest with
            | inl hF =>
              let ⟨_, hf⟩ := hF
              cases hf
              rfl
            | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv
    | inr i2 =>
      cases i2 with
      | inl e =>
        cases e with
        | emit obs =>
          dsimp only
          cases hk : k PUnit.unit with
          | running _ =>
            constructor
            · intro he; cases he
            · intro hD
              cases hD with
              | inl hT => cases hT
              | inr hRest =>
                cases hRest with
                | inl hF => let ⟨_, hf⟩ := hF; cases hf
                | inr hV =>
                  let ⟨_, _, hv, hk'⟩ := hV
                  cases hv; rw [hk] at hk'; cases hk'
          | halted _ =>
            constructor
            · intro he; cases he
            · intro hD
              cases hD with
              | inl hT => cases hT
              | inr hRest =>
                cases hRest with
                | inl hF => let ⟨_, hf⟩ := hF; cases hf
                | inr hV =>
                  let ⟨_, _, hv, hk'⟩ := hV
                  cases hv; rw [hk] at hk'; cases hk'
          | faulted fk' =>
            constructor
            · intro he
              injection he with hF; injection hF with hEq; subst hEq
              exact Or.inr (Or.inr ⟨obs, k, rfl, hk⟩)
            · intro hD
              cases hD with
              | inl hT => cases hT
              | inr hRest =>
                cases hRest with
                | inl hF => let ⟨_, hf⟩ := hF; cases hf
                | inr hV =>
                  let ⟨_, _, hv, hk'⟩ := hV
                  cases hv; rw [hk] at hk'
                  injection hk' with hEq; subst hEq; rfl
      | inr c =>
        cases c with
        | call _ =>
          constructor
          · intro he; cases he
          · intro hD
            cases hD with
            | inl hT => cases hT
            | inr hRest =>
              cases hRest with
              | inl hF => let ⟨_, hf⟩ := hF; cases hf
              | inr hV => let ⟨_, _, hv, _⟩ := hV; cases hv

/-- Exact characterization of `.fault (.extCall req)` under `v2026Step`. -/
theorem v2026Step_fault_extCall_iff {body : CapturedMir} {s : MachineState}
    {req : MirCallReq} :
    v2026Step body s = .fault (.extCall req) ↔
      ∃ k, stepMirFn body s = .vis (.inr (.inr (.call req))) k := by
  unfold v2026Step ofV2026MirStepNode
  cases h : stepMirFn body s with
  | ret _ =>
    constructor
    · intro he; cases he
    · intro ⟨_, hv⟩; cases hv
  | tau st =>
    cases st <;>
      exact ⟨(fun he => by cases he), (fun ⟨_, hv⟩ => by cases hv)⟩
  | vis i k =>
    cases i with
    | inl f =>
      cases f
      exact ⟨(fun he => by cases he), (fun ⟨_, hv⟩ => by cases hv)⟩
    | inr i2 =>
      cases i2 with
      | inl e =>
        cases e
        dsimp only
        cases k PUnit.unit <;>
          exact ⟨(fun he => by cases he), (fun ⟨_, hv⟩ => by cases hv)⟩
      | inr c =>
        cases c with
        | call req' =>
          constructor
          · intro he
            injection he with hF
            injection hF with hEq
            subst hEq
            exact ⟨k, rfl⟩
          · intro ⟨_, hv⟩
            cases hv
            rfl

/-- `v2026Step` never produces `.fault .stuck` because `MirStepNode` is
exhaustively classified into `.step`, `.done`, `.fault (.fail _)`, and
`.fault (.extCall _)`. -/
theorem v2026Step_never_stuck (body : CapturedMir) (s : MachineState) :
    v2026Step body s ≠ .fault .stuck := by
  unfold v2026Step ofV2026MirStepNode
  cases stepMirFn body s with
  | ret _ => intro h; cases h
  | tau st => cases st <;> (intro h; cases h)
  | vis i k =>
    cases i with
    | inl f => cases f; intro h; cases h
    | inr i2 =>
      cases i2 with
      | inl e =>
        cases e
        dsimp only
        cases k PUnit.unit <;> (intro h; cases h)
      | inr c => cases c; intro h; cases h

/-- Exact `.step` correspondence between `v2026Step` and
`Anneal.PureMirExec.mirStep`. -/
theorem v2026Step_step_iff_mirStep_cont {body : CapturedMir}
    {s s' : MachineState} :
    v2026Step body s = .step s' ↔
      Anneal.PureMirExec.mirStep body s = .cont s' := by
  rw [v2026Step_step_iff]
  constructor
  · intro h
    unfold Anneal.PureMirExec.mirStep
    cases h with
    | inl hTau => rw [hTau]
    | inr hVis =>
      let ⟨obs, k, hv, hk⟩ := hVis
      rw [hv]
      dsimp only
      rw [hk]
  · exact Anneal.PureMirExec.stepMirFn_of_mirStep_cont

/-- Exact `.step` correspondence between `v2026Step` and
`Anneal.ParametricCore.V2026Bridge.mirDetStep`. -/
theorem v2026Step_step_iff_mirDetStep_step {body : CapturedMir}
    {s s' : MachineState} :
    v2026Step body s = .step s' ↔
      Anneal.ParametricCore.V2026Bridge.mirDetStep body s = .step s' :=
  Iff.trans v2026Step_step_iff_mirStep_cont
    Anneal.ParametricCore.V2026Bridge.mirDetStep_step_iff.symm

/-- Every `.done` transition of `PureMirExec.mirStep` is a `.done` transition
of `v2026Step`. -/
theorem v2026Step_done_of_mirStep_done {body : CapturedMir}
    {s : MachineState} {out : MirOutcome}
    (h : Anneal.PureMirExec.mirStep body s = .done out) :
    v2026Step body s = .done out :=
  v2026Step_done_iff.mpr
    (Or.inl (Anneal.PureMirExec.stepMirFn_of_mirStep_done h))

/-- Every `.done` transition of `ParametricCore.V2026Bridge.mirDetStep` is a
`.done` transition of `v2026Step`. -/
theorem v2026Step_done_of_mirDetStep_done {body : CapturedMir}
    {s : MachineState} {out : MirOutcome}
    (h : Anneal.ParametricCore.V2026Bridge.mirDetStep body s = .done out) :
    v2026Step body s = .done out :=
  v2026Step_done_of_mirStep_done
    (Anneal.ParametricCore.V2026Bridge.mirDetStep_done_iff.mp h)

/-- Every `.fault` transition of `v2026Step` maps to `.fault` in
`PureMirExec.mirStep`. -/
theorem mirStep_fault_of_v2026Step_fault {body : CapturedMir}
    {s : MachineState} {fk : V2026StepFault}
    (h : v2026Step body s = .fault fk) :
    Anneal.PureMirExec.mirStep body s = .fault := by
  unfold v2026Step ofV2026MirStepNode at h
  unfold Anneal.PureMirExec.mirStep
  cases hStep : stepMirFn body s with
  | ret _ => rw [hStep] at h; cases h
  | tau st =>
    rw [hStep] at h
    cases st with
    | running _ => cases h
    | halted _ => cases h
    | faulted _ => rfl
  | vis i k =>
    rw [hStep] at h
    cases i with
    | inl f => cases f; rfl
    | inr i2 =>
      cases i2 with
      | inl e =>
        cases e
        dsimp only at h ⊢
        cases hk : k PUnit.unit with
        | running _ => rw [hk] at h; cases h
        | halted _ => rfl
        | faulted _ => rfl
      | inr c => cases c; rfl

/-- Every `.fault` transition of `v2026Step` maps to `.fault ()` in
`ParametricCore.V2026Bridge.mirDetStep`. -/
theorem mirDetStep_fault_of_v2026Step_fault {body : CapturedMir}
    {s : MachineState} {fk : V2026StepFault}
    (h : v2026Step body s = .fault fk) :
    Anneal.ParametricCore.V2026Bridge.mirDetStep body s = .fault () :=
  Anneal.ParametricCore.V2026Bridge.toStepOutcome_fault_iff.mpr
    (mirStep_fault_of_v2026Step_fault h)

/-- Exact `.step` correspondence between `v2026Step` and
`ParametricCore.V2026Bridge.mirNoCallStep`. -/
theorem v2026Step_step_iff_mirNoCallStep_step {body : CapturedMir}
    {s s' : MachineState} :
    v2026Step body s = .step s' ↔
      Anneal.ParametricCore.V2026Bridge.mirNoCallStep body s = .step s' := by
  unfold v2026Step ofV2026MirStepNode
    Anneal.ParametricCore.V2026Bridge.mirNoCallStep
  dsimp only [stepMirState]
  cases stepMirFn body s with
  | ret _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | tau st =>
    cases st with
    | running s₁ =>
      exact ⟨(fun h => by injection h with hEq; rw [hEq]),
             (fun h => by injection h with hEq; rw [hEq])⟩
    | halted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | faulted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | vis i k =>
    rcases i with f | (e | c)
    · cases f; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    · cases e
      dsimp only
      cases k PUnit.unit with
      | running s₁ =>
        exact ⟨(fun h => by injection h with hEq; rw [hEq]),
               (fun h => by injection h with hEq; rw [hEq])⟩
      | halted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | faulted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    · cases c; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-- Exact `.done` correspondence between `v2026Step` and
`ParametricCore.V2026Bridge.mirNoCallStep` (two-way, because both handle
`.ret`, `.tau (.halted _)`, and observable `.vis _ (.halted _)`). -/
theorem v2026Step_done_iff_mirNoCallStep_done {body : CapturedMir}
    {s : MachineState} {out : MirOutcome} :
    v2026Step body s = .done out ↔
      Anneal.ParametricCore.V2026Bridge.mirNoCallStep body s = .done out := by
  unfold v2026Step ofV2026MirStepNode
    Anneal.ParametricCore.V2026Bridge.mirNoCallStep
  dsimp only [stepMirState]
  cases stepMirFn body s with
  | ret o =>
    exact ⟨(fun h => by injection h with hEq; rw [hEq]),
           (fun h => by injection h with hEq; rw [hEq])⟩
  | tau st =>
    cases st with
    | running _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | halted o =>
      exact ⟨(fun h => by injection h with hEq; rw [hEq]),
             (fun h => by injection h with hEq; rw [hEq])⟩
    | faulted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | vis i k =>
    rcases i with f | (e | c)
    · cases f; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    · cases e
      dsimp only
      cases k PUnit.unit with
      | running _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | halted o =>
        exact ⟨(fun h => by injection h with hEq; rw [hEq]),
               (fun h => by injection h with hEq; rw [hEq])⟩
      | faulted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    · cases c; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-- Exact `.fault (.fail fk)` correspondence between `v2026Step` and
`ParametricCore.V2026Bridge.mirNoCallStep`. -/
theorem v2026Step_fault_fail_iff_mirNoCallStep_fail {body : CapturedMir}
    {s : MachineState} {fk : FailureKind} :
    v2026Step body s = .fault (.fail fk) ↔
      Anneal.ParametricCore.V2026Bridge.mirNoCallStep body s = .fault (.fail fk) := by
  unfold v2026Step ofV2026MirStepNode
    Anneal.ParametricCore.V2026Bridge.mirNoCallStep
  dsimp only [stepMirState]
  cases stepMirFn body s with
  | ret _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | tau st =>
    cases st with
    | running _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | halted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | faulted fk' =>
      exact ⟨(fun h => by injection h with hf; injection hf with hEq; rw [hEq]),
             (fun h => by injection h with hf; injection hf with hEq; rw [hEq])⟩
  | vis i k =>
    rcases i with f | (e | c)
    · cases f with
      | fail fk' =>
        exact ⟨(fun h => by injection h with hf; injection hf with hEq; rw [hEq]),
               (fun h => by injection h with hf; injection hf with hEq; rw [hEq])⟩
    · cases e
      dsimp only
      cases k PUnit.unit with
      | running _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | halted _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | faulted fk' =>
        exact ⟨(fun h => by injection h with hf; injection hf with hEq; rw [hEq]),
               (fun h => by injection h with hf; injection hf with hEq; rw [hEq])⟩
    · cases c; exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-- Exact external-call fault correspondence between `v2026Step` and
`ParametricCore.V2026Bridge.mirNoCallStep`. -/
theorem v2026Step_fault_extCall_iff_mirNoCallStep_extCall {body : CapturedMir}
    {s : MachineState} :
    (∃ req, v2026Step body s = .fault (.extCall req)) ↔
      Anneal.ParametricCore.V2026Bridge.mirNoCallStep body s = .fault .extCall := by
  unfold v2026Step ofV2026MirStepNode
    Anneal.ParametricCore.V2026Bridge.mirNoCallStep
  dsimp only [stepMirState]
  cases stepMirFn body s with
  | ret _ => exact ⟨(fun ⟨_, h⟩ => by cases h), (fun h => by cases h)⟩
  | tau st =>
    cases st <;> exact ⟨(fun ⟨_, h⟩ => by cases h), (fun h => by cases h)⟩
  | vis i k =>
    rcases i with f | (e | c)
    · cases f; exact ⟨(fun ⟨_, h⟩ => by cases h), (fun h => by cases h)⟩
    · cases e
      dsimp only
      cases k PUnit.unit <;>
        exact ⟨(fun ⟨_, h⟩ => by cases h), (fun h => by cases h)⟩
    · cases c with
      | call req => exact ⟨fun _ => rfl, fun _ => ⟨req, rfl⟩⟩

/-! ### Exact One-Step `wpMirSym` Unfolding Lemmas (Silent `.tau` & Observable `.vis`) -/

/-- Exact one-step unfolding of `wpMirExecSym` on a `.halted out` state. -/
theorem wpMirExecSym_succ_of_halted {fuel : Nat} {body : CapturedMir}
    {out : MirOutcome} {post : MirOutcome → Prop} :
    wpMirExecSym (fuel + 1) body (.halted out) post ↔ post out :=
  Iff.rfl

/-- Exact one-step unfolding of `wpMirSym` on `.ret out`. -/
theorem wpMirSym_succ_of_ret {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {out : MirOutcome} {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .ret out) :
    wpMirSym (fuel + 1) body s post ↔ post out := by
  constructor
  · intro h
    unfold wpMirSym wpMirExecSym at h
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h
    dsimp only [stepMirState] at h
    rw [hStep] at h
    exact h
  · intro h
    unfold wpMirSym wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    dsimp only [stepMirState]
    rw [hStep]
    exact h

/-- Exact one-step unfolding of `wpMirSym` on silent `.tau (.running s')`. -/
theorem wpMirSym_succ_of_tau_running {fuel : Nat} {body : CapturedMir}
    {s s' : MachineState} {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .tau (.running s')) :
    wpMirSym (fuel + 1) body s post ↔ wpMirSym fuel body s' post := by
  constructor
  · intro h
    unfold wpMirSym wpMirExecSym at h
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h
    dsimp only [stepMirState] at h
    rw [hStep] at h
    exact h
  · intro h
    unfold wpMirSym wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    dsimp only [stepMirState]
    rw [hStep]
    exact h

/-- Exact one-step unfolding of `wpMirSym` on observable
`.vis (.inr (.inl (.emit obs))) k` (covering `switchInt` and `MirObsE`
emissions). -/
theorem wpMirSym_succ_of_vis_emit {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {obs : MirObs} {k : PUnit → MirExecState}
    {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .vis (.inr (.inl (.emit obs))) k) :
    wpMirSym (fuel + 1) body s post ↔
      wpMirExecSym fuel body (k PUnit.unit) post := by
  constructor
  · intro h
    unfold wpMirSym wpMirExecSym at h
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h
    dsimp only [stepMirState] at h
    rw [hStep] at h
    exact h
  · intro h
    unfold wpMirSym wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    dsimp only [stepMirState]
    rw [hStep]
    exact h

/-- Exact one-step unfolding of `wpMirSym` on observable
`.vis (.inr (.inl (.emit obs))) k` continuing to `.running s'`. -/
theorem wpMirSym_succ_of_vis_emit_running {fuel : Nat} {body : CapturedMir}
    {s s' : MachineState} {obs : MirObs} {k : PUnit → MirExecState}
    {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .vis (.inr (.inl (.emit obs))) k)
    (hk : k PUnit.unit = .running s') :
    wpMirSym (fuel + 1) body s post ↔ wpMirSym fuel body s' post := by
  rw [wpMirSym_succ_of_vis_emit hStep, hk]
  exact Iff.rfl

/-- Exact one-step unfolding of `wpMirSym` on `MirStepNode.emitStep obs s'`. -/
theorem wpMirSym_succ_of_emitStep {fuel : Nat} {body : CapturedMir}
    {s s' : MachineState} {obs : MirObs} {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = MirStepNode.emitStep obs s') :
    wpMirSym (fuel + 1) body s post ↔ wpMirSym fuel body s' post := by
  cases obs with
  | silent => exact wpMirSym_succ_of_tau_running hStep
  | event _ => exact wpMirSym_succ_of_vis_emit_running hStep rfl

/-- Exact two-step unfolding of `wpMirSym` on `.tau (.halted out)`. -/
theorem wpMirSym_two_of_tau_halted {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {out : MirOutcome} {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .tau (.halted out)) :
    wpMirSym (fuel + 2) body s post ↔ post out := by
  constructor
  · intro h
    unfold wpMirSym wpMirExecSym at h
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h
    dsimp only [stepMirState] at h
    rw [hStep] at h
    exact wpMirExecSym_succ_of_halted.mp h
  · intro h
    unfold wpMirSym wpMirExecSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    dsimp only [stepMirState]
    rw [hStep]
    exact wpMirExecSym_succ_of_halted.mpr h

/-- Exact two-step unfolding of `wpMirSym` on observable
`.vis (.inr (.inl (.emit obs))) k` halting with `k PUnit.unit = .halted out`. -/
theorem wpMirSym_two_of_vis_emit_halted {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {obs : MirObs} {k : PUnit → MirExecState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (hStep : stepMirFn body s = .vis (.inr (.inl (.emit obs))) k)
    (hk : k PUnit.unit = .halted out) :
    wpMirSym (fuel + 2) body s post ↔ post out := by
  rw [wpMirSym_succ_of_vis_emit hStep, hk, wpMirExecSym_succ_of_halted]

/-- Exact one-step `wpMirSym` unfolding on any `v2026Step body s = .step s'`,
uniformly covering both silent `.tau` and observable `MirObsE` transitions. -/
theorem wpMirSym_succ_of_v2026Step {fuel : Nat} {body : CapturedMir}
    {s s' : MachineState} {post : MirOutcome → Prop}
    (hStep : v2026Step body s = .step s') :
    wpMirSym (fuel + 1) body s post ↔ wpMirSym fuel body s' post := by
  cases v2026Step_step_iff.mp hStep with
  | inl hTau => exact wpMirSym_succ_of_tau_running hTau
  | inr hVis =>
    let ⟨_, _, hv, hk⟩ := hVis
    exact wpMirSym_succ_of_vis_emit_running hv hk

/-! ### Adequacy Bridges into `wpMirSym`, `MirWpConverges`, `MirNoUBTree`, & Certificates -/

/-- Lift any fault-free `execStepOutcome (v2026Step body)` derivation at budget
`fuel` directly into unmodified `wpMirSym (fuel + 1)`. The `+ 1` headroom
uniformly accounts for `.tau (.halted out)` and `.vis ... (.halted out)` taking
one additional coalgebra `.ret` step under `stepMirState`. -/
theorem wpMirSym_of_v2026Exec {body : CapturedMir} {post : MirOutcome → Prop} :
    ∀ {fuel : Nat} {s : MachineState},
      execStepOutcome (v2026Step body) post (fun _ => False) fuel s →
      wpMirSym (fuel + 1) body s post
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    dsimp only [execStepOutcome] at h
    rw [execStepPred_succ_iff] at h
    cases hStep : v2026Step body s with
    | step s' =>
      rw [hStep] at h
      exact (wpMirSym_succ_of_v2026Step hStep).mpr (wpMirSym_of_v2026Exec h)
    | done out =>
      rw [hStep] at h
      cases v2026Step_done_iff.mp hStep with
      | inl hRet => exact (wpMirSym_succ_of_ret hRet).mpr h
      | inr hRest =>
        cases hRest with
        | inl hTauH => exact (wpMirSym_two_of_tau_halted hTauH).mpr h
        | inr hVisH =>
          let ⟨_, _, hv, hk⟩ := hVisH
          exact (wpMirSym_two_of_vis_emit_halted hv hk).mpr h
    | fault _ =>
      rw [hStep] at h
      exact False.elim h

/-- Lift any fault-free `execStepOutcome (v2026Step body)` derivation into
call-free `wpMirNoCallSym (fuel + 1)`. -/
theorem wpMirNoCallSym_of_v2026Exec {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {fuel : Nat} {s : MachineState},
      execStepOutcome (v2026Step body) post (fun _ => False) fuel s →
      wpMirNoCallSym (fuel + 1) body s post
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    dsimp only [execStepOutcome] at h
    rw [execStepPred_succ_iff] at h
    cases hStep : v2026Step body s with
    | step s' =>
      rw [hStep] at h
      have hSub := wpMirNoCallSym_of_v2026Exec h
      unfold wpMirNoCallSym wpMirExecNoCallSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
      dsimp only [stepMirState]
      cases v2026Step_step_iff.mp hStep with
      | inl hTau =>
        rw [hTau]
        exact hSub
      | inr hVis =>
        let ⟨_, k, hv, hk⟩ := hVis
        rw [hv]
        change wpMirExecNoCallSym (fuel + 1) body (k PUnit.unit) post
        rw [hk]
        exact hSub
    | done out =>
      rw [hStep] at h
      unfold wpMirNoCallSym wpMirExecNoCallSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
      dsimp only [stepMirState]
      cases v2026Step_done_iff.mp hStep with
      | inl hRet =>
        rw [hRet]
        exact h
      | inr hRest =>
        cases hRest with
        | inl hTauH =>
          rw [hTauH]
          exact h
        | inr hVisH =>
          let ⟨_, k, hv, hk⟩ := hVisH
          rw [hv]
          change wpMirExecNoCallSym (fuel + 1) body (k PUnit.unit) post
          rw [hk]
          exact h
    | fault _ =>
      rw [hStep] at h
      exact False.elim h

/-- Adequacy bridge from `execStepOutcome (v2026Step body)` directly into
`Anneal.MirFuelFree.MirWpConverges`. -/
theorem mirWpConverges_of_v2026Exec {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} {fuel : Nat}
    (h : execStepOutcome (v2026Step body) post (fun _ => False) fuel s) :
    MirWpConverges body s post :=
  ⟨fuel + 1, wpMirSym_of_v2026Exec h⟩

/-- Call-free adequacy bridge from `execStepOutcome (v2026Step body)` into
`Anneal.MirFuelFree.MirNoCallWpConverges`. -/
theorem mirNoCallWpConverges_of_v2026Exec {body : CapturedMir}
    {s : MachineState} {post : MirOutcome → Prop} {fuel : Nat}
    (h : execStepOutcome (v2026Step body) post (fun _ => False) fuel s) :
    MirNoCallWpConverges body s post :=
  ⟨fuel + 1, wpMirNoCallSym_of_v2026Exec h⟩

/-! ### Choice-Free Direct `TreeSafe` Adequacy -/

private theorem tauStar_eq_of_observe_ret' {t u : ITree MirEffect MirOutcome}
    {r : MirOutcome} (h : t.observe = .ret r) (hs : TauStar t u) : u = t := by
  cases hs with
  | refl _ => rfl
  | step hObs _ => rw [h] at hObs; cases hObs

private theorem tauStar_eq_of_observe_vis' {t u : ITree MirEffect MirOutcome}
    {i : MirEffect.I} {k : MirEffect.O i → ITree MirEffect MirOutcome}
    (h : t.observe = .vis i k) (hs : TauStar t u) : u = t := by
  cases hs with
  | refl _ => rfl
  | step hObs _ => rw [h] at hObs; cases hObs

/-- A MIR interaction tree whose head node is `.ret r` is `TreeSafe`
(proved directly from `Trusted.ITree.Reaches`, `0` `Classical.choice`). -/
theorem treeSafe_of_observe_ret_v2026 {t : ITree MirEffect MirOutcome}
    {r : MirOutcome} (h : t.observe = .ret r) : TreeSafe t := by
  intro tr u hR hF
  cases hR with
  | refl _ =>
    obtain ⟨t', i, k, hTs, hObs, _⟩ := hF
    rw [tauStar_eq_of_observe_ret' h hTs, h] at hObs
    cases hObs
  | tau hObs _ => rw [h] at hObs; cases hObs
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

/-- `TreeSafe` propagates backwards across a silent `.tau` head node. -/
theorem treeSafe_of_observe_tau_v2026 {t t' : ITree MirEffect MirOutcome}
    (h : t.observe = .tau t') (hSafe : TreeSafe t') : TreeSafe t := by
  intro tr u hR hF
  cases hR with
  | refl _ =>
    obtain ⟨t'', i, k, hTs, hObs, hFault⟩ := hF
    cases hTs with
    | refl _ => rw [h] at hObs; cases hObs
    | step hObs' hTs' =>
      rw [h] at hObs'
      injection hObs' with hEq
      subst hEq
      exact hSafe [] _ (Reaches.refl _) ⟨t'', i, k, hTs', hObs, hFault⟩
  | tau hObs hR' =>
    rw [h] at hObs
    injection hObs with hEq
    subst hEq
    exact hSafe _ _ hR' hF
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

/-- `TreeSafe` propagates backwards across a non-fault visible head node
(e.g. an observable `MirObsE` emission) whose every continuation is safe. -/
theorem treeSafe_of_observe_vis_v2026 {t : ITree MirEffect MirOutcome}
    {i : MirEffect.I} {k : MirEffect.O i → ITree MirEffect MirOutcome}
    (h : t.observe = .vis i k) (hNF : ¬ FaultEffect.isFault i)
    (hSafe : ∀ o, TreeSafe (k o)) : TreeSafe t := by
  intro tr u hR hF
  cases hR with
  | refl _ =>
    obtain ⟨t'', i', k', hTs, hObs, hFault⟩ := hF
    rw [tauStar_eq_of_observe_vis' h hTs, h] at hObs
    cases hObs
    exact hNF hFault
  | tau hObs _ => rw [h] at hObs; cases hObs
  | vis hObs _ o hR' =>
    rw [h] at hObs
    cases hObs
    exact hSafe o _ _ hR' hF

/-- One-layer observation of `mirTree body s` over unmodified `stepMirFn`. -/
theorem mirTree_observe (body : CapturedMir) (s : MachineState) :
    (mirTree body s).observe =
      (stepMirFn body s).map (ITree.cofix (stepMirState body)) :=
  ITree.observe_cofix _ _

private theorem treeSafe_cofix_halted (body : CapturedMir) (out : MirOutcome) :
    TreeSafe (ITree.cofix (stepMirState body) (.halted out)) :=
  treeSafe_of_observe_ret_v2026 (r := out) (ITree.observe_cofix _ _)

/-- Choice-free all-prefix UB-freedom: every fault-free
`execStepOutcome (v2026Step body)` derivation yields
`TreeSafe (mirTree body s)` directly (`{propext, Quot.sound}` only). -/
theorem treeSafe_mirTree_of_v2026Exec {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {fuel : Nat} {s : MachineState},
      execStepOutcome (v2026Step body) post (fun _ => False) fuel s →
      TreeSafe (mirTree body s)
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    dsimp only [execStepOutcome] at h
    rw [execStepPred_succ_iff] at h
    have hObs := mirTree_observe body s
    cases hStep : v2026Step body s with
    | step s' =>
      rw [hStep] at h
      have ih : TreeSafe (mirTree body s') := treeSafe_mirTree_of_v2026Exec h
      cases v2026Step_step_iff.mp hStep with
      | inl hTau =>
        rw [hTau] at hObs
        exact treeSafe_of_observe_tau_v2026 (t' := mirTree body s') hObs ih
      | inr hVis =>
        obtain ⟨obs, k, hv, hk⟩ := hVis
        rw [hv] at hObs
        refine treeSafe_of_observe_vis_v2026
          (k := fun o => ITree.cofix (stepMirState body) (k o)) hObs
          (fun hF => hF) (fun o => ?_)
        cases o
        show TreeSafe (ITree.cofix (stepMirState body) (k PUnit.unit))
        rw [hk]
        exact ih
    | done out =>
      cases v2026Step_done_iff.mp hStep with
      | inl hRet =>
        rw [hRet] at hObs
        exact treeSafe_of_observe_ret_v2026 (r := out) hObs
      | inr hRest =>
        cases hRest with
        | inl hTauH =>
          rw [hTauH] at hObs
          exact treeSafe_of_observe_tau_v2026 hObs (treeSafe_cofix_halted body out)
        | inr hVisH =>
          obtain ⟨obs, k, hv, hk⟩ := hVisH
          rw [hv] at hObs
          refine treeSafe_of_observe_vis_v2026
            (k := fun o => ITree.cofix (stepMirState body) (k o)) hObs
            (fun hF => hF) (fun o => ?_)
          cases o
          show TreeSafe (ITree.cofix (stepMirState body) (k PUnit.unit))
          rw [hk]
          exact treeSafe_cofix_halted body out
    | fault _ =>
      rw [hStep] at h
      exact False.elim h

/-! ### Choice-Free Direct `ReachesRet` & `Productive` Adequacy -/

/-- A MIR interaction tree whose head node is `.ret r` can only reach `.ret`
with outcome `out = r` (proved directly from `Trusted.ITree.Reaches`). -/
theorem reachesRet_of_observe_ret_v2026 {t : ITree MirEffect MirOutcome}
    {r out : MirOutcome} {tr : List (Event MirEffect)}
    (h : t.observe = .ret r) (hR : ReachesRet t tr out) : out = r := by
  let ⟨u, hReach, hRet⟩ := hR
  cases hReach with
  | refl _ =>
    rw [h] at hRet
    injection hRet with hEq
    exact hEq.symm
  | tau hObs _ => rw [h] at hObs; cases hObs
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

/-- `ReachesRet` steps forward across a silent `.tau` head node. -/
theorem reachesRet_of_observe_tau_v2026 {t t' : ITree MirEffect MirOutcome}
    {out : MirOutcome} {tr : List (Event MirEffect)}
    (h : t.observe = .tau t') (hR : ReachesRet t tr out) :
    ReachesRet t' tr out := by
  let ⟨u, hReach, hRet⟩ := hR
  cases hReach with
  | refl _ => rw [h] at hRet; cases hRet
  | tau hObs hNext =>
    rw [h] at hObs
    injection hObs with hEq
    subst hEq
    exact ⟨u, hNext, hRet⟩
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

/-- `ReachesRet` steps forward across a visible `.vis` head node. -/
theorem reachesRet_of_observe_vis_v2026 {t : ITree MirEffect MirOutcome}
    {i : MirEffect.I} {k : MirEffect.O i → ITree MirEffect MirOutcome}
    {out : MirOutcome} {tr : List (Event MirEffect)}
    (h : t.observe = .vis i k) (hR : ReachesRet t tr out) :
    ∃ (o : MirEffect.O i) (tr' : List (Event MirEffect)),
      ReachesRet (k o) tr' out := by
  let ⟨u, hReach, hRet⟩ := hR
  cases hReach with
  | refl _ => rw [h] at hRet; cases hRet
  | tau hObs _ => rw [h] at hObs; cases hObs
  | vis hObs _ o hNext =>
    rw [h] at hObs
    cases hObs
    exact ⟨o, _, ⟨u, hNext, hRet⟩⟩

private theorem reachesRet_cofix_halted (body : CapturedMir)
    {out retOut : MirOutcome} {tr : List (Event MirEffect)}
    (hR : ReachesRet (ITree.cofix (stepMirState body) (.halted out)) tr retOut) :
    retOut = out :=
  reachesRet_of_observe_ret_v2026 (r := out) (ITree.observe_cofix _ _) hR

/-- Choice-free return-postcondition adequacy: every fault-free
`execStepOutcome (v2026Step body)` derivation implies `post out` for every
`ReachesRet (mirTree body s) tr out` (`{propext, Quot.sound}` only). -/
theorem reachesRet_post_of_v2026Exec {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {fuel : Nat} {s : MachineState},
      execStepOutcome (v2026Step body) post (fun _ => False) fuel s →
      ∀ tr out, ReachesRet (mirTree body s) tr out → post out
  | 0, _, h, _, _, _ => False.elim h
  | fuel + 1, s, h, tr, out, hR => by
    dsimp only [execStepOutcome] at h
    rw [execStepPred_succ_iff] at h
    have hObs := mirTree_observe body s
    cases hStep : v2026Step body s with
    | step s' =>
      rw [hStep] at h
      cases v2026Step_step_iff.mp hStep with
      | inl hTau =>
        rw [hTau] at hObs
        exact reachesRet_post_of_v2026Exec h tr out
          (reachesRet_of_observe_tau_v2026 (t' := mirTree body s') hObs hR)
      | inr hVis =>
        let ⟨_, k, hv, hk⟩ := hVis
        rw [hv] at hObs
        let ⟨o, tr', hR'⟩ := reachesRet_of_observe_vis_v2026
          (k := fun o => ITree.cofix (stepMirState body) (k o)) hObs hR
        cases o
        have hR'' : ReachesRet (mirTree body s') tr' out := by
          unfold mirTree
          rw [← hk]
          exact hR'
        exact reachesRet_post_of_v2026Exec h tr' out hR''
    | done out' =>
      rw [hStep] at h
      cases v2026Step_done_iff.mp hStep with
      | inl hRet =>
        rw [hRet] at hObs
        have hEq := reachesRet_of_observe_ret_v2026 (r := out') hObs hR
        rw [hEq]
        exact h
      | inr hRest =>
        cases hRest with
        | inl hTauH =>
          rw [hTauH] at hObs
          have hEq := reachesRet_cofix_halted body
            (reachesRet_of_observe_tau_v2026 hObs hR)
          rw [hEq]
          exact h
        | inr hVisH =>
          let ⟨_, k, hv, hk⟩ := hVisH
          rw [hv] at hObs
          let ⟨o, tr', hR'⟩ := reachesRet_of_observe_vis_v2026
            (k := fun o => ITree.cofix (stepMirState body) (k o)) hObs hR
          cases o
          have hR'' :
              ReachesRet (ITree.cofix (stepMirState body) (.halted out')) tr' out := by
            rw [← hk]
            exact hR'
          have hEq := reachesRet_cofix_halted body hR''
          rw [hEq]
          exact h
    | fault _ =>
      rw [hStep] at h
      exact False.elim h

/-- A MIR interaction tree whose head node is `.ret r` is `Productive`. -/
theorem productive_of_observe_ret_v2026 {t : ITree MirEffect MirOutcome}
    {r : MirOutcome} (h : t.observe = .ret r) : Productive t := by
  intro tr u hR
  cases hR with
  | refl _ =>
    refine ⟨t, TauStar.refl t, fun w hTau => ?_⟩
    rw [h] at hTau
    cases hTau
  | tau hObs _ => rw [h] at hObs; cases hObs
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

/-- `Productive` propagates backwards across a silent `.tau` head node. -/
theorem productive_of_observe_tau_v2026 {t t' : ITree MirEffect MirOutcome}
    (h : t.observe = .tau t') (hProd : Productive t') : Productive t := by
  intro tr u hR
  cases hR with
  | refl _ =>
    let ⟨u', hTs, hNotTau⟩ := hProd [] t' (Reaches.refl t')
    exact ⟨u', TauStar.step h hTs, hNotTau⟩
  | tau hObs hNext =>
    rw [h] at hObs
    injection hObs with hEq
    subst hEq
    exact hProd _ _ hNext
  | vis hObs _ _ _ => rw [h] at hObs; cases hObs

/-- `Productive` propagates backwards across a visible `.vis` head node whose
every continuation is `Productive`. -/
theorem productive_of_observe_vis_v2026 {t : ITree MirEffect MirOutcome}
    {i : MirEffect.I} {k : MirEffect.O i → ITree MirEffect MirOutcome}
    (h : t.observe = .vis i k) (hProd : ∀ o, Productive (k o)) :
    Productive t := by
  intro tr u hR
  cases hR with
  | refl _ =>
    refine ⟨t, TauStar.refl t, fun w hTau => ?_⟩
    rw [h] at hTau
    cases hTau
  | tau hObs _ => rw [h] at hObs; cases hObs
  | vis hObs _ o hNext =>
    rw [h] at hObs
    cases hObs
    exact hProd o _ _ hNext

private theorem productive_cofix_halted (body : CapturedMir) (out : MirOutcome) :
    Productive (ITree.cofix (stepMirState body) (.halted out)) :=
  productive_of_observe_ret_v2026 (r := out) (ITree.observe_cofix _ _)

/-- Choice-free reactive productivity adequacy: every fault-free
`execStepOutcome (v2026Step body)` derivation implies `Productive (mirTree body s)`
directly (`{propext, Quot.sound}` only). -/
theorem productive_mirTree_of_v2026Exec {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {fuel : Nat} {s : MachineState},
      execStepOutcome (v2026Step body) post (fun _ => False) fuel s →
      Productive (mirTree body s)
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
    dsimp only [execStepOutcome] at h
    rw [execStepPred_succ_iff] at h
    have hObs := mirTree_observe body s
    cases hStep : v2026Step body s with
    | step s' =>
      rw [hStep] at h
      have ih : Productive (mirTree body s') := productive_mirTree_of_v2026Exec h
      cases v2026Step_step_iff.mp hStep with
      | inl hTau =>
        rw [hTau] at hObs
        exact productive_of_observe_tau_v2026 (t' := mirTree body s') hObs ih
      | inr hVis =>
        let ⟨_, k, hv, hk⟩ := hVis
        rw [hv] at hObs
        refine productive_of_observe_vis_v2026
          (k := fun o => ITree.cofix (stepMirState body) (k o)) hObs (fun o => ?_)
        cases o
        show Productive (ITree.cofix (stepMirState body) (k PUnit.unit))
        rw [hk]
        exact ih
    | done out =>
      cases v2026Step_done_iff.mp hStep with
      | inl hRet =>
        rw [hRet] at hObs
        exact productive_of_observe_ret_v2026 (r := out) hObs
      | inr hRest =>
        cases hRest with
        | inl hTauH =>
          rw [hTauH] at hObs
          exact productive_of_observe_tau_v2026 hObs (productive_cofix_halted body out)
        | inr hVisH =>
          let ⟨_, k, hv, hk⟩ := hVisH
          rw [hv] at hObs
          refine productive_of_observe_vis_v2026
            (k := fun o => ITree.cofix (stepMirState body) (k o)) hObs (fun o => ?_)
          cases o
          show Productive (ITree.cofix (stepMirState body) (k PUnit.unit))
          rw [hk]
          exact productive_cofix_halted body out
    | fault _ =>
      rw [hStep] at h
      exact False.elim h

/-- Exact bidirectional equivalence between fuel-free
`ParametricCore.wpStateOk (ops := V2026Bridge.mirNoCallDetWpOps body)` and
existence of a finite fault-free `execStepOutcome (v2026Step body)` run. -/
theorem wpStateOk_mirNoCallDet_iff_exists_v2026Exec {body : CapturedMir}
    {s : MachineState} {post : MirOutcome → Prop} :
    Anneal.ParametricCore.wpStateOk
        (ops := Anneal.ParametricCore.V2026Bridge.mirNoCallDetWpOps body) post s ↔
      ∃ fuel : Nat,
        execStepOutcome (v2026Step body) post (fun _ => False) fuel s := by
  constructor
  · intro hWp
    exact Anneal.ParametricCore.wpOutcome_det_induction
      (C := fun st => ∃ fuel : Nat,
        execStepOutcome (v2026Step body) post (fun _ => False) fuel st)
      (fun st st' hStep ih => by
        let ⟨fuel, hF⟩ := ih
        refine ⟨fuel + 1, ?_⟩
        dsimp only [execStepOutcome]
        rw [execStepPred_succ_iff, v2026Step_step_iff_mirNoCallStep_step.mpr hStep]
        exact hF)
      (fun st out hDone hPost => by
        refine ⟨1, ?_⟩
        dsimp only [execStepOutcome]
        rw [execStepPred_succ_iff, v2026Step_done_iff_mirNoCallStep_done.mpr hDone]
        exact hPost)
      (fun _ _ _ hF => False.elim hF) hWp
  · intro ⟨fuel, hExec⟩
    induction fuel generalizing s with
    | zero => exact False.elim hExec
    | succ fuel ih =>
      dsimp only [execStepOutcome] at hExec
      rw [execStepPred_succ_iff] at hExec
      cases hStep : v2026Step body s with
      | step s' =>
        rw [hStep] at hExec
        refine Anneal.ParametricCore.wpUntil_step
          (ops := Anneal.ParametricCore.V2026Bridge.mirNoCallDetWpOps body) ?_
        change (Anneal.ParametricCore.V2026Bridge.mirNoCallStep body s).wp _ _ _
        rw [v2026Step_step_iff_mirNoCallStep_step.mp hStep]
        exact ih hExec
      | done out =>
        rw [hStep] at hExec
        refine Anneal.ParametricCore.wpUntil_step
          (ops := Anneal.ParametricCore.V2026Bridge.mirNoCallDetWpOps body) ?_
        change (Anneal.ParametricCore.V2026Bridge.mirNoCallStep body s).wp _ _ _
        rw [v2026Step_done_iff_mirNoCallStep_done.mp hStep]
        exact hExec
      | fault _ =>
        rw [hStep] at hExec
        exact False.elim hExec

/-! ### Exact Completeness: `wpMirNoCallSym` ⇒ `execStepOutcome (v2026Step body)` -/

private theorem v2026ExecSt_of_wpMirExecNoCallSym {body : CapturedMir}
    {post : MirOutcome → Prop} :
    ∀ {fuel : Nat} {st : MirExecState},
      wpMirExecNoCallSym fuel body st post →
      (match st with
        | .running s => execStepOutcome (v2026Step body) post (fun _ => False) fuel s
        | .halted out => post out
        | .faulted _ => False)
  | 0, _, h => False.elim h
  | fuel + 1, st, h => by
    unfold wpMirExecNoCallSym at h
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h
    cases st with
    | halted out => exact h
    | faulted fk => exact h
    | running s =>
      dsimp only [stepMirState] at h
      dsimp only [execStepOutcome]
      rw [execStepPred_succ_iff]
      unfold v2026Step
      cases hN : stepMirFn body s with
      | ret out =>
        rw [hN] at h
        exact h
      | tau st' =>
        rw [hN] at h
        have ih := v2026ExecSt_of_wpMirExecNoCallSym h
        cases st' with
        | running s' => exact ih
        | halted out => exact ih
        | faulted _ => exact ih
      | vis i k =>
        rw [hN] at h
        rcases i with f | (e | c)
        · cases f
          exact h
        · cases e
          have ih := v2026ExecSt_of_wpMirExecNoCallSym h
          dsimp only [ofV2026MirStepNode]
          cases hk : k PUnit.unit with
          | running s' => rw [hk] at ih; exact ih
          | halted out => rw [hk] at ih; exact ih
          | faulted _ => rw [hk] at ih; exact ih
        · cases c
          exact h

/-- Exact completeness of the lossless `v2026Step` adapter: every call-free
`wpMirNoCallSym fuel` derivation over unmodified `stepMirState` yields a
fault-free `execStepOutcome (v2026Step body)` derivation at the SAME fuel. -/
theorem v2026Exec_of_wpMirNoCallSym {body : CapturedMir}
    {post : MirOutcome → Prop} {fuel : Nat} {s : MachineState}
    (h : wpMirNoCallSym fuel body s post) :
    execStepOutcome (v2026Step body) post (fun _ => False) fuel s :=
  v2026ExecSt_of_wpMirExecNoCallSym (st := .running s) h

/-- Exact fuel-free characterization: call-free MIR convergence
(`MirNoCallWpConverges`) holds iff some finite fault-free
`execStepOutcome (v2026Step body)` run exists. -/
theorem mirNoCallWpConverges_iff_exists_v2026Exec {body : CapturedMir}
    {s : MachineState} {post : MirOutcome → Prop} :
    MirNoCallWpConverges body s post ↔
      ∃ fuel : Nat,
        execStepOutcome (v2026Step body) post (fun _ => False) fuel s :=
  ⟨fun ⟨fuel, h⟩ => ⟨fuel, v2026Exec_of_wpMirNoCallSym h⟩,
   fun ⟨_, h⟩ => mirNoCallWpConverges_of_v2026Exec h⟩

/-- Total-correctness `DWP mirDefaultWP` adequacy of
`execStepOutcome (v2026Step body)` over `mirTree body s`. -/
theorem dwp_of_v2026Exec {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} {fuel : Nat}
    (h : execStepOutcome (v2026Step body) post (fun _ => False) fuel s) :
    DWP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  dwp_of_mirWpConverges (mirWpConverges_of_v2026Exec h)

/-- Partial-correctness `DWLP mirDefaultWP` adequacy of
`execStepOutcome (v2026Step body)` over `mirTree body s`. -/
theorem dwlp_of_v2026Exec {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} {fuel : Nat}
    (h : execStepOutcome (v2026Step body) post (fun _ => False) fuel s) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  dwlp_of_mirWpConverges (mirWpConverges_of_v2026Exec h)

/-- All-prefix UB-freedom (`MirNoUBTree (mirTree body s)`) directly from
`execStepOutcome (v2026Step body)`, via the choice-free direct `TreeSafe`
argument `treeSafe_mirTree_of_v2026Exec` (`{propext, Quot.sound}` only; does
NOT route through the `Classical.choice`-dependent `dwlp_pure_adequacy`). -/
theorem mirNoUBTree_of_v2026Exec {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop} {fuel : Nat}
    (h : execStepOutcome (v2026Step body) post (fun _ => False) fuel s) :
    MirNoUBTree (mirTree body s) :=
  treeSafe_mirTree_of_v2026Exec h

/-- Whole-function stateless `VerificationResult` (`mirSafePost`) lifting
directly from `execStepOutcome (v2026Step c.body)` via choice-free `TreeSafe` +
`ReachesRet` adequacy (`{propext, Quot.sound}` only). -/
theorem verifyMirSafe_of_v2026Exec (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ fuel : Nat,
        execStepOutcome (v2026Step c.body)
          (mirSafePost (fun retVal _ => c.post args retVal))
          (fun _ => False) fuel
          (initMachineStateWithCallees c.body args c.callees)) :
    VerificationResult c := by
  refine ⟨fun args hPre => ?_⟩
  let ⟨_, hExec⟩ := h args hPre
  refine ⟨treeSafe_mirTree_of_v2026Exec hExec,
    fun outPair hRet _ retVal mem' hEq => ?_⟩
  have hSafe := reachesRet_post_of_v2026Exec hExec outPair.1 outPair.2 hRet
  rw [hEq] at hSafe
  exact hSafe

/-- Whole-function panic-forbidding stateless `VerificationResult`
(`mirNormalPost`) lifting directly from `execStepOutcome (v2026Step c.body)`
(`{propext, Quot.sound}` only). -/
theorem verifyMirNoPanic_of_v2026Exec (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ fuel : Nat,
        execStepOutcome (v2026Step c.body)
          (mirNormalPost (fun retVal _ => c.post args retVal))
          (fun _ => False) fuel
          (initMachineStateWithCallees c.body args c.callees)) :
    VerificationResult c :=
  verifyMirSafe_of_v2026Exec c (fun args hPre => by
    let ⟨fuel, hExec⟩ := h args hPre
    exact ⟨fuel, execStepPred_mono
      (fun _ _ ho => mirNormalPost_imp_mirSafePost ho) (fun _ _ hf => hf) hExec⟩)

/-- Whole-function stateful `StatefulVerificationResult` (`mirSafePost`)
lifting directly from `execStepOutcome (v2026Step c.body)`
(`{propext, Quot.sound}` only). -/
theorem verifyStatefulMirSafe_of_v2026Exec (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ fuel : Nat,
        execStepOutcome (v2026Step c.body)
          (mirSafePost (c.post args mem))
          (fun _ => False) fuel
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)) :
    StatefulVerificationResult c := by
  refine ⟨fun args mem hPre => ?_⟩
  let ⟨_, hExec⟩ := h args mem hPre
  refine ⟨treeSafe_mirTree_of_v2026Exec hExec,
    fun outPair hRet _ retVal mem' hEq => ?_⟩
  have hSafe := reachesRet_post_of_v2026Exec hExec outPair.1 outPair.2 hRet
  rw [hEq] at hSafe
  exact hSafe

/-- Whole-function panic-forbidding stateful `StatefulVerificationResult`
(`mirNormalPost`) lifting directly from `execStepOutcome (v2026Step c.body)`
(`{propext, Quot.sound}` only). -/
theorem verifyStatefulMirNoPanic_of_v2026Exec (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ fuel : Nat,
        execStepOutcome (v2026Step c.body)
          (mirNormalPost (c.post args mem))
          (fun _ => False) fuel
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_v2026Exec c (fun args mem hPre => by
    let ⟨fuel, hExec⟩ := h args mem hPre
    exact ⟨fuel, execStepPred_mono
      (fun _ _ ho => mirNormalPost_imp_mirSafePost ho) (fun _ _ hf => hf) hExec⟩)

/-- Whole-function total-correctness `TotalVerificationResult`
(`mirNormalPost`) lifting directly from `execStepOutcome (v2026Step c.body)`
via direct `TreeSafe`, `Productive`, `productive_not_mayDiverge`, and
`ReachesRet` adequacy (bypassing `DWP` / `DWLP`). -/
theorem verifyTotalMir_of_v2026Exec (c : TotalClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ fuel : Nat,
        execStepOutcome (v2026Step c.body)
          (mirNormalPost (c.post args mem))
          (fun _ => False) fuel
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)) :
    TotalVerificationResult c := by
  refine ⟨fun args mem hPre => ?_⟩
  let ⟨_, hExec⟩ := h args mem hPre
  have hProd := productive_mirTree_of_v2026Exec hExec
  refine ⟨treeSafe_mirTree_of_v2026Exec hExec, hProd,
    Anneal.ITree.productive_not_mayDiverge hProd, fun tr out hRet => ?_⟩
  have hNorm := reachesRet_post_of_v2026Exec hExec tr out hRet
  cases out with
  | normal p => exact ⟨p.1, p.2, rfl, hNorm⟩
  | panic => exact False.elim hNorm
  | abort => exact False.elim hNorm

/-! ## Part II: Deterministic `execWlp*`, Anti-Monotonicity, & Asymmetric Two-Pass Splitting -/

/-- Singleton-choice `wpStepOutcome` specialization for `v2026Step body`. -/
abbrev wpOutcomeV2026 (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (fuel : Nat) (s : MachineState) : Prop :=
  wpStepOutcome (C := Unit) (fun _ c => c = ()) (fun _ => v2026Step body)
    onDone onFault fuel s

/-- Fault-forbidding total state WP over `v2026Step body`. -/
abbrev wpStateV2026 (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpOutcomeV2026 body post (fun _ => False) fuel s

/-- Whole-function fault-forbidding total WP over `v2026Step body` starting at
`initMachineStateWithCallees body args callees`. -/
def wpProgV2026 (body : CapturedMir) (fuel : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  wpStateV2026 body fuel (initMachineStateWithCallees body args callees) post

/-- Deterministic total outcome WP over `v2026Step body`. -/
abbrev execOutcomeV2026 (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (fuel : Nat) (s : MachineState) : Prop :=
  execStepOutcome (v2026Step body) onDone onFault fuel s

/-- Deterministic fault-forbidding total state WP over `v2026Step body`. -/
abbrev execStateV2026 (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  execOutcomeV2026 body post (fun _ => False) fuel s

/-- Deterministic whole-function fault-forbidding total WP over
`v2026Step body`. -/
def execProgV2026 (body : CapturedMir) (fuel : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  execStateV2026 body fuel (initMachineStateWithCallees body args callees) post

/-- Singleton-choice weakest liberal precondition over `v2026Step body`. -/
abbrev wlpOutcomeV2026 (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (fuel : Nat) (s : MachineState) : Prop :=
  wlpStepOutcome (C := Unit) (fun _ c => c = ()) (fun _ => v2026Step body)
    onDone onFault fuel s

/-- Fault-forbidding state-level weakest liberal precondition over
`v2026Step body`. -/
abbrev wlpStateV2026 (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wlpOutcomeV2026 body post (fun _ => False) fuel s

/-- Whole-function weakest liberal precondition leaving fault absence to a
companion safety pass (`onFault := fun _ => True`). -/
def wlpProgV2026 (body : CapturedMir) (fuel : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  wlpOutcomeV2026 body post (fun _ => True) fuel
    (initMachineStateWithCallees body args callees)

/-- Whole-function strict weakest liberal precondition forbidding faults along
every `fuel`-step prefix. -/
def wlpProgStrictV2026 (body : CapturedMir) (fuel : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  wlpStateV2026 body fuel (initMachineStateWithCallees body args callees) post

/-- Deterministic fast-path weakest liberal precondition over
`v2026Step body` (`@Nat.rec` directly via `execWlpStepOutcome`). -/
abbrev execWlpOutcomeV2026 (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (fuel : Nat) (s : MachineState) : Prop :=
  execWlpStepOutcome (v2026Step body) onDone onFault fuel s

/-- Deterministic fault-forbidding state-level weakest liberal precondition
over `v2026Step body`. -/
abbrev execWlpStateV2026 (body : CapturedMir) (fuel : Nat) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  execWlpOutcomeV2026 body post (fun _ => False) fuel s

/-- Deterministic whole-function weakest liberal precondition
(`onFault := fun _ => True`). -/
def execWlpProgV2026 (body : CapturedMir) (fuel : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  execWlpOutcomeV2026 body post (fun _ => True) fuel
    (initMachineStateWithCallees body args callees)

/-- Deterministic whole-function strict weakest liberal precondition forbidding
faults. -/
def execWlpProgStrictV2026 (body : CapturedMir) (fuel : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  execWlpStateV2026 body fuel (initMachineStateWithCallees body args callees) post

/-- Exact equivalence between `wpOutcomeV2026` and `execOutcomeV2026`. -/
theorem wpOutcomeV2026_iff_execOutcomeV2026 {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel : Nat} {s : MachineState} :
    wpOutcomeV2026 body onDone onFault fuel s ↔
      execOutcomeV2026 body onDone onFault fuel s :=
  wpStepPred_iff_execStepPred (c₀ := ()) (fun _ _ => Iff.rfl)

/-- Unfold `wlpOutcomeV2026` at fuel `0`. -/
theorem wlpOutcomeV2026_zero (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (s : MachineState) :
    wlpOutcomeV2026 body onDone onFault 0 s :=
  trivial

/-- Exact equivalence between `wlpOutcomeV2026` and deterministic
`execWlpOutcomeV2026`. -/
theorem wlpOutcomeV2026_iff_execWlpOutcomeV2026 {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel : Nat} {s : MachineState} :
    wlpOutcomeV2026 body onDone onFault fuel s ↔
      execWlpOutcomeV2026 body onDone onFault fuel s :=
  wlpStepPred_iff_execWlpStepPred (c₀ := ()) (fun _ _ => Iff.rfl)

/-- Lift deterministic `execWlpOutcomeV2026` into `wlpOutcomeV2026`. -/
theorem wlpOutcomeV2026_of_execWlpOutcomeV2026 {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel : Nat} {s : MachineState}
    (h : execWlpOutcomeV2026 body onDone onFault fuel s) :
    wlpOutcomeV2026 body onDone onFault fuel s :=
  wlpOutcomeV2026_iff_execWlpOutcomeV2026.mpr h

/-- Exact equivalence between `wlpProgV2026` and `execWlpProgV2026`. -/
theorem wlpProgV2026_iff_execWlpProgV2026 {body : CapturedMir} {fuel : Nat}
    {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop} :
    wlpProgV2026 body fuel args callees post ↔
      execWlpProgV2026 body fuel args callees post :=
  wlpOutcomeV2026_iff_execWlpOutcomeV2026

/-- Exact equivalence between `wlpProgStrictV2026` and
`execWlpProgStrictV2026`. -/
theorem wlpProgStrictV2026_iff_execWlpProgStrictV2026 {body : CapturedMir}
    {fuel : Nat} {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop} :
    wlpProgStrictV2026 body fuel args callees post ↔
      execWlpProgStrictV2026 body fuel args callees post :=
  wlpOutcomeV2026_iff_execWlpOutcomeV2026

/-- Single-step introduction rule for `wlpOutcomeV2026`. -/
theorem wlpOutcomeV2026_step_eq {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel : Nat} {s s' : MachineState}
    (hStep : v2026Step body s = .step s')
    (h : wlpOutcomeV2026 body onDone onFault fuel s') :
    wlpOutcomeV2026 body onDone onFault (fuel + 1) s :=
  wlpOutcomeV2026_of_execWlpOutcomeV2026
    (execWlpStepPred_step hStep (wlpOutcomeV2026_iff_execWlpOutcomeV2026.mp h))

/-- Terminal `.done` introduction rule for `wlpOutcomeV2026`. -/
theorem wlpOutcomeV2026_done_eq {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel : Nat} {s : MachineState} {out : MirOutcome}
    (hStep : v2026Step body s = .done out) (h : onDone out) :
    wlpOutcomeV2026 body onDone onFault (fuel + 1) s := by
  refine wlpOutcomeV2026_of_execWlpOutcomeV2026 ?_
  dsimp only [execWlpOutcomeV2026, execWlpStepOutcome]
  rw [execWlpStepPred_succ_iff, hStep]
  exact h

/-- Rule of consequence for `wlpOutcomeV2026`. -/
theorem wlpOutcomeV2026_mono {body : CapturedMir}
    {onDone₁ onDone₂ : MirOutcome → Prop}
    {onFault₁ onFault₂ : V2026StepFault → Prop}
    (hDone : ∀ out, onDone₁ out → onDone₂ out)
    (hFault : ∀ k, onFault₁ k → onFault₂ k)
    {fuel : Nat} {s : MachineState}
    (h : wlpOutcomeV2026 body onDone₁ onFault₁ fuel s) :
    wlpOutcomeV2026 body onDone₂ onFault₂ fuel s :=
  wlpStepPred_mono (fun _ => hDone) (fun _ => hFault) h

/-- Fuel anti-monotonicity for `wlpOutcomeV2026`: checking `fuel₂` steps
implies checking any shorter prefix `fuel₁ ≤ fuel₂`. -/
theorem wlpOutcomeV2026_fuel_anti {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel₁ fuel₂ : Nat} {s : MachineState}
    (hLe : fuel₁ ≤ fuel₂)
    (h : wlpOutcomeV2026 body onDone onFault fuel₂ s) :
    wlpOutcomeV2026 body onDone onFault fuel₁ s :=
  wlpStepPred_fuel_anti hLe h

/-- Fuel anti-monotonicity for deterministic `execWlpOutcomeV2026`. -/
theorem execWlpOutcomeV2026_fuel_anti {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel₁ fuel₂ : Nat} {s : MachineState}
    (hLe : fuel₁ ≤ fuel₂)
    (h : execWlpOutcomeV2026 body onDone onFault fuel₂ s) :
    execWlpOutcomeV2026 body onDone onFault fuel₁ s :=
  execWlpStepPred_fuel_anti hLe h

/-- Every terminating `wpOutcomeV2026` implies `wlpOutcomeV2026` at the same
fuel. -/
theorem wlpOutcomeV2026_of_wp {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {fuel : Nat} {s : MachineState}
    (h : wpOutcomeV2026 body onDone onFault fuel s) :
    wlpOutcomeV2026 body onDone onFault fuel s :=
  wlpStepPred_of_wpStepPred h

/-- Asymmetric-fuel two-pass outcome combination (`fuelSafe ≤ fuelWlp`):
combines a functional `wlpOutcomeV2026` proof at `fuelWlp` with a
termination/safety `wpOutcomeV2026` proof at `fuelSafe`. -/
theorem wpOutcomeV2026_of_wlp_and_safety_le {body : CapturedMir}
    {dWlp dSafe : MirOutcome → Prop} {fWlp fSafe : V2026StepFault → Prop}
    {fuelSafe fuelWlp : Nat} {s : MachineState}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpOutcomeV2026 body dWlp fWlp fuelWlp s)
    (hSafe : wpOutcomeV2026 body dSafe fSafe fuelSafe s) :
    wpOutcomeV2026 body (fun o => dWlp o ∧ dSafe o)
      (fun k => fWlp k ∧ fSafe k) fuelSafe s :=
  wpStepPred_of_wlp_and_safety_le hLe hWlp hSafe

/-- Asymmetric-fuel two-pass state combination (`fuelSafe ≤ fuelWlp`): combines
`wlpOutcomeV2026` at `fuelWlp` with a `post := fun _ => True` fault-free safety
pass at `fuelSafe`. -/
theorem wpStateV2026_of_wlp_and_safety_le {body : CapturedMir}
    {fuelSafe fuelWlp : Nat} {s : MachineState}
    {post : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpOutcomeV2026 body post onFault fuelWlp s)
    (hSafe : wpStateV2026 body fuelSafe s (fun _ => True)) :
    wpStateV2026 body fuelSafe s post :=
  wpStepPred_mono (fun _ _ h => h.1) (fun _ _ h => h.2)
    (wpOutcomeV2026_of_wlp_and_safety_le hLe hWlp hSafe)

/-- Whole-function asymmetric-fuel two-pass rule (`fuelSafe ≤ fuelWlp`):
`wlpProgV2026` at `fuelWlp` plus a `post := fun _ => True` safety
`wpProgV2026` at `fuelSafe` yields `wpProgV2026` at `fuelSafe`. -/
theorem wpProgV2026_of_wlp_and_safety_le {body : CapturedMir}
    {fuelSafe fuelWlp : Nat} {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpProgV2026 body fuelWlp args callees post)
    (hSafe : wpProgV2026 body fuelSafe args callees (fun _ => True)) :
    wpProgV2026 body fuelSafe args callees post :=
  wpStateV2026_of_wlp_and_safety_le hLe hWlp hSafe

/-- Deterministic fast-path asymmetric-fuel two-pass state combination
(`fuelSafe ≤ fuelWlp`). -/
theorem execStateV2026_of_execWlp_and_safety_le {body : CapturedMir}
    {fuelSafe fuelWlp : Nat} {s : MachineState}
    {post : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : execWlpOutcomeV2026 body post onFault fuelWlp s)
    (hSafe : execStateV2026 body fuelSafe s (fun _ => True)) :
    execStateV2026 body fuelSafe s post :=
  execStepPred_mono (fun _ _ h => h.1) (fun _ _ h => h.2)
    (execStepPred_of_wlp_and_safety_le hLe hWlp hSafe)

/-- Deterministic fast-path whole-function asymmetric-fuel two-pass rule
(`fuelSafe ≤ fuelWlp`). -/
theorem execProgV2026_of_execWlp_and_safety_le {body : CapturedMir}
    {fuelSafe fuelWlp : Nat} {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : execWlpProgV2026 body fuelWlp args callees post)
    (hSafe : execProgV2026 body fuelSafe args callees (fun _ => True)) :
    execProgV2026 body fuelSafe args callees post :=
  execStateV2026_of_execWlp_and_safety_le hLe hWlp hSafe

/-- Asymmetric-fuel two-pass adequacy into `Anneal.MirFuelFree.MirWpConverges`
whenever `fuelSafe ≤ fuelWlp`. -/
theorem mirWpConverges_of_wlp_and_safety_le {body : CapturedMir}
    {fuelSafe fuelWlp : Nat} {s : MachineState}
    {post : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpOutcomeV2026 body post onFault fuelWlp s)
    (hSafe : wpStateV2026 body fuelSafe s (fun _ => True)) :
    MirWpConverges body s post :=
  mirWpConverges_of_v2026Exec
    (wpOutcomeV2026_iff_execOutcomeV2026.mp
      (wpStateV2026_of_wlp_and_safety_le hLe hWlp hSafe))

/-- Asymmetric-fuel two-pass adequacy into `MirNoUBTree (mirTree body s)`. -/
theorem mirNoUBTree_of_wlp_and_safety_le {body : CapturedMir}
    {fuelSafe fuelWlp : Nat} {s : MachineState}
    {post : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    (hLe : fuelSafe ≤ fuelWlp)
    (hWlp : wlpOutcomeV2026 body post onFault fuelWlp s)
    (hSafe : wpStateV2026 body fuelSafe s (fun _ => True)) :
    MirNoUBTree (mirTree body s) :=
  mirNoUBTree_of_v2026Exec
    (wpOutcomeV2026_iff_execOutcomeV2026.mp
      (wpStateV2026_of_wlp_and_safety_le hLe hWlp hSafe))

/-- Whole-function stateless `VerificationResult` (`mirSafePost`) from an
asymmetric-fuel two-pass (`wlpProgV2026` at `fuelWlp` + safety `wpProgV2026` at
`fuelSafe ≤ fuelWlp`) derivation (`{propext, Quot.sound}` only). -/
theorem verifyMirSafe_of_wlp_and_safety_le (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ fuelSafe fuelWlp : Nat,
        fuelSafe ≤ fuelWlp ∧
        wlpProgV2026 c.body fuelWlp args c.callees
          (mirSafePost (fun retVal _ => c.post args retVal)) ∧
        wpProgV2026 c.body fuelSafe args c.callees (fun _ => True)) :
    VerificationResult c :=
  verifyMirSafe_of_v2026Exec c (fun args hPre => by
    let ⟨fuelSafe, _, hLe, hWlp, hSafe⟩ := h args hPre
    exact ⟨fuelSafe, wpOutcomeV2026_iff_execOutcomeV2026.mp
      (wpProgV2026_of_wlp_and_safety_le hLe hWlp hSafe)⟩)

/-- Whole-function panic-forbidding stateless `VerificationResult`
(`mirNormalPost`) from an asymmetric-fuel two-pass derivation
(`{propext, Quot.sound}` only). -/
theorem verifyMirNoPanic_of_wlp_and_safety_le (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ fuelSafe fuelWlp : Nat,
        fuelSafe ≤ fuelWlp ∧
        wlpProgV2026 c.body fuelWlp args c.callees
          (mirNormalPost (fun retVal _ => c.post args retVal)) ∧
        wpProgV2026 c.body fuelSafe args c.callees (fun _ => True)) :
    VerificationResult c :=
  verifyMirNoPanic_of_v2026Exec c (fun args hPre => by
    let ⟨fuelSafe, _, hLe, hWlp, hSafe⟩ := h args hPre
    exact ⟨fuelSafe, wpOutcomeV2026_iff_execOutcomeV2026.mp
      (wpProgV2026_of_wlp_and_safety_le hLe hWlp hSafe)⟩)

/-- Whole-function stateful `StatefulVerificationResult` (`mirSafePost`) from
an asymmetric-fuel two-pass derivation (`{propext, Quot.sound}` only). -/
theorem verifyStatefulMirSafe_of_wlp_and_safety_le (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ fuelSafe fuelWlp : Nat,
        fuelSafe ≤ fuelWlp ∧
        wlpOutcomeV2026 c.body (mirSafePost (c.post args mem))
          (fun _ => True) fuelWlp
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees) ∧
        wpStateV2026 c.body fuelSafe
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (fun _ => True)) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_v2026Exec c (fun args mem hPre => by
    let ⟨fuelSafe, _, hLe, hWlp, hSafe⟩ := h args mem hPre
    exact ⟨fuelSafe, wpOutcomeV2026_iff_execOutcomeV2026.mp
      (wpStateV2026_of_wlp_and_safety_le hLe hWlp hSafe)⟩)

/-- Whole-function panic-forbidding stateful `StatefulVerificationResult`
(`mirNormalPost`) from an asymmetric-fuel two-pass derivation
(`{propext, Quot.sound}` only). -/
theorem verifyStatefulMirNoPanic_of_wlp_and_safety_le (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ fuelSafe fuelWlp : Nat,
        fuelSafe ≤ fuelWlp ∧
        wlpOutcomeV2026 c.body (mirNormalPost (c.post args mem))
          (fun _ => True) fuelWlp
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees) ∧
        wpStateV2026 c.body fuelSafe
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (fun _ => True)) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_v2026Exec c (fun args mem hPre => by
    let ⟨fuelSafe, _, hLe, hWlp, hSafe⟩ := h args mem hPre
    exact ⟨fuelSafe, wpOutcomeV2026_iff_execOutcomeV2026.mp
      (wpStateV2026_of_wlp_and_safety_le hLe hWlp hSafe)⟩)

/-- Whole-function total-correctness `TotalVerificationResult`
(`mirNormalPost`) from an asymmetric-fuel two-pass derivation. -/
theorem verifyTotalMir_of_wlp_and_safety_le (c : TotalClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ fuelSafe fuelWlp : Nat,
        fuelSafe ≤ fuelWlp ∧
        wlpOutcomeV2026 c.body (mirNormalPost (c.post args mem))
          (fun _ => True) fuelWlp
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees) ∧
        wpStateV2026 c.body fuelSafe
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (fun _ => True)) :
    TotalVerificationResult c :=
  verifyTotalMir_of_v2026Exec c (fun args mem hPre => by
    let ⟨fuelSafe, _, hLe, hWlp, hSafe⟩ := h args mem hPre
    exact ⟨fuelSafe, wpOutcomeV2026_iff_execOutcomeV2026.mp
      (wpStateV2026_of_wlp_and_safety_le hLe hWlp hSafe)⟩)

/-! ## Part III: Minimum-Budget Conjunctive Composition (`compNatMin`) -/

/-- Re-export of computable minimum `compNatMin` from `Framework.StepWp`. -/
abbrev compNatMin : Nat → Nat → Nat := Anneal.Framework.StepWp.compNatMin

/-- Successor reduction for `compNatMin`. -/
theorem compNatMin_succ_succ (a b : Nat) :
    compNatMin (a + 1) (b + 1) = compNatMin a b + 1 :=
  Anneal.Framework.StepWp.compNatMin_succ_succ a b

/-- Left lower-bound law `compNatMin a b ≤ a`. -/
theorem compNatMin_le_left (a b : Nat) : compNatMin a b ≤ a :=
  Anneal.Framework.StepWp.compNatMin_le_left a b

/-- Right lower-bound law `compNatMin a b ≤ b`. -/
theorem compNatMin_le_right (a b : Nat) : compNatMin a b ≤ b :=
  Anneal.Framework.StepWp.compNatMin_le_right a b

/-- Conjunctive composition for `wlpOutcomeV2026` at `compNatMin n₁ n₂`. -/
theorem wlpOutcomeV2026_conj {body : CapturedMir}
    {d₁ d₂ : MirOutcome → Prop} {f₁ f₂ : V2026StepFault → Prop}
    {n₁ n₂ : Nat} {s : MachineState}
    (h₁ : wlpOutcomeV2026 body d₁ f₁ n₁ s)
    (h₂ : wlpOutcomeV2026 body d₂ f₂ n₂ s) :
    wlpOutcomeV2026 body (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
      (compNatMin n₁ n₂) s :=
  wlpStepPred_conj h₁ h₂

/-- Conjunctive composition for deterministic `execWlpOutcomeV2026` at
`compNatMin n₁ n₂`. -/
theorem execWlpOutcomeV2026_conj {body : CapturedMir}
    {d₁ d₂ : MirOutcome → Prop} {f₁ f₂ : V2026StepFault → Prop}
    {n₁ n₂ : Nat} {s : MachineState}
    (h₁ : execWlpOutcomeV2026 body d₁ f₁ n₁ s)
    (h₂ : execWlpOutcomeV2026 body d₂ f₂ n₂ s) :
    execWlpOutcomeV2026 body (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
      (compNatMin n₁ n₂) s :=
  execWlpStepPred_conj h₁ h₂

/-- Conjunctive composition for `wpOutcomeV2026` at `compNatMin n₁ n₂`. -/
theorem wpOutcomeV2026_conj {body : CapturedMir}
    {d₁ d₂ : MirOutcome → Prop} {f₁ f₂ : V2026StepFault → Prop}
    {n₁ n₂ : Nat} {s : MachineState}
    (h₁ : wpOutcomeV2026 body d₁ f₁ n₁ s)
    (h₂ : wpOutcomeV2026 body d₂ f₂ n₂ s) :
    wpOutcomeV2026 body (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
      (compNatMin n₁ n₂) s :=
  wpStepPred_conj h₁ h₂

/-- Conjunctive composition for deterministic `execStepOutcome` over an
arbitrary step function at `compNatMin n₁ n₂`. -/
theorem execStepOutcome_conj {S Out F : Type} {step : S → StepResult S Out F}
    {d₁ d₂ : Out → Prop} {f₁ f₂ : F → Prop}
    {n₁ n₂ : Nat} {s : S}
    (h₁ : execStepOutcome step d₁ f₁ n₁ s)
    (h₂ : execStepOutcome step d₂ f₂ n₂ s) :
    execStepOutcome step (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
      (compNatMin n₁ n₂) s :=
  execStepPred_conj h₁ h₂

/-- Conjunctive composition for `wpProgV2026` at `compNatMin n₁ n₂`. -/
theorem wpProgV2026_conj {body : CapturedMir} {n₁ n₂ : Nat}
    {args : List Value} {callees : List CapturedMir}
    {post₁ post₂ : MirOutcome → Prop}
    (h₁ : wpProgV2026 body n₁ args callees post₁)
    (h₂ : wpProgV2026 body n₂ args callees post₂) :
    wpProgV2026 body (compNatMin n₁ n₂) args callees
      (fun out => post₁ out ∧ post₂ out) :=
  wpStepPred_mono (fun _ _ h => h) (fun _ _ h => h.1)
    (wpOutcomeV2026_conj h₁ h₂)

/-- Conjunctive composition for `wlpProgV2026` at `compNatMin n₁ n₂`. -/
theorem wlpProgV2026_conj {body : CapturedMir} {n₁ n₂ : Nat}
    {args : List Value} {callees : List CapturedMir}
    {post₁ post₂ : MirOutcome → Prop}
    (h₁ : wlpProgV2026 body n₁ args callees post₁)
    (h₂ : wlpProgV2026 body n₂ args callees post₂) :
    wlpProgV2026 body (compNatMin n₁ n₂) args callees
      (fun out => post₁ out ∧ post₂ out) :=
  wlpOutcomeV2026_mono (fun _ h => h) (fun _ _ => trivial)
    (wlpOutcomeV2026_conj h₁ h₂)

/-- Conjunctive composition for strict fault-forbidding `wlpProgStrictV2026`
at `compNatMin n₁ n₂`. -/
theorem wlpProgStrictV2026_conj {body : CapturedMir} {n₁ n₂ : Nat}
    {args : List Value} {callees : List CapturedMir}
    {post₁ post₂ : MirOutcome → Prop}
    (h₁ : wlpProgStrictV2026 body n₁ args callees post₁)
    (h₂ : wlpProgStrictV2026 body n₂ args callees post₂) :
    wlpProgStrictV2026 body (compNatMin n₁ n₂) args callees
      (fun out => post₁ out ∧ post₂ out) :=
  wlpOutcomeV2026_mono (fun _ h => h) (fun _ h => h.1)
    (wlpOutcomeV2026_conj h₁ h₂)

/-- Conjunctive composition for deterministic `execUntil` sharing a checkpoint
predicate `stop` at `compNatMin n₁ n₂`. -/
theorem execUntil_conj_same_stop {S Out F : Type}
    {step : S → StepResult S Out F} {stop : S → Prop}
    {d₁ d₂ : Out → Prop} {f₁ f₂ : F → Prop}
    {n₁ n₂ : Nat} {s : S}
    (h₁ : execUntil step stop d₁ f₁ n₁ s)
    (h₂ : execUntil step stop d₂ f₂ n₂ s) :
    execUntil step stop (fun o => d₁ o ∧ d₂ o) (fun k => f₁ k ∧ f₂ k)
      (compNatMin n₁ n₂) s :=
  execUntilPred_conj_same_stop h₁ h₂

/-- Conjunctive composition for `wpUntil` sharing a checkpoint predicate `stop`
at `compNatMin n₁ n₂`. -/
theorem wpUntil_conj_same_stop {S Out F C : Type}
    {validChoice : S → C → Prop} {step : C → S → StepResult S Out F}
    {stop : S → Prop} {d₁ d₂ : Out → Prop} {f₁ f₂ : F → Prop} :
    ∀ {n₁ n₂ : Nat} {s : S},
      wpUntil validChoice step stop d₁ f₁ n₁ s →
      wpUntil validChoice step stop d₂ f₂ n₂ s →
      wpUntil validChoice step stop (fun o => d₁ o ∧ d₂ o)
        (fun k => f₁ k ∧ f₂ k) (compNatMin n₁ n₂) s
  | 0, _, _, h₁, _ => wpUntilPred_stop (wpUntilPred_zero_iff.mp h₁)
  | _ + 1, 0, _, _, h₂ => wpUntilPred_stop (wpUntilPred_zero_iff.mp h₂)
  | n₁ + 1, n₂ + 1, s, h₁, h₂ => by
    rw [compNatMin_succ_succ]
    cases wpUntilPred_succ_iff.mp h₁ with
    | inl hStop => exact wpUntilPred_stop hStop
    | inr hStep₁ =>
      cases wpUntilPred_succ_iff.mp h₂ with
      | inl hStop => exact wpUntilPred_stop hStop
      | inr hStep₂ =>
        refine wpUntilPred_succ_iff.mpr (Or.inr ⟨hStep₁.1, fun c hc => ?_⟩)
        have hc₁ := hStep₁.2 c hc
        have hc₂ := hStep₂.2 c hc
        cases hEval : step c s with
        | step st' =>
          rw [hEval] at hc₁ hc₂
          exact wpUntil_conj_same_stop hc₁ hc₂
        | done out =>
          rw [hEval] at hc₁ hc₂
          exact ⟨hc₁, hc₂⟩
        | fault k =>
          rw [hEval] at hc₁ hc₂
          exact ⟨hc₁, hc₂⟩

/-! ## Part IV: Productive State-Transition Divergence Certificates -/

/-- Infinite `.step` transition trace witness for `v2026Step body` starting
from `s`. -/
def DivergesV2026 (body : CapturedMir) (s : MachineState) : Prop :=
  ∃ trace : Nat → MachineState,
    trace 0 = s ∧
    ∀ n : Nat, v2026Step body (trace n) = .step (trace (n + 1))

/-- Every `DivergesV2026` witness refutes `execStepOutcome (v2026Step body)`
for every finite fuel budget and every `onDone` / `onFault` predicate. -/
theorem not_execStepOutcome_of_divergesV2026 {body : CapturedMir}
    {s : MachineState} (hDiv : DivergesV2026 body s)
    (onDone : MirOutcome → Prop) (onFault : V2026StepFault → Prop)
    (fuel : Nat) :
    ¬ execStepOutcome (v2026Step body) onDone onFault fuel s := by
  intro hExec
  let ⟨trace, hTr0, hSteps⟩ := hDiv
  rw [← hTr0] at hExec
  exact not_infinite_trace_of_execStepPred trace hExec hSteps

/-- Every `DivergesV2026` witness refutes `wpOutcomeV2026` at every fuel. -/
theorem not_wpOutcomeV2026_of_divergesV2026 {body : CapturedMir}
    {s : MachineState} (hDiv : DivergesV2026 body s)
    (onDone : MirOutcome → Prop) (onFault : V2026StepFault → Prop)
    (fuel : Nat) :
    ¬ wpOutcomeV2026 body onDone onFault fuel s :=
  fun hWp =>
    not_execStepOutcome_of_divergesV2026 hDiv onDone onFault fuel
      (wpOutcomeV2026_iff_execOutcomeV2026.mp hWp)

private theorem not_wpMirSym_of_infinite_v2026Step {body : CapturedMir}
    {post : MirOutcome → Prop} (trace : Nat → MachineState)
    (hSteps : ∀ n : Nat, v2026Step body (trace n) = .step (trace (n + 1))) :
    ∀ (fuel : Nat) (n : Nat), ¬ wpMirSym fuel body (trace n) post
  | 0, _, h => h
  | fuel + 1, n, h =>
    not_wpMirSym_of_infinite_v2026Step trace hSteps fuel (n + 1)
      ((wpMirSym_succ_of_v2026Step (hSteps n)).mp h)

/-- Every `DivergesV2026` witness directly refutes unmodified
`Anneal.MirFuelFree.MirWpConverges` for every postcondition `post`. -/
theorem not_mirWpConverges_of_divergesV2026 {body : CapturedMir}
    {s : MachineState} (hDiv : DivergesV2026 body s)
    (post : MirOutcome → Prop) :
    ¬ MirWpConverges body s post := by
  intro ⟨fuel, hWp⟩
  let ⟨trace, hTr0, hSteps⟩ := hDiv
  rw [← hTr0] at hWp
  exact not_wpMirSym_of_infinite_v2026Step trace hSteps fuel 0 hWp

/-- Constructive productive step witness for `body`: every state satisfying
`inv` steps deterministically under `v2026Step body` to `next s`, which again
satisfies `inv`. -/
structure ProductiveStepWitness (body : CapturedMir)
    (next : MachineState → MachineState) (inv : MachineState → Prop) : Prop where
  stepOk : ∀ s : MachineState, inv s → v2026Step body s = .step (next s)
  preserves : ∀ s : MachineState, inv s → inv (next s)

/-- Iterates `next` `n` times starting from `s₀` via `@Nat.rec`. -/
def iterMachineState (next : MachineState → MachineState)
    (s₀ : MachineState) (n : Nat) : MachineState :=
  @Nat.rec (fun _ => MachineState) s₀ (fun _ st => next st) n

private theorem iterMachineState_inv {body : CapturedMir}
    {next : MachineState → MachineState} {inv : MachineState → Prop}
    (hw : ProductiveStepWitness body next inv) {s₀ : MachineState}
    (h₀ : inv s₀) :
    ∀ n : Nat, inv (iterMachineState next s₀ n)
  | 0 => h₀
  | n + 1 => hw.preserves (iterMachineState next s₀ n)
      (iterMachineState_inv hw h₀ n)

/-- Constructive `DivergesV2026` certificate from a `ProductiveStepWitness`
using `@Nat.rec` (`0` classical choice). -/
theorem divergesV2026_of_productiveWitness {body : CapturedMir}
    {next : MachineState → MachineState} {inv : MachineState → Prop}
    {s₀ : MachineState} (hInv₀ : inv s₀)
    (hw : ProductiveStepWitness body next inv) :
    DivergesV2026 body s₀ :=
  ⟨iterMachineState next s₀, rfl, fun n =>
    hw.stepOk (iterMachineState next s₀ n) (iterMachineState_inv hw hInv₀ n)⟩

/-- Any state satisfying a `ProductiveStepWitness` invariant satisfies
`wlpOutcomeV2026` for every finite `fuel` and every `onDone` / `onFault`
predicate (confirming that `wlpOutcomeV2026` alone is partial correctness and
must be paired with termination/safety for total adequacy). -/
theorem wlpOutcomeV2026_of_productiveWitness {body : CapturedMir}
    {next : MachineState → MachineState} {inv : MachineState → Prop}
    (hw : ProductiveStepWitness body next inv)
    (onDone : MirOutcome → Prop) (onFault : V2026StepFault → Prop) :
    ∀ (fuel : Nat) {s : MachineState}, inv s →
      wlpOutcomeV2026 body onDone onFault fuel s
  | 0, _, _ => trivial
  | fuel + 1, s, hs =>
    wlpOutcomeV2026_step_eq (hw.stepOk s hs)
      (wlpOutcomeV2026_of_productiveWitness hw onDone onFault fuel
        (hw.preserves s hs))

/-! ## Part V: Logarithmic Binary-Doubling Fuel (`pow2Fuel`, `wpPow2Cont`, `execPow2Cont`) -/

/-- Exact power-of-two fuel count `2^k` computed via `@Nat.rec` doubling. -/
def pow2Fuel (k : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => ih + ih) k

/-- `pow2Fuel (k + 1) = pow2Fuel k + pow2Fuel k`. -/
theorem pow2Fuel_succ (k : Nat) :
    pow2Fuel (k + 1) = pow2Fuel k + pow2Fuel k :=
  rfl

/-- Exact arithmetic identity `pow2Fuel k = 2 ^ k` (`[]` zero axioms). -/
theorem pow2Fuel_eq_pow2 : ∀ k : Nat, pow2Fuel k = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    rw [pow2Fuel_succ, Nat.pow_succ, Nat.mul_two, pow2Fuel_eq_pow2 k]

/-- Continuation-passing singleton-choice WP executing up to `2^k` `V2026_06_01`
steps in recursion depth `k`, handing any surviving state after `2^k` steps to
`cont`. -/
def wpPow2Cont (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (k : Nat) (cont : MachineState → Prop)
    (s : MachineState) : Prop :=
  @Nat.rec (fun _ => (MachineState → Prop) → MachineState → Prop)
    (fun c st =>
      (∃ c₀ : Unit, c₀ = ()) ∧
      ∀ ch : Unit, ch = () →
        match v2026Step body st with
        | .step st' => c st'
        | .done out => onDone out
        | .fault fk => onFault fk)
    (fun _ ih c st => ih (fun st' => ih c st') st)
    k cont s

/-- Continuation-passing deterministic fast-path WP executing up to `2^k`
`V2026_06_01` steps in recursion depth `k`. -/
def execPow2Cont (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (k : Nat) (cont : MachineState → Prop)
    (s : MachineState) : Prop :=
  @Nat.rec (fun _ => (MachineState → Prop) → MachineState → Prop)
    (fun c st =>
      match v2026Step body st with
      | .step st' => c st'
      | .done out => onDone out
      | .fault fk => onFault fk)
    (fun _ ih c st => ih (fun st' => ih c st') st)
    k cont s

/-- Binary-doubling WP requiring termination within `2^k` steps
(`cont := fun _ => False`). -/
abbrev wpPow2 (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (k : Nat) (s : MachineState) : Prop :=
  wpPow2Cont body onDone onFault k (fun _ => False) s

/-- Fault-forbidding state WP with binary-doubling fuel `2^k`. -/
abbrev wpStatePow2 (body : CapturedMir) (k : Nat) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  wpPow2 body post (fun _ => False) k s

/-- Whole-function fault-forbidding WP with binary-doubling fuel `2^k`. -/
def wpProgPow2 (body : CapturedMir) (k : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  wpStatePow2 body k (initMachineStateWithCallees body args callees) post

/-- Deterministic binary-doubling WP requiring termination within `2^k`
steps. -/
abbrev execPow2 (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (k : Nat) (s : MachineState) : Prop :=
  execPow2Cont body onDone onFault k (fun _ => False) s

/-- Deterministic fault-forbidding state WP with budget `2^k`. -/
abbrev execStatePow2 (body : CapturedMir) (k : Nat) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  execPow2 body post (fun _ => False) k s

/-- Deterministic whole-function WP with binary-doubling budget `2^k`. -/
def execProgPow2 (body : CapturedMir) (k : Nat) (args : List Value)
    (callees : List CapturedMir) (post : MirOutcome → Prop) : Prop :=
  execStatePow2 body k (initMachineStateWithCallees body args callees) post

/-- Exact doubling identity for `wpPow2Cont`. -/
theorem wpPow2Cont_succ (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (k : Nat) (cont : MachineState → Prop)
    (s : MachineState) :
    wpPow2Cont body onDone onFault (k + 1) cont s ↔
      wpPow2Cont body onDone onFault k
        (wpPow2Cont body onDone onFault k cont) s :=
  Iff.rfl

/-- Covariant monotonicity of `wpPow2Cont` in `onDone`, `onFault`, and
`cont`. -/
theorem wpPow2Cont_mono {body : CapturedMir}
    {d₁ d₂ : MirOutcome → Prop} {f₁ f₂ : V2026StepFault → Prop}
    (hD : ∀ out, d₁ out → d₂ out) (hF : ∀ fk, f₁ fk → f₂ fk) :
    ∀ {k : Nat} {c₁ c₂ : MachineState → Prop},
      (∀ st, c₁ st → c₂ st) →
      ∀ {s : MachineState},
        wpPow2Cont body d₁ f₁ k c₁ s →
        wpPow2Cont body d₂ f₂ k c₂ s
  | 0, _, _, hC, s, h => by
    refine ⟨h.1, fun ch hch => ?_⟩
    have hStep := h.2 ch hch
    cases hEv : v2026Step body s with
    | step st' =>
      rw [hEv] at hStep
      exact hC st' hStep
    | done out =>
      rw [hEv] at hStep
      exact hD out hStep
    | fault fk =>
      rw [hEv] at hStep
      exact hF fk hStep
  | _ + 1, _, _, hC, _, h =>
    wpPow2Cont_mono hD hF
      (fun _ hInner => wpPow2Cont_mono hD hF hC hInner) h

/-- Exact equivalence between `wpPow2Cont` and deterministic `execPow2Cont`. -/
theorem wpPow2Cont_iff_execPow2Cont {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop} :
    ∀ {k : Nat} {c₁ c₂ : MachineState → Prop},
      (∀ st, c₁ st ↔ c₂ st) →
      ∀ {s : MachineState},
        wpPow2Cont body onDone onFault k c₁ s ↔
        execPow2Cont body onDone onFault k c₂ s
  | 0, c₁, c₂, hC, s => by
    change ((∃ c₀ : Unit, c₀ = ()) ∧
        ∀ ch : Unit, ch = () →
          match v2026Step body s with
          | .step st' => c₁ st'
          | .done out => onDone out
          | .fault fk => onFault fk) ↔
      (match v2026Step body s with
        | .step st' => c₂ st'
        | .done out => onDone out
        | .fault fk => onFault fk)
    refine ⟨?_, ?_⟩
    · intro h
      have h0 := h.2 () rfl
      cases hEv : v2026Step body s with
      | step st' =>
        rw [hEv] at h0
        exact (hC st').mp h0
      | done out =>
        rw [hEv] at h0
        exact h0
      | fault fk =>
        rw [hEv] at h0
        exact h0
    · intro h
      refine ⟨⟨(), rfl⟩, fun ch hch => ?_⟩
      subst hch
      cases hEv : v2026Step body s with
      | step st' =>
        rw [hEv] at h
        exact (hC st').mpr h
      | done out =>
        rw [hEv] at h
        exact h
      | fault fk =>
        rw [hEv] at h
        exact h
  | _ + 1, _, _, hC, _ =>
    wpPow2Cont_iff_execPow2Cont
      (fun _ => wpPow2Cont_iff_execPow2Cont hC)

/-- Lift deterministic `execPow2` into `wpPow2`. -/
theorem wpPow2_of_execPow2 {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {k : Nat} {s : MachineState} (h : execPow2 body onDone onFault k s) :
    wpPow2 body onDone onFault k s :=
  (wpPow2Cont_iff_execPow2Cont (fun _ => Iff.rfl)).mpr h

/-- Lift deterministic `execProgPow2` into `wpProgPow2`. -/
theorem wpProgPow2_of_execProgPow2 {body : CapturedMir} {k : Nat}
    {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop} (h : execProgPow2 body k args callees post) :
    wpProgPow2 body k args callees post :=
  wpPow2_of_execPow2 h

private def execStepsCont (body : CapturedMir) (onDone : MirOutcome → Prop)
    (onFault : V2026StepFault → Prop) (n : Nat) (cont : MachineState → Prop)
    (s : MachineState) : Prop :=
  @Nat.rec (fun _ => (MachineState → Prop) → MachineState → Prop)
    (fun c st => c st)
    (fun _ ih c st =>
      match v2026Step body st with
      | .step st' => ih c st'
      | .done out => onDone out
      | .fault fk => onFault fk)
    n cont s

private theorem execStepsCont_add {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop} :
    ∀ {m n : Nat} {cont : MachineState → Prop} {s : MachineState},
      execStepsCont body onDone onFault (m + n) cont s ↔
      execStepsCont body onDone onFault m
        (execStepsCont body onDone onFault n cont) s
  | 0, _, _, _ => by
    rw [Nat.zero_add]
    exact Iff.rfl
  | m + 1, n, cont, s => by
    rw [Nat.succ_add]
    change (match v2026Step body s with
      | .step st' => execStepsCont body onDone onFault (m + n) cont st'
      | .done out => onDone out
      | .fault fk => onFault fk) ↔
      (match v2026Step body s with
      | .step st' => execStepsCont body onDone onFault m
          (execStepsCont body onDone onFault n cont) st'
      | .done out => onDone out
      | .fault fk => onFault fk)
    cases v2026Step body s with
    | step st' => exact execStepsCont_add
    | done _ => exact Iff.rfl
    | fault _ => exact Iff.rfl

private theorem execStepsCont_congr {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop} :
    ∀ {n : Nat} {c₁ c₂ : MachineState → Prop},
      (∀ st, c₁ st ↔ c₂ st) →
      ∀ {s : MachineState},
        execStepsCont body onDone onFault n c₁ s ↔
        execStepsCont body onDone onFault n c₂ s
  | 0, _, _, hC, s => hC s
  | n + 1, c₁, c₂, hC, s => by
    change (match v2026Step body s with
      | .step st' => execStepsCont body onDone onFault n c₁ st'
      | .done out => onDone out
      | .fault fk => onFault fk) ↔
      (match v2026Step body s with
      | .step st' => execStepsCont body onDone onFault n c₂ st'
      | .done out => onDone out
      | .fault fk => onFault fk)
    cases v2026Step body s with
    | step st' => exact execStepsCont_congr hC
    | done _ => exact Iff.rfl
    | fault _ => exact Iff.rfl

private theorem execPow2Cont_iff_execStepsCont {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop} :
    ∀ {k : Nat} {cont : MachineState → Prop} {s : MachineState},
      execPow2Cont body onDone onFault k cont s ↔
      execStepsCont body onDone onFault (pow2Fuel k) cont s
  | 0, _, _ => Iff.rfl
  | k + 1, _, _ => by
    rw [pow2Fuel_succ]
    refine Iff.trans (execPow2Cont_iff_execStepsCont (k := k)) ?_
    refine Iff.trans
      (execStepsCont_congr (fun _ => execPow2Cont_iff_execStepsCont (k := k))) ?_
    exact execStepsCont_add.symm

private theorem execStepsCont_false_iff_execStepOutcome {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop} :
    ∀ {n : Nat} {s : MachineState},
      execStepsCont body onDone onFault n (fun _ => False) s ↔
      execStepOutcome (v2026Step body) onDone onFault n s
  | 0, _ => Iff.rfl
  | n + 1, s => by
    dsimp only [execStepOutcome]
    rw [execStepPred_succ_iff]
    change (match v2026Step body s with
      | .step st' => execStepsCont body onDone onFault n (fun _ => False) st'
      | .done out => onDone out
      | .fault fk => onFault fk) ↔ _
    cases v2026Step body s with
    | step st' => exact execStepsCont_false_iff_execStepOutcome
    | done _ => exact Iff.rfl
    | fault _ => exact Iff.rfl

/-- Exact equivalence between depth-`k` deterministic binary-doubling `execPow2`
and linear `execStepOutcome (v2026Step body)` at fuel `pow2Fuel k` (`2^k`). -/
theorem execPow2_iff_execStepOutcome {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {k : Nat} {s : MachineState} :
    execPow2 body onDone onFault k s ↔
      execStepOutcome (v2026Step body) onDone onFault (pow2Fuel k) s :=
  Iff.trans execPow2Cont_iff_execStepsCont execStepsCont_false_iff_execStepOutcome

/-- Exact equivalence between depth-`k` binary-doubling `wpPow2` and linear
`execStepOutcome (v2026Step body)` at fuel `pow2Fuel k` (`2^k`). -/
theorem wpPow2_iff_execStepOutcome {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {k : Nat} {s : MachineState} :
    wpPow2 body onDone onFault k s ↔
      execStepOutcome (v2026Step body) onDone onFault (pow2Fuel k) s :=
  Iff.trans (wpPow2Cont_iff_execPow2Cont (fun _ => Iff.rfl))
    execPow2_iff_execStepOutcome

/-- Exact equivalence between depth-`k` binary-doubling `wpPow2` and
`wpOutcomeV2026` at fuel `pow2Fuel k`. -/
theorem wpPow2_iff_wpOutcomeV2026 {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {k : Nat} {s : MachineState} :
    wpPow2 body onDone onFault k s ↔
      wpOutcomeV2026 body onDone onFault (pow2Fuel k) s :=
  Iff.trans wpPow2_iff_execStepOutcome wpOutcomeV2026_iff_execOutcomeV2026.symm

/-- Exact equivalence between whole-function binary-doubling `wpProgPow2` at
depth `k` and `wpProgV2026` at fuel `pow2Fuel k`. -/
theorem wpProgPow2_iff_wpProgV2026 {body : CapturedMir} {k : Nat}
    {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop} :
    wpProgPow2 body k args callees post ↔
      wpProgV2026 body (pow2Fuel k) args callees post :=
  wpPow2_iff_wpOutcomeV2026

/-- Lift a 1-step `wpPow2Cont` invariant (`k = 0`) to depth `k` (`2^k` steps)
in $O(k)$ recursive-doubling steps without unary induction over
`pow2Fuel k`. -/
theorem wpPow2Cont_inv {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {inv : MachineState → Prop}
    (hStep : ∀ s : MachineState, inv s →
      wpPow2Cont body onDone onFault 0 inv s) :
    ∀ (k : Nat) {s : MachineState}, inv s →
      wpPow2Cont body onDone onFault k inv s
  | 0, _, hs => hStep _ hs
  | k + 1, _, hs =>
    wpPow2Cont_mono (fun _ h => h) (fun _ h => h)
      (fun _ hMid => wpPow2Cont_inv hStep k hMid)
      (wpPow2Cont_inv hStep k hs)

private theorem execWlp_of_execStepsCont {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop} :
    ∀ {n : Nat} {cont : MachineState → Prop} {s : MachineState},
      execStepsCont body onDone onFault n cont s →
      execWlpOutcomeV2026 body onDone onFault n s
  | 0, _, _, _ => trivial
  | _ + 1, _, s, h => by
    change (match v2026Step body s with
      | .step st' => execStepsCont body onDone onFault _ _ st'
      | .done out => onDone out
      | .fault fk => onFault fk) at h
    dsimp only [execWlpOutcomeV2026, execWlpStepOutcome]
    rw [execWlpStepPred_succ_iff]
    cases hEv : v2026Step body s with
    | step st' =>
      rw [hEv] at h
      exact execWlp_of_execStepsCont h
    | done out =>
      rw [hEv] at h
      exact h
    | fault fk =>
      rw [hEv] at h
      exact h

/-- Any depth-`k` `wpPow2Cont` derivation (for any continuation `cont`) implies
bounded partial correctness `wlpOutcomeV2026` across all `pow2Fuel k` (`2^k`)
steps. -/
theorem wlpOutcomeV2026_of_wpPow2Cont {body : CapturedMir}
    {onDone : MirOutcome → Prop} {onFault : V2026StepFault → Prop}
    {k : Nat} {cont : MachineState → Prop} {s : MachineState}
    (h : wpPow2Cont body onDone onFault k cont s) :
    wlpOutcomeV2026 body onDone onFault (pow2Fuel k) s :=
  wlpOutcomeV2026_of_execWlpOutcomeV2026
    (execWlp_of_execStepsCont
      (execPow2Cont_iff_execStepsCont.mp
        ((wpPow2Cont_iff_execPow2Cont (fun _ => Iff.rfl)).mp h)))

/-- Adequacy of `wpStatePow2` directly into `Anneal.MirFuelFree.MirWpConverges`. -/
theorem mirWpConverges_of_wpPow2 {body : CapturedMir} {k : Nat}
    {s : MachineState} {post : MirOutcome → Prop}
    (h : wpStatePow2 body k s post) :
    MirWpConverges body s post :=
  mirWpConverges_of_v2026Exec (wpPow2_iff_execStepOutcome.mp h)

/-- Adequacy of `wpStatePow2` directly into `MirNoUBTree (mirTree body s)`. -/
theorem mirNoUBTree_of_wpPow2 {body : CapturedMir} {k : Nat}
    {s : MachineState} {post : MirOutcome → Prop}
    (h : wpStatePow2 body k s post) :
    MirNoUBTree (mirTree body s) :=
  mirNoUBTree_of_v2026Exec (wpPow2_iff_execStepOutcome.mp h)

/-- Whole-function stateless `VerificationResult` (`mirSafePost`) from
`wpProgPow2`. -/
theorem verifyMirSafe_of_wpProgPow2 (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ k : Nat,
        wpProgPow2 c.body k args c.callees
          (mirSafePost (fun retVal _ => c.post args retVal))) :
    VerificationResult c :=
  verifyMirSafe_of_v2026Exec c (fun args hPre => by
    let ⟨k, hk⟩ := h args hPre
    exact ⟨pow2Fuel k, wpPow2_iff_execStepOutcome.mp hk⟩)

/-- Whole-function panic-forbidding stateless `VerificationResult`
(`mirNormalPost`) from `wpProgPow2`. -/
theorem verifyMirNoPanic_of_wpProgPow2 (c : Claim)
    (h : ∀ args : List Value, c.pre args →
      ∃ k : Nat,
        wpProgPow2 c.body k args c.callees
          (mirNormalPost (fun retVal _ => c.post args retVal))) :
    VerificationResult c :=
  verifyMirNoPanic_of_v2026Exec c (fun args hPre => by
    let ⟨k, hk⟩ := h args hPre
    exact ⟨pow2Fuel k, wpPow2_iff_execStepOutcome.mp hk⟩)

/-- Whole-function stateful `StatefulVerificationResult` (`mirSafePost`) from
`wpStatePow2` (`{propext, Quot.sound}` only). -/
theorem verifyStatefulMirSafe_of_wpProgPow2 (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ k : Nat,
        wpStatePow2 c.body k
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirSafePost (c.post args mem))) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_v2026Exec c (fun args mem hPre => by
    let ⟨k, hk⟩ := h args mem hPre
    exact ⟨pow2Fuel k, wpPow2_iff_execStepOutcome.mp hk⟩)

/-- Whole-function panic-forbidding stateful `StatefulVerificationResult`
(`mirNormalPost`) from `wpStatePow2` (`{propext, Quot.sound}` only). -/
theorem verifyStatefulMirNoPanic_of_wpProgPow2 (c : StatefulClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ k : Nat,
        wpStatePow2 c.body k
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirNormalPost (c.post args mem))) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_v2026Exec c (fun args mem hPre => by
    let ⟨k, hk⟩ := h args mem hPre
    exact ⟨pow2Fuel k, wpPow2_iff_execStepOutcome.mp hk⟩)

/-- Whole-function total-correctness `TotalVerificationResult` (`mirNormalPost`)
from `wpStatePow2`. -/
theorem verifyTotalMir_of_wpProgPow2 (c : TotalClaim)
    (h : ∀ (args : List Value) (mem : Memory), c.pre args mem →
      ∃ k : Nat,
        wpStatePow2 c.body k
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirNormalPost (c.post args mem))) :
    TotalVerificationResult c :=
  verifyTotalMir_of_v2026Exec c (fun args mem hPre => by
    let ⟨k, hk⟩ := h args mem hPre
    exact ⟨pow2Fuel k, wpPow2_iff_execStepOutcome.mp hk⟩)

/-! ## Part VI: Concrete `V2026_06_01` Non-Vacuity Canaries -/

/-- Minimal 1-block `CapturedMir` whose `bb0` loops forever via `goto 0`. -/
def canaryDivergingMirBody : CapturedMir :=
  { defPath := "Anneal::ConjunctiveWp::canaryDiverging"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := [{ mutability := .mut, ty := u32Ty, debugName := some "_0" }]
    basicBlocks :=
      [ { statements := []
          terminator := { kind := .goto 0, span := "WlpV2026.lean:div:bb0" }
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

/-- Concrete `V2026_06_01` divergence canary: `canaryDivergingMirBody` admits a
constructive `ProductiveStepWitness`, satisfies `DivergesV2026`, refutes
`execStepOutcome` and `MirWpConverges` for all finite fuel/postconditions, and
still satisfies partial-correctness `wlpOutcomeV2026` at every fuel. -/
theorem canary_v2026_diverging_witness (fuel : Nat)
    (post : MirOutcome → Prop) :
    DivergesV2026 canaryDivergingMirBody
      (initMachineState canaryDivergingMirBody []) ∧
    ¬ execStepOutcome (v2026Step canaryDivergingMirBody) post (fun _ => False)
        fuel (initMachineState canaryDivergingMirBody []) ∧
    ¬ MirWpConverges canaryDivergingMirBody
        (initMachineState canaryDivergingMirBody []) post ∧
    wlpOutcomeV2026 canaryDivergingMirBody post (fun _ => False)
      fuel (initMachineState canaryDivergingMirBody []) := by
  let s0 := initMachineState canaryDivergingMirBody []
  have hStepSelf : v2026Step canaryDivergingMirBody s0 = .step s0 := rfl
  have hW : ProductiveStepWitness canaryDivergingMirBody id (fun st => st = s0) :=
    { stepOk := fun st hEq => by subst hEq; exact hStepSelf
      preserves := fun st hEq => hEq }
  have hDiv : DivergesV2026 canaryDivergingMirBody s0 :=
    divergesV2026_of_productiveWitness (inv := fun st => st = s0) rfl hW
  exact ⟨hDiv,
    not_execStepOutcome_of_divergesV2026 hDiv post (fun _ => False) fuel,
    not_mirWpConverges_of_divergesV2026 hDiv post,
    wlpOutcomeV2026_of_productiveWitness hW post (fun _ => False) fuel rfl⟩

/-- Concrete observable-step (`switchInt` -> `.vis (.inr (.inl (.emit _)))`)
canary over `Anneal.MirFuelFree.branchingTracePipelineBody`: exercises
`v2026Step`, binary-doubling `execPow2` (`k = 2`, `2^2 = 4` steps), asymmetric
two-pass `mirWpConverges_of_wlp_and_safety_le` (`fuelSafe = 4 ≤ fuelWlp = 6`),
and `mirNoUBTree_of_v2026Exec`. -/
theorem canary_v2026_branching_emit_and_pow2 :
    let s0 := initMachineState branchingTracePipelineBody
      [.scalar { bits := 7, sizeBytes := 4 }]
    let post : MirOutcome → Prop :=
      fun out => out = .normal
        (.scalar { bits := 7, sizeBytes := 4 }, s0.memory)
    execPow2 branchingTracePipelineBody post (fun _ => False) 2 s0 ∧
    MirWpConverges branchingTracePipelineBody s0 post ∧
    MirNoUBTree (mirTree branchingTracePipelineBody s0) := by
  dsimp only
  let s0 := initMachineState branchingTracePipelineBody
    [.scalar { bits := 7, sizeBytes := 4 }]
  let post : MirOutcome → Prop :=
    fun out => out = .normal
      (.scalar { bits := 7, sizeBytes := 4 }, s0.memory)
  have hPow2 : execPow2 branchingTracePipelineBody post (fun _ => False) 2 s0 :=
    rfl
  have hExec : execStepOutcome (v2026Step branchingTracePipelineBody)
      post (fun _ => False) 4 s0 :=
    execPow2_iff_execStepOutcome.mp hPow2
  have hWlp : wlpOutcomeV2026 branchingTracePipelineBody post
      (fun _ => True) 6 s0 :=
    wlpOutcomeV2026_of_execWlpOutcomeV2026 rfl
  have hSafe : wpStateV2026 branchingTracePipelineBody 4 s0 (fun _ => True) :=
    wpOutcomeV2026_iff_execOutcomeV2026.mpr
      (execStepPred_mono (fun _ _ _ => trivial) (fun _ _ h => h) hExec)
  have hLe : 4 ≤ 6 := Nat.le_succ_of_le (Nat.le_succ 4)
  exact ⟨hPow2,
    mirWpConverges_of_wlp_and_safety_le hLe hWlp hSafe,
    mirNoUBTree_of_v2026Exec hExec⟩

/-- Concrete observable-step soundness canary: the `switchInt` head step of
`branchingTracePipelineBody` is a genuine *visible* `MirObsE` emission
`.vis (.inr (.inl (.emit (.event 7)))) _` (NOT a silent `.tau`), `v2026Step`
maps it to `.step` of the same successor, and `wpMirSym` unfolds across it in
exactly one unit of fuel. -/
theorem canary_v2026_switchInt_observable_vis :
    let s0 := initMachineState branchingTracePipelineBody
      [.scalar { bits := 7, sizeBytes := 4 }]
    let s1 := branchingTraceMidState 7 s0.memory
    stepMirFn branchingTracePipelineBody s0 =
        MirStepNode.emitStep (.event 7) s1 ∧
    (∀ st : MirExecState, stepMirFn branchingTracePipelineBody s0 ≠ .tau st) ∧
    v2026Step branchingTracePipelineBody s0 = .step s1 ∧
    (∀ (fuel : Nat) (post : MirOutcome → Prop),
      wpMirSym (fuel + 1) branchingTracePipelineBody s0 post ↔
        wpMirSym fuel branchingTracePipelineBody s1 post) := by
  dsimp only
  have hEmit : stepMirFn branchingTracePipelineBody
      (initMachineState branchingTracePipelineBody
        [.scalar { bits := 7, sizeBytes := 4 }]) =
      MirStepNode.emitStep (.event 7)
        (branchingTraceMidState 7
          (initMachineState branchingTracePipelineBody
            [.scalar { bits := 7, sizeBytes := 4 }]).memory) := rfl
  refine ⟨hEmit, fun st hTau => ?_, rfl,
    fun _ _ => wpMirSym_succ_of_emitStep hEmit⟩
  rw [hEmit] at hTau
  cases hTau

private def canaryUnreachableMirBody : CapturedMir :=
  { defPath := "Anneal::ConjunctiveWp::canaryUnreachable"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := [{ mutability := .mut, ty := u32Ty, debugName := some "_0" }]
    basicBlocks :=
      [ { statements := []
          terminator := { kind := .unreachable, span := "WlpV2026.lean:ub:bb0" }
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

/-- Concrete canary covering:
1. Faulting `wlpProgV2026` (`onFault := True`) vs strict `wlpProgStrictV2026`
   (`onFault := False`) on `canaryUnreachableMirBody` (confirming relaxed WLP
   cannot imply safety alone while strict WLP refutes UB).
2. `wpPow2Cont_inv` lifting a 1-step invariant to arbitrary depth `k : Nat`
   (`2^k` steps) in `O(k)` on `canaryDivergingMirBody`, plus
   `wlpOutcomeV2026_of_wpPow2Cont`.
3. Choice-free `VerificationResult` via `verifyMirNoPanic_of_wpProgPow2` on
   `branchingTracePipelineBody`. -/
theorem canary_v2026_wlp_strict_pow2_inv_and_verify (k : Nat) :
    wlpProgV2026 canaryUnreachableMirBody 2 [] [] (fun _ => False) ∧
    ¬ wlpProgStrictV2026 canaryUnreachableMirBody 2 [] [] (fun _ => True) ∧
    wlpOutcomeV2026 canaryDivergingMirBody (fun _ => False) (fun _ => False)
      (pow2Fuel k) (initMachineState canaryDivergingMirBody []) ∧
    VerificationResult
      { body := branchingTracePipelineBody
        pre := fun args => args = [.scalar { bits := 7, sizeBytes := 4 }]
        post := fun _ retVal => retVal = .scalar { bits := 7, sizeBytes := 4 } } := by
  have hRelax : wlpProgV2026 canaryUnreachableMirBody 2 [] [] (fun _ => False) :=
    wlpProgV2026_iff_execWlpProgV2026.mpr trivial
  have hStrict : ¬ wlpProgStrictV2026 canaryUnreachableMirBody 2 [] [] (fun _ => True) := by
    intro hS
    exact wlpProgStrictV2026_iff_execWlpProgStrictV2026.mp hS
  let sDiv := initMachineState canaryDivergingMirBody []
  have hStepSelf : v2026Step canaryDivergingMirBody sDiv = .step sDiv := rfl
  have hPowK : wpPow2Cont canaryDivergingMirBody (fun _ => False)
      (fun _ => False) k (fun st => st = sDiv) sDiv := by
    refine wpPow2Cont_inv (inv := fun st => st = sDiv) (fun st hEq => ?_) k rfl
    subst hEq
    refine ⟨⟨(), rfl⟩, fun ch hch => ?_⟩
    subst hch
    rw [hStepSelf]
  have hWlpPowK := wlpOutcomeV2026_of_wpPow2Cont hPowK
  have hVerify : VerificationResult
      { body := branchingTracePipelineBody
        pre := fun args => args = [.scalar { bits := 7, sizeBytes := 4 }]
        post := fun _ retVal => retVal = .scalar { bits := 7, sizeBytes := 4 } } := by
    refine verifyMirNoPanic_of_wpProgPow2 _ (fun args hPre => ?_)
    subst hPre
    exact ⟨2, wpProgPow2_of_execProgPow2 rfl⟩
  exact ⟨hRelax, hStrict, hWlpPowK, hVerify⟩

end Anneal.ConjunctiveWp
