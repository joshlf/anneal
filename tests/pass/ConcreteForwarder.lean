import Trusted
import Anneal.Refinement
import Anneal.Effect
import Anneal.ITree
import Anneal.Pass
import ToyCFG

/-!
Zero-axiom negative controls and `.tau`-erasure separation tests for Layer 2
(`Anneal.Pass` and `ToyCFG`):
1. Self-loop forwarder (`b = c`) rejection by `checkForwarder`.
2. Unflattened chained forwarder (`1 ↦ 2 ↦ 3 ↦ 4`) rejection and
   `¬ ExactPass` proof.
3. True `.tau`-erasure separation (`tauCfgMachine.run entryFwdProg ≠
   tauCfgMachine.run (redirectTauEdges entryFwdProg 0 1)` yet `Eutt` and
   `ExactPass`).
-/

namespace ConcreteForwarder

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Anneal.Refinement
open Anneal.Effect
open Anneal.ITree
open Anneal.Pass
open ToyCFG

private theorem observe_cfgTree (p : CFGProg) (s : Nat) :
    (cfgMachine.tree p s).observe =
      ITreeF.map (cfgMachine.tree p) (cfgStepFn p s) :=
  ITree.observe_cofix (cfgStepFn p) s

/-! ## 1. Self-Loop Forwarder Rejection (`b = c`) -/

def selfLoopProg : CFGProg where
  entry := 0
  blocks
    | 0 => .emitAndGoto 1 1
    | 1 => .forward 1
    | _ => .returnVal 0

def selfLoopCert : ForwarderCert selfLoopProg (redirectEdges selfLoopProg 1 1) where
  b := 1
  c := 1
  eq_redirect := rfl

theorem selfLoop_rejected_by_checker :
    checkForwarder selfLoopProg (redirectEdges selfLoopProg 1 1) selfLoopCert = false :=
  rfl

/-! ## 2. Unflattened Chained Forwarder (`1 ↦ 2 ↦ 3 ↦ 4`) Is Not an `ExactPass` -/

def chainedProg : CFGProg where
  entry := 0
  blocks
    | 0 => .emitAndGoto 5 1
    | 1 => .forward 2
    | 2 => .forward 3
    | 3 => .forward 4
    | _ => .returnVal 42

def chainedCert : ForwarderCert chainedProg (redirectEdges chainedProg 1 2) where
  b := 1
  c := 2
  eq_redirect := rfl

theorem chained_forwarder_rejected_by_checker :
    checkForwarder chainedProg (redirectEdges chainedProg 1 2) chainedCert = false :=
  rfl

private theorem chainedProg_treeSafe : TreeSafe (cfgMachine.run chainedProg) := by
  have h₀ : (cfgMachine.run chainedProg).observe =
      .vis (.inr (.emit 5)) (fun _ => cfgMachine.tree chainedProg 2) := by
    unfold ITreeMachine.run; rw [observe_cfgTree]; rfl
  have h₂ : (cfgMachine.tree chainedProg 2).observe =
      .vis (.inr (.emit 0)) (fun _ => cfgMachine.tree chainedProg 4) := by
    rw [observe_cfgTree]; rfl
  have h₄ : (cfgMachine.tree chainedProg 4).observe = .ret (.normal 42) := by
    rw [observe_cfgTree]; rfl
  intro tr u hru ⟨u', i, k, hsu, hvu, hfi⟩
  cases hru with
  | refl =>
    cases hsu with
    | refl => rw [h₀] at hvu; injection hvu with hi _; subst hi; exact hfi
    | step ht => rw [h₀] at ht; nomatch ht
  | tau ht => rw [h₀] at ht; nomatch ht
  | vis hv₁ _ _ hr₁ =>
    rw [h₀] at hv₁; injection hv₁ with hi₁ hk₁; subst hi₁
    have hk₁_eq := eq_of_heq hk₁; subst hk₁_eq
    cases hr₁ with
    | refl =>
      cases hsu with
      | refl => rw [h₂] at hvu; injection hvu with hi _; subst hi; exact hfi
      | step ht => rw [h₂] at ht; nomatch ht
    | tau ht => rw [h₂] at ht; nomatch ht
    | vis hv₂ _ _ hr₂ =>
      rw [h₂] at hv₂; injection hv₂ with hi₂ hk₂; subst hi₂
      have hk₂_eq := eq_of_heq hk₂; subst hk₂_eq
      cases hr₂ with
      | refl =>
        cases hsu with
        | refl => rw [h₄] at hvu; nomatch hvu
        | step ht => rw [h₄] at ht; nomatch ht
      | tau ht => rw [h₄] at ht; nomatch ht
      | vis hv₃ => rw [h₄] at hv₃; nomatch hv₃

theorem chained_unflattened_forwarder_not_exactPass :
    ¬ ExactPass
        (MachineSemantics cfgMachine cfgProj)
        (MachineSemantics cfgMachine cfgProj)
        id id chainedProg (redirectEdges chainedProg 1 2) := by
  intro hexact
  let p_red := redirectEdges chainedProg 1 2
  have h_red₀ : (cfgMachine.run p_red).observe =
      .vis (.inr (.emit 5)) (fun _ => cfgMachine.tree p_red 3) := by
    unfold ITreeMachine.run; rw [observe_cfgTree]; rfl
  have h_red₃ : (cfgMachine.tree p_red 3).observe = .ret (.normal 42) := by
    rw [observe_cfgTree]; rfl
  have hp_red : MachineSemantics cfgMachine cfgProj p_red ⟨[5], .ret (.normal 42)⟩ :=
    Or.inl ⟨[⟨.inr (.emit 5), PUnit.unit⟩],
      ⟨_, .vis h_red₀ (fun h => h) PUnit.unit (.refl _), h_red₃⟩, rfl⟩
  have hp_orig : MachineSemantics cfgMachine cfgProj chainedProg ⟨[5], .ret (.normal 42)⟩ :=
    hexact.down_refines trivial _ hp_red
  change UBClosedObsPrefixes cfgProj (cfgMachine.run chainedProg) _ at hp_orig
  rw [ubClosedObsPrefixes_eq_of_treeSafe cfgProj chainedProg_treeSafe] at hp_orig
  have h_orig₀ : (cfgMachine.run chainedProg).observe =
      .vis (.inr (.emit 5)) (fun _ => cfgMachine.tree chainedProg 2) := by
    unfold ITreeMachine.run; rw [observe_cfgTree]; rfl
  have h_orig₂ : (cfgMachine.tree chainedProg 2).observe =
      .vis (.inr (.emit 0)) (fun _ => cfgMachine.tree chainedProg 4) := by
    rw [observe_cfgTree]; rfl
  rcases hp_orig with ⟨tr, ⟨u, hru, hur⟩, htr⟩
  cases hru with
  | refl => rw [h_orig₀] at hur; nomatch hur
  | tau ht => rw [h_orig₀] at ht; nomatch ht
  | vis hv₁ _ _ hr₁ =>
    rw [h_orig₀] at hv₁; injection hv₁ with hi₁ hk₁; subst hi₁
    have hk₁_eq := eq_of_heq hk₁; subst hk₁_eq
    cases hr₁ with
    | refl => rw [h_orig₂] at hur; nomatch hur
    | tau ht => rw [h_orig₂] at ht; nomatch ht
    | vis hv₂ =>
      rw [h_orig₂] at hv₂; injection hv₂ with hi₂ _; subst hi₂
      nomatch htr

/-! ## 3. True `.tau`-Erasure Separation (`≠` on `ITree`, `Eutt`, and `ExactPass`) -/

def entryFwdProg : CFGProg where
  entry := 0
  blocks
    | 0 => .forward 1
    | _ => .returnVal 42

theorem tau_forwarder_distinct_trees_yet_eutt_and_exactPass :
    tauCfgMachine.run entryFwdProg ≠
      tauCfgMachine.run (redirectTauEdges entryFwdProg 0 1) ∧
    Eutt
      (tauCfgMachine.run entryFwdProg)
      (tauCfgMachine.run (redirectTauEdges entryFwdProg 0 1)) ∧
    ExactPass
      (MachineSemantics tauCfgMachine cfgProj)
      (MachineSemantics tauCfgMachine cfgProj)
      id id entryFwdProg (redirectTauEdges entryFwdProg 0 1) :=
  ⟨(fun h_eq => by
     have h_obs_l : (tauCfgMachine.run entryFwdProg).observe =
         .tau (tauCfgMachine.tree entryFwdProg 1) := by
       unfold ITreeMachine.run ITreeMachine.tree; rw [ITree.observe_cofix]; rfl
     have h_obs_r : (tauCfgMachine.run (redirectTauEdges entryFwdProg 0 1)).observe =
         .ret (.normal 42) := by
       unfold ITreeMachine.run ITreeMachine.tree; rw [ITree.observe_cofix]; rfl
     have h_abs := h_obs_l.symm.trans ((congrArg ITree.observe h_eq).trans h_obs_r)
     nomatch h_abs),
   tauCfg_eliminateForwarder_eutt entryFwdProg 0 1 (by decide) rfl,
   tauCfg_eliminateForwarder_exact entryFwdProg 0 1 (by decide) rfl⟩

end ConcreteForwarder
