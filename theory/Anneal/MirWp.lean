-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.MirModel
import Trusted.MirSemantics

namespace Anneal.MirWp

open Trusted.MirModel Trusted.MirSemantics

/-!
# Fuel-Bounded Weakest Precondition and Non-Vacuity Canaries (`Anneal.MirWp`)

This module defines the untrusted fuel-bounded weakest-precondition combinators
(`wpOutcomeState`, `wpProg`, `wpFaultProg`) over `Trusted.MirSemantics`, proves
their soundness and productivity claims (`wellFormed_and_spec_of_wp :
WpSoundnessClaim wpProg` and `reaches_fault_and_exclusive_of_wpFault :
WpFaultSoundnessClaim wpFaultProg`), and discharges the Pass 1
$M_{\text{anneal}}$ non-vacuity and parameter-boundary canary claims covering
all three outcome poles, every supported Day 1 statement, rvalue, terminator,
unary and binary operator, and all six integer widths in signed and unsigned
modes. It also provides fuel-bounded segment cut combinators (`wpStepsOutcome`,
`wpSteps`, `wpOutcomeState_mono`, `wpOutcomeState_trans`, `wpState_cut`),
single-body execution certificates (`run`, `Executes`, `SafeFrom`,
`wpState_of_executes`), and block-modular `BlockExec` rules for executions whose
arguments contain universally quantified values.
-/

/-- Unified structural fuel-bounded weakest precondition over `evalStep`. -/
noncomputable def wpOutcomeState (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
      (∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step s' => wpOutcomeState p onDone onFault fuel s'
        | .done out => onDone out
        | .fault k => onFault k

/-- State-level weakest precondition requiring normal termination satisfying
`post` and forbidding all faults (`onFault := fun _ => False`). -/
abbrev wpState (p : Program) (fuel : Nat) (s : State)
    (post : TerminalOut → Prop) : Prop :=
  wpOutcomeState p post (fun _ => False) fuel s

/-- State-level fault verifier requiring every execution path from `s` to
terminate in `.fault expected`. -/
abbrev wpFaultState (p : Program) (fuel : Nat) (s : State)
    (expected : FaultKind) : Prop :=
  wpOutcomeState p (fun _ => False) (fun k => k = expected) fuel s

/-- Whole-program fuel-bounded weakest precondition starting from
`initState p q`. -/
noncomputable def wpProg (p : Program) (fuel : Nat) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => wpState p fuel s₀ post

/-- Whole-program fuel-bounded fault verifier starting from `initState p q`. -/
noncomputable def wpFaultProg (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initState p q with
  | .error k => k = expected
  | .ok s₀ => wpFaultState p fuel s₀ expected

/-- Monotonicity of `wpOutcomeState` in its outcome predicates and fuel
budget. -/
theorem wpOutcomeState_mono {p : Program}
    {onDone₁ onDone₂ : TerminalOut → Prop}
    {onFault₁ onFault₂ : FaultKind → Prop}
    {fuel₁ fuel₂ : Nat} {s : State}
    (h_wp : wpOutcomeState p onDone₁ onFault₁ fuel₁ s)
    (h_done : ∀ out, onDone₁ out → onDone₂ out)
    (h_fault : ∀ k, onFault₁ k → onFault₂ k)
    (h_fuel : fuel₁ ≤ fuel₂) :
    wpOutcomeState p onDone₂ onFault₂ fuel₂ s := by
  induction fuel₁ generalizing fuel₂ s with
  | zero => exact False.elim h_wp
  | succ f₁ ih =>
    cases fuel₂ with
    | zero => exact False.elim (Nat.not_succ_le_zero f₁ h_fuel)
    | succ f₂ =>
      refine ⟨h_wp.1, fun c hc => ?_⟩
      have h_step := h_wp.2 c hc
      cases h_eval : evalStep p c s with
      | step s' =>
        rw [h_eval] at h_step
        exact ih h_step (Nat.le_of_succ_le_succ h_fuel)
      | done out =>
        rw [h_eval] at h_step
        exact h_done out h_step
      | fault k =>
        rw [h_eval] at h_step
        exact h_fault k h_step

/-- Segment weakest precondition: along every valid choice, `s` either reaches
a state satisfying `onMid` after exactly `steps` transitions or terminates
earlier with `.done out` satisfying `onDone out` or `.fault k` satisfying
`onFault k`. Every state before the end of the segment must admit a valid
choice. -/
noncomputable def wpStepsOutcome (p : Program) (onMid : State → Prop)
    (onDone : TerminalOut → Prop) (onFault : FaultKind → Prop) :
    Nat → State → Prop
  | 0, s => onMid s
  | steps + 1, s =>
      (∃ c₀ : Choice, ValidChoice p s c₀) ∧
      ∀ c : Choice, ValidChoice p s c →
        match evalStep p c s with
        | .step s' => wpStepsOutcome p onMid onDone onFault steps s'
        | .done out => onDone out
        | .fault k => onFault k

/-- Fault-free `wpStepsOutcome`: reach `onMid` after exactly `steps`
transitions, or return earlier with an outcome satisfying `post`. -/
abbrev wpSteps (p : Program) (steps : Nat) (s : State)
    (onMid : State → Prop)
    (post : TerminalOut → Prop := fun _ => False) : Prop :=
  wpStepsOutcome p onMid post (fun _ => False) steps s

/-- Monotonicity of `wpStepsOutcome` in its midpoint and terminal predicates. -/
theorem wpStepsOutcome_mono {p : Program}
    {onMid₁ onMid₂ : State → Prop}
    {onDone₁ onDone₂ : TerminalOut → Prop}
    {onFault₁ onFault₂ : FaultKind → Prop}
    {steps : Nat} {s : State}
    (h_seg : wpStepsOutcome p onMid₁ onDone₁ onFault₁ steps s)
    (h_mid : ∀ s', onMid₁ s' → onMid₂ s')
    (h_done : ∀ out, onDone₁ out → onDone₂ out)
    (h_fault : ∀ k, onFault₁ k → onFault₂ k) :
    wpStepsOutcome p onMid₂ onDone₂ onFault₂ steps s := by
  induction steps generalizing s with
  | zero => exact h_mid s h_seg
  | succ k ih =>
    refine ⟨h_seg.1, fun c hc => ?_⟩
    have h_step := h_seg.2 c hc
    cases h_eval : evalStep p c s with
    | step s' =>
      rw [h_eval] at h_step
      exact ih h_step
    | done out =>
      rw [h_eval] at h_step
      exact h_done out h_step
    | fault f =>
      rw [h_eval] at h_step
      exact h_fault f h_step

/-- Transitivity (cut rule) of `wpStepsOutcome` followed by `wpOutcomeState`:
discharge a prefix of `steps` transitions to `onMid`, then continue from any
state satisfying `onMid` with `fuel` steps. -/
theorem wpOutcomeState_trans {p : Program} {onMid : State → Prop}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {steps fuel : Nat} {s : State}
    (h_seg : wpStepsOutcome p onMid onDone onFault steps s)
    (h_cont : ∀ s_mid, onMid s_mid →
      wpOutcomeState p onDone onFault fuel s_mid) :
    wpOutcomeState p onDone onFault (steps + fuel) s := by
  induction steps generalizing s with
  | zero =>
    rw [Nat.zero_add]
    exact h_cont s h_seg
  | succ k ih =>
    rw [Nat.succ_add]
    refine ⟨h_seg.1, fun c hc => ?_⟩
    have h_step := h_seg.2 c hc
    cases h_eval : evalStep p c s with
    | step s' =>
      rw [h_eval] at h_step
      exact ih h_step
    | done out =>
      rw [h_eval] at h_step
      exact h_step
    | fault f =>
      rw [h_eval] at h_step
      exact h_step

/-- Cut `wpState` at an explicitly named intermediate state `s_mid`: if every
valid path from `s` reaches `s_mid` after `steps` fault-free transitions or
returns earlier with `post`, then `wpState p fuel s_mid post` extends to `s`.
Writing `s_mid` with a literal list of local slots lets the continuation start
from a reduced state instead of the nested `setElem?` updates of the prefix. -/
theorem wpState_cut {p : Program} {post : TerminalOut → Prop}
    {steps fuel : Nat} {s s_mid : State}
    (h_seg : wpSteps p steps s (fun s' => s' = s_mid) post)
    (h_cont : wpState p fuel s_mid post) :
    wpState p (steps + fuel) s post := by
  refine wpOutcomeState_trans h_seg (fun s' h_eq => ?_)
  subst h_eq
  exact h_cont

/-- Any state `s₂` reachable from `s₁` preserves `wpOutcomeState` at some
remaining fuel `fuel'`. -/
theorem wpOutcomeState_of_reaches
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s₁ s₂ : State} {fuel : Nat}
    (h_wp : wpOutcomeState p onDone onFault fuel s₁)
    (h_reach : Reaches p s₁ s₂) :
    ∃ fuel', wpOutcomeState p onDone onFault fuel' s₂ := by
  induction h_reach with
  | refl => exact ⟨fuel, h_wp⟩
  | tail _ h_step ih =>
    let ⟨fuel₁, h_wp₁⟩ := ih
    cases fuel₁ with
    | zero => exact False.elim h_wp₁
    | succ fuel₂ =>
      let ⟨c, hc, h_eval⟩ := h_step
      have h_branch := h_wp₁.2 c hc
      rw [h_eval] at h_branch
      exact ⟨fuel₂, h_branch⟩

/-- Prepend a single step `Step p s₁ (.step s₂)` to a reachability chain
`Reaches p s₂ s₃`. -/
theorem Reaches.head {p : Program} {s₁ s₂ s₃ : State}
    (h_first : Step p s₁ (.step s₂))
    (h_rest : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction h_rest with
  | refl => exact Reaches.tail (Reaches.refl s₁) h_first
  | tail _ h_last ih => exact Reaches.tail ih h_last

/-- Every state satisfying `wpOutcomeState` reaches a terminal `.done` or
`.fault` step within `fuel` steps along its witnessed choice path. -/
theorem exists_terminal_of_wpOutcomeState
    {p : Program} {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (h_wp : wpOutcomeState p onDone onFault fuel s) :
    ∃ s_end res, Reaches p s s_end ∧ Step p s_end res ∧
      match res with
      | .step _ => False
      | .done out => onDone out
      | .fault k => onFault k := by
  induction fuel generalizing s with
  | zero => exact False.elim h_wp
  | succ f ih =>
    let ⟨⟨c₀, hc₀⟩, h_all⟩ := h_wp
    have h_step := h_all c₀ hc₀
    cases h_eval : evalStep p c₀ s with
    | step s' =>
      rw [h_eval] at h_step
      let ⟨s_end, res, h_reach, h_term, h_res⟩ := ih h_step
      exact ⟨s_end, res, Reaches.head ⟨c₀, hc₀, h_eval⟩ h_reach, h_term, h_res⟩
    | done out =>
      rw [h_eval] at h_step
      exact ⟨s, .done out, Reaches.refl s, ⟨c₀, hc₀, h_eval⟩, h_step⟩
    | fault k =>
      rw [h_eval] at h_step
      exact ⟨s, .fault k, Reaches.refl s, ⟨c₀, hc₀, h_eval⟩, h_step⟩

/-- Soundness and productivity of `wpProg`: proving `wpProg p fuel q post`
establishes `SatisfiesPost p q post` and the existence of a terminating
execution `Behavior p q out ∧ post out`. -/
theorem wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg := by
  intro p q fuel post h_wp
  unfold wpProg at h_wp
  cases h_init : initState p q with
  | error k =>
    rw [h_init] at h_wp
    exact False.elim h_wp
  | ok s₀ =>
    rw [h_init] at h_wp
    refine ⟨⟨⟨⟨s₀, h_init, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro s h_reach
      let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_reach
      cases fuel' with
      | zero => exact False.elim h_wp'
      | succ f => exact h_wp'.1
    · intro k h_fault
      unfold ReachesResult at h_fault
      rw [h_init] at h_fault
      let ⟨s, h_reach, c, hc, h_eval⟩ := h_fault
      let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_reach
      cases fuel' with
      | zero => exact False.elim h_wp'
      | succ f =>
        have h_b := h_wp'.2 c hc
        rw [h_eval] at h_b
        exact h_b
    · intro out h_beh
      unfold Behavior ReachesResult at h_beh
      rw [h_init] at h_beh
      let ⟨s, h_reach, c, hc, h_eval⟩ := h_beh
      let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_reach
      cases fuel' with
      | zero => exact False.elim h_wp'
      | succ f =>
        have h_b := h_wp'.2 c hc
        rw [h_eval] at h_b
        exact h_b
    · let ⟨s_end, res, h_reach, h_term, h_res⟩ :=
        exists_terminal_of_wpOutcomeState h_wp
      cases res with
      | step _ => exact False.elim h_res
      | fault _ => exact False.elim h_res
      | done out =>
        refine ⟨out, ?_, h_res⟩
        unfold Behavior ReachesResult
        rw [h_init]
        exact ⟨s_end, h_reach, h_term⟩

/-- Soundness and exclusivity of `wpFaultProg`: proving
`wpFaultProg p fuel q expected` establishes
`ReachesResult p q (.fault expected)`, rules out any other fault kind
`k ≠ expected` and any normal terminal outcome `.done out`, and refutes
`WellFormed p q`. -/
theorem reaches_fault_and_exclusive_of_wpFault :
    WpFaultSoundnessClaim wpFaultProg := by
  intro p q fuel expected h_wp
  unfold wpFaultProg at h_wp
  cases h_init : initState p q with
  | error k =>
    rw [h_init] at h_wp
    subst h_wp
    have h_reaches_exp : ReachesResult p q (.fault k) := by
      unfold ReachesResult; rw [h_init]
    refine ⟨h_reaches_exp, ?_, ?_, fun hwf => hwf.2 k h_reaches_exp⟩
    · intro k' h_ne h_res
      unfold ReachesResult at h_res
      rw [h_init] at h_res
      injection h_res with h_eq
      exact h_ne h_eq
    · intro out h_res
      unfold ReachesResult at h_res
      rw [h_init] at h_res
      cases h_res
  | ok s₀ =>
    rw [h_init] at h_wp
    let ⟨s_end, res, h_reach, h_term, h_res⟩ :=
      exists_terminal_of_wpOutcomeState h_wp
    cases res with
    | step _ => exact False.elim h_res
    | done _ => exact False.elim h_res
    | fault k_end =>
      dsimp only at h_res
      subst h_res
      have h_reaches_exp : ReachesResult p q (.fault k_end) := by
        unfold ReachesResult; rw [h_init]; exact ⟨s_end, h_reach, h_term⟩
      refine ⟨h_reaches_exp, ?_, ?_, fun hwf => hwf.2 k_end h_reaches_exp⟩
      · intro k h_ne h_res_k
        unfold ReachesResult at h_res_k
        rw [h_init] at h_res_k
        let ⟨s, h_r, c, hc, h_eval⟩ := h_res_k
        let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_r
        cases fuel' with
        | zero => exact False.elim h_wp'
        | succ f =>
          have h_b := h_wp'.2 c hc
          rw [h_eval] at h_b
          exact h_ne h_b
      · intro out h_res_done
        unfold ReachesResult at h_res_done
        rw [h_init] at h_res_done
        let ⟨s, h_r, c, hc, h_eval⟩ := h_res_done
        let ⟨fuel', h_wp'⟩ := wpOutcomeState_of_reaches h_wp h_r
        cases fuel' with
        | zero => exact False.elim h_wp'
        | succ f =>
          have h_b := h_wp'.2 c hc
          rw [h_eval] at h_b
          exact h_b

/-! ## Concrete Non-Vacuity and Parameter-Boundary Canaries -/

/-- Establish `PositiveCanaryClaim p q expectedRet` from a `wpProg` proof. -/
theorem positiveCanary_of_wp {p : Program} {q : Query} {fuel : Nat}
    {expectedRet : Val}
    (h_wp : wpProg p fuel q (fun out => out = .returned ⟨expectedRet, ⟨[]⟩⟩)) :
    PositiveCanaryClaim p q expectedRet := by
  let ⟨h_sat, out, h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp p q fuel _ h_wp
  subst h_eq
  exact ⟨h_sat.1, h_beh⟩

/-- Establish `NegativeCanaryClaim p q expectedFault otherFault` from a
`wpFaultProg` proof. -/
theorem negativeCanary_of_wpFault {p : Program} {q : Query} {fuel : Nat}
    {expectedFault otherFault : FaultKind}
    (h_ne : otherFault ≠ expectedFault)
    (h_wp : wpFaultProg p fuel q expectedFault) :
    NegativeCanaryClaim p q expectedFault otherFault := by
  let ⟨h_f, h_excl, _, h_nwf⟩ :=
    reaches_fault_and_exclusive_of_wpFault p q fuel expectedFault h_wp
  exact ⟨h_f, h_excl otherFault h_ne, h_nwf⟩

/-- Canary `D1`: `progAddU32` on `(30, 12)` is well-formed and returns `42`. -/
theorem canary_positive_add_anneal : CanaryPositiveAddAnnealClaim := by
  apply positiveCanary_of_wp (fuel := 2)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Canary `D2`: `progEmptyUnitFn` is well-formed and returns `Val.unit`. -/
theorem canary_positive_empty_unit_fn : CanaryPositiveEmptyUnitFnClaim := by
  apply positiveCanary_of_wp (fuel := 1)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Control-flow and statement canary (`nop`, `storageLive`, `storageDead`,
`goto`, and both matched and `otherwise` arms of `switchInt`). -/
theorem canary_positive_stmts_and_cf_anneal :
    CanaryPositiveStmtsAndCfAnnealClaim := by
  constructor
  · apply positiveCanary_of_wp (fuel := 10)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl
  · apply positiveCanary_of_wp (fuel := 10)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl

/-- Unary-operator canary (`UnOp.not` on `bool` and `u8`, `UnOp.neg` on signed
`i8` including wrapping `-INT_MIN == INT_MIN`). -/
theorem canary_positive_unop_anneal : CanaryPositiveUnopAnnealClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl

/-- Binary-operator canary covering every supported `BinOp` variant at boundary
values across unsigned integers, signed integers, shifts, and booleans. -/
theorem canary_positive_all_binops_anneal :
    CanaryPositiveAllBinopsAnnealClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl

/-- Integer-width boundary canary covering all six `IntWidth` variants (`.i8`,
`.i16`, `.i32`, `.i64`, `.i128`, `.isize`) in both unsigned (`MAX + 1 = 0`) and
signed (`INT_MAX + 1 = INT_MIN`) modes. -/
theorem canary_positive_all_int_widths_anneal :
    CanaryPositiveAllIntWidthsAnnealClaim := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl

/-- Canary `D3`: dividing by zero reaches `.fault .undefined` (and not
`.fault .unsupported`) and refutes `WellFormed`. -/
theorem canary_negative_ub_div_zero_anneal :
    CanaryNegativeUbDivZeroAnnealClaim := by
  apply negativeCanary_of_wpFault (fuel := 1) (fun h => FaultKind.noConfusion h)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Canary `D4`: signed `(-128i8) % (-1i8)` reaches `.fault .undefined` (and
not `.fault .unsupported`) and refutes `WellFormed`. -/
theorem canary_negative_ub_signed_rem_overflow_i8 :
    CanaryNegativeUbSignedRemOverflowI8Claim := by
  apply negativeCanary_of_wpFault (fuel := 1) (fun h => FaultKind.noConfusion h)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Canary `D5`: executing `.unsupported` reaches `.fault .unsupported` (and
not `.fault .undefined`) and refutes `WellFormed`. -/
theorem canary_negative_unsupported_anneal :
    CanaryNegativeUnsupportedAnnealClaim := by
  apply negativeCanary_of_wpFault (fuel := 1) (fun h => FaultKind.noConfusion h)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Unchecked-overflow canary: on `(u32::MAX, 1)`, `AddUnchecked`
(`progAddUncheckedU32`) reaches `.fault .undefined` (and not
`.fault .unsupported`) and refutes `WellFormed`, while wrapping `Add`
(`progAddU32`) on the same inputs is well-formed and returns `0`. -/
theorem canary_negative_ub_add_unchecked_overflow_u32 :
    CanaryNegativeUbAddUncheckedOverflowU32Claim := by
  constructor
  · apply negativeCanary_of_wpFault (fuel := 1)
      (fun h => FaultKind.noConfusion h)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl
  · apply positiveCanary_of_wp (fuel := 2)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl

/-- Shift-overflow canary: `ShlUnchecked` at shift amount `== bitWidth` (`32`
on `u32`) and `ShrUnchecked` at negative signed shift (`-1i8` on `u32`) both
reach `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_shift_unchecked_at_bitwidth_anneal :
    CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim := by
  constructor
  · apply negativeCanary_of_wpFault (fuel := 1)
      (fun h => FaultKind.noConfusion h)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl
  · apply negativeCanary_of_wpFault (fuel := 1)
      (fun h => FaultKind.noConfusion h)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl

/-- Storage-dead read canary: reading a local after `StatementKind.storageDead`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_storage_dead_read_anneal :
    CanaryNegativeUbStorageDeadReadAnnealClaim := by
  apply negativeCanary_of_wpFault (fuel := 4) (fun h => FaultKind.noConfusion h)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Storage-dead return-place canary: executing `StatementKind.storageDead 0`
on `_0` reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_ub_storage_dead_return_place_anneal :
    CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim := by
  apply negativeCanary_of_wpFault (fuel := 1) (fun h => FaultKind.noConfusion h)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Unreachable terminator canary: executing `TerminatorKind.unreachable`
reaches `.fault .undefined` (and not `.fault .unsupported`). -/
theorem canary_negative_ub_unreachable_anneal :
    CanaryNegativeUbUnreachableAnnealClaim := by
  apply negativeCanary_of_wpFault (fuel := 1) (fun h => FaultKind.noConfusion h)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Unsigned-negation canary: executing `UnOp.neg` on an unsigned integer
(`u32`) reaches `.fault .unsupported` (and not `.fault .undefined`). -/
theorem canary_negative_unsupported_unsigned_neg_anneal :
    CanaryNegativeUnsupportedUnsignedNegAnnealClaim := by
  apply negativeCanary_of_wpFault (fuel := 1) (fun h => FaultKind.noConfusion h)
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
  rfl

/-- Explicit-repr fieldless enum positive canary: `#[repr(u8)]` non-index tag
decoding + `u8` `Rvalue.discriminant` and signed `i8` -> `isize` sign-extended
tag decoding. -/
theorem canary_positive_enum_explicit_repr_anneal :
    CanaryPositiveEnumExplicitReprAnnealClaim := by
  constructor
  · apply positiveCanary_of_wp (fuel := 5)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 5)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl

/-- Single-variant inhabited ZST enum positive canary: implicit return without
writing `_0`, non-deinitializing `Operand.move`, `ConstLit.zeroSized`, and
`Rvalue.discriminant`. -/
theorem canary_positive_zst_single_enum_anneal :
    CanaryPositiveZstSingleEnumAnnealClaim := by
  constructor
  · apply positiveCanary_of_wp (fuel := 1)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
  · apply positiveCanary_of_wp (fuel := 10)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl

/-- Fieldless enum negative UB canary: invalid constant scalar tag `1` on
`ReprU8 { A = 10, B = 20 }` and reading `Rvalue.discriminant` from an
uninitialized scalar-tagged enum local both reach `.fault .undefined`. -/
theorem canary_negative_ub_enum_invalid_tag_and_uninit_anneal :
    CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim := by
  constructor
  · apply negativeCanary_of_wpFault (fuel := 2)
      (fun h => FaultKind.noConfusion h)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl
  · apply negativeCanary_of_wpFault (fuel := 2)
      (fun h => FaultKind.noConfusion h)
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl

/-- Crate/unit/body verification canary exercising `CrateTheorem`, safe vs.
`unsafe` contract gating (`isUnsafe`), `MirTy.never` static-admission
non-vacuity, `p.bodies[defId]` lookup binding in `BodyVerified`, and
empty-`bodies` / out-of-bounds `entryDefId` / duplicate `identity` rejection. -/
theorem canary_crate_and_body_verified_anneal :
    CanaryCrateAndBodyVerifiedAnnealClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    intro defId body hGet
    cases defId with
    | zero =>
      injection hGet with hBody; subst hBody
      refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
      cases args with
      | nil =>
        refine (positiveCanary_of_wp (fuel := 1) (expectedRet := .unit) ?_).1
        refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
      | cons _ _ => exact Bool.noConfusion hArgs
    | succ defId =>
      cases defId with
      | zero =>
        injection hGet with hBody; subst hBody
        refine ⟨rfl, rfl, fun args _ hSafe => ?_⟩
        have hEq : args = [.bool true] := hSafe rfl
        subst hEq
        refine (positiveCanary_of_wp (fuel := 3)
          (expectedRet := u32Val 42) ?_).1
        refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
        refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
        refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc; rfl
      | succ defId =>
        cases defId with
        | zero =>
          injection hGet with hBody; subst hBody
          refine ⟨rfl, rfl, fun args hArgs _ => ?_⟩
          cases args with
          | nil => exact Bool.noConfusion hArgs
          | cons v rest =>
            have hCheck : checkVal v .never = true := by
              revert hArgs
              change (checkVal v .never && checkArgsMatch rest []) = true → _
              cases checkVal v .never <;> intro h <;>
                first | rfl | exact Bool.noConfusion h
            cases v with
            | scalar sv =>
              revert hCheck
              dsimp [checkVal, Val.ty?, MirTy.beq]
              cases sv.wf <;> intro h <;> exact Bool.noConfusion h
            | ptr _ | bool _ | unit | tuple _ | bytes _ =>
              exact Bool.noConfusion hCheck
            | enumVal ety idx =>
              revert hCheck
              dsimp [checkVal, Val.ty?, MirTy.beq]
              cases enumAdmitted ety <;>
                cases Nat.blt idx ety.discriminants.length <;>
                intro h <;> exact Bool.noConfusion h
        | succ _ =>
          dsimp [canaryValidCrate, Trusted.MirSemantics.getElem?] at hGet
          cases hGet
  · intro hVer
    have hWf := hVer.2.2 [.bool false] rfl (fun h => Bool.noConfusion h)
    have hNeg : NegativeCanaryClaim
        (entryProgForBody { bodies := [canaryUnsafeGuardedBody false] } 0)
        { args := [.bool false] } .undefined .unsupported := by
      apply negativeCanary_of_wpFault (fuel := 2)
        (fun h => FaultKind.noConfusion h)
      refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
      refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
      rfl
    exact hNeg.2.2 hWf
  · intro hVer
    exact Bool.noConfusion hVer.2.1
  · intro hVer
    have hEq : canarySafeUnitBody = canaryUnsafeGuardedBody false := by
      injection hVer.1
    have hArg : (canarySafeUnitBody).argumentCount =
        (canaryUnsafeGuardedBody false).argumentCount :=
      congrArg Body.argumentCount hEq
    exact Nat.noConfusion hArg
  · intro hVer
    have hEq : canaryUnsafeGuardedBody false = canaryNeverParamBody false := by
      injection hVer.1
    have hLoc : (canaryUnsafeGuardedBody false).locals =
        (canaryNeverParamBody false).locals :=
      congrArg Body.locals hEq
    injection hLoc with hHead
    exact MirTy.noConfusion hHead
  · intro hCrate
    exact Bool.noConfusion hCrate.2.2.2.1
  · intro hUnit
    exact Bool.noConfusion hUnit.2.2.2.2.1
  · intro hCrate
    exact Bool.noConfusion hCrate.2.2.2.2.2.1

/-! ## Single-Body Execution Certificates and Invariant Helpers -/

/-- Single-body program wrapper for unit-level execution of `body`. -/
def bodyProg (body : Body) : Program :=
  { scope := .unit, bodies := [body] }

/-- Single-frame running state in body `defId` (default `0`) with empty
`callerMem`. -/
def mkState (blockIdx stmtIdx : Nat) (locals : List LocalSlot)
    (defId : DefId := 0) : State :=
  {
    frames := [{
      defId := defId
      blockIdx := blockIdx
      stmtIdx := stmtIdx
      locals := locals
    }]
    callerMem := ⟨[]⟩
  }

/-- Entry state of `body` on `args` at `defId := 0` with empty `callerMem`. -/
noncomputable def initial (body : Body) (args : List Val) : State :=
  mkState 0 0 (initLocalsLoop body args 0 body.locals)

/-- Single-step transition of `body` on `s` (`evalStep (bodyProg body) 0 s`). -/
noncomputable def step (body : Body) (s : State) :
    StepResult State TerminalOut :=
  evalStep (bodyProg body) 0 s

/-- Finite-step reachability in `body`. -/
inductive Reach (body : Body) : State → State → Prop where
  | refl {state : State} : Reach body state state
  | next {start mid next : State} :
      Reach body start mid →
      step body mid = .step next →
      Reach body start next

/-- Prefix fault-freedom of `body` starting from `start`. -/
noncomputable def SafeFrom (body : Body) (start : State) : Prop :=
  ∀ state kind, Reach body start state → step body state ≠ .fault kind

/-- Prefix fault-freedom of `body` starting from `initial body args`. -/
noncomputable def Safe (body : Body) (args : List Val) : Prop :=
  SafeFrom body (initial body args)

/-- Normal return of `output` from `start` in `body`. -/
noncomputable def ReturnsFrom (body : Body) (start : State) (output : Val) :
    Prop :=
  ∃ state, Reach body start state ∧
    step body state = .done (.returned ⟨output, ⟨[]⟩⟩)

/-- Normal return of `output` from `initial body args` in `body`. -/
noncomputable def Returns (body : Body) (args : List Val) (output : Val) :
    Prop :=
  ReturnsFrom body (initial body args) output

/-- Fuel-bounded evaluator for `body` returning `some val` when execution
terminates in `.done (.returned ⟨val, ⟨[]⟩⟩)` within `fuel` steps. -/
noncomputable def run (body : Body) : Nat → State → Option Val
  | 0, _ => none
  | fuel + 1, s =>
    match step body s with
    | .done (.returned ⟨val, ⟨[]⟩⟩) => some val
    | .done _ => none
    | .step next => run body fuel next
    | .fault _ => none

theorem step_deterministic {body : Body} {state : State}
    {r1 r2 : StepResult State TerminalOut}
    (first : step body state = r1) (second : step body state = r2) :
    r1 = r2 :=
  first.symm.trans second

theorem reach_prepend {body : Body} {start next finish : State}
    (first : step body start = .step next) (rest : Reach body next finish) :
    Reach body start finish := by
  induction rest with
  | refl => exact .next .refl first
  | next _ transition ih => exact .next ih transition

theorem reach_cases {body : Body} {start next finish : State}
    (first : step body start = .step next) (reached : Reach body start finish) :
    finish = start ∨ Reach body next finish := by
  induction reached with
  | refl => exact .inl rfl
  | @next before after _ transition ih =>
    cases ih with
    | inl equal =>
      subst before
      have same : StepResult.step next = .step after :=
        first.symm.trans transition
      injection same with h_eq
      subst h_eq
      exact .inr .refl
    | inr rest => exact .inr (.next rest transition)

theorem reachable_after_return {body : Body} {start finish : State}
    {value : Val}
    (returned : step body start = .done (.returned ⟨value, ⟨[]⟩⟩))
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [returned] at transition
    cases transition

theorem reachable_after_fault {body : Body} {start finish : State}
    {reason : FaultKind}
    (faulted : step body start = .fault reason)
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    rw [faulted] at transition
    cases transition

theorem safeFrom_return {body : Body} {start : State} {value : Val}
    (returned : step body start = .done (.returned ⟨value, ⟨[]⟩⟩)) :
    SafeFrom body start := by
  intro finish reason reached
  have same := reachable_after_return returned reached
  subst finish
  rw [returned]
  intro h
  cases h

theorem safeFrom_next {body : Body} {start next : State}
    (first : step body start = .step next) (rest : SafeFrom body next) :
    SafeFrom body start := by
  intro finish reason reached
  cases reach_cases first reached with
  | inl equal =>
    subst finish
    rw [first]
    intro h
    cases h
  | inr tail => exact rest finish reason tail

theorem safeFrom_of_reach {body : Body} {start checkpoint : State}
    (segment : Reach body start checkpoint)
    (suffix : SafeFrom body checkpoint) :
    SafeFrom body start := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (safeFrom_next transition suffix)

inductive Executes (body : Body) : State → Val → Prop where
  | ret {start : State} {value : Val} :
      step body start = .done (.returned ⟨value, ⟨[]⟩⟩) →
      Executes body start value
  | next {start next : State} {value : Val} :
      step body start = .step next →
      Executes body next value →
      Executes body start value

theorem executes_prepend {body : Body} {start checkpoint : State} {value : Val}
    (segment : Reach body start checkpoint)
    (suffix : Executes body checkpoint value) :
    Executes body start value := by
  induction segment with
  | refl => exact suffix
  | next _ transition ih => exact ih (.next transition suffix)

theorem executes_safe {body : Body} {start : State} {value : Val}
    (execution : Executes body start value) :
    SafeFrom body start := by
  induction execution with
  | ret returned => exact safeFrom_return returned
  | next transition _ ih => exact safeFrom_next transition ih

theorem executes_returns {body : Body} {start : State} {value : Val}
    (execution : Executes body start value) :
    ReturnsFrom body start value := by
  induction execution with
  | ret returned => exact ⟨_, .refl, returned⟩
  | next transition _ ih =>
    let ⟨finish, h_reach, h_ret⟩ := ih
    exact ⟨finish, reach_prepend transition h_reach, h_ret⟩

theorem run_executes {body : Body} {fuel : Nat} {start : State} {value : Val}
    (success : run body fuel start = some value) :
    Executes body start value := by
  induction fuel generalizing start with
  | zero => cases success
  | succ fuel ih =>
    unfold run at success
    cases transition : step body start with
    | step next =>
      rw [transition] at success
      exact .next transition (ih success)
    | done out =>
      rw [transition] at success
      cases out with
      | unwound _ => cases success
      | returned retOut =>
        cases retOut with
        | mk retVal cm =>
          cases cm with
          | mk allocs =>
            cases allocs with
            | nil =>
              injection success with h_val
              subst h_val
              exact .ret transition
            | cons _ _ => cases success
    | fault _ =>
      rw [transition] at success
      cases success

theorem run_success {body : Body} {fuel : Nat} {start : State} {value : Val}
    (success : run body fuel start = some value) :
    SafeFrom body start ∧ ReturnsFrom body start value :=
  ⟨executes_safe (run_executes success),
    executes_returns (run_executes success)⟩

theorem run_initial_success {body : Body} {fuel : Nat} {args : List Val}
    {value : Val}
    (success : run body fuel (initial body args) = some value) :
    Safe body args ∧ Returns body args value :=
  run_success success

theorem executes_unique {body : Body} {start : State} {left right : Val}
    (execution : Executes body start left)
    (returned : ReturnsFrom body start right) :
    left = right := by
  induction execution with
  | ret first =>
    let ⟨finish, h_reach, h_ret⟩ := returned
    have same := reachable_after_return first h_reach
    subst finish
    have equal := first.symm.trans h_ret
    injection equal with h_term
    injection h_term with h_out
    injection h_out with h_val _
  | next first _ ih =>
    let ⟨finish, h_reach, h_ret⟩ := returned
    cases reach_cases first h_reach with
    | inl same =>
      subst finish
      rw [first] at h_ret
      cases h_ret
    | inr tail => exact ih ⟨finish, tail, h_ret⟩

theorem run_result_unique {body : Body} {fuel : Nat} {start : State}
    {left right : Val}
    (success : run body fuel start = some left)
    (returned : ReturnsFrom body start right) :
    left = right :=
  executes_unique (run_executes success) returned

theorem invariant_reachable {body : Body} {start finish : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      step body before = .step after → invariant after)
    (reached : Reach body start finish) :
    invariant finish := by
  induction reached with
  | refl => exact entry
  | next _ transition ih => exact closed _ _ ih transition

theorem safeFrom_invariant {body : Body} {start : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before →
      step body before = .step after → invariant after)
    (noFault : ∀ state, invariant state → ∀ reason,
      step body state ≠ .fault reason) :
    SafeFrom body start := by
  intro finish reason reached
  have preserved := invariant_reachable invariant entry closed reached
  exact noFault finish preserved reason

theorem reachable_selfLoop {body : Body} {start finish : State}
    (loop : step body start = .step start)
    (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before _ _ transition ih =>
    subst before
    have equal := loop.symm.trans transition
    injection equal with h_eq
    exact h_eq.symm

theorem safeFrom_selfLoop {body : Body} {start : State}
    (loop : step body start = .step start) :
    SafeFrom body start := by
  intro finish reason reached
  have same := reachable_selfLoop loop reached
  subst finish
  rw [loop]
  intro h
  cases h

/-! ## Block-Modular Execution Certificates

An `Executes` certificate can be built one `step` at a time, but if each
successor state is left as the unreduced result of `step`, its locals are a
`setElem?` term over the previous state's locals. Each later step then
re-reduces an ever deeper spine. When the arguments contain a universally
quantified value, `checkVal` on a symbolic scalar never reduces to `true` at
all, so such a step cannot close by reduction.

The combinators below cut a path at basic-block boundaries and pre-normalize
the body's `basicBlocks` and `locals` spines once at entry
(`executes_of_blockExec`). `BlockExec` carries the pre-forced `blocks`,
`locals`, and remaining statements of the current block, so stepping a statement
neither re-reduces `body` nor looks up the block again. Every rule states its
successor as `mkState b i L'` with `L'` fixed by one equational premise
(`setElem?`), reducing the successor's local-slot spine to a literal list before
the next statement runs, while `blockExec_assign_local` and
`evalStatement_assign` turn the dynamic `checkVal` test and the stored value
into explicit premises discharged with value-level lemmas. -/

/-- Every `Executes body start value` witness yields a finite `fuel` budget
establishing `wpState (bodyProg body) fuel start`. -/
theorem wpState_of_executes {body : Body} {start : State} {value : Val}
    (h_exec : Executes body start value) :
    ∃ fuel, wpState (bodyProg body) fuel start
      (fun out => out = .returned ⟨value, ⟨[]⟩⟩) := by
  induction h_exec with
  | @ret s₀ val h_done =>
    refine ⟨1, ⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    unfold step at h_done
    rw [h_done]
  | @next s₀ s₁ val h_step _ ih =>
    let ⟨fuel, h_wp⟩ := ih
    refine ⟨fuel + 1, ⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    unfold step at h_step
    rw [h_step]
    exact h_wp

/-- Reconstruct a list spine from its constructors so closing
`forceList? xs = some ys` by `rfl` normalizes `xs` to a flat `::` list. -/
noncomputable def forceList? {α : Type} : List α → Option (List α)
  | [] => some []
  | x :: xs =>
    match forceList? xs with
    | some xs' => some (x :: xs')
    | none => none

theorem forceList?_eq {α : Type} {xs ys : List α}
    (h : forceList? xs = some ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases h
    rfl
  | cons x rest ih =>
    dsimp only [forceList?] at h
    cases hr : forceList? rest with
    | none =>
      rw [hr] at h
      cases h
    | some rest' =>
      rw [hr] at h
      cases h
      rw [ih hr]

/-- Reconstruct a `LocalSlot` from its constructors so closing
`forceSlot? s = some s'` by `rfl` reduces an unevaluated slot such as
`liveUninitSlot ty` to `.dead`, `.live none`, or `.live (some v)`. -/
noncomputable def forceSlot? : LocalSlot → Option LocalSlot
  | .dead => some .dead
  | .live none => some (.live none)
  | .live (some v) => some (.live (some v))

theorem forceSlot?_eq {s s' : LocalSlot}
    (h : forceSlot? s = some s') : s = s' := by
  cases s with
  | dead =>
    cases h
    rfl
  | live opt =>
    cases opt <;> (cases h; rfl)

/-- Minimal `Body` carrier holding a pre-normalized `locals` table, used so
statement and terminator premises never re-reduce `body` when `body` is an
unreduced AST-interpreter application. -/
noncomputable def localsBody (locals : List MirTy) : Body :=
  { argumentCount := 0, locals := locals, basicBlocks := [] }

theorem evalStatement_localsBody {body : Body} {locals : List MirTy}
    (h_loc : body.locals = locals) (f : FrameState) (cm : CallerMemory)
    (stmt : StatementKind) :
    evalStatement body f cm stmt =
      evalStatement (localsBody locals) f cm stmt := by
  dsimp only [evalStatement, localsBody]
  rw [h_loc]

theorem evalTerminator_localsBody {body : Body} {locals : List MirTy}
    (h_loc : body.locals = locals) (bb : BasicBlock) (f : FrameState)
    (cm : CallerMemory) :
    evalTerminator body bb f cm =
      evalTerminator (localsBody locals) bb f cm := by
  dsimp only [evalTerminator, localsBody]
  rw [h_loc]

/-- One `step` of a single-frame `mkState` state: look up block `b`, then run
statement `i`, or the terminator once `i` reaches the end of the block. -/
theorem step_mkState (body : Body) (b i : Nat) (L : List LocalSlot) :
    step body (mkState b i L) =
      match Trusted.MirSemantics.getElem? body.basicBlocks b with
      | none => .fault .unsupported
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements i with
        | some stmt => evalStatement body ⟨0, b, i, L⟩ ⟨[]⟩ stmt
        | none =>
          if Nat.beq i bb.statements.length then
            evalTerminator body bb ⟨0, b, i, L⟩ ⟨[]⟩
          else
            .fault .undefined :=
  rfl

/-- Execution of `body` (with pre-normalized `blocks = body.basicBlocks` and
`locals = body.locals`) from statement `i` of basic block `b` (`bb`) with
remaining statements `stmts` and local-slot spine `L`, returning `v`. -/
noncomputable def BlockExec (body : Body) (blocks : List BasicBlock)
    (locals : List MirTy) (bb : BasicBlock) (b i : Nat)
    (stmts : List StatementKind) (L : List LocalSlot) (v : Val) : Prop :=
  body.basicBlocks = blocks →
    body.locals = locals →
    Trusted.MirSemantics.getElem? blocks b = some bb →
    i ≤ bb.statements.length →
    bb.statements.drop i = stmts →
    Executes body (mkState b i L) v

theorem getElem?_of_drop_eq_cons {α : Type} (l : List α) (i : Nat) (x : α)
    (rest : List α) (h : l.drop i = x :: rest) :
    Trusted.MirSemantics.getElem? l i = some x := by
  induction l generalizing i with
  | nil => cases i <;> cases h
  | cons y ys ih =>
    cases i with
    | zero =>
      cases h
      rfl
    | succ i => exact ih i h

theorem drop_succ_of_drop_eq_cons {α : Type} (l : List α) (i : Nat) (x : α)
    (rest : List α) (h : l.drop i = x :: rest) : l.drop (i + 1) = rest := by
  induction l generalizing i with
  | nil => cases i <;> cases h
  | cons y ys ih =>
    cases i with
    | zero =>
      cases h
      rfl
    | succ i => exact ih i h

theorem le_length_succ_of_drop_eq_cons {α : Type} (l : List α) (i : Nat)
    (x : α) (rest : List α) (h : l.drop i = x :: rest) :
    i + 1 ≤ l.length := by
  induction l generalizing i with
  | nil => cases i <;> cases h
  | cons _ ys ih =>
    cases i with
    | zero => exact Nat.succ_le_succ (Nat.zero_le ys.length)
    | succ j => exact Nat.succ_le_succ (ih j h)

theorem getElem?_of_drop_eq_nil {α : Type} (l : List α) (i : Nat)
    (h : l.drop i = []) : Trusted.MirSemantics.getElem? l i = none := by
  induction l generalizing i with
  | nil => rfl
  | cons _ ys ih =>
    cases i with
    | zero => cases h
    | succ i => exact ih i h

theorem beq_length_of_drop_eq_nil {α : Type} (l : List α) (i : Nat)
    (h_le : i ≤ l.length) (h_drop : l.drop i = []) :
    Nat.beq i l.length = true := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ j => exact False.elim (Nat.not_succ_le_zero j h_le)
  | cons _ ys ih =>
    cases i with
    | zero => cases h_drop
    | succ j => exact ih j (Nat.le_of_succ_le_succ h_le) h_drop

/-- Enter basic block `b` at its first statement with pre-normalized `blocks`,
`locals`, and statement list `stmts`. -/
theorem executes_of_blockExec {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb : BasicBlock} {b : Nat}
    {stmts : List StatementKind} {L : List LocalSlot} {v : Val}
    (h_blocks : forceList? body.basicBlocks = some blocks)
    (h_locals : forceList? body.locals = some locals)
    (h_bb : Trusted.MirSemantics.getElem? blocks b = some bb)
    (h_stmts : forceList? bb.statements = some stmts)
    (h_exec : BlockExec body blocks locals bb b 0 stmts L v) :
    Executes body (mkState b 0 L) v :=
  h_exec (forceList?_eq h_blocks) (forceList?_eq h_locals) h_bb
    (Nat.zero_le bb.statements.length) (forceList?_eq h_stmts)

/-- Run the next statement `s` of the current block. -/
theorem blockExec_cons {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb : BasicBlock} {b i : Nat}
    {s : StatementKind} {rest : List StatementKind} {L L' : List LocalSlot}
    {v : Val}
    (h_stmt : evalStatement (localsBody locals) ⟨0, b, i, L⟩ ⟨[]⟩ s =
      .step (mkState b (i + 1) L'))
    (h_rest : BlockExec body blocks locals bb b (i + 1) rest L' v) :
    BlockExec body blocks locals bb b i (s :: rest) L v := by
  intro h_blocks h_locals h_bb _ h_drop
  have h_step : step body (mkState b i L) = .step (mkState b (i + 1) L') := by
    rw [step_mkState, h_blocks, h_bb]
    dsimp only
    rw [getElem?_of_drop_eq_cons bb.statements i s rest h_drop]
    dsimp only
    rw [evalStatement_localsBody h_locals]
    exact h_stmt
  exact .next h_step (h_rest h_blocks h_locals h_bb
    (le_length_succ_of_drop_eq_cons bb.statements i s rest h_drop)
    (drop_succ_of_drop_eq_cons bb.statements i s rest h_drop))

/-- Run a `nop` statement without additional premises. -/
theorem blockExec_nop {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb : BasicBlock} {b i : Nat}
    {rest : List StatementKind} {L : List LocalSlot} {v : Val}
    (h_rest : BlockExec body blocks locals bb b (i + 1) rest L v) :
    BlockExec body blocks locals bb b i (.nop :: rest) L v :=
  blockExec_cons rfl h_rest

/-- Run a `StorageLive k` statement, normalizing `liveUninitSlot ty` via
`forceSlot?` before updating `L`. -/
theorem blockExec_storageLive {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb : BasicBlock} {b i k : Nat}
    {rest : List StatementKind} {L L' : List LocalSlot} {ty : MirTy}
    {slot : LocalSlot} {v : Val}
    (h_ty : Trusted.MirSemantics.getElem? locals k = some ty)
    (h_slot : forceSlot? (liveUninitSlot ty) = some slot)
    (h_set : setElem? L k slot = some L')
    (h_rest : BlockExec body blocks locals bb b (i + 1) rest L' v) :
    BlockExec body blocks locals bb b i (.storageLive k :: rest) L v := by
  refine blockExec_cons ?_ h_rest
  dsimp only [evalStatement, localsBody]
  rw [h_ty]
  dsimp only
  rw [forceSlot?_eq h_slot, h_set]
  rfl

/-- Run a `StorageDead k` statement for a local other than the return place. -/
theorem blockExec_storageDead {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb : BasicBlock} {b i k : Nat}
    {rest : List StatementKind} {L L' : List LocalSlot} {v : Val}
    (h_k : Nat.beq k 0 = false)
    (h_set : setElem? L k .dead = some L')
    (h_rest : BlockExec body blocks locals bb b (i + 1) rest L' v) :
    BlockExec body blocks locals bb b i (.storageDead k :: rest) L v := by
  refine blockExec_cons ?_ h_rest
  dsimp only [evalStatement, localsBody]
  rw [h_k, h_set]
  rfl

/-- Leave the current block through a terminator that steps to the first
statement of block `t`, continuing directly in `BlockExec` with the same
pre-normalized `blocks` and `locals`. -/
theorem blockExec_nil_step {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb bb' : BasicBlock} {b i t : Nat}
    {stmts' : List StatementKind} {L L' : List LocalSlot} {v : Val}
    (h_term : evalTerminator (localsBody locals) bb ⟨0, b, i, L⟩ ⟨[]⟩ =
      .step (mkState t 0 L'))
    (h_bb' : Trusted.MirSemantics.getElem? blocks t = some bb')
    (h_stmts' : forceList? bb'.statements = some stmts')
    (h_next : BlockExec body blocks locals bb' t 0 stmts' L' v) :
    BlockExec body blocks locals bb b i [] L v := by
  intro h_blocks h_locals h_bb h_le h_drop
  have h_step : step body (mkState b i L) = .step (mkState t 0 L') := by
    rw [step_mkState, h_blocks, h_bb]
    dsimp only
    rw [getElem?_of_drop_eq_nil bb.statements i h_drop]
    dsimp only
    rw [beq_length_of_drop_eq_nil bb.statements i h_le h_drop,
      evalTerminator_localsBody h_locals]
    exact h_term
  exact .next h_step (h_next h_blocks h_locals h_bb'
    (Nat.zero_le bb'.statements.length) (forceList?_eq h_stmts'))

/-- Fast-path block exit for `TerminatorKind.goto t`. -/
theorem blockExec_nil_goto {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb bb' : BasicBlock} {b i t : Nat}
    {stmts' : List StatementKind} {L : List LocalSlot} {v : Val}
    (h_term : bb.terminator = .goto t)
    (h_bb' : Trusted.MirSemantics.getElem? blocks t = some bb')
    (h_stmts' : forceList? bb'.statements = some stmts')
    (h_next : BlockExec body blocks locals bb' t 0 stmts' L v) :
    BlockExec body blocks locals bb b i [] L v := by
  refine blockExec_nil_step ?_ h_bb' h_stmts' h_next
  dsimp only [evalTerminator, jumpToBlock]
  rw [h_term]
  rfl

/-- Leave the current block through a terminator that returns `v`. -/
theorem blockExec_nil_ret {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb : BasicBlock} {b i : Nat}
    {L : List LocalSlot} {v : Val}
    (h_term : evalTerminator (localsBody locals) bb ⟨0, b, i, L⟩ ⟨[]⟩ =
      .done (.returned ⟨v, ⟨[]⟩⟩)) :
    BlockExec body blocks locals bb b i [] L v := by
  intro h_blocks h_locals h_bb h_le h_drop
  have h_step :
      step body (mkState b i L) = .done (.returned ⟨v, ⟨[]⟩⟩) := by
    rw [step_mkState, h_blocks, h_bb]
    dsimp only
    rw [getElem?_of_drop_eq_nil bb.statements i h_drop]
    dsimp only
    rw [beq_length_of_drop_eq_nil bb.statements i h_le h_drop,
      evalTerminator_localsBody h_locals]
    exact h_term
  exact .ret h_step

/-- An assignment step whose stored value is given by premises rather than by
reduction. `h_val` lets a caller replace the value that `evalRvalue` computes
by an equal normal form, and `h_check` is the dynamic type test of
`writePlace`; neither reduces by `rfl` when the value mentions a free
variable. -/
theorem evalStatement_assign {body : Body} {b i : Nat}
    {L L₁ L₂ : List LocalSlot} {stmt : StatementKind} {dst : Place}
    {rv : Rvalue} {ty : MirTy} {v v' : Val} {o : Option Val}
    (h_stmt : stmt = .assign dst rv)
    (h_proj : dst.projection.isEmpty = true)
    (h_ty : Trusted.MirSemantics.getElem? body.locals dst.localId = some ty)
    (h_rv : evalRvalue body.locals L ty rv = .ok (v, L₁))
    (h_val : v = v')
    (h_check : checkVal v' ty = true)
    (h_live : Trusted.MirSemantics.getElem? L₁ dst.localId = some (.live o))
    (h_set : setElem? L₁ dst.localId (.live (some v')) = some L₂) :
    evalStatement body ⟨0, b, i, L⟩ ⟨[]⟩ stmt =
      .step (mkState b (i + 1) L₂) := by
  subst h_stmt h_val
  dsimp only [evalStatement]
  rw [h_proj, h_ty]
  dsimp only
  rw [h_rv]
  dsimp only [writePlace]
  rw [h_check, h_live, h_set]
  rfl

/-- Run a projection-free local assignment `.assign ⟨dstId, []⟩ rv` in
`BlockExec` using `evalStatement_assign` over the pre-normalized `locals`
table. -/
theorem blockExec_assign_local {body : Body} {blocks : List BasicBlock}
    {locals : List MirTy} {bb : BasicBlock} {b i dstId : Nat}
    {rv : Rvalue} {rest : List StatementKind} {L L₁ L₂ : List LocalSlot}
    {ty : MirTy} {v v' : Val} {o : Option Val} {out : Val}
    (h_ty : Trusted.MirSemantics.getElem? locals dstId = some ty)
    (h_rv : evalRvalue locals L ty rv = .ok (v, L₁))
    (h_val : v = v')
    (h_check : checkVal v' ty = true)
    (h_live : Trusted.MirSemantics.getElem? L₁ dstId = some (.live o))
    (h_set : setElem? L₁ dstId (.live (some v')) = some L₂)
    (h_rest : BlockExec body blocks locals bb b (i + 1) rest L₂ out) :
    BlockExec body blocks locals bb b i
      (.assign ⟨dstId, []⟩ rv :: rest) L out :=
  blockExec_cons
    (evalStatement_assign rfl rfl h_ty h_rv h_val h_check h_live h_set)
    h_rest

theorem bitVec_eq_of_toNat_eq {n : Nat} {a b : BitVec n}
    (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

theorem truncateBits_i64_idem (x : BitVec 128) :
    truncateBits .i64 (truncateBits .i64 x) = truncateBits .i64 x := by
  let b : BitVec 64 := bvExtractLsb 63 0 x
  have hb : (bvZeroExtend 128 b).toNat = b.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide))
  have hb64 : BitVec.ofNat 64 (bvZeroExtend 128 b).toNat = b := by
    apply bitVec_eq_of_toNat_eq
    change Nat.mod (bvZeroExtend 128 b).toNat (Nat.pow 2 64) = b.toNat
    rw [hb]
    exact Nat.mod_eq_of_lt b.isLt
  change bvZeroExtend 128 (BitVec.ofNat 64 (bvZeroExtend 128 b).toNat) =
    bvZeroExtend 128 b
  rw [hb64]

theorem checkVal_u64_truncateBits (x : BitVec 128) :
    checkVal (.scalar ⟨.i64, false, truncateBits .i64 x⟩) (.int .i64 false) =
      true := by
  unfold checkVal Val.ty? ScalarVal.wf
  dsimp only
  have h_eq :
      (truncateBits .i64 (truncateBits .i64 x) == truncateBits .i64 x) =
      true := by
    rw [truncateBits_i64_idem]
    exact beq_self_eq_true (truncateBits .i64 x)
  rw [h_eq]
  rfl

noncomputable def retagDefId (d : DefId) (s : State) : State :=
  match s.frames with
  | [f] => { s with frames := [{ f with defId := d }] }
  | _ => s

noncomputable def IsSingleFrame0 (s : State) : Prop :=
  ∃ f : FrameState, s.frames = [f] ∧ f.defId = 0

theorem evalStatement_singleFrame0 {body : Body} {f : FrameState}
    {cm : CallerMemory} {stmt : StatementKind} {s' : State}
    (h_id : f.defId = 0)
    (h_step : evalStatement body f cm stmt = .step s') :
    IsSingleFrame0 s' := by
  cases stmt with
  | nop =>
    unfold evalStatement at h_step
    injection h_step with h_eq; subst h_eq
    exact ⟨_, rfl, h_id⟩
  | storageLive lid =>
    unfold evalStatement at h_step
    dsimp only at h_step
    cases h_ty : Trusted.MirSemantics.getElem? body.locals lid with
    | none => rw [h_ty] at h_step; cases h_step
    | some ty =>
      rw [h_ty] at h_step
      dsimp only at h_step
      cases h_set : setElem? f.locals lid (liveUninitSlot ty) with
      | none => rw [h_set] at h_step; cases h_step
      | some l' =>
        rw [h_set] at h_step
        injection h_step with h_eq; subst h_eq
        exact ⟨_, rfl, h_id⟩
  | storageDead lid =>
    unfold evalStatement at h_step
    dsimp only at h_step
    cases h_zero : Nat.beq lid 0 with
    | true => rw [h_zero] at h_step; cases h_step
    | false =>
      rw [h_zero] at h_step
      cases h_set : setElem? f.locals lid .dead with
      | none => rw [h_set] at h_step; cases h_step
      | some l' =>
        rw [h_set] at h_step
        injection h_step with h_eq; subst h_eq
        exact ⟨_, rfl, h_id⟩
  | assign dst rv =>
    unfold evalStatement at h_step
    dsimp only at h_step
    cases h_proj : (!dst.projection.isEmpty) with
    | true => rw [h_proj] at h_step; cases h_step
    | false =>
      rw [h_proj] at h_step
      cases h_dst : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [h_dst] at h_step; cases h_step
      | some dstTy =>
        rw [h_dst] at h_step
        dsimp only at h_step
        cases h_rv : evalRvalue body.locals f.locals dstTy rv with
        | error k => rw [h_rv] at h_step; cases h_step
        | ok pair =>
          rw [h_rv] at h_step
          dsimp only at h_step
          cases h_wp : writePlace pair.2 dst.localId dstTy pair.1 with
          | error k => rw [h_wp] at h_step; cases h_step
          | ok l' =>
            rw [h_wp] at h_step
            injection h_step with h_eq; subst h_eq
            exact ⟨_, rfl, h_id⟩
  | unsupported => cases h_step

theorem evalTerminator_singleFrame0 {body : Body} {bb : BasicBlock}
    {f : FrameState} {cm : CallerMemory} {s' : State}
    (h_id : f.defId = 0)
    (h_step : evalTerminator body bb f cm = .step s') :
    IsSingleFrame0 s' := by
  unfold evalTerminator at h_step
  cases h_term : bb.terminator with
  | goto target =>
    rw [h_term] at h_step
    unfold jumpToBlock at h_step
    injection h_step with h_eq; subst h_eq
    exact ⟨_, rfl, h_id⟩
  | return_ =>
    rw [h_term] at h_step
    dsimp only at h_step
    cases h_cl : bb.cleanup with
    | true => rw [h_cl] at h_step; cases h_step
    | false =>
      rw [h_cl] at h_step
      cases h_r0 : Trusted.MirSemantics.getElem? f.locals 0 with
      | none => rw [h_r0] at h_step; cases h_step
      | some slot =>
        rw [h_r0] at h_step
        cases slot with
        | dead => cases h_step
        | live opt => cases opt <;> cases h_step
  | unreachable =>
    rw [h_term] at h_step; cases h_step
  | switchInt discr targets =>
    rw [h_term] at h_step
    dsimp only at h_step
    cases h_op : evalPrimitiveOperand body.locals f.locals discr with
    | error k => rw [h_op] at h_step; cases h_step
    | ok pair =>
      rw [h_op] at h_step
      dsimp only at h_step
      cases h_v : pair.1 with
      | scalar sv =>
        rw [h_v] at h_step
        dsimp only at h_step
        cases h_br : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
        | error k => rw [h_br] at h_step; cases h_step
        | ok tgt =>
          rw [h_br] at h_step
          unfold jumpToBlock at h_step
          injection h_step with h_eq; subst h_eq
          exact ⟨_, rfl, h_id⟩
      | bool b =>
        rw [h_v] at h_step
        dsimp only at h_step
        cases h_br : evalBoolSwitchBranches b targets.otherwise targets.branches with
        | error k => rw [h_br] at h_step; cases h_step
        | ok tgt =>
          rw [h_br] at h_step
          unfold jumpToBlock at h_step
          injection h_step with h_eq; subst h_eq
          exact ⟨_, rfl, h_id⟩
      | ptr _ => rw [h_v] at h_step; cases h_step
      | unit => rw [h_v] at h_step; cases h_step
      | tuple _ => rw [h_v] at h_step; cases h_step
      | bytes _ => rw [h_v] at h_step; cases h_step
      | enumVal _ _ => rw [h_v] at h_step; cases h_step
  | unwindResume => rw [h_term] at h_step; cases h_step
  | assert _ _ _ _ _ => rw [h_term] at h_step; cases h_step
  | call _ _ _ _ _ => rw [h_term] at h_step; cases h_step
  | unsupported => rw [h_term] at h_step; cases h_step

theorem isSingleFrame0_of_step {body : Body} {s s' : State}
    (h_f0 : IsSingleFrame0 s)
    (h_step : step body s = .step s') :
    IsSingleFrame0 s' := by
  let ⟨f, hf, h_id⟩ := h_f0
  cases s with
  | mk frames cm =>
    dsimp only at hf
    subst hf
    unfold step bodyProg evalStep at h_step
    dsimp only at h_step
    rw [h_id] at h_step
    dsimp only [Trusted.MirSemantics.getElem?] at h_step
    cases h_bb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none => rw [h_bb] at h_step; cases h_step
    | some bb =>
      rw [h_bb] at h_step
      dsimp only at h_step
      cases h_stmt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        rw [h_stmt] at h_step
        exact evalStatement_singleFrame0 h_id h_step
      | none =>
        rw [h_stmt] at h_step
        dsimp only at h_step
        cases h_len : Nat.beq f.stmtIdx bb.statements.length with
        | false => rw [h_len] at h_step; cases h_step
        | true =>
          rw [h_len] at h_step
          exact evalTerminator_singleFrame0 h_id h_step

theorem isSingleFrame0_of_reach {body : Body} {args : List Val} {s : State}
    (h_reach : Reach body (initial body args) s) :
    IsSingleFrame0 s := by
  induction h_reach with
  | refl => exact ⟨_, rfl, rfl⟩
  | next _ h_step ih => exact isSingleFrame0_of_step ih h_step

theorem evalStatement_retagDefId (body : Body) (defId : DefId)
    (f : FrameState) (cm : CallerMemory) (stmt : StatementKind) :
    evalStatement body { f with defId := defId } cm stmt =
      match evalStatement body f cm stmt with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  unfold evalStatement retagDefId
  cases stmt with
  | nop => rfl
  | storageLive lid =>
    dsimp only
    cases Trusted.MirSemantics.getElem? body.locals lid with
    | none => rfl
    | some ty =>
      dsimp only
      cases setElem? f.locals lid (liveUninitSlot ty) <;> rfl
  | storageDead lid =>
    dsimp only
    cases Nat.beq lid 0 with
    | true => rfl
    | false =>
      cases setElem? f.locals lid .dead <;> rfl
  | assign dst rv =>
    dsimp only
    cases (!dst.projection.isEmpty) with
    | true => rfl
    | false =>
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp only
        cases evalRvalue body.locals f.locals dstTy rv with
        | error k => rfl
        | ok pair =>
          dsimp only
          cases writePlace pair.2 dst.localId dstTy pair.1 <;> rfl
  | unsupported => rfl

theorem evalTerminator_retagDefId (body : Body) (bb : BasicBlock)
    (defId : DefId) (f : FrameState) (cm : CallerMemory) :
    evalTerminator body bb { f with defId := defId } cm =
      match evalTerminator body bb f cm with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  unfold evalTerminator jumpToBlock retagDefId
  cases bb.terminator with
  | goto target => rfl
  | return_ =>
    dsimp only
    cases bb.cleanup with
    | true => rfl
    | false =>
      cases Trusted.MirSemantics.getElem? f.locals 0 with
      | none => rfl
      | some slot =>
        cases slot with
        | dead => rfl
        | live opt => cases opt <;> rfl
  | unreachable => rfl
  | switchInt discr targets =>
    dsimp only
    cases evalPrimitiveOperand body.locals f.locals discr with
    | error k => rfl
    | ok pair =>
      dsimp only
      cases pair.1 with
      | scalar sv =>
        dsimp only
        cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;> rfl
      | bool b =>
        dsimp only
        cases evalBoolSwitchBranches b targets.otherwise targets.branches <;> rfl
      | ptr _ => rfl
      | unit => rfl
      | tuple _ => rfl
      | bytes _ => rfl
      | enumVal _ _ => rfl
  | unwindResume => rfl
  | assert _ _ _ _ _ => rfl
  | call _ _ _ _ _ => rfl
  | unsupported => rfl

theorem evalStep_retagDefId {p : Program} {defId : DefId} {body : Body}
    {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_f0 : IsSingleFrame0 s) :
    evalStep (entryProgForBody p defId) 0 (retagDefId defId s) =
      match step body s with
      | .step next => .step (retagDefId defId next)
      | .done out => .done out
      | .fault k => .fault k := by
  let ⟨f, hf, h_id⟩ := h_f0
  cases s with
  | mk frames cm =>
    dsimp only at hf
    subst hf
    unfold step bodyProg evalStep retagDefId entryProgForBody
    dsimp only
    rw [h_body, h_id]
    dsimp only [Trusted.MirSemantics.getElem?]
    cases Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none => rfl
    | some bb =>
      dsimp only
      cases Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        exact evalStatement_retagDefId body defId f cm stmt
      | none =>
        dsimp only
        cases Nat.beq f.stmtIdx bb.statements.length with
        | false => rfl
        | true =>
          exact evalTerminator_retagDefId body bb defId f cm

theorem initState_entryProgForBody {p : Program} {defId : DefId} {body : Body}
    {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args) :
    initState (entryProgForBody p defId) { args := args } =
      .ok (retagDefId defId (initial body args)) := by
  unfold BodyStaticAdmitted at h_adm
  unfold ValidEntryArgs at h_args
  unfold initState entryProgForBody initial mkState retagDefId
  dsimp only
  rw [h_body]
  dsimp only
  rw [h_args]
  cases h1 : Nat.beq p.pointerWidthBits 64 <;>
    cases h2 : Nat.beq p.mirProfileVersion 1 <;>
    cases hid : stringBeq body.identity "" <;>
    cases h3 : body.basicBlocks.isEmpty <;>
    cases h4 : Nat.blt body.argumentCount body.locals.length <;>
    cases h5 : storageAnnotationsInBounds body <;>
    cases h6 : body.locals.all isSupportedScalarOrUnitTy <;>
    rw [h1, h2, hid, h3, h4, h5, h6] at h_adm <;>
    cases h_adm
  rfl

theorem reach_of_reaches_entryProg {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {s_d : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_reaches : Reaches (entryProgForBody p defId)
      (retagDefId defId (initial body args)) s_d) :
    ∃ s : State, s_d = retagDefId defId s ∧ Reach body (initial body args) s := by
  induction h_reaches with
  | refl =>
    exact ⟨initial body args, rfl, .refl⟩
  | tail _ h_step ih =>
    let ⟨s, hs, h_reach_s⟩ := ih
    let ⟨c, hc, h_eval⟩ := h_step
    subst hc
    subst hs
    have h_f0 := isSingleFrame0_of_reach h_reach_s
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : step body s with
    | step next =>
      rw [h_st] at h_eval
      injection h_eval with h_eq
      exact ⟨next, h_eq.symm, .next h_reach_s h_st⟩
    | done _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval

theorem bodyVerified_of_safe {p : Program} {defId : DefId} {body : Body}
    {safetyPre : List Val → Prop}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_safe : ∀ args : List Val,
      ValidEntryArgs body args →
      (body.isUnsafe = true → safetyPre args) →
      Safe body args) :
    BodyVerified p defId body safetyPre := by
  refine ⟨h_body, h_adm, ?_⟩
  intro args h_args h_req
  have h_s := h_safe args h_args h_req
  have h_init := initState_entryProgForBody h_body h_adm h_args
  refine ⟨⟨retagDefId defId (initial body args), h_init, ?_⟩, ?_⟩
  · intro _ _
    exact ⟨0, rfl⟩
  · intro k h_fault
    unfold ReachesResult at h_fault
    rw [h_init] at h_fault
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_fault
    subst hc
    let ⟨s, hs, h_reach_s⟩ := reach_of_reaches_entryProg h_body h_reaches
    subst hs
    have h_f0 := isSingleFrame0_of_reach h_reach_s
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : step body s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | done _ => rw [h_st] at h_eval; cases h_eval
    | fault k' =>
      rw [h_st] at h_eval
      injection h_eval with h_k
      subst h_k
      exact h_s s k' h_reach_s h_st

theorem reaches_entryProg_of_reach {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {s : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_reach : Reach body (initial body args) s) :
    Reaches (entryProgForBody p defId)
      (retagDefId defId (initial body args))
      (retagDefId defId s) := by
  induction h_reach with
  | refl => exact .refl _
  | next h_prev h_st ih =>
    have h_f0 := isSingleFrame0_of_reach h_prev
    refine .tail ih ⟨0, rfl, ?_⟩
    rw [evalStep_retagDefId h_body h_f0, h_st]

theorem behavior_of_returns {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args)
    (h_ret : Returns body args ret) :
    Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩) := by
  let ⟨s, h_reach, h_done⟩ := h_ret
  unfold Behavior ReachesResult
  rw [initState_entryProgForBody h_body h_adm h_args]
  refine ⟨retagDefId defId s, reaches_entryProg_of_reach h_body h_reach,
    0, rfl, ?_⟩
  have h_f0 := isSingleFrame0_of_reach h_reach
  rw [evalStep_retagDefId h_body h_f0, h_done]

theorem initState_entryProgForBody_ok {p : Program} {defId : DefId}
    {body : Body} {args : List Val} {s₀ : State}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_init : initState (entryProgForBody p defId) { args := args } = .ok s₀) :
    ValidEntryArgs body args ∧ s₀ = retagDefId defId (initial body args) := by
  unfold initState entryProgForBody at h_init
  unfold ValidEntryArgs initial mkState retagDefId
  dsimp only at h_init
  dsimp only
  rw [h_body] at h_init
  dsimp only at h_init
  cases h1 : Nat.beq p.pointerWidthBits 64 <;>
    cases h2 : Nat.beq p.mirProfileVersion 1 <;>
    cases h3 : body.basicBlocks.isEmpty <;>
    cases h4 : Nat.blt body.argumentCount body.locals.length <;>
    cases h5 : storageAnnotationsInBounds body <;>
    cases h6 : body.locals.all isSupportedScalarOrUnitTy <;>
    cases h7 : checkArgsMatch args
      ((body.locals.drop 1).take body.argumentCount) <;>
    rw [h1, h2, h3, h4, h5, h6, h7] at h_init <;>
    cases h_init
  exact ⟨rfl, rfl⟩

theorem returns_of_behavior {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_beh : Behavior (entryProgForBody p defId) { args := args }
      (.returned ⟨ret, ⟨[]⟩⟩)) :
    ValidEntryArgs body args ∧ Returns body args ret := by
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState (entryProgForBody p defId) { args := args } with
  | error _ => rw [h_init] at h_beh; cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨h_args, hs₀⟩ := initState_entryProgForBody_ok h_body h_init
    subst hs₀
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_beh
    subst hc
    let ⟨s, hs, h_reach⟩ := reach_of_reaches_entryProg h_body h_reaches
    subst hs
    have h_f0 := isSingleFrame0_of_reach h_reach
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : step body s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval
    | done out =>
      rw [h_st] at h_eval
      injection h_eval with h_out
      subst h_out
      exact ⟨h_args, s, h_reach, h_st⟩

theorem not_behavior_of_no_done {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {out : TerminalOut}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_no_done : ∀ s, Reach body (initial body args) s →
      step body s ≠ .done out) :
    ¬ Behavior (entryProgForBody p defId) { args := args } out := by
  intro h_beh
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState (entryProgForBody p defId) { args := args } with
  | error _ => rw [h_init] at h_beh; cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨_, hs₀⟩ := initState_entryProgForBody_ok h_body h_init
    subst hs₀
    let ⟨s_d, h_reaches, c, hc, h_eval⟩ := h_beh
    subst hc
    let ⟨s, hs, h_reach⟩ := reach_of_reaches_entryProg h_body h_reaches
    subst hs
    have h_f0 := isSingleFrame0_of_reach h_reach
    rw [evalStep_retagDefId h_body h_f0] at h_eval
    cases h_st : step body s with
    | step _ => rw [h_st] at h_eval; cases h_eval
    | fault _ => rw [h_st] at h_eval; cases h_eval
    | done out' =>
      rw [h_st] at h_eval
      injection h_eval with h_out
      subst h_out
      exact h_no_done s h_reach h_st

end Anneal.MirWp
