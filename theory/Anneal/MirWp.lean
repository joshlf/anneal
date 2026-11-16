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
import Trusted.MirAst
import Trusted.MirSemantics

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

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
modes.
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

end Anneal.MirWp
