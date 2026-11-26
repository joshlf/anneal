-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted
import Anneal.ITreeWP
import Anneal.Rustc.V2026_06_01.Lower
import Anneal.Rustc.V2026_06_01.SymbolicEval
import Anneal.FunctionalTranslation

namespace Anneal.MirFuelFree

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.Effect
open Anneal.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower
open Anneal.Rustc.V2026_06_01.SymbolicEval
open Anneal.FunctionalTranslation

/-!
# Kleene Monotonicity & Fuel-Free MIR Weakest Preconditions (`FF-1.1`)

Fuel-indexed evaluators (`wpMirExecSym fuel`, `wpMirSym fuel`,
`wpCoalBounded fuel`) evaluate to `False` at `fuel = 0` and unroll the
operational transition coalgebra `stepMirState body` at `fuel' + 1`. Because
`MirStepNode.ret out` halts immediately without consuming remaining fuel, these
evaluators are monotone in `fuel`: once a postcondition is established at `f₁`,
it remains valid at every `f₂ ≥ f₁`.

This module establishes Kleene fuel monotonicity across the symbolic and
computable MIR evaluators and packages the fuel-free existential supremum
predicates (`MirWpConverges`, `MirConverges`, `MirStepsConverges`) together with
sequential composition (`MirWpConverges.step`, `MirWpConverges.bind`) and
top-level adequacy bridges (`dwp_of_mirWpConverges`, `verifyMir_of_wpConverges`,
`verifyMirNoPanic_of_wpConverges`, `verifyStatefulMir_of_wpConverges`,
`verifyStatefulMirNoPanic_of_wpConverges`, `verifyTotalMir_of_wpConverges`).
-/

/-! ## 1. General Coalgebraic Fuel Monotonicity (`wpCoalBounded`) -/

/--
Kleene fuel monotonicity for `wpCoalBounded` over any `StateEffectWP S E`:
increasing the fuel budget from `f₁` to `f₂ ≥ f₁` preserves any established
weakest precondition across `.ret`, `.tau`, and `.vis` effect branches.
-/
theorem wpCoalBounded_mono_fuel
    {S State : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {step : State → ITreeF E R State}
    {Q : R → S → Prop} {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂) :
    ∀ {st : State} {s : S},
      wpCoalBounded f₁ ewp step Q st s →
      wpCoalBounded f₂ ewp step Q st s := by
  induction f₁ generalizing f₂ with
  | zero =>
    intro st s h
    exact False.elim h
  | succ f₁' ih =>
    intro st s h
    cases f₂ with
    | zero => exact absurd h_le (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have h_le' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ h_le
      unfold wpCoalBounded at h ⊢
      cases h_step : step st with
      | ret r =>
        simp only [h_step] at h ⊢
        exact h
      | tau st' =>
        simp only [h_step] at h ⊢
        exact ih h_le' h
      | vis i k =>
        simp only [h_step] at h ⊢
        exact ewp.mono (fun _ _ hw => ih h_le' hw) h

/--
Combined fuel and postcondition monotonicity for `wpCoalBounded`.
-/
theorem wpCoalBounded_mono_both
    {S State : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} {step : State → ITreeF E R State}
    {P Q : R → S → Prop} {f₁ f₂ : Nat}
    (h_le : f₁ ≤ f₂)
    (h_imp : ∀ r s, P r s → Q r s)
    {st : State} {s : S}
    (h : wpCoalBounded f₁ ewp step P st s) :
    wpCoalBounded f₂ ewp step Q st s := by
  have h_f₂ := wpCoalBounded_mono_fuel h_le h
  clear h h_le f₁
  induction f₂ generalizing st s with
  | zero => exact False.elim h_f₂
  | succ f₂' ih =>
    unfold wpCoalBounded at h_f₂ ⊢
    cases h_step : step st with
    | ret r =>
      simp only [h_step] at h_f₂ ⊢
      exact h_imp r s h_f₂
    | tau st' =>
      simp only [h_step] at h_f₂ ⊢
      exact ih h_f₂
    | vis i k =>
      simp only [h_step] at h_f₂ ⊢
      exact ewp.mono (fun _ _ hw => ih hw) h_f₂

/--
Conjunction of two `wpCoalBounded` proofs at the same fuel budget for any
conjunctive `StateEffectWP`.
-/
theorem wpCoalBounded_conj
    {S State : Type u} {E : Effect.{u}} {R : Type u}
    {ewp : StateEffectWP S E} [h_conj : StateEffectWP.Conjunctive ewp]
    {step : State → ITreeF E R State}
    {P Q : R → S → Prop} {fuel : Nat} {st : State} {s : S}
    (hP : wpCoalBounded fuel ewp step P st s)
    (hQ : wpCoalBounded fuel ewp step Q st s) :
    wpCoalBounded fuel ewp step (fun r s' => P r s' ∧ Q r s') st s := by
  induction fuel generalizing st s with
  | zero => exact False.elim hP
  | succ fuel' ih =>
    unfold wpCoalBounded at hP hQ ⊢
    cases h_step : step st with
    | ret r =>
      simp only [h_step] at hP hQ ⊢
      exact ⟨hP, hQ⟩
    | tau st' =>
      simp only [h_step] at hP hQ ⊢
      exact ih hP hQ
    | vis i k =>
      simp only [h_step] at hP hQ ⊢
      exact ewp.mono (fun _ _ ⟨hp, hq⟩ => ih hp hq) (h_conj.conj hP hQ)

/-! ## 2. Kleene Fuel Monotonicity for `wpMirExecSym` and `wpMirSym` -/

/--
Postcondition weakening for `wpMirExecSym` (re-exported under an explicit suffix
so `wpMirExecSym_mono` denotes fuel monotonicity).
-/
theorem wpMirExecSym_mono_post
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirExecSym fuel body st P) :
    wpMirExecSym fuel body st Q :=
  Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirExecSym_mono h_imp h

/--
Postcondition weakening for `wpMirSym` (re-exported under an explicit suffix so
`wpMirSym_mono` denotes fuel monotonicity).
-/
theorem wpMirSym_mono_post
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirSym fuel body s P) :
    wpMirSym fuel body s Q :=
  Anneal.Rustc.V2026_06_01.SymbolicEval.wpMirSym_mono h_imp h

/--
Kleene fuel monotonicity for `wpMirExecSym`: if `wpMirExecSym f₁ body st post`
holds and `f₁ ≤ f₂`, then `wpMirExecSym f₂ body st post` holds.
-/
theorem wpMirExecSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h : wpMirExecSym f₁ body st post) :
    wpMirExecSym f₂ body st post := by
  rw [wpMirExecSym_eq_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_fuel h_le h

/--
Kleene fuel monotonicity for `wpMirSym`: if `wpMirSym f₁ body s post` holds and
`f₁ ≤ f₂`, then `wpMirSym f₂ body s post` holds.
-/
theorem wpMirSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirSym f₁ body s post) :
    wpMirSym f₂ body s post :=
  wpMirExecSym_mono h_le h

/--
Combined fuel (`f₁ ≤ f₂`) and postcondition (`P → Q`) monotonicity for
`wpMirExecSym`.
-/
theorem wpMirExecSym_mono_both
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirExecSym f₁ body st P) :
    wpMirExecSym f₂ body st Q :=
  wpMirExecSym_mono_post h_imp (wpMirExecSym_mono h_le h)

/--
Combined fuel (`f₁ ≤ f₂`) and postcondition (`P → Q`) monotonicity for
`wpMirSym`.
-/
theorem wpMirSym_mono_both
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirSym f₁ body s P) :
    wpMirSym f₂ body s Q :=
  wpMirSym_mono_post h_imp (wpMirSym_mono h_le h)

/-- Kleene fuel monotonicity for `Lower.wpMirBounded`. -/
theorem wpMirBounded_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirBounded f₁ body s post) :
    wpMirBounded f₂ body s post :=
  wpCoalBounded_mono_fuel h_le h

/-- Kleene fuel monotonicity for `wpMirExecNoCallSym`. -/
theorem wpMirExecNoCallSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h : wpMirExecNoCallSym f₁ body st post) :
    wpMirExecNoCallSym f₂ body st post := by
  rw [wpMirExecNoCallSym_eq_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_fuel h_le h

/-- Kleene fuel monotonicity for `wpMirNoCallSym`. -/
theorem wpMirNoCallSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirNoCallSym f₁ body s post) :
    wpMirNoCallSym f₂ body s post :=
  wpMirExecNoCallSym_mono h_le h

/-- Postcondition weakening for `wpMirExecNoCallSym`. -/
theorem wpMirExecNoCallSym_mono_post
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirExecNoCallSym fuel body st P) :
    wpMirExecNoCallSym fuel body st Q := by
  rw [wpMirExecNoCallSym_eq_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_both (Nat.le_refl fuel) (fun out _ hp => h_imp out hp) h

/-- Postcondition weakening for `wpMirNoCallSym`. -/
theorem wpMirNoCallSym_mono_post
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirNoCallSym fuel body s P) :
    wpMirNoCallSym fuel body s Q :=
  wpMirExecNoCallSym_mono_post h_imp h

/-- Every call-free `wpMirExecNoCallSym` proof implies `wpMirExecSym`. -/
theorem wpMirExecSym_of_wpMirExecNoCallSym
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {post : MirOutcome → Prop}
    (h : wpMirExecNoCallSym fuel body st post) :
    wpMirExecSym fuel body st post := by
  rw [wpMirExecNoCallSym_eq_wpCoalBounded] at h
  rw [wpMirExecSym_eq_wpCoalBounded]
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpCoalBounded at h ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      exact h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih h
      · exact False.elim h

/-- Every call-free `wpMirNoCallSym` proof implies `wpMirSym`. -/
theorem wpMirSym_of_wpMirNoCallSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirNoCallSym fuel body s post) :
    wpMirSym fuel body s post :=
  wpMirExecSym_of_wpMirExecNoCallSym h

/-- Kleene fuel monotonicity for `wpMirExecUbWaivedSym`. -/
theorem wpMirExecUbWaivedSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h : wpMirExecUbWaivedSym f₁ body st post) :
    wpMirExecUbWaivedSym f₂ body st post := by
  rw [wpMirExecUbWaivedSym_eq_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_fuel h_le h

/-- Kleene fuel monotonicity for `wpMirUbWaivedSym`. -/
theorem wpMirUbWaivedSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirUbWaivedSym f₁ body s post) :
    wpMirUbWaivedSym f₂ body s post :=
  wpMirExecUbWaivedSym_mono h_le h

/-- Kleene fuel monotonicity for `wpMirExecModularSym`. -/
theorem wpMirExecModularSym_mono
    {contract : MirCallContract} {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h : wpMirExecModularSym contract f₁ body st post) :
    wpMirExecModularSym contract f₂ body st post := by
  rw [wpMirExecModularSym_eq_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_fuel h_le h

/-- Kleene fuel monotonicity for `wpMirModularSym`. -/
theorem wpMirModularSym_mono
    {contract : MirCallContract} {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirModularSym contract f₁ body s post) :
    wpMirModularSym contract f₂ body s post :=
  wpMirExecModularSym_mono h_le h

/-- Kleene fuel monotonicity for `Lower.wpMirTraceBounded`. -/
theorem wpMirTraceBounded_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : wpMirTraceBounded f₁ body s post) :
    wpMirTraceBounded f₂ body s post :=
  wpCoalBounded_mono_fuel h_le h

/-- Kleene fuel monotonicity for `Lower.wpMirSilentBounded`. -/
theorem wpMirSilentBounded_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirSilentBounded f₁ body s post) :
    wpMirSilentBounded f₂ body s post :=
  wpCoalBounded_mono_fuel h_le h

/-- Postcondition weakening for `wpMirExecUbWaivedSym`. -/
theorem wpMirExecUbWaivedSym_mono_post
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirExecUbWaivedSym fuel body st P) :
    wpMirExecUbWaivedSym fuel body st Q := by
  rw [wpMirExecUbWaivedSym_eq_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_both (Nat.le_refl fuel) (fun out _ hp => h_imp out hp) h

/-- Postcondition weakening for `wpMirUbWaivedSym`. -/
theorem wpMirUbWaivedSym_mono_post
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirUbWaivedSym fuel body s P) :
    wpMirUbWaivedSym fuel body s Q :=
  wpMirExecUbWaivedSym_mono_post h_imp h

/-- Postcondition weakening for `wpMirExecModularSym`. -/
theorem wpMirExecModularSym_mono_post
    {contract : MirCallContract} {fuel : Nat} {body : CapturedMir}
    {st : MirExecState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirExecModularSym contract fuel body st P) :
    wpMirExecModularSym contract fuel body st Q := by
  rw [wpMirExecModularSym_eq_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_both (Nat.le_refl fuel) (fun out _ hp => h_imp out hp) h

/-- Postcondition weakening for `wpMirModularSym`. -/
theorem wpMirModularSym_mono_post
    {contract : MirCallContract} {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : wpMirModularSym contract fuel body s P) :
    wpMirModularSym contract fuel body s Q :=
  wpMirExecModularSym_mono_post h_imp h

/-- Every strict `wpMirExecSym` proof implies `wpMirExecUbWaivedSym`. -/
theorem wpMirExecUbWaivedSym_of_wpMirExecSym
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {post : MirOutcome → Prop}
    (h : wpMirExecSym fuel body st post) :
    wpMirExecUbWaivedSym fuel body st post := by
  rw [wpMirExecSym_eq_wpCoalBounded] at h
  rw [wpMirExecUbWaivedSym_eq_wpCoalBounded]
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpCoalBounded at h ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      exact h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih h
      · cases c
        intro ans
        exact ih (h ans)

/-- Every strict `wpMirSym` proof implies `wpMirUbWaivedSym`. -/
theorem wpMirUbWaivedSym_of_wpMirSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirSym fuel body s post) :
    wpMirUbWaivedSym fuel body s post :=
  wpMirExecUbWaivedSym_of_wpMirExecSym h

/-- Every call-free `wpMirExecNoCallSym` proof implies `wpMirExecModularSym`. -/
theorem wpMirExecModularSym_of_wpMirExecNoCallSym
    {contract : MirCallContract} {fuel : Nat} {body : CapturedMir}
    {st : MirExecState} {post : MirOutcome → Prop}
    (h : wpMirExecNoCallSym fuel body st post) :
    wpMirExecModularSym contract fuel body st post := by
  rw [wpMirExecNoCallSym_eq_wpCoalBounded] at h
  rw [wpMirExecModularSym_eq_wpCoalBounded]
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpCoalBounded at h ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      exact h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih h
      · exact False.elim h

/-- Every call-free `wpMirNoCallSym` proof implies `wpMirModularSym`. -/
theorem wpMirModularSym_of_wpMirNoCallSym
    {contract : MirCallContract} {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirNoCallSym fuel body s post) :
    wpMirModularSym contract fuel body s post :=
  wpMirExecModularSym_of_wpMirExecNoCallSym h

/-! ### Conjunction and Excluded-Miracle Laws for `wpMirExecSym` -/

/-- Conjunction of two `wpMirExecSym` proofs at the same fuel budget. -/
theorem wpMirExecSym_conj
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P Q : MirOutcome → Prop}
    (hP : wpMirExecSym fuel body st P)
    (hQ : wpMirExecSym fuel body st Q) :
    wpMirExecSym fuel body st (fun out => P out ∧ Q out) := by
  rw [wpMirExecSym_eq_wpCoalBounded] at hP hQ ⊢
  induction fuel generalizing st with
  | zero => exact False.elim hP
  | succ fuel' ih =>
    unfold wpCoalBounded at hP hQ ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at hP hQ ⊢
      exact ⟨hP, hQ⟩
    | tau st' =>
      simp only [h_step] at hP hQ ⊢
      exact ih hP hQ
    | vis i k =>
      simp only [h_step] at hP hQ ⊢
      rcases i with f | (e | c)
      · exact False.elim hP
      · cases e
        exact ih hP hQ
      · cases c
        intro ans
        exact ih (hP ans) (hQ ans)

/-- Conjunction of two `wpMirSym` proofs at the same fuel budget. -/
theorem wpMirSym_conj
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {P Q : MirOutcome → Prop}
    (hP : wpMirSym fuel body s P)
    (hQ : wpMirSym fuel body s Q) :
    wpMirSym fuel body s (fun out => P out ∧ Q out) :=
  wpMirExecSym_conj hP hQ

/--
Excluded-miracle law for `wpMirExecSym`: no finite-fuel symbolic execution can
establish the empty postcondition `fun _ => False`.
-/
theorem wpMirExecSym_not_false
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) :
    ¬ wpMirExecSym fuel body st (fun _ => False) := by
  intro h
  rw [wpMirExecSym_eq_wpCoalBounded] at h
  induction fuel generalizing st with
  | zero => exact h
  | succ fuel' ih =>
    unfold wpCoalBounded at h
    revert h
    cases stepMirState body st with
    | ret out =>
      intro h; exact h
    | tau st' =>
      intro h; exact ih st' h
    | vis i k =>
      rcases i with f | (e | c)
      · intro h; exact h
      · cases e; intro h; exact ih (k PUnit.unit) h
      · cases c; intro h; exact ih (k .aborted) (h .aborted)

/-- Excluded-miracle law for `wpMirSym`. -/
theorem wpMirSym_not_false
    (fuel : Nat) (body : CapturedMir) (s : MachineState) :
    ¬ wpMirSym fuel body s (fun _ => False) :=
  wpMirExecSym_not_false fuel body (.running s)

/--
Every `wpMirExecSym fuel body st P` proof witnesses that `P` is satisfiable by
some `MirOutcome` (and constructively extracts a reachable outcome along the
canonical `.aborted` call probe).
-/
theorem wpMirExecSym_exists_outcome
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P : MirOutcome → Prop}
    (h : wpMirExecSym fuel body st P) :
    ∃ out : MirOutcome, P out := by
  rw [wpMirExecSym_eq_wpCoalBounded] at h
  induction fuel generalizing st with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpCoalBounded at h
    revert h
    cases stepMirState body st with
    | ret out =>
      intro h; exact ⟨out, h⟩
    | tau st' =>
      intro h; exact ih h
    | vis i k =>
      rcases i with f | (e | c)
      · intro h; exact False.elim h
      · cases e; intro h; exact ih h
      · cases c; intro h; exact ih (h .aborted)

/-- Every `wpMirSym fuel body s P` proof witnesses `∃ out, P out`. -/
theorem wpMirSym_exists_outcome
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {P : MirOutcome → Prop}
    (h : wpMirSym fuel body s P) :
    ∃ out : MirOutcome, P out :=
  wpMirExecSym_exists_outcome h

/-! ## 3. Computable Bounded Runner (`runMirBounded`) & Runner Monotonicity -/

/--
Computable bounded MIR evaluator over `MirExecState`: steps `stepMirState body`
across `.tau` and `MirObsE` transitions for up to `fuel` steps, returning
`some out` on `.ret out` and `none` on fuel exhaustion, fault, or unresolved
external call.
-/
def runMirExecBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState) : Option MirOutcome :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stepMirState body st with
    | .ret out => some out
    | .tau st' => runMirExecBounded fuel' body st'
    | .vis (.inr (.inl _)) k => runMirExecBounded fuel' body (k PUnit.unit)
    | .vis (.inl _) _ => none
    | .vis (.inr (.inr _)) _ => none

/--
Computable bounded MIR evaluator starting from `s : MachineState`.
-/
def runMirBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState) : Option MirOutcome :=
  runMirExecBounded fuel body (.running s)

/--
Kleene fuel monotonicity for `runMirExecBounded`: if `runMirExecBounded f₁`
returns `some out` and `f₁ ≤ f₂`, then `runMirExecBounded f₂` returns `some out`.
-/
theorem runMirExecBounded_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {out : MirOutcome}
    (h : runMirExecBounded f₁ body st = some out) :
    runMirExecBounded f₂ body st = some out := by
  induction f₁ generalizing f₂ st with
  | zero => nomatch h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd h_le (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have h_le' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ h_le
      unfold runMirExecBounded at h ⊢
      cases h_step : stepMirState body st with
      | ret out₀ =>
        simp only [h_step] at h ⊢
        exact h
      | tau st' =>
        simp only [h_step] at h ⊢
        exact ih h_le' h
      | vis i k =>
        rcases i with f | (e | c)
        · simp only [h_step] at h; nomatch h
        · simp only [h_step] at h ⊢
          exact ih h_le' h
        · simp only [h_step] at h; nomatch h

/--
Kleene fuel monotonicity for `runMirBounded`: if `runMirBounded f₁ body s = some out`
and `f₁ ≤ f₂`, then `runMirBounded f₂ body s = some out`.
-/
theorem runMirBounded_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h : runMirBounded f₁ body s = some out) :
    runMirBounded f₂ body s = some out :=
  runMirExecBounded_mono h_le h

/--
Determinism of `runMirExecBounded` across any two fuel budgets `f₁` and `f₂`.
-/
theorem runMirExecBounded_det
    {f₁ f₂ : Nat} {body : CapturedMir} {st : MirExecState}
    {out₁ out₂ : MirOutcome}
    (h₁ : runMirExecBounded f₁ body st = some out₁)
    (h₂ : runMirExecBounded f₂ body st = some out₂) :
    out₁ = out₂ := by
  have h₁' := runMirExecBounded_mono (Nat.le_max_left f₁ f₂) h₁
  have h₂' := runMirExecBounded_mono (Nat.le_max_right f₁ f₂) h₂
  rw [h₁'] at h₂'
  injection h₂'

/--
Determinism of `runMirBounded` across any two fuel budgets `f₁` and `f₂`.
-/
theorem runMirBounded_det
    {f₁ f₂ : Nat} {body : CapturedMir} {s : MachineState}
    {out₁ out₂ : MirOutcome}
    (h₁ : runMirBounded f₁ body s = some out₁)
    (h₂ : runMirBounded f₂ body s = some out₂) :
    out₁ = out₂ :=
  runMirExecBounded_det h₁ h₂

/-- Soundness of `runMirExecBounded` with respect to `wpMirExecNoCallSym`. -/
theorem wpMirExecNoCallSym_of_runMirExecBounded
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_run : runMirExecBounded fuel body st = some out)
    (h_post : post out) :
    wpMirExecNoCallSym fuel body st post := by
  rw [wpMirExecNoCallSym_eq_wpCoalBounded]
  induction fuel generalizing st with
  | zero => nomatch h_run
  | succ fuel' ih =>
    unfold runMirExecBounded at h_run
    unfold wpCoalBounded
    cases h_step : stepMirState body st with
    | ret out₀ =>
      simp only [h_step] at h_run ⊢
      injection h_run with h_eq
      subst h_eq
      exact h_post
    | tau st' =>
      simp only [h_step] at h_run ⊢
      exact ih h_run
    | vis i k =>
      rcases i with f | (e | c)
      · simp only [h_step] at h_run; nomatch h_run
      · simp only [h_step] at h_run ⊢
        cases e
        exact ih h_run
      · simp only [h_step] at h_run; nomatch h_run

/-- Soundness of `runMirBounded` with respect to `wpMirNoCallSym`. -/
theorem wpMirNoCallSym_of_runMirBounded
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_run : runMirBounded fuel body s = some out)
    (h_post : post out) :
    wpMirNoCallSym fuel body s post :=
  wpMirExecNoCallSym_of_runMirExecBounded h_run h_post

/-- Soundness of `runMirExecBounded` with respect to `wpMirExecSym`. -/
theorem wpMirExecSym_of_runMirExecBounded
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_run : runMirExecBounded fuel body st = some out)
    (h_post : post out) :
    wpMirExecSym fuel body st post :=
  wpMirExecSym_of_wpMirExecNoCallSym
    (wpMirExecNoCallSym_of_runMirExecBounded h_run h_post)

/-- Soundness of `runMirBounded` with respect to `wpMirSym`. -/
theorem wpMirSym_of_runMirBounded
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_run : runMirBounded fuel body s = some out)
    (h_post : post out) :
    wpMirSym fuel body s post :=
  wpMirExecSym_of_runMirExecBounded h_run h_post

/-! ### Fuel Monotonicity for `FunctionalTranslation` & `SymbolicEval` Runners -/

/-- Kleene fuel monotonicity for `runMirTauToRet`. -/
theorem runMirTauToRet_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h : runMirTauToRet f₁ body s = some out) :
    runMirTauToRet f₂ body s = some out := by
  induction f₁ generalizing f₂ s with
  | zero => nomatch h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd h_le (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have h_le' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ h_le
      unfold runMirTauToRet at h ⊢
      cases h_step : stepMirFn body s with
      | ret out₀ =>
        simp only [h_step] at h ⊢
        exact h
      | vis _ _ =>
        simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h ⊢
        cases execNext with
        | running s' => exact ih h_le' h
        | halted out₀ => exact h
        | faulted _ => nomatch h

/-- Kleene fuel monotonicity for `runMirTauToBlock`. -/
theorem runMirTauToBlock_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState}
    (h : runMirTauToBlock f₁ body targetBlock s = some s') :
    runMirTauToBlock f₂ body targetBlock s = some s' := by
  induction f₁ generalizing f₂ s with
  | zero => nomatch h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd h_le (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have h_le' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ h_le
      unfold runMirTauToBlock at h ⊢
      revert h
      split
      · intro h; exact h
      · intro h; cases h_step : stepMirFn body s with
        | ret _ => simp only [h_step] at h; nomatch h
        | vis _ _ => simp only [h_step] at h; nomatch h
        | tau execNext =>
          simp only [h_step] at h ⊢
          cases execNext with
          | running s₁ => exact ih h_le' h
          | halted _ => nomatch h
          | faulted _ => nomatch h

/-- Kleene fuel monotonicity for `runMirToBlock`. -/
theorem runMirToBlock_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState}
    (h : runMirToBlock f₁ body targetBlock s = some s') :
    runMirToBlock f₂ body targetBlock s = some s' := by
  induction f₁ generalizing f₂ s with
  | zero => nomatch h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd h_le (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have h_le' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ h_le
      unfold runMirToBlock at h ⊢
      revert h
      split
      · intro h; exact h
      · intro h; cases h_step : stepMirFn body s with
        | ret _ => simp only [h_step] at h; nomatch h
        | tau execNext =>
          simp only [h_step] at h ⊢
          cases execNext with
          | running s₁ => exact ih h_le' h
          | halted _ => nomatch h
          | faulted _ => nomatch h
        | vis req k =>
          simp only [h_step] at h ⊢
          rcases req with f | (e | c)
          · nomatch h
          · cases e
            cases hk : k PUnit.unit with
            | running s₁ =>
              simp only [hk] at h ⊢
              exact ih h_le' h
            | halted _ => simp only [hk] at h; nomatch h
            | faulted _ => simp only [hk] at h; nomatch h
          · nomatch h

/-- Kleene fuel monotonicity for `runMirToBinarySwitch`. -/
theorem runMirToBinarySwitch_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState}
    {res : Bool × Nat × MachineState × MachineState}
    (h : runMirToBinarySwitch f₁ body s = some res) :
    runMirToBinarySwitch f₂ body s = some res := by
  induction f₁ generalizing f₂ s with
  | zero => nomatch h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd h_le (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have h_le' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ h_le
      unfold runMirToBinarySwitch at h ⊢
      cases h_sw : inspectBinarySwitch body s with
      | some sw =>
        simp only [h_sw] at h ⊢
        exact h
      | none =>
        simp only [h_sw] at h ⊢
        cases h_step : stepMirFn body s with
        | ret _ => simp only [h_step] at h; nomatch h
        | vis _ _ => simp only [h_step] at h; nomatch h
        | tau execNext =>
          simp only [h_step] at h ⊢
          cases execNext with
          | running s₁ => exact ih h_le' h
          | halted _ => nomatch h
          | faulted _ => nomatch h

/-- Kleene fuel monotonicity for `checkMirBoolExecBounded`. -/
theorem checkMirBoolExecBounded_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState}
    (h : checkMirBoolExecBounded f₁ body st = true) :
    checkMirBoolExecBounded f₂ body st = true := by
  induction f₁ generalizing f₂ st with
  | zero => nomatch h
  | succ f₁' ih =>
    cases f₂ with
    | zero => exact absurd h_le (Nat.not_succ_le_zero f₁')
    | succ f₂' =>
      have h_le' : f₁' ≤ f₂' := Nat.le_of_succ_le_succ h_le
      unfold checkMirBoolExecBounded at h ⊢
      simp only [Anneal.Rustc.V2026_06_01.SymbolicEval.stepMirStatePeriodic_eq] at h ⊢
      revert h
      cases stepMirState body st with
      | ret out =>
        intro h; clear ih; revert h
        cases out
        · rename_i rv; rcases rv with ⟨val, mem'⟩
          split <;> intro h <;> try (rename_i heq; cases heq) <;> exact h
        · intro h; exact h
        · intro h; exact h
      | tau st' =>
        intro h
        exact ih h_le' h
      | vis i k =>
        rcases i with f | (e | c)
        · intro h; nomatch h
        · intro h; exact ih h_le' h
        · intro h; nomatch h

/-- Kleene fuel monotonicity for `checkMirBoolBounded`. -/
theorem checkMirBoolBounded_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {specBody : CapturedMir} {args : List Value}
    (h : checkMirBoolBounded f₁ specBody args = true) :
    checkMirBoolBounded f₂ specBody args = true :=
  checkMirBoolExecBounded_mono h_le h

/-! ## 4. Fuel-Free Predicates (`MirWpConverges` & `MirConverges`) -/

/--
Fuel-free symbolic weakest precondition over `MirExecState`, defined as the
Kleene supremum `∃ fuel : Nat, wpMirExecSym fuel body st post`.
-/
def MirExecWpConverges
    (body : CapturedMir) (st : MirExecState) (post : MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirExecSym fuel body st post

/--
Fuel-free symbolic weakest precondition over `MachineState`, defined as the
Kleene supremum `∃ fuel : Nat, wpMirSym fuel body s post`.
-/
def MirWpConverges
    (body : CapturedMir) (s : MachineState) (post : MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirSym fuel body s post

/--
Fuel-free deterministic outcome convergence over `MirExecState`.
-/
def MirExecConverges
    (body : CapturedMir) (st : MirExecState) (out : MirOutcome) : Prop :=
  MirExecWpConverges body st (· = out)

/--
Fuel-free deterministic outcome convergence over `MachineState`.
-/
def MirConverges
    (body : CapturedMir) (s : MachineState) (out : MirOutcome) : Prop :=
  MirWpConverges body s (· = out)

/--
Fuel-free call-forbidding symbolic weakest precondition over `MachineState`.
-/
def MirNoCallWpConverges
    (body : CapturedMir) (s : MachineState) (post : MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirNoCallSym fuel body s post

@[simp]
theorem mirWpConverges_eq_mirExecWpConverges
    (body : CapturedMir) (s : MachineState) (post : MirOutcome → Prop) :
    MirWpConverges body s post = MirExecWpConverges body (.running s) post :=
  rfl

@[simp]
theorem mirConverges_eq_mirExecConverges
    (body : CapturedMir) (s : MachineState) (out : MirOutcome) :
    MirConverges body s out = MirExecConverges body (.running s) out :=
  rfl

/-- Lift any bounded `wpMirExecSym` proof into `MirExecWpConverges`. -/
theorem MirExecWpConverges.of_wpMirExecSym
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {post : MirOutcome → Prop}
    (h : wpMirExecSym fuel body st post) :
    MirExecWpConverges body st post :=
  ⟨fuel, h⟩

/-- Lift any bounded `wpMirSym` proof into `MirWpConverges`. -/
theorem MirWpConverges.of_wpMirSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirSym fuel body s post) :
    MirWpConverges body s post :=
  ⟨fuel, h⟩

/-- Lift any bounded `Lower.wpMirBounded` proof into `MirWpConverges`. -/
theorem MirWpConverges.of_wpMirBounded
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirBounded fuel body s post) :
    MirWpConverges body s post :=
  ⟨fuel, (wpMirSym_eq_wpMirBounded fuel body s post).symm ▸ h⟩

/-- Lift any call-free `MirNoCallWpConverges` proof into `MirWpConverges`. -/
theorem MirWpConverges.of_noCall
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirNoCallWpConverges body s post) :
    MirWpConverges body s post := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirSym_of_wpMirNoCallSym h_wp⟩

/-- Lift any bounded `wpMirNoCallSym` proof into `MirNoCallWpConverges`. -/
theorem MirNoCallWpConverges.of_wpMirNoCallSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirNoCallSym fuel body s post) :
    MirNoCallWpConverges body s post :=
  ⟨fuel, h⟩

/-- Lift a computable `runMirBounded` evaluation into `MirNoCallWpConverges`. -/
theorem MirNoCallWpConverges.of_runMirBounded
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_run : runMirBounded fuel body s = some out)
    (h_post : post out) :
    MirNoCallWpConverges body s post :=
  ⟨fuel, wpMirNoCallSym_of_runMirBounded h_run h_post⟩

/-- Lift a computable `runMirBounded` evaluation into `MirWpConverges`. -/
theorem MirWpConverges.of_runMirBounded
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_run : runMirBounded fuel body s = some out)
    (h_post : post out) :
    MirWpConverges body s post :=
  ⟨fuel, wpMirSym_of_runMirBounded h_run h_post⟩

/-- Lift a computable `runMirBounded` evaluation into `MirConverges`. -/
theorem MirConverges.of_runMirBounded
    {fuel : Nat} {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h_run : runMirBounded fuel body s = some out) :
    MirConverges body s out :=
  MirWpConverges.of_runMirBounded h_run rfl

/-- Lift a computable `runMirTauToRet` evaluation into `MirConverges`. -/
theorem MirConverges.of_runMirTauToRet
    {fuel : Nat} {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h_run : runMirTauToRet fuel body s = some out) :
    MirConverges body s out := by
  have h_run_b : ∀ {f : Nat} {st : MachineState},
      runMirTauToRet f body st = some out →
      runMirExecBounded (f + 1) body (.running st) = some out := by
    intro f
    induction f with
    | zero => intro _ h; nomatch h
    | succ f' ih =>
      intro st h
      unfold runMirTauToRet at h
      unfold runMirExecBounded
      dsimp only [stepMirState]
      cases h_step : stepMirFn body st with
      | ret out₀ =>
        simp only [h_step] at h ⊢
        exact h
      | vis _ _ =>
        simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h ⊢
        cases execNext with
        | running s' => exact ih h
        | halted out₀ =>
          unfold runMirExecBounded
          dsimp only [stepMirState]
          exact h
        | faulted _ => nomatch h
  exact MirConverges.of_runMirBounded (h_run_b h_run)

/-- Lift a computable `runMirTauToRet` evaluation into `MirWpConverges`. -/
theorem MirWpConverges.of_runMirTauToRet
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_run : runMirTauToRet fuel body s = some out)
    (h_post : post out) :
    MirWpConverges body s post := by
  rcases MirConverges.of_runMirTauToRet h_run with ⟨f, hf⟩
  exact ⟨f, wpMirSym_mono_post (fun x (h_eq : x = out) => h_eq ▸ h_post) hf⟩

/-- Postcondition monotonicity for `MirExecWpConverges`. -/
theorem MirExecWpConverges.mono
    {body : CapturedMir} {st : MirExecState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : MirExecWpConverges body st P) :
    MirExecWpConverges body st Q := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_mono_post h_imp h_wp⟩

/-- Postcondition monotonicity for `MirWpConverges`. -/
theorem MirWpConverges.mono
    {body : CapturedMir} {s : MachineState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : MirWpConverges body s P) :
    MirWpConverges body s Q :=
  MirExecWpConverges.mono h_imp h

/-- Postcondition monotonicity for `MirNoCallWpConverges`. -/
theorem MirNoCallWpConverges.mono
    {body : CapturedMir} {s : MachineState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : MirNoCallWpConverges body s P) :
    MirNoCallWpConverges body s Q := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirNoCallSym_mono_post h_imp h_wp⟩

/--
Convert a deterministic outcome proof `MirConverges body s out` and `post out`
into `MirWpConverges body s post`.
-/
theorem MirWpConverges.of_mirConverges
    {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_conv : MirConverges body s out)
    (h_post : post out) :
    MirWpConverges body s post :=
  MirWpConverges.mono (fun x (h_eq : x = out) => h_eq ▸ h_post) h_conv

/-- Alias for `MirWpConverges.of_mirConverges`. -/
theorem MirConverges.to_mirWpConverges
    {body : CapturedMir} {s : MachineState}
    {out : MirOutcome} {post : MirOutcome → Prop}
    (h_conv : MirConverges body s out)
    (h_post : post out) :
    MirWpConverges body s post :=
  MirWpConverges.of_mirConverges h_conv h_post

/--
Conjunction of two fuel-free `MirExecWpConverges` proofs by aligning fuel to
`max f₁ f₂` via `wpMirExecSym_mono`.
-/
theorem MirExecWpConverges.conj
    {body : CapturedMir} {st : MirExecState} {P Q : MirOutcome → Prop}
    (hP : MirExecWpConverges body st P)
    (hQ : MirExecWpConverges body st Q) :
    MirExecWpConverges body st (fun out => P out ∧ Q out) := by
  rcases hP with ⟨f₁, h₁⟩
  rcases hQ with ⟨f₂, h₂⟩
  exact ⟨max f₁ f₂,
    wpMirExecSym_conj
      (wpMirExecSym_mono (Nat.le_max_left f₁ f₂) h₁)
      (wpMirExecSym_mono (Nat.le_max_right f₁ f₂) h₂)⟩

/--
Conjunction of two fuel-free `MirWpConverges` proofs by aligning fuel to
`max f₁ f₂` via `wpMirSym_mono`.
-/
theorem MirWpConverges.conj
    {body : CapturedMir} {s : MachineState} {P Q : MirOutcome → Prop}
    (hP : MirWpConverges body s P)
    (hQ : MirWpConverges body s Q) :
    MirWpConverges body s (fun out => P out ∧ Q out) :=
  MirExecWpConverges.conj hP hQ

/-- Excluded-miracle law for `MirExecWpConverges`. -/
theorem MirExecWpConverges.not_false
    (body : CapturedMir) (st : MirExecState) :
    ¬ MirExecWpConverges body st (fun _ => False) := by
  rintro ⟨fuel, h⟩
  exact wpMirExecSym_not_false fuel body st h

/-- Excluded-miracle law for `MirWpConverges`. -/
theorem MirWpConverges.not_false
    (body : CapturedMir) (s : MachineState) :
    ¬ MirWpConverges body s (fun _ => False) :=
  MirExecWpConverges.not_false body (.running s)

/-- Every `MirExecWpConverges body st P` proof witnesses `∃ out, P out`. -/
theorem MirExecWpConverges.exists_outcome
    {body : CapturedMir} {st : MirExecState} {P : MirOutcome → Prop}
    (h : MirExecWpConverges body st P) :
    ∃ out : MirOutcome, P out := by
  rcases h with ⟨fuel, h_wp⟩
  exact wpMirExecSym_exists_outcome h_wp

/-- Every `MirWpConverges body s P` proof witnesses `∃ out, P out`. -/
theorem MirWpConverges.exists_outcome
    {body : CapturedMir} {s : MachineState} {P : MirOutcome → Prop}
    (h : MirWpConverges body s P) :
    ∃ out : MirOutcome, P out :=
  MirExecWpConverges.exists_outcome h

/--
Outcome uniqueness / determinism for `MirExecConverges`: if `st` converges to
`out₁` and to `out₂`, then `out₁ = out₂`.
-/
theorem MirExecConverges.det
    {body : CapturedMir} {st : MirExecState} {out₁ out₂ : MirOutcome}
    (h₁ : MirExecConverges body st out₁)
    (h₂ : MirExecConverges body st out₂) :
    out₁ = out₂ := by
  rcases MirExecWpConverges.exists_outcome (MirExecWpConverges.conj h₁ h₂) with
    ⟨out, rfl, h_eq⟩
  exact h_eq

/--
Outcome uniqueness / determinism for `MirConverges`: if `(body, s)` converges to
`out₁` and to `out₂`, then `out₁ = out₂`.
-/
theorem MirConverges.det
    {body : CapturedMir} {s : MachineState} {out₁ out₂ : MirOutcome}
    (h₁ : MirConverges body s out₁)
    (h₂ : MirConverges body s out₂) :
    out₁ = out₂ :=
  MirExecConverges.det h₁ h₂

/--
Definitional equivalence between `MirWpConverges body s (· = out)` and
`MirConverges body s out`.
-/
@[simp]
theorem MirWpConverges.iff_mirConverges_eq
    (body : CapturedMir) (s : MachineState) (out : MirOutcome) :
    MirWpConverges body s (· = out) ↔ MirConverges body s out :=
  Iff.rfl

/--
Once `MirConverges body s out` holds, any fuel-free weakest precondition
`MirWpConverges body s post` is equivalent to `post out`.
-/
theorem MirConverges.iff_wpConverges_of_det
    {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    {post : MirOutcome → Prop}
    (h_conv : MirConverges body s out) :
    MirWpConverges body s post ↔ post out := by
  constructor
  · intro h_wp
    rcases MirWpConverges.exists_outcome (MirWpConverges.conj h_conv h_wp) with
      ⟨out', rfl, h_post⟩
    exact h_post
  · intro h_post
    exact MirWpConverges.of_mirConverges h_conv h_post

/--
Conjunction of two call-free `wpMirExecNoCallSym` proofs at the same fuel budget.
-/
theorem wpMirExecNoCallSym_conj
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {P Q : MirOutcome → Prop}
    (hP : wpMirExecNoCallSym fuel body st P)
    (hQ : wpMirExecNoCallSym fuel body st Q) :
    wpMirExecNoCallSym fuel body st (fun out => P out ∧ Q out) := by
  rw [wpMirExecNoCallSym_eq_wpCoalBounded] at hP hQ ⊢
  induction fuel generalizing st with
  | zero => exact False.elim hP
  | succ fuel' ih =>
    unfold wpCoalBounded at hP hQ ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at hP hQ ⊢
      exact ⟨hP, hQ⟩
    | tau st' =>
      simp only [h_step] at hP hQ ⊢
      exact ih hP hQ
    | vis i k =>
      simp only [h_step] at hP hQ ⊢
      rcases i with f | (e | c)
      · exact False.elim hP
      · cases e
        exact ih hP hQ
      · exact False.elim hP

/--
Conjunction of two fuel-free `MirNoCallWpConverges` proofs by aligning fuel to
`max f₁ f₂`.
-/
theorem MirNoCallWpConverges.conj
    {body : CapturedMir} {s : MachineState} {P Q : MirOutcome → Prop}
    (hP : MirNoCallWpConverges body s P)
    (hQ : MirNoCallWpConverges body s Q) :
    MirNoCallWpConverges body s (fun out => P out ∧ Q out) := by
  rcases hP with ⟨f₁, h₁⟩
  rcases hQ with ⟨f₂, h₂⟩
  exact ⟨max f₁ f₂,
    wpMirExecNoCallSym_conj
      (wpMirNoCallSym_mono (Nat.le_max_left f₁ f₂) h₁)
      (wpMirNoCallSym_mono (Nat.le_max_right f₁ f₂) h₂)⟩

/-! ## 5. Fuel-Free Step and Sequential Composition (`step` & `bind`) -/

/--
Every `evalSymNodeTreeNoCall` node evaluation implies `evalSymNodeTree`.
-/
theorem evalSymNodeTree_of_evalSymNodeTreeNoCall
    {cont : MirExecState → Prop} {post : MirOutcome → Prop}
    {t : SymTree MirStepNode}
    (h : evalSymNodeTreeNoCall cont post t) :
    evalSymNodeTree cont post t := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => exact h
    | tau _ => exact h
    | vis i _ =>
      rcases i with f | (e | c)
      · exact False.elim h
      · exact h
      · exact False.elim h
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2 h
    · exact ih1 h

/--
Constructive fuel extraction across `SymTree MirStepNode` for call-free symbolic
transitions: because every `.branch c t1 t2` splits on a concrete `Bool` and
every non-failing leaf has at most one successor `MirExecState`, an existential
fuel witness inside the continuation commutes outward without choice.
-/
theorem evalSymNodeTreeNoCall_exists_fuel
    {cont : Nat → MirExecState → Prop} {post : MirOutcome → Prop}
    (t : SymTree MirStepNode)
    (h : evalSymNodeTreeNoCall (fun st' => ∃ f, cont f st') post t) :
    ∃ f : Nat, evalSymNodeTreeNoCall (cont f) post t := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => exact ⟨0, h⟩
    | tau _ => exact h
    | vis i _ =>
      rcases i with f | (e | c)
      · exact False.elim h
      · exact h
      · exact False.elim h
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2 h
    · exact ih1 h

/-- Halted execution state converges immediately in 1 step. -/
theorem MirExecWpConverges.halted
    {body : CapturedMir} {out : MirOutcome} {post : MirOutcome → Prop}
    (h : post out) :
    MirExecWpConverges body (.halted out) post :=
  ⟨1, h⟩

/-- Single-step `.ret` rule for `MirWpConverges`. -/
theorem MirWpConverges.ret_of_step
    {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    {post : MirOutcome → Prop}
    (h_step : stepMirFn body s = .ret out)
    (h_post : post out) :
    MirWpConverges body s post := by
  refine ⟨1, ?_⟩
  unfold wpMirSym wpMirExecSym
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_post

/-- Single-step silent `.tau` transition rule for `MirWpConverges`. -/
theorem MirWpConverges.step_tau
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h_step : stepMirFn body s = .tau (.running s'))
    (h_next : MirWpConverges body s' post) :
    MirWpConverges body s post := by
  rcases h_next with ⟨fuel, h_wp⟩
  refine ⟨fuel + 1, ?_⟩
  unfold wpMirSym wpMirExecSym
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_wp

/-- Single-step `MirObsE` emission rule for `MirWpConverges`. -/
theorem MirWpConverges.step_emit
    {body : CapturedMir} {s s' : MachineState} {obs : MirObs}
    {post : MirOutcome → Prop}
    (h_step : stepMirFn body s = MirStepNode.emitStep obs s')
    (h_next : MirWpConverges body s' post) :
    MirWpConverges body s post := by
  rcases h_next with ⟨fuel, h_wp⟩
  refine ⟨fuel + 1, ?_⟩
  unfold wpMirSym wpMirExecSym
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
  dsimp only [stepMirState]
  rw [h_step]
  cases obs <;> (dsimp [MirStepNode.emitStep]; exact h_wp)

/--
Fuel-free single-step symbolic unfolding rule for `MirExecWpConverges` via
`stepMirExecSymTree`.
-/
theorem MirExecWpConverges.step
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h :
      evalSymNodeTreeNoCall
        (fun st' => MirExecWpConverges body st' post)
        post
        (stepMirExecSymTree body st)) :
    MirExecWpConverges body st post := by
  rcases evalSymNodeTreeNoCall_exists_fuel (stepMirExecSymTree body st) h with
    ⟨fuel, h_fuel⟩
  exact ⟨fuel + 1, evalSymNodeTree_of_evalSymNodeTreeNoCall h_fuel⟩

/--
Fuel-free single-step symbolic unfolding rule for `MirWpConverges` via
`stepMirSymTree`.
-/
theorem MirWpConverges.step
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h :
      evalSymNodeTreeNoCall
        (fun st' => MirExecWpConverges body st' post)
        post
        (stepMirSymTree body s)) :
    MirWpConverges body s post :=
  MirExecWpConverges.step h

/--
Fuel-free single-step symbolic unfolding rule for `MirWpConverges` with an
explicit uniform continuation fuel witness (supporting external `.call` nodes).
-/
theorem MirWpConverges.step_uniform
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    {fuel : Nat}
    (h :
      evalSymNodeTree
        (fun st' => wpMirExecSym fuel body st' post)
        post
        (stepMirSymTree body s)) :
    MirWpConverges body s post :=
  ⟨fuel + 1, h⟩

/-! ### Multi-Step Symbolic Reachability (`wpMirStepsSym` & `MirStepsConverges`) -/

/--
Single-pass fuel-bounded symbolic state-to-state stepper over `MirExecState`:
steps `stepMirExecSymTree body` for `fuel` steps to an intermediate state
satisfying `mid` (or halts early with `post`).
-/
def wpMirExecStepsSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (mid : MirExecState → Prop) (post : MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => mid st
  | fuel' + 1 =>
    evalSymNodeTreeNoCall
      (fun st' => wpMirExecStepsSym fuel' body st' mid post)
      post
      (stepMirExecSymTree body st)

/--
Single-pass fuel-bounded symbolic state-to-state stepper over `MachineState`:
steps `body` from `s` for `fuel` steps to an intermediate `MachineState`
satisfying `mid` (or halts early with `post`).
-/
def wpMirStepsSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (mid : MachineState → Prop)
    (post : MirOutcome → Prop := fun _ => False) : Prop :=
  wpMirExecStepsSym fuel body (.running s)
    (fun
      | .running s' => mid s'
      | .halted out => post out
      | .faulted _ => False)
    post

/--
Fuel-free intermediate state convergence over `MirExecState`.
-/
def MirExecStepsConverges
    (body : CapturedMir) (st : MirExecState)
    (mid : MirExecState → Prop) (post : MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirExecStepsSym fuel body st mid post

/--
Fuel-free intermediate state convergence over `MachineState`: there exists a
finite step count `fuel` after which `body` from `s` reaches a state satisfying
`mid` (or halts early satisfying `post`).
-/
def MirStepsConverges
    (body : CapturedMir) (s : MachineState)
    (mid : MachineState → Prop)
    (post : MirOutcome → Prop := fun _ => False) : Prop :=
  ∃ fuel : Nat, wpMirStepsSym fuel body s mid post

/--
Fuel-free state-to-state reachability from `s` to a target `MachineState` `s'`.
-/
def MirReachState
    (body : CapturedMir) (s s' : MachineState) : Prop :=
  MirStepsConverges body s (· = s') (fun _ => False)

/-- Lift a bounded `wpMirStepsSym` proof into `MirStepsConverges`. -/
theorem MirStepsConverges.of_wpMirStepsSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : wpMirStepsSym fuel body s mid post) :
    MirStepsConverges body s mid post :=
  ⟨fuel, h⟩

/-- Zero-step reflexivity for `MirStepsConverges`. -/
theorem MirStepsConverges.refl
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : mid s) :
    MirStepsConverges body s mid post :=
  ⟨0, h⟩

/-- Monotonicity of `wpMirExecStepsSym` in both `mid` and `post`. -/
theorem wpMirExecStepsSym_mono
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {mid₁ mid₂ : MirExecState → Prop} {post₁ post₂ : MirOutcome → Prop}
    (h_mid : ∀ st', mid₁ st' → mid₂ st')
    (h_post : ∀ out, post₁ out → post₂ out)
    (h : wpMirExecStepsSym fuel body st mid₁ post₁) :
    wpMirExecStepsSym fuel body st mid₂ post₂ := by
  induction fuel generalizing st with
  | zero => exact h_mid st h
  | succ fuel' ih =>
    unfold wpMirExecStepsSym at h ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      exact h_post out h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih h
      · exact False.elim h

/-- Monotonicity of `wpMirStepsSym` in both `mid` and `post`. -/
theorem wpMirStepsSym_mono
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {mid₁ mid₂ : MachineState → Prop} {post₁ post₂ : MirOutcome → Prop}
    (h_mid : ∀ s', mid₁ s' → mid₂ s')
    (h_post : ∀ out, post₁ out → post₂ out)
    (h : wpMirStepsSym fuel body s mid₁ post₁) :
    wpMirStepsSym fuel body s mid₂ post₂ := by
  refine wpMirExecStepsSym_mono ?_ h_post h
  intro st' h_st'
  cases st' with
  | running s' => exact h_mid s' h_st'
  | halted out => exact h_post out h_st'
  | faulted _ => exact False.elim h_st'

/-- Monotonicity of `MirStepsConverges` in both `mid` and `post`. -/
theorem MirStepsConverges.mono
    {body : CapturedMir} {s : MachineState}
    {mid₁ mid₂ : MachineState → Prop} {post₁ post₂ : MirOutcome → Prop}
    (h_mid : ∀ s', mid₁ s' → mid₂ s')
    (h_post : ∀ out, post₁ out → post₂ out)
    (h : MirStepsConverges body s mid₁ post₁) :
    MirStepsConverges body s mid₂ post₂ := by
  rcases h with ⟨fuel, h_steps⟩
  exact ⟨fuel, wpMirStepsSym_mono h_mid h_post h_steps⟩

/--
Internal `f₁ + f₂` step-addition theorem for `wpMirExecStepsSym`.
-/
theorem wpMirExecStepsSym_add
    {f₁ f₂ : Nat} {body : CapturedMir} {st : MirExecState}
    {mid₁ mid₂ : MirExecState → Prop} {post : MirOutcome → Prop}
    (h₁ : wpMirExecStepsSym f₁ body st mid₁ post)
    (h₂ : ∀ st', mid₁ st' → wpMirExecStepsSym f₂ body st' mid₂ post) :
    wpMirExecStepsSym (f₁ + f₂) body st mid₂ post := by
  induction f₁ generalizing st with
  | zero =>
    rw [Nat.zero_add]
    exact h₂ st h₁
  | succ f₁' ih =>
    rw [Nat.succ_add]
    unfold wpMirExecStepsSym at h₁ ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h₁ ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h₁ ⊢
      exact h₁
    | tau st' =>
      simp only [h_step] at h₁ ⊢
      exact ih h₁
    | vis i k =>
      simp only [h_step] at h₁ ⊢
      rcases i with f | (e | c)
      · exact False.elim h₁
      · cases e
        exact ih h₁
      · exact False.elim h₁

/--
Internal `f₁ + f₂` composition theorem combining `wpMirExecStepsSym f₁` with
`wpMirExecSym f₂` into `wpMirExecSym (f₁ + f₂)`.
-/
theorem wpMirExecSym_add_of_stepsSym
    {f₁ f₂ : Nat} {body : CapturedMir} {st : MirExecState}
    {mid : MirExecState → Prop} {post : MirOutcome → Prop}
    (h₁ : wpMirExecStepsSym f₁ body st mid post)
    (h₂ : ∀ st', mid st' → wpMirExecSym f₂ body st' post) :
    wpMirExecSym (f₁ + f₂) body st post := by
  induction f₁ generalizing st with
  | zero =>
    rw [Nat.zero_add]
    exact h₂ st h₁
  | succ f₁' ih =>
    rw [Nat.succ_add]
    unfold wpMirExecStepsSym at h₁
    unfold wpMirExecSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h₁
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq]
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h₁ ⊢
      exact h₁
    | tau st' =>
      simp only [h_step] at h₁ ⊢
      exact ih h₁
    | vis i k =>
      simp only [h_step] at h₁ ⊢
      rcases i with f | (e | c)
      · exact False.elim h₁
      · cases e
        exact ih h₁
      · exact False.elim h₁

/--
Internal `f₁ + (f₂ + 1)` composition theorem combining `wpMirStepsSym f₁` with
`wpMirSym f₂` into `wpMirSym (f₁ + (f₂ + 1))`.
-/
theorem wpMirSym_add_of_stepsSym
    {f₁ f₂ : Nat} {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : wpMirStepsSym f₁ body s mid post)
    (h₂ : ∀ s', mid s' → wpMirSym f₂ body s' post) :
    wpMirSym (f₁ + (f₂ + 1)) body s post := by
  refine wpMirExecSym_add_of_stepsSym h₁ ?_
  intro st' h_mid
  cases st' with
  | running s' =>
    exact wpMirExecSym_mono (Nat.le_succ f₂) (h₂ s' h_mid)
  | halted out =>
    exact h_mid
  | faulted _ =>
    exact False.elim h_mid

/--
Exact `f₁ + f₂` composition theorem combining `wpMirStepsSym f₁` with
`wpMirSym f₂` when `0 < f₂`.
-/
theorem wpMirSym_add_of_stepsSym_pos
    {f₁ f₂ : Nat} (h_pos : 0 < f₂)
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : wpMirStepsSym f₁ body s mid post)
    (h₂ : ∀ s', mid s' → wpMirSym f₂ body s' post) :
    wpMirSym (f₁ + f₂) body s post := by
  cases f₂ with
  | zero => exact absurd h_pos (Nat.lt_irrefl 0)
  | succ f₂' =>
    refine wpMirExecSym_add_of_stepsSym h₁ ?_
    intro st' h_mid
    cases st' with
    | running s' => exact h₂ s' h_mid
    | halted out => exact h_mid
    | faulted _ => exact False.elim h_mid

/--
Internal `f₁ + f₂` step-addition theorem for `wpMirStepsSym` over `MachineState`.
-/
theorem wpMirStepsSym_add
    {f₁ f₂ : Nat} {body : CapturedMir} {s : MachineState}
    {mid₁ mid₂ : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : wpMirStepsSym f₁ body s mid₁ post)
    (h₂ : ∀ s', mid₁ s' → wpMirStepsSym f₂ body s' mid₂ post) :
    wpMirStepsSym (f₁ + f₂) body s mid₂ post := by
  refine wpMirExecStepsSym_add h₁ ?_
  intro st' h_mid
  cases st' with
  | running s' => exact h₂ s' h_mid
  | halted out =>
    clear h₁ h₂
    induction f₂ with
    | zero => exact h_mid
    | succ f₂' _ =>
      unfold wpMirExecStepsSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
      dsimp only [stepMirState]
      exact h_mid
  | faulted _ => exact False.elim h_mid

/--
Internal `f₁ + (f₂ + 1)` composition theorem combining `wpMirStepsSym f₁` with
`wpMirNoCallSym f₂` into `wpMirNoCallSym (f₁ + (f₂ + 1))`.
-/
theorem wpMirNoCallSym_add_of_stepsSym
    {f₁ f₂ : Nat} {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : wpMirStepsSym f₁ body s mid post)
    (h₂ : ∀ s', mid s' → wpMirNoCallSym f₂ body s' post) :
    wpMirNoCallSym (f₁ + (f₂ + 1)) body s post := by
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym f₁ body st
        (fun
          | .running s' => mid s'
          | .halted out => post out
          | .faulted _ => False)
        post →
      wpMirExecNoCallSym (f₁ + (f₂ + 1)) body st post from
    this (.running s) h₁
  clear h₁
  induction f₁ with
  | zero =>
    intro st h_st
    rw [Nat.zero_add]
    cases st with
    | running s' => exact wpMirExecNoCallSym_mono (Nat.le_succ f₂) (h₂ s' h_st)
    | halted out => exact h_st
    | faulted _ => exact False.elim h_st
  | succ f₁' ih =>
    intro st h_st
    rw [Nat.succ_add]
    unfold wpMirExecStepsSym at h_st
    unfold wpMirExecNoCallSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h_st ⊢
      exact h_st
    | tau st' =>
      simp only [h_step] at h_st ⊢
      exact ih st' h_st
    | vis i k =>
      simp only [h_step] at h_st ⊢
      rcases i with f | (e | c)
      · exact False.elim h_st
      · cases e
        exact ih (k PUnit.unit) h_st
      · exact False.elim h_st

/--
Fuel-free sequential composition (`MirExecWpConverges.bind`): composes an
intermediate stage `wpMirExecStepsSym` with a continuation
`∀ st', mid st' → MirExecWpConverges body st' post` without exposing fuel.
-/
theorem MirExecWpConverges.bind
    {body : CapturedMir} {st : MirExecState}
    {mid : MirExecState → Prop} {post : MirOutcome → Prop}
    (h₁ : MirExecStepsConverges body st mid post)
    (h₂ : ∀ st', mid st' → MirExecWpConverges body st' post) :
    MirExecWpConverges body st post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  induction f₁ generalizing st with
  | zero => exact h₂ st hf₁
  | succ f₁' ih =>
    unfold wpMirExecStepsSym at hf₁
    refine MirExecWpConverges.step ?_
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at hf₁ ⊢
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at hf₁ ⊢
      exact hf₁
    | tau st' =>
      simp only [h_step] at hf₁ ⊢
      exact ih hf₁
    | vis i k =>
      simp only [h_step] at hf₁ ⊢
      rcases i with f | (e | c)
      · exact False.elim hf₁
      · cases e
        exact ih hf₁
      · exact False.elim hf₁

/--
Fuel-free sequential composition (`MirWpConverges.bind`): composes a first stage
`MirStepsConverges body s mid post` with a continuation
`∀ s', mid s' → MirWpConverges body s' post` without exposing fuel.
-/
theorem MirWpConverges.bind
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : MirStepsConverges body s mid post)
    (h₂ : ∀ s', mid s' → MirWpConverges body s' post) :
    MirWpConverges body s post := by
  refine MirExecWpConverges.bind h₁ ?_
  intro st' h_mid
  cases st' with
  | running s' => exact h₂ s' h_mid
  | halted out => exact MirExecWpConverges.halted h_mid
  | faulted _ => exact False.elim h_mid

/--
Pointwise state-to-state `bind` specialization for `MirReachState`: if `s`
reaches `s'` (`MirReachState body s s'`) and `MirWpConverges body s' post`
holds, then `MirWpConverges body s post` holds.
-/
theorem MirWpConverges.bind_reachState
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h₁ : MirReachState body s s')
    (h₂ : MirWpConverges body s' post) :
    MirWpConverges body s post :=
  MirWpConverges.bind
    (MirStepsConverges.mono (fun _ h => h) (fun _ h => h.elim) h₁)
    (fun _ h_eq => h_eq ▸ h₂)

/--
Fuel-free sequential composition for deterministic convergence (`MirConverges.bind`).
-/
theorem MirConverges.bind
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {out : MirOutcome}
    (h₁ : MirStepsConverges body s mid (· = out))
    (h₂ : ∀ s', mid s' → MirConverges body s' out) :
    MirConverges body s out :=
  MirWpConverges.bind h₁ h₂

/--
Pointwise state-to-state `bind` specialization for `MirConverges` via
`MirReachState`.
-/
theorem MirConverges.bind_reachState
    {body : CapturedMir} {s s' : MachineState} {out : MirOutcome}
    (h₁ : MirReachState body s s')
    (h₂ : MirConverges body s' out) :
    MirConverges body s out :=
  MirWpConverges.bind_reachState h₁ h₂

/--
Monotonicity of `evalSymNodeTreeNoCall` in both continuation `cont` and
postcondition `post`.
-/
theorem evalSymNodeTreeNoCall_mono
    {cont₁ cont₂ : MirExecState → Prop} {post₁ post₂ : MirOutcome → Prop}
    (h_cont : ∀ st', cont₁ st' → cont₂ st')
    (h_post : ∀ out, post₁ out → post₂ out)
    {t : SymTree MirStepNode}
    (h : evalSymNodeTreeNoCall cont₁ post₁ t) :
    evalSymNodeTreeNoCall cont₂ post₂ t := by
  induction t with
  | leaf node =>
    cases node with
    | ret out => exact h_post out h
    | tau st' => exact h_cont st' h
    | vis i k =>
      rcases i with f | (e | c)
      · exact False.elim h
      · exact h_cont (k PUnit.unit) h
      · exact False.elim h
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2 h
    · exact ih1 h

/--
Fuel-free single-step symbolic unfolding rule for `MirNoCallWpConverges`.
-/
theorem MirNoCallWpConverges.step
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h :
      evalSymNodeTreeNoCall
        (fun
          | .running s' => MirNoCallWpConverges body s' post
          | .halted out => post out
          | .faulted _ => False)
        post
        (stepMirSymTree body s)) :
    MirNoCallWpConverges body s post := by
  have h_ex :
      evalSymNodeTreeNoCall
        (fun st' => ∃ f, wpMirExecNoCallSym (f + 1) body st' post)
        post
        (stepMirSymTree body s) := by
    refine evalSymNodeTreeNoCall_mono ?_ (fun _ hp => hp) h
    intro st' h_st'
    cases st' with
    | running s' =>
      rcases h_st' with ⟨f, hf⟩
      exact ⟨f, wpMirExecNoCallSym_mono (Nat.le_succ f) hf⟩
    | halted out => exact ⟨0, h_st'⟩
    | faulted _ => exact False.elim h_st'
  rcases evalSymNodeTreeNoCall_exists_fuel (stepMirSymTree body s) h_ex with
    ⟨fuel, h_fuel⟩
  exact ⟨fuel + 2, h_fuel⟩

/--
Fuel-free sequential composition (`MirNoCallWpConverges.bind`): composes a first
stage `MirStepsConverges body s mid post` with a continuation
`∀ s', mid s' → MirNoCallWpConverges body s' post` without exposing fuel.
-/
theorem MirNoCallWpConverges.bind
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : MirStepsConverges body s mid post)
    (h₂ : ∀ s', mid s' → MirNoCallWpConverges body s' post) :
    MirNoCallWpConverges body s post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym f₁ body st
        (fun
          | .running s' => mid s'
          | .halted out => post out
          | .faulted _ => False)
        post →
      ∃ f : Nat, wpMirExecNoCallSym f body st post from
    this (.running s) hf₁
  clear hf₁
  induction f₁ with
  | zero =>
    intro st h_st
    cases st with
    | running s' => exact h₂ s' h_st
    | halted out => exact ⟨1, h_st⟩
    | faulted _ => exact False.elim h_st
  | succ f₁' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st
    have h_ex :
        evalSymNodeTreeNoCall
          (fun st' => ∃ f, wpMirExecNoCallSym f body st' post)
          post
          (stepMirExecSymTree body st) := by
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
      cases h_step : stepMirState body st with
      | ret out =>
        simp only [h_step] at h_st ⊢
        exact h_st
      | tau st' =>
        simp only [h_step] at h_st ⊢
        exact ih st' h_st
      | vis i k =>
        simp only [h_step] at h_st ⊢
        rcases i with f | (e | c)
        · exact False.elim h_st
        · cases e
          exact ih (k PUnit.unit) h_st
        · exact False.elim h_st
    rcases evalSymNodeTreeNoCall_exists_fuel (stepMirExecSymTree body st) h_ex with
      ⟨f₂, hf₂⟩
    exact ⟨f₂ + 1, hf₂⟩

/--
Pointwise state-to-state `bind` specialization for `MirNoCallWpConverges` via
`MirReachState`.
-/
theorem MirNoCallWpConverges.bind_reachState
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h₁ : MirReachState body s s')
    (h₂ : MirNoCallWpConverges body s' post) :
    MirNoCallWpConverges body s post :=
  MirNoCallWpConverges.bind
    (MirStepsConverges.mono (fun _ h => h) (fun _ h => h.elim) h₁)
    (fun _ h_eq => h_eq ▸ h₂)

/--
Single-step symbolic unfolding rule for `MirStepsConverges`.
-/
theorem MirStepsConverges.step
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h :
      evalSymNodeTreeNoCall
        (fun
          | .running s' => MirStepsConverges body s' mid post
          | .halted out => post out
          | .faulted _ => False)
        post
        (stepMirSymTree body s)) :
    MirStepsConverges body s mid post := by
  have h_ex :
      evalSymNodeTreeNoCall
        (fun st' =>
          ∃ f,
            wpMirExecStepsSym f body st'
              (fun
                | .running s' => mid s'
                | .halted out => post out
                | .faulted _ => False)
              post)
        post
        (stepMirSymTree body s) := by
    refine evalSymNodeTreeNoCall_mono ?_ (fun _ hp => hp) h
    intro st' h_st'
    cases st' with
    | running s' => exact h_st'
    | halted out => exact ⟨0, h_st'⟩
    | faulted _ => exact False.elim h_st'
  rcases evalSymNodeTreeNoCall_exists_fuel (stepMirSymTree body s) h_ex with
    ⟨fuel, h_fuel⟩
  exact ⟨fuel + 1, h_fuel⟩

/-- Single-step silent `.tau` transition rule for `MirStepsConverges`. -/
theorem MirStepsConverges.step_tau
    {body : CapturedMir} {s s' : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h_step : stepMirFn body s = .tau (.running s'))
    (h_next : MirStepsConverges body s' mid post) :
    MirStepsConverges body s mid post := by
  rcases h_next with ⟨fuel, h_wp⟩
  refine ⟨fuel + 1, ?_⟩
  unfold wpMirStepsSym wpMirExecStepsSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_wp

/-- Single-step `MirObsE` emission rule for `MirStepsConverges`. -/
theorem MirStepsConverges.step_emit
    {body : CapturedMir} {s s' : MachineState} {obs : MirObs}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h_step : stepMirFn body s = MirStepNode.emitStep obs s')
    (h_next : MirStepsConverges body s' mid post) :
    MirStepsConverges body s mid post := by
  rcases h_next with ⟨fuel, h_wp⟩
  refine ⟨fuel + 1, ?_⟩
  unfold wpMirStepsSym wpMirExecStepsSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
  dsimp only [stepMirState]
  rw [h_step]
  cases obs <;> (dsimp [MirStepNode.emitStep]; exact h_wp)

/-- Single-step early `.ret` rule for `MirStepsConverges`. -/
theorem MirStepsConverges.ret_of_step
    {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h_step : stepMirFn body s = .ret out)
    (h_post : post out) :
    MirStepsConverges body s mid post := by
  refine ⟨1, ?_⟩
  unfold wpMirStepsSym wpMirExecStepsSym
  rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_post

/--
Fuel-free transitivity of `MirStepsConverges` across multi-stage executions.
-/
theorem MirStepsConverges.trans
    {body : CapturedMir} {s : MachineState}
    {mid₁ mid₂ : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : MirStepsConverges body s mid₁ post)
    (h₂ : ∀ s', mid₁ s' → MirStepsConverges body s' mid₂ post) :
    MirStepsConverges body s mid₂ post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym f₁ body st
        (fun
          | .running s' => mid₁ s'
          | .halted out => post out
          | .faulted _ => False)
        post →
      ∃ f : Nat,
        wpMirExecStepsSym f body st
          (fun
            | .running s' => mid₂ s'
            | .halted out => post out
            | .faulted _ => False)
          post from
    this (.running s) hf₁
  clear hf₁
  induction f₁ with
  | zero =>
    intro st h_st
    cases st with
    | running s' => exact h₂ s' h_st
    | halted out => exact ⟨0, h_st⟩
    | faulted _ => exact False.elim h_st
  | succ f₁' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st
    have h_ex :
        evalSymNodeTreeNoCall
          (fun st' =>
            ∃ f,
              wpMirExecStepsSym f body st'
                (fun
                  | .running s' => mid₂ s'
                  | .halted out => post out
                  | .faulted _ => False)
                post)
          post
          (stepMirExecSymTree body st) := by
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
      cases h_step : stepMirState body st with
      | ret out =>
        simp only [h_step] at h_st ⊢
        exact h_st
      | tau st' =>
        simp only [h_step] at h_st ⊢
        exact ih st' h_st
      | vis i k =>
        simp only [h_step] at h_st ⊢
        rcases i with f | (e | c)
        · exact False.elim h_st
        · cases e
          exact ih (k PUnit.unit) h_st
        · exact False.elim h_st
    rcases evalSymNodeTreeNoCall_exists_fuel (stepMirExecSymTree body st) h_ex with
      ⟨f₂, hf₂⟩
    exact ⟨f₂ + 1, hf₂⟩

/-- Reflexivity of `MirReachState`. -/
theorem MirReachState.refl
    (body : CapturedMir) (s : MachineState) :
    MirReachState body s s :=
  ⟨0, rfl⟩

/-- Transitivity of `MirReachState`. -/
theorem MirReachState.trans
    {body : CapturedMir} {s₁ s₂ s₃ : MachineState}
    (h₁₂ : MirReachState body s₁ s₂)
    (h₂₃ : MirReachState body s₂ s₃) :
    MirReachState body s₁ s₃ :=
  MirStepsConverges.trans h₁₂ (fun _ h_eq => h_eq ▸ h₂₃)

/-- Single-step `.tau` rule for `MirReachState`. -/
theorem MirReachState.step_tau
    {body : CapturedMir} {s₁ s₂ s₃ : MachineState}
    (h_step : stepMirFn body s₁ = .tau (.running s₂))
    (h_next : MirReachState body s₂ s₃) :
    MirReachState body s₁ s₃ :=
  MirStepsConverges.step_tau h_step h_next

/-- Single-step `MirObsE` emission rule for `MirReachState`. -/
theorem MirReachState.step_emit
    {body : CapturedMir} {s₁ s₂ s₃ : MachineState} {obs : MirObs}
    (h_step : stepMirFn body s₁ = MirStepNode.emitStep obs s₂)
    (h_next : MirReachState body s₂ s₃) :
    MirReachState body s₁ s₃ :=
  MirStepsConverges.step_emit h_step h_next

/-! ### Bridges from `runMirToBlock`, `runMirTauToBlock`, and `runMirToBinarySwitch` -/

/--
Every `runMirToBlock fuel body targetBlock s = some s'` execution witnesses
`MirStepsConverges body s (· = s') post`.
-/
theorem MirStepsConverges.of_runMirToBlock
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState} {post : MirOutcome → Prop}
    (h : runMirToBlock fuel body targetBlock s = some s') :
    MirStepsConverges body s (· = s') post := by
  induction fuel generalizing s with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold runMirToBlock at h
    split at h
    · injection h with h_eq
      subst h_eq
      exact ⟨0, rfl⟩
    · cases h_step : stepMirFn body s with
      | ret _ => simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h
        cases execNext with
        | running s₁ =>
          rcases ih h with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          unfold wpMirStepsSym wpMirExecStepsSym
          rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
          dsimp only [stepMirState]
          rw [h_step]
          exact hk
        | halted _ => nomatch h
        | faulted _ => nomatch h
      | vis req k =>
        simp only [h_step] at h
        rcases req with f | (e | c)
        · nomatch h
        · cases e
          cases hk_eq : k PUnit.unit with
          | running s₁ =>
            simp only [hk_eq] at h
            rcases ih h with ⟨k_fuel, hk_steps⟩
            refine ⟨k_fuel + 1, ?_⟩
            unfold wpMirStepsSym wpMirExecStepsSym
            rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
            dsimp only [stepMirState]
            rename_i ev
            cases ev <;> (
              rw [h_step]
              change wpMirExecStepsSym k_fuel body (k PUnit.unit) _ _
              rw [hk_eq]
              exact hk_steps
            )
          | halted _ => simp only [hk_eq] at h; nomatch h
          | faulted _ => simp only [hk_eq] at h; nomatch h
        · nomatch h

/--
Every `runMirTauToBlock fuel body targetBlock s = some s'` execution witnesses
`MirStepsConverges body s (· = s') post`.
-/
theorem MirStepsConverges.of_runMirTauToBlock
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState} {post : MirOutcome → Prop}
    (h : runMirTauToBlock fuel body targetBlock s = some s') :
    MirStepsConverges body s (· = s') post := by
  induction fuel generalizing s with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold runMirTauToBlock at h
    split at h
    · injection h with h_eq
      subst h_eq
      exact ⟨0, rfl⟩
    · cases h_step : stepMirFn body s with
      | ret _ => simp only [h_step] at h; nomatch h
      | vis _ _ => simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h
        cases execNext with
        | running s₁ =>
          rcases ih h with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          unfold wpMirStepsSym wpMirExecStepsSym
          rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
          dsimp only [stepMirState]
          rw [h_step]
          exact hk
        | halted _ => nomatch h
        | faulted _ => nomatch h

/--
Every `runMirToBinarySwitch fuel body s = some (cond, bits, sThen, sElse)`
execution witnesses `MirStepsConverges body s (· = if cond then sThen else sElse) post`.
-/
theorem MirStepsConverges.of_runMirToBinarySwitch
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {cond : Bool} {bits : Nat} {sThen sElse : MachineState}
    {post : MirOutcome → Prop}
    (h : runMirToBinarySwitch fuel body s = some (cond, bits, sThen, sElse)) :
    MirStepsConverges body s (· = if cond then sThen else sElse) post := by
  induction fuel generalizing s with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold runMirToBinarySwitch at h
    cases h_sw : inspectBinarySwitch body s with
    | some res =>
      rw [h_sw] at h
      injection h with h_eq
      subst h_eq
      refine ⟨1, ?_⟩
      unfold wpMirStepsSym wpMirExecStepsSym
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
      dsimp only [stepMirState]
      rw [stepMirFn_of_inspectBinarySwitch h_sw]
      rfl
    | none =>
      rw [h_sw] at h
      cases h_step : stepMirFn body s with
      | ret _ => simp only [h_step] at h; nomatch h
      | vis _ _ => simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h
        cases execNext with
        | running s₁ =>
          rcases ih h with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          unfold wpMirStepsSym wpMirExecStepsSym
          rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
          dsimp only [stepMirState]
          rw [h_step]
          exact hk
        | halted _ => nomatch h
        | faulted _ => nomatch h

/--
Every `runMirToBlock fuel body targetBlock s = some s'` execution witnesses
`MirReachState body s s'`.
-/
theorem MirReachState.of_runMirToBlock
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState}
    (h : runMirToBlock fuel body targetBlock s = some s') :
    MirReachState body s s' :=
  MirStepsConverges.of_runMirToBlock h

/--
Every `runMirTauToBlock fuel body targetBlock s = some s'` execution witnesses
`MirReachState body s s'`.
-/
theorem MirReachState.of_runMirTauToBlock
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState}
    (h : runMirTauToBlock fuel body targetBlock s = some s') :
    MirReachState body s s' :=
  MirStepsConverges.of_runMirTauToBlock h

/--
Compose `runMirToBlock` with a continuation `MirWpConverges` proof.
-/
theorem MirWpConverges.of_runMirToBlock
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState} {post : MirOutcome → Prop}
    (h_blk : runMirToBlock fuel body targetBlock s = some s')
    (h_next : MirWpConverges body s' post) :
    MirWpConverges body s post :=
  MirWpConverges.bind
    (MirStepsConverges.of_runMirToBlock h_blk)
    (fun _ h_eq => h_eq ▸ h_next)

/--
Compose `runMirTauToBlock` with a continuation `MirWpConverges` proof.
-/
theorem MirWpConverges.of_runMirTauToBlock
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState} {post : MirOutcome → Prop}
    (h_blk : runMirTauToBlock fuel body targetBlock s = some s')
    (h_next : MirWpConverges body s' post) :
    MirWpConverges body s post :=
  MirWpConverges.bind
    (MirStepsConverges.of_runMirTauToBlock h_blk)
    (fun _ h_eq => h_eq ▸ h_next)

/--
Compose `runMirToBinarySwitch` with a continuation `MirWpConverges` proof on
`if cond then sThen else sElse`.
-/
theorem MirWpConverges.of_runMirToBinarySwitch
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {cond : Bool} {bits : Nat} {sThen sElse : MachineState}
    {post : MirOutcome → Prop}
    (h_sw : runMirToBinarySwitch fuel body s = some (cond, bits, sThen, sElse))
    (h_next : MirWpConverges body (if cond then sThen else sElse) post) :
    MirWpConverges body s post :=
  MirWpConverges.bind
    (MirStepsConverges.of_runMirToBinarySwitch h_sw)
    (fun _ h_eq => h_eq ▸ h_next)

/-! ## 6. Callee-Aware Machine State Initialization (`BRIEF-3.2` Compatibility) -/

/--
Populate `mem.callees` with `defaultCallees` when `defaultCallees` is non-empty,
matching `adv/brief-3-2` (`Trusted.VerificationResult.Memory.withDefaultCallees`)
so that `Memory.withDefaultCallees mem [] = mem` holds definitionally (`rfl`)
for any abstract `mem : Memory`.
-/
def Memory.withDefaultCallees
    (mem : Memory) (defaultCallees : List CapturedMir) : Memory :=
  match defaultCallees with
  | [] => mem
  | _ :: _ => { mem with callees := defaultCallees }

@[simp]
theorem Memory.withDefaultCallees_nil (mem : Memory) :
    Memory.withDefaultCallees mem [] = mem :=
  rfl

@[simp]
theorem Memory.withDefaultCallees_cons
    (mem : Memory) (c : CapturedMir) (cs : List CapturedMir) :
    Memory.withDefaultCallees mem (c :: cs) = { mem with callees := c :: cs } :=
  rfl

@[simp]
theorem Memory.withDefaultCallees_activeCallee
    (mem : Memory) (callees : List CapturedMir) :
    (Memory.withDefaultCallees mem callees).activeCallee = mem.activeCallee := by
  cases callees <;> rfl

@[simp]
theorem Memory.withDefaultCallees_callStack
    (mem : Memory) (callees : List CapturedMir) :
    (Memory.withDefaultCallees mem callees).callStack = mem.callStack := by
  cases callees <;> rfl

/--
Initialize `MachineState` for `body` on `(args, mem)` with default callee table
`callees` (matching `adv/brief-3-2`).
-/
def initMachineStateWithMemoryAndCallees
    (body : CapturedMir)
    (args : List Value)
    (mem : Memory)
    (callees : List CapturedMir := .nil) :
    MachineState :=
  initMachineStateWithMemory body args (Memory.withDefaultCallees mem callees)

@[simp]
theorem initMachineStateWithCallees_nil
    (body : CapturedMir) (args : List Value) :
    initMachineStateWithCallees body args [] = initMachineState body args :=
  rfl

@[simp]
theorem initMachineStateWithMemoryAndCallees_nil
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    initMachineStateWithMemoryAndCallees body args mem [] =
      initMachineStateWithMemory body args mem :=
  rfl

/--
Coinductive interaction tree of `body` on `args` with linked callee table
`callees` (matching `adv/brief-3-2`).
-/
def mirCallTreeWithCallees
    (body : CapturedMir)
    (args : List Value)
    (callees : List CapturedMir := .nil) :
    ITree MirEffect MirOutcome :=
  mirTree body (initMachineStateWithCallees body args callees)

/--
Coinductive interaction tree of `body` from `(args, mem)` with default callee
table `callees` (matching `adv/brief-3-2`).
-/
def mirStatefulTreeWithCallees
    (body : CapturedMir)
    (args : List Value)
    (mem : Memory)
    (callees : List CapturedMir := .nil) :
    ITree MirEffect MirOutcome :=
  mirTree body (initMachineStateWithMemoryAndCallees body args mem callees)

@[simp]
theorem mirCallTreeWithCallees_nil
    (body : CapturedMir) (args : List Value) :
    mirCallTreeWithCallees body args [] = mirCallTree body args :=
  rfl

@[simp]
theorem mirStatefulTreeWithCallees_nil
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    mirStatefulTreeWithCallees body args mem [] = mirStatefulTree body args mem :=
  rfl

/--
Predicate asserting that `mem` is at a borrow-free root caller activation
(`mem.borrows = []`, `mem.callStack = []`, `mem.activeCallee = none`,
`mem.activeProtectors = []`) that may unwind (`mem.rootUnwindCeiling = true`:
a panic leaving the root activation is `.halted .panic`, not the
`DIV-LM-TAILCALL-NOUNWIND-UNWIND` undefined behavior of unwinding out of a
root-level tail callee that cannot unwind), while leaving heap allocations
(`globals`, `nextAllocId`), tag/protector counters (`nextTag`,
`nextProtector`), caller locals (`callerLocals`), and linked callee tables
(`callees`) completely unconstrained.
-/
def RootActiveMemory (mem : Memory) : Prop :=
  mem.borrows = [] ∧
  mem.callStack = [] ∧
  mem.activeCallee = none ∧
  mem.activeProtectors = [] ∧
  mem.rootUnwindCeiling = true

@[simp]
theorem rootActiveMemory_initMachineState
    (body : CapturedMir) (args : List Value) :
    RootActiveMemory (initMachineState body args).memory :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

@[simp]
theorem rootActiveMemory_initMachineStateWithCallees
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    RootActiveMemory (initMachineStateWithCallees body args callees).memory := by
  cases callees <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
`initMachineStateWithCallees body args callees` is the frame of
`initMachineStateWithMemory` over its own initial memory.

The trusted definition matches on `callees` (`[]` reuses `initMachineState`,
while a non-empty table also seeds `Memory.traitImpls`), so for an abstract
`callees` the equation needs a case split rather than `rfl`. Proofs that
discharge claims through `initMachineStateWithMemory`-shaped lemmas rewrite
with this equation.
-/
theorem initMachineStateWithCallees_eq_withMemory
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    initMachineStateWithCallees body args callees =
      initMachineStateWithMemory body args
        (initMachineStateWithCallees body args callees).memory := by
  cases callees <;> rfl

@[simp]
theorem rootActiveMemory_withDefaultCallees
    (mem : Memory) (callees : List CapturedMir) :
    RootActiveMemory (Memory.withDefaultCallees mem callees) ↔
      RootActiveMemory mem := by
  cases callees <;> rfl

/--
Smyth `Partial` behavior of `body` on `args` with linked `callees`, projected
from `mirCallTreeWithCallees` (matching `adv/brief-3-2`).
-/
def MirExecPartialWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) :
    Trusted.Refinement.Partial (Trusted.Refinement.BehaviorSet (List (Event MirEffect) × MirOutcome)) :=
  (mirCallTreeWithCallees body args callees).toPartial

/--
Pointwise Smyth refinement claim with linked `callees` and separate `safetyPre`
and `pre` (matching `adv/brief-3-2`).
-/
def MirContractHoldsWithSafetyAndCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirExecPartialWithCallees body callees ≤ MirContractSpec safetyPre pre post

/--
Pointwise Smyth refinement claim with linked `callees` (`safetyPre := pre`,
matching `adv/brief-3-2`).
-/
def MirContractHoldsWithCallees
    (body : CapturedMir)
    (callees : List CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirContractHoldsWithSafetyAndCallees body callees pre pre post

/--
Companion boolean contract helper predicate with linked `callees` (matching
`adv/brief-3-2`): on `args`, `specBody` with `callees` is `TreeSafe` and every
normal return yields `true` (`.scalar ⟨1, 1⟩`).
-/
def MirBoolPredicateHoldsWithCallees
    (specBody : CapturedMir)
    (callees : List CapturedMir)
    (args : List Value) : Prop :=
  MirContractHoldsWithCallees
    specBody
    callees
    (· = args)
    (fun _ ret => ret = .scalar { bits := 1, sizeBytes := 1 })

@[simp]
theorem mirBoolPredicateHoldsWithCallees_nil
    (specBody : CapturedMir) (args : List Value) :
    MirBoolPredicateHoldsWithCallees specBody [] args =
      MirBoolPredicateHolds specBody args :=
  rfl

/-! ## 7. Fuel-Free Adequacy Bridges (`DWP`, `DWLP`, `VerificationResult`) -/

/--
Total-correctness (`DWP mirDefaultWP`) soundness of `MirExecWpConverges`.
-/
theorem dwp_of_mirExecWpConverges
    {body : CapturedMir} {st : MirExecState} {post : MirOutcome → Prop}
    (h : MirExecWpConverges body st post) :
    DWP mirDefaultWP (ITree.cofix (stepMirState body) st)
      (fun out _ => post out) PUnit.unit := by
  rcases h with ⟨fuel, h_wp⟩
  rw [wpMirExecSym_eq_wpCoalBounded] at h_wp
  exact dwp_cofix_of_wpCoalBounded fuel h_wp

/--
Total-correctness (`DWP mirDefaultWP`) soundness of `MirWpConverges` on
`mirTree body s`.
-/
theorem dwp_of_mirWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirWpConverges body s post) :
    DWP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rcases h with ⟨fuel, h_wp⟩
  exact dwp_of_wpMirSym h_wp

/--
Partial-correctness (`DWLP mirDefaultWP`) soundness of `MirWpConverges` on
`mirTree body s`.
-/
theorem dwlp_of_mirWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirWpConverges body s post) :
    DWLP mirDefaultWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  (dwp_of_mirWpConverges h).toDWLP

/--
Total-correctness (`DWP mirDefaultWP`) soundness of `MirWpConverges` on
`mirCallTreeWithCallees body args callees`.
-/
theorem dwp_mirCallTreeWithCallees_of_mirWpConverges
    {body : CapturedMir} {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop}
    (h : MirWpConverges body (initMachineStateWithCallees body args callees) post) :
    DWP mirDefaultWP (mirCallTreeWithCallees body args callees)
      (fun out _ => post out) PUnit.unit :=
  dwp_of_mirWpConverges h

/--
Partial-correctness (`DWLP mirDefaultWP`) soundness of `MirWpConverges` on
`mirCallTreeWithCallees body args callees`.
-/
theorem dwlp_mirCallTreeWithCallees_of_mirWpConverges
    {body : CapturedMir} {args : List Value} {callees : List CapturedMir}
    {post : MirOutcome → Prop}
    (h : MirWpConverges body (initMachineStateWithCallees body args callees) post) :
    DWLP mirDefaultWP (mirCallTreeWithCallees body args callees)
      (fun out _ => post out) PUnit.unit :=
  dwlp_of_mirWpConverges h

/--
Total-correctness (`DWP mirDefaultWP`) soundness of `MirWpConverges` on
`mirStatefulTreeWithCallees body args mem callees`.
-/
theorem dwp_mirStatefulTreeWithCallees_of_mirWpConverges
    {body : CapturedMir} {args : List Value} {mem : Memory}
    {callees : List CapturedMir} {post : MirOutcome → Prop}
    (h :
      MirWpConverges body
        (initMachineStateWithMemoryAndCallees body args mem callees) post) :
    DWP mirDefaultWP (mirStatefulTreeWithCallees body args mem callees)
      (fun out _ => post out) PUnit.unit :=
  dwp_of_mirWpConverges h

/--
Partial-correctness (`DWLP mirDefaultWP`) soundness of `MirWpConverges` on
`mirStatefulTreeWithCallees body args mem callees`.
-/
theorem dwlp_mirStatefulTreeWithCallees_of_mirWpConverges
    {body : CapturedMir} {args : List Value} {mem : Memory}
    {callees : List CapturedMir} {post : MirOutcome → Prop}
    (h :
      MirWpConverges body
        (initMachineStateWithMemoryAndCallees body args mem callees) post) :
    DWLP mirDefaultWP (mirStatefulTreeWithCallees body args mem callees)
      (fun out _ => post out) PUnit.unit :=
  dwlp_of_mirWpConverges h

/--
Total-correctness (`DWP mirNoCallWP`) soundness of `MirNoCallWpConverges` on
`mirTree body s`.
-/
theorem dwp_of_mirNoCallWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirNoCallWpConverges body s post) :
    DWP mirNoCallWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rcases h with ⟨fuel, h_wp⟩
  rw [wpMirNoCallSym_eq_wpMirNoCallBounded] at h_wp
  exact dwp_cofix_of_wpCoalBounded fuel h_wp

/--
Fuel-free sufficiency bridge for `MirBoolPredicateHolds specBody args`.
-/
theorem mirBoolPredicateHolds_of_wpConverges
    (specBody : CapturedMir) (args : List Value)
    (h :
      MirWpConverges specBody (initMachineState specBody args)
        (mirSafePost
          (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))) :
    MirBoolPredicateHolds specBody args := by
  rcases h with ⟨fuel, h_wp⟩
  exact mirBoolPredicateHolds_of_wpMirSym fuel specBody args h_wp

/--
Fuel-free equivalence between `MirBoolPredicateHolds specBody args` and
`MirWpConverges` whenever `specBody` terminates without UB on `args`.
-/
theorem mirBoolPredicateHolds_iff_wpConverges
    (specBody : CapturedMir) (args : List Value)
    (h_term :
      MirWpConverges specBody (initMachineState specBody args) (fun _ => True)) :
    MirBoolPredicateHolds specBody args ↔
      MirWpConverges specBody (initMachineState specBody args)
        (mirSafePost
          (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 })) := by
  constructor
  · intro h_holds
    rcases h_term with ⟨fuel, hf_term⟩
    exact ⟨fuel, (mirBoolPredicateHolds_iff_wpMirBoolSym fuel specBody args hf_term).1 h_holds⟩
  · exact mirBoolPredicateHolds_of_wpConverges specBody args

/--
Prove `MirBoolPredicateHoldsWithCallees specBody callees args` from
`DWP mirDefaultWP`.
-/
theorem mirBoolPredicateHoldsWithCallees_of_dwp
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (h_dwp :
      DWP mirDefaultWP (mirCallTreeWithCallees specBody args callees)
        (fun out _ =>
          ∀ retVal mem',
            out = .normal (retVal, mem') →
            retVal = .scalar { bits := 1, sizeBytes := 1 })
        PUnit.unit) :
    MirBoolPredicateHoldsWithCallees specBody callees args := by
  intro a h_eq
  subst h_eq
  have h_adeq := dwlp_pure_adequacy h_dwp.toDWLP
  exact ⟨h_adeq.1, fun outPair h_ret _ retVal mem' h_out =>
    h_adeq.2 outPair.1 outPair.2 h_ret retVal mem' h_out⟩

/--
Fuel-free sufficiency bridge for `MirBoolPredicateHoldsWithCallees specBody callees args`.
-/
theorem mirBoolPredicateHoldsWithCallees_of_wpConverges
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (h :
      MirWpConverges specBody
        (initMachineStateWithCallees specBody args callees)
        (mirSafePost
          (fun retVal _ => retVal = .scalar { bits := 1, sizeBytes := 1 }))) :
    MirBoolPredicateHoldsWithCallees specBody callees args := by
  refine mirBoolPredicateHoldsWithCallees_of_dwp specBody callees args ?_
  have h_conv :=
    MirWpConverges.mono
      (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
      h
  exact dwp_mirCallTreeWithCallees_of_mirWpConverges h_conv

/--
Discharge a stateless `VerificationResult c` from fuel-free `MirWpConverges`
(`mirSafePost`: panics/unwinds are safe defined behavior; normal returns must
satisfy `c.post args retVal`).

The hypothesis starts from `initMachineStateWithCallees c.body args c.callees`,
the initial state that `Claim.holds` quantifies over; for a claim without
linked callees it reduces definitionally to `initMachineState c.body args`.

Unlike `verifyMirSafeSym`, the existential step count inside `MirWpConverges`
may vary arbitrarily with `args`.
-/
theorem verifyMirSafe_of_wpConverges
    (c : Claim)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        MirWpConverges c.body (initMachineStateWithCallees c.body args c.callees)
          (mirSafePost (fun retVal _ => c.post args retVal))) :
    VerificationResult c := by
  refine verifyByDWLP c (fun args h_pre => ?_)
  have h_conv :=
    MirWpConverges.mono
      (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
      (h_wp args h_pre)
  exact dwlp_of_mirWpConverges h_conv

/-- Primary fuel-free stateless verification alias (`verifyMirSafe_of_wpConverges`). -/
abbrev verifyMir_of_wpConverges := @verifyMirSafe_of_wpConverges

/--
Discharge a stateless `VerificationResult c` from panic-forbidding fuel-free
`MirWpConverges` (`mirNormalPost`: requires normal return satisfying `c.post`
and rejects `.panic` / `.abort` as well as UB).
-/
theorem verifyMirNoPanic_of_wpConverges
    (c : Claim)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        MirWpConverges c.body (initMachineStateWithCallees c.body args c.callees)
          (mirNormalPost (fun retVal _ => c.post args retVal))) :
    VerificationResult c :=
  verifyMirSafe_of_wpConverges c (fun args h_pre =>
    MirWpConverges.mono (fun _ => mirNormalPost_imp_mirSafePost) (h_wp args h_pre))

/--
Discharge a stateful `StatefulVerificationResult c` from fuel-free
`MirWpConverges` (`mirSafePost`).

The hypothesis starts from the trusted
`Trusted.VerificationResult.initMachineStateWithMemoryAndCallees`, the initial
state that `StatefulClaim.holds` quantifies over; for a claim without linked
callees it reduces definitionally to `initMachineStateWithMemory c.body args
mem`. The stateful, total, UB-exception, trace, and equivalence combinators
below start from the same trusted state.

The existential step count inside `MirWpConverges` may vary arbitrarily with
`(args, mem)`.
-/
theorem verifyStatefulMirSafe_of_wpConverges
    (c : StatefulClaim)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirWpConverges c.body
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirSafePost (c.post args mem))) :
    StatefulVerificationResult c := by
  refine verifyStatefulByDWLP c (fun args mem h_pre => ?_)
  have h_conv :=
    MirWpConverges.mono
      (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
      (h_wp args mem h_pre)
  exact dwlp_of_mirWpConverges h_conv

/-- Primary fuel-free stateful verification alias (`verifyStatefulMirSafe_of_wpConverges`). -/
abbrev verifyStatefulMir_of_wpConverges := @verifyStatefulMirSafe_of_wpConverges

/--
Discharge a stateful `StatefulVerificationResult c` from panic-forbidding
fuel-free `MirWpConverges` (`mirNormalPost`).
-/
theorem verifyStatefulMirNoPanic_of_wpConverges
    (c : StatefulClaim)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirWpConverges c.body
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirNormalPost (c.post args mem))) :
    StatefulVerificationResult c :=
  verifyStatefulMirSafe_of_wpConverges c (fun args mem h_pre =>
    MirWpConverges.mono
      (fun _ => mirNormalPost_imp_mirSafePost)
      (h_wp args mem h_pre))

/--
Discharge a total-correctness `TotalVerificationResult c` from fuel-free
`MirWpConverges` (`mirNormalPost`: establishes `TreeSafe`, `Productive`,
`¬ MayDiverge`, absence of panics/aborts, and `c.post` on all returns).
-/
theorem verifyTotalMir_of_wpConverges
    (c : TotalClaim)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirWpConverges c.body
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirNormalPost (c.post args mem))) :
    TotalVerificationResult c := by
  refine verifyTotalByDWP c (fun args mem h_pre => ?_)
  have h_conv :=
    MirWpConverges.mono
      (fun out ho => (mirNormalPost_iff_exists_normal _ out).1 ho)
      (h_wp args mem h_pre)
  exact dwp_of_mirWpConverges h_conv

/--
Discharge a program-to-program `StatefulEquivVerificationResult c` from
fuel-free call-forbidding `MirNoCallWpConverges` proofs on `c.implBody` and
`c.specBody`.
-/
theorem verifyStatefulEquivMir_of_wpConverges
    (c : StatefulEquivClaim)
    (model : List Value → Memory → Value × Memory)
    (h_impl :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirNoCallWpConverges c.implBody
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.implBody args mem c.implCallees)
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2))
    (h_spec :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirNoCallWpConverges c.specBody
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.specBody args mem c.specCallees)
          (fun out => out = .normal (model args mem))) :
    StatefulEquivVerificationResult c :=
  verifyStatefulEquivViaPureModel c model
    (fun args mem h_pre => dwp_of_mirNoCallWpConverges (h_impl args mem h_pre))
    (fun args mem h_pre => dwp_of_mirNoCallWpConverges (h_spec args mem h_pre))

/-! ### Fuel-Free UB-Waived, Modular, Trace & Scalar Discharge Combinators -/

/--
Fuel-free UB-waived symbolic weakest precondition over `MachineState`, defined
as the Kleene supremum `∃ fuel : Nat, wpMirUbWaivedSym fuel body s post`.
-/
def MirUbWaivedWpConverges
    (body : CapturedMir) (s : MachineState) (post : MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirUbWaivedSym fuel body s post

/-- Lift a bounded `wpMirUbWaivedSym` proof into `MirUbWaivedWpConverges`. -/
theorem MirUbWaivedWpConverges.of_wpMirUbWaivedSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : wpMirUbWaivedSym fuel body s post) :
    MirUbWaivedWpConverges body s post :=
  ⟨fuel, h⟩

/-- Every strict `MirWpConverges` proof implies `MirUbWaivedWpConverges`. -/
theorem MirUbWaivedWpConverges.of_mirWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirWpConverges body s post) :
    MirUbWaivedWpConverges body s post := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirUbWaivedSym_of_wpMirSym h_wp⟩

/-- Postcondition monotonicity for `MirUbWaivedWpConverges`. -/
theorem MirUbWaivedWpConverges.mono
    {body : CapturedMir} {s : MachineState} {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : MirUbWaivedWpConverges body s P) :
    MirUbWaivedWpConverges body s Q := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirUbWaivedSym_mono_post h_imp h_wp⟩

/--
Fuel-free sequential composition (`MirUbWaivedWpConverges.bind`) composing a
call-free `MirStepsConverges` prefix with a `MirUbWaivedWpConverges`
continuation.
-/
theorem MirUbWaivedWpConverges.bind
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : MirStepsConverges body s mid post)
    (h₂ : ∀ s', mid s' → MirUbWaivedWpConverges body s' post) :
    MirUbWaivedWpConverges body s post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym f₁ body st
        (fun
          | .running s' => mid s'
          | .halted out => post out
          | .faulted _ => False)
        post →
      ∃ f : Nat, wpMirExecUbWaivedSym f body st post from
    this (.running s) hf₁
  clear hf₁
  induction f₁ with
  | zero =>
    intro st h_st
    cases st with
    | running s' => exact h₂ s' h_st
    | halted out => exact ⟨1, h_st⟩
    | faulted _ => exact False.elim h_st
  | succ f₁' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st
    have h_ex :
        evalSymNodeTreeNoCall
          (fun st' => ∃ f, wpMirExecUbWaivedSym f body st' post)
          post
          (stepMirExecSymTree body st) := by
      refine evalSymNodeTreeNoCall_mono ?_ (fun _ hp => hp) h_st
      intro st' h_st'
      exact ih st' h_st'
    rcases evalSymNodeTreeNoCall_exists_fuel (stepMirExecSymTree body st) h_ex with
      ⟨f₂, hf₂⟩
    refine ⟨f₂ + 1, ?_⟩
    unfold wpMirExecUbWaivedSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at hf₂
    rw [evalSymNodeTreeUbWaived_eq, stepMirExecSymTree_eval, evalNodeUbWaivedWP_eq]
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at hf₂ ⊢
      exact hf₂
    | tau st' =>
      simp only [h_step] at hf₂ ⊢
      exact hf₂
    | vis i k =>
      simp only [h_step] at hf₂ ⊢
      rcases i with f | (e | c)
      · exact False.elim hf₂
      · cases e
        exact hf₂
      · exact False.elim hf₂

/--
Pointwise state-to-state `bind` specialization for `MirUbWaivedWpConverges` via
`MirReachState`.
-/
theorem MirUbWaivedWpConverges.bind_reachState
    {body : CapturedMir} {s s' : MachineState} {post : MirOutcome → Prop}
    (h₁ : MirReachState body s s')
    (h₂ : MirUbWaivedWpConverges body s' post) :
    MirUbWaivedWpConverges body s post :=
  MirUbWaivedWpConverges.bind
    (MirStepsConverges.mono (fun _ h => h) (fun _ h => h.elim) h₁)
    (fun _ h_eq => h_eq ▸ h₂)

/--
Fuel-free single-step symbolic unfolding rule for `MirUbWaivedWpConverges`.
-/
theorem MirUbWaivedWpConverges.step
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h :
      evalSymNodeTreeNoCall
        (fun
          | .running s' => MirUbWaivedWpConverges body s' post
          | .halted out => post out
          | .faulted _ => False)
        post
        (stepMirSymTree body s)) :
    MirUbWaivedWpConverges body s post := by
  refine MirUbWaivedWpConverges.bind (mid := fun s' => MirUbWaivedWpConverges body s' post) ?_ ?_
  · refine ⟨1, ?_⟩
    exact h
  · intro _ h_next
    exact h_next

/--
Conjunction of two fuel-free `MirUbWaivedWpConverges` proofs by aligning fuel
to `max f₁ f₂`.
-/
theorem MirUbWaivedWpConverges.conj
    {body : CapturedMir} {s : MachineState} {P Q : MirOutcome → Prop}
    (hP : MirUbWaivedWpConverges body s P)
    (hQ : MirUbWaivedWpConverges body s Q) :
    MirUbWaivedWpConverges body s (fun out => P out ∧ Q out) := by
  rcases hP with ⟨f₁, h₁⟩
  rcases hQ with ⟨f₂, h₂⟩
  have h₁' := wpMirUbWaivedSym_mono (Nat.le_max_left f₁ f₂) h₁
  have h₂' := wpMirUbWaivedSym_mono (Nat.le_max_right f₁ f₂) h₂
  rw [wpMirUbWaivedSym_eq_wpMirUbWaivedBounded] at h₁' h₂'
  refine ⟨max f₁ f₂, ?_⟩
  rw [wpMirUbWaivedSym_eq_wpMirUbWaivedBounded]
  exact wpCoalBounded_conj h₁' h₂'

/-- Total-correctness (`DWP mirUbWaivedWP`) soundness of `MirUbWaivedWpConverges`. -/
theorem dwp_of_mirUbWaivedWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirUbWaivedWpConverges body s post) :
    DWP mirUbWaivedWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rcases h with ⟨fuel, h_wp⟩
  rw [wpMirUbWaivedSym_eq_wpMirUbWaivedBounded] at h_wp
  exact dwp_cofix_of_wpCoalBounded fuel h_wp

/-- Partial-correctness (`DWLP mirUbWaivedWP`) soundness of `MirUbWaivedWpConverges`. -/
theorem dwlp_of_mirUbWaivedWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirUbWaivedWpConverges body s post) :
    DWLP mirUbWaivedWP (mirTree body s) (fun out _ => post out) PUnit.unit :=
  (dwp_of_mirUbWaivedWpConverges h).toDWLP

/--
Fuel-free discharge of `UbExceptionVerificationResult c` from `MirWpConverges`
on `c.pre ∧ c.strictSafetyPre` and `MirUbWaivedWpConverges` across `c.pre`.
-/
theorem verifyUbExceptionMir_of_wpConverges
    (c : UbExceptionClaim)
    (h_strict :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        c.strictSafetyPre args mem →
        MirWpConverges c.body
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirSafePost (c.post args mem)))
    (h_waived :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirUbWaivedWpConverges c.body
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (mirSafePost (c.post args mem))) :
    UbExceptionVerificationResult c := by
  refine verifyUbExceptionByDWLP c
    (fun args mem h_pre h_sp => ?_)
    (fun args mem h_pre => ?_)
  · exact dwlp_of_mirWpConverges
      (MirWpConverges.mono
        (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
        (h_strict args mem h_pre h_sp))
  · exact dwlp_of_mirUbWaivedWpConverges
      (MirUbWaivedWpConverges.mono
        (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
        (h_waived args mem h_pre))

/--
Fuel-free modular call-contract weakest precondition over `MachineState`.
-/
def MirModularWpConverges
    (contract : MirCallContract) (body : CapturedMir) (s : MachineState)
    (post : MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirModularSym contract fuel body s post

/-- Lift a bounded `wpMirModularSym` proof into `MirModularWpConverges`. -/
theorem MirModularWpConverges.of_wpMirModularSym
    {contract : MirCallContract} {fuel : Nat} {body : CapturedMir}
    {s : MachineState} {post : MirOutcome → Prop}
    (h : wpMirModularSym contract fuel body s post) :
    MirModularWpConverges contract body s post :=
  ⟨fuel, h⟩

/-- Every call-free `MirNoCallWpConverges` proof implies `MirModularWpConverges`. -/
theorem MirModularWpConverges.of_noCall
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : MirNoCallWpConverges body s post) :
    MirModularWpConverges contract body s post := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirModularSym_of_wpMirNoCallSym h_wp⟩

/-- Postcondition monotonicity for `MirModularWpConverges`. -/
theorem MirModularWpConverges.mono
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {P Q : MirOutcome → Prop}
    (h_imp : ∀ out, P out → Q out)
    (h : MirModularWpConverges contract body s P) :
    MirModularWpConverges contract body s Q := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirModularSym_mono_post h_imp h_wp⟩

/--
Fuel-free sequential composition (`MirModularWpConverges.bind`) composing a
call-free `MirStepsConverges` prefix with a `MirModularWpConverges`
continuation.
-/
theorem MirModularWpConverges.bind
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h₁ : MirStepsConverges body s mid post)
    (h₂ : ∀ s', mid s' → MirModularWpConverges contract body s' post) :
    MirModularWpConverges contract body s post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym f₁ body st
        (fun
          | .running s' => mid s'
          | .halted out => post out
          | .faulted _ => False)
        post →
      ∃ f : Nat, wpMirExecModularSym contract f body st post from
    this (.running s) hf₁
  clear hf₁
  induction f₁ with
  | zero =>
    intro st h_st
    cases st with
    | running s' => exact h₂ s' h_st
    | halted out => exact ⟨1, h_st⟩
    | faulted _ => exact False.elim h_st
  | succ f₁' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st
    have h_ex :
        evalSymNodeTreeNoCall
          (fun st' => ∃ f, wpMirExecModularSym contract f body st' post)
          post
          (stepMirExecSymTree body st) := by
      refine evalSymNodeTreeNoCall_mono ?_ (fun _ hp => hp) h_st
      intro st' h_st'
      exact ih st' h_st'
    rcases evalSymNodeTreeNoCall_exists_fuel (stepMirExecSymTree body st) h_ex with
      ⟨f₂, hf₂⟩
    refine ⟨f₂ + 1, ?_⟩
    unfold wpMirExecModularSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at hf₂
    rw [evalSymNodeTreeModular_eq, stepMirExecSymTree_eval, evalNodeModularWP_eq]
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at hf₂ ⊢
      exact hf₂
    | tau st' =>
      simp only [h_step] at hf₂ ⊢
      exact hf₂
    | vis i k =>
      simp only [h_step] at hf₂ ⊢
      rcases i with f | (e | c)
      · exact False.elim hf₂
      · cases e
        exact hf₂
      · exact False.elim hf₂

/--
Pointwise state-to-state `bind` specialization for `MirModularWpConverges` via
`MirReachState`.
-/
theorem MirModularWpConverges.bind_reachState
    {contract : MirCallContract} {body : CapturedMir} {s s' : MachineState}
    {post : MirOutcome → Prop}
    (h₁ : MirReachState body s s')
    (h₂ : MirModularWpConverges contract body s' post) :
    MirModularWpConverges contract body s post :=
  MirModularWpConverges.bind
    (MirStepsConverges.mono (fun _ h => h) (fun _ h => h.elim) h₁)
    (fun _ h_eq => h_eq ▸ h₂)

/--
Fuel-free single-step symbolic unfolding rule for `MirModularWpConverges`.
-/
theorem MirModularWpConverges.step
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h :
      evalSymNodeTreeNoCall
        (fun
          | .running s' => MirModularWpConverges contract body s' post
          | .halted out => post out
          | .faulted _ => False)
        post
        (stepMirSymTree body s)) :
    MirModularWpConverges contract body s post := by
  refine MirModularWpConverges.bind
    (mid := fun s' => MirModularWpConverges contract body s' post) ?_ ?_
  · exact ⟨1, h⟩
  · intro _ h_next
    exact h_next

/--
Conjunction of two fuel-free `MirModularWpConverges` proofs by aligning fuel to
`max f₁ f₂`.
-/
theorem MirModularWpConverges.conj
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {P Q : MirOutcome → Prop}
    (hP : MirModularWpConverges contract body s P)
    (hQ : MirModularWpConverges contract body s Q) :
    MirModularWpConverges contract body s (fun out => P out ∧ Q out) := by
  rcases hP with ⟨f₁, h₁⟩
  rcases hQ with ⟨f₂, h₂⟩
  have h₁' := wpMirModularSym_mono (Nat.le_max_left f₁ f₂) h₁
  have h₂' := wpMirModularSym_mono (Nat.le_max_right f₁ f₂) h₂
  rw [wpMirModularSym, wpMirExecModularSym_eq_wpCoalBounded] at h₁' h₂'
  refine ⟨max f₁ f₂, ?_⟩
  rw [wpMirModularSym, wpMirExecModularSym_eq_wpCoalBounded]
  exact wpCoalBounded_conj h₁' h₂'

/--
Total-correctness (`DWP (mirModularWP contract.toCallContract)`) soundness of
`MirModularWpConverges`.
-/
theorem dwp_of_mirModularWpConverges
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : MirModularWpConverges contract body s post) :
    DWP (mirModularWP contract.toCallContract) (mirTree body s)
      (fun out _ => post out) PUnit.unit := by
  rcases h with ⟨fuel, h_wp⟩
  rw [wpMirModularSym, wpMirExecModularSym_eq_wpCoalBounded] at h_wp
  exact dwp_cofix_of_wpCoalBounded fuel h_wp

/--
Partial-correctness (`DWLP (mirModularWP contract.toCallContract)`) soundness of
`MirModularWpConverges`.
-/
theorem dwlp_of_mirModularWpConverges
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : MirModularWpConverges contract body s post) :
    DWLP (mirModularWP contract.toCallContract) (mirTree body s)
      (fun out _ => post out) PUnit.unit :=
  (dwp_of_mirModularWpConverges h).toDWLP

/--
Fuel-free discharge of `ModularVerificationResult` for `body` under
`contract.holdsOn` from `MirModularWpConverges`.
-/
theorem verifyModularContractMir_of_wpConverges
    (contract : MirCallContract)
    (body : CapturedMir)
    (pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        pre args mem →
        MirModularWpConverges contract body
          (initMachineStateWithMemory body args mem)
          (mirSafePost (post args mem))) :
    ModularVerificationResult
      { body := body
        envAssumed := contract.holdsOn
        pre := pre
        post := post } := by
  refine verifyModularContractByDWLP contract body pre post
    (fun args mem h_pre => ?_)
  exact dwlp_of_mirModularWpConverges
    (MirModularWpConverges.mono
      (fun out ho => (mirSafePost_iff_forall_normal _ out).1 ho)
      (h_wp args mem h_pre))

/-! ### Single-Pass Trace-Aware Symbolic Evaluation & `MirTraceWpConverges` -/

/-- Direct `Prop`-valued node evaluator matching `mirTraceWP` on `MirStepNode`. -/
@[reducible]
def evalNodeTraceWP
    (cont : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (tr : List (Event MirEffect)) :
    MirStepNode → Prop
  | .ret out => post tr out
  | .tau st' => cont st' tr
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl e)) k =>
    cont (k PUnit.unit) (tr ++ [⟨.inr (.inl e), PUnit.unit⟩])
  | .vis (.inr (.inr (.call req))) k =>
    ∀ ans : MirCallAns,
      cont (k ans) (tr ++ [⟨.inr (.inr (.call req)), ans⟩])

theorem evalNodeTraceWP_iff
    (cont : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (tr : List (Event MirEffect))
    (node : MirStepNode) :
    evalNodeTraceWP cont post tr node ↔
      match node with
      | .ret out => post tr out
      | .tau st' => cont st' tr
      | .vis i k => mirTraceWP.wp i (fun o tr' => cont (k o) tr') tr := by
  cases node with
  | ret _ => exact Iff.rfl
  | tau _ => exact Iff.rfl
  | vis i k =>
    rcases i with f | (e | c)
    · cases f
      dsimp [evalNodeTraceWP, mirTraceWP, eventTraceWP, FaultEffect.isFault, Sum.elim]
      exact ⟨False.elim, fun h => h.1 trivial⟩
    · cases e
      dsimp [evalNodeTraceWP, mirTraceWP, eventTraceWP, FaultEffect.isFault, Sum.elim]
      exact ⟨fun h => ⟨not_false, fun | PUnit.unit => h⟩, fun h => h.2 PUnit.unit⟩
    · cases c
      dsimp [evalNodeTraceWP, mirTraceWP, eventTraceWP, FaultEffect.isFault, Sum.elim]
      exact ⟨fun h => ⟨not_false, h⟩, fun h => h.2⟩

/-- Structural `Prop`-valued trace-recording evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeTrace
    (cont : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (tr : List (Event MirEffect)) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post tr out
  | .leaf (.tau st') => cont st' tr
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl e)) k) =>
    cont (k PUnit.unit) (tr ++ [⟨.inr (.inl e), PUnit.unit⟩])
  | .leaf (.vis (.inr (.inr (.call req))) k) =>
    ∀ ans : MirCallAns,
      cont (k ans) (tr ++ [⟨.inr (.inr (.call req)), ans⟩])
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeTrace cont post tr t1
    | false => evalSymNodeTreeTrace cont post tr t2

theorem evalSymNodeTreeTrace_eq
    (cont : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (tr : List (Event MirEffect))
    (t : SymTree MirStepNode) :
    evalSymNodeTreeTrace cont post tr t = evalNodeTraceWP cont post tr t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

/-- Single-pass fuel-bounded trace-aware symbolic WP over `MirExecState`. -/
def wpMirExecTraceSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (tr : List (Event MirEffect))
    (post : List (Event MirEffect) → MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    evalSymNodeTreeTrace
      (fun st' tr' => wpMirExecTraceSym fuel' body st' tr' post)
      post tr
      (stepMirExecSymTree body st)

/-- Single-pass fuel-bounded trace-aware symbolic WP over `MachineState`. -/
def wpMirTraceSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : List (Event MirEffect) → MirOutcome → Prop) : Prop :=
  wpMirExecTraceSym fuel body (.running s) [] post

/--
Equivalence between single-pass `wpMirExecTraceSym` and
`wpCoalBounded fuel mirTraceWP`.
-/
theorem wpMirExecTraceSym_iff_wpCoalBounded
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (tr : List (Event MirEffect))
    (post : List (Event MirEffect) → MirOutcome → Prop) :
    wpMirExecTraceSym fuel body st tr post ↔
      wpCoalBounded fuel mirTraceWP (stepMirState body)
        (fun out tr' => post tr' out) st tr := by
  induction fuel generalizing st tr with
  | zero => exact Iff.rfl
  | succ fuel' ih =>
    unfold wpMirExecTraceSym wpCoalBounded
    rw [evalSymNodeTreeTrace_eq, stepMirExecSymTree_eval, evalNodeTraceWP_iff]
    cases stepMirState body st with
    | ret _ => exact Iff.rfl
    | tau st' => exact ih st' tr
    | vis i k =>
      dsimp [mirTraceWP, eventTraceWP]
      exact and_congr_right (fun _ => forall_congr' (fun o => ih (k o) _))

/--
Equivalence between single-pass `wpMirTraceSym` and `Lower.wpMirTraceBounded`.
-/
theorem wpMirTraceSym_iff_wpMirTraceBounded
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (post : List (Event MirEffect) → MirOutcome → Prop) :
    wpMirTraceSym fuel body s post ↔ wpMirTraceBounded fuel body s post :=
  wpMirExecTraceSym_iff_wpCoalBounded fuel body (.running s) [] post

/-- Kleene fuel monotonicity for `wpMirExecTraceSym`. -/
theorem wpMirExecTraceSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {st : MirExecState} {tr : List (Event MirEffect)}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : wpMirExecTraceSym f₁ body st tr post) :
    wpMirExecTraceSym f₂ body st tr post := by
  rw [wpMirExecTraceSym_iff_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_fuel h_le h

/-- Kleene fuel monotonicity for `wpMirTraceSym`. -/
theorem wpMirTraceSym_mono
    {f₁ f₂ : Nat} (h_le : f₁ ≤ f₂)
    {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : wpMirTraceSym f₁ body s post) :
    wpMirTraceSym f₂ body s post :=
  wpMirExecTraceSym_mono h_le h

/-- Postcondition weakening for `wpMirExecTraceSym`. -/
theorem wpMirExecTraceSym_mono_post
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {tr : List (Event MirEffect)}
    {P Q : List (Event MirEffect) → MirOutcome → Prop}
    (h_imp : ∀ tr' out, P tr' out → Q tr' out)
    (h : wpMirExecTraceSym fuel body st tr P) :
    wpMirExecTraceSym fuel body st tr Q := by
  rw [wpMirExecTraceSym_iff_wpCoalBounded] at h ⊢
  exact wpCoalBounded_mono_both (Nat.le_refl fuel)
    (fun out tr' hp => h_imp tr' out hp) h

/-- Postcondition weakening for `wpMirTraceSym`. -/
theorem wpMirTraceSym_mono_post
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {P Q : List (Event MirEffect) → MirOutcome → Prop}
    (h_imp : ∀ tr' out, P tr' out → Q tr' out)
    (h : wpMirTraceSym fuel body s P) :
    wpMirTraceSym fuel body s Q :=
  wpMirExecTraceSym_mono_post h_imp h

/--
Trace-prefix shift invariance for `wpMirExecTraceSym`: starting at trace
`tr₁ ++ tr₂` with postcondition `post` is equivalent to starting at `tr₂` with
shifted postcondition `fun tr out => post (tr₁ ++ tr) out`.
-/
theorem wpMirExecTraceSym_append
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (tr₁ tr₂ : List (Event MirEffect))
    (post : List (Event MirEffect) → MirOutcome → Prop) :
    wpMirExecTraceSym fuel body st (tr₁ ++ tr₂) post ↔
      wpMirExecTraceSym fuel body st tr₂ (fun tr out => post (tr₁ ++ tr) out) := by
  induction fuel generalizing st tr₂ with
  | zero => exact Iff.rfl
  | succ fuel' ih =>
    unfold wpMirExecTraceSym
    rw [evalSymNodeTreeTrace_eq, evalSymNodeTreeTrace_eq, stepMirExecSymTree_eval]
    cases stepMirState body st with
    | ret _ => exact Iff.rfl
    | tau st' => exact ih st' tr₂
    | vis i k =>
      rcases i with f | (e | c)
      · exact Iff.rfl
      · cases e
        dsimp [evalNodeTraceWP]
        rw [List.append_assoc]
        exact ih (k PUnit.unit) _
      · rcases c with ⟨req⟩
        dsimp [evalNodeTraceWP]
        refine forall_congr' (fun ans => ?_)
        rw [List.append_assoc]
        exact ih (k ans) _

/--
Every `wpMirExecSym fuel body st post` proof implies `wpMirExecTraceSym` for any
initial trace `tr` when the trace is ignored in the postcondition.
-/
theorem wpMirExecTraceSym_of_wpMirExecSym
    {fuel : Nat} {body : CapturedMir} {st : MirExecState}
    {tr : List (Event MirEffect)} {post : MirOutcome → Prop}
    (h : wpMirExecSym fuel body st post) :
    wpMirExecTraceSym fuel body st tr (fun _ out => post out) := by
  induction fuel generalizing st tr with
  | zero => exact False.elim h
  | succ fuel' ih =>
    unfold wpMirExecSym at h
    unfold wpMirExecTraceSym
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval] at h
    rw [evalSymNodeTreeTrace_eq, stepMirExecSymTree_eval]
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h ⊢
      exact h
    | tau st' =>
      simp only [h_step] at h ⊢
      exact ih h
    | vis i k =>
      simp only [h_step] at h ⊢
      rcases i with f | (e | c)
      · exact False.elim h
      · cases e
        exact ih h
      · rcases c with ⟨req⟩
        intro ans
        exact ih (h ans)

/-- Direct `Prop`-valued call-free trace node evaluator on `MirStepNode`. -/
@[reducible]
def evalNodeTraceNoCallWP
    (cont : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (tr : List (Event MirEffect)) :
    MirStepNode → Prop
  | .ret out => post tr out
  | .tau st' => cont st' tr
  | .vis (.inl _) _ => False
  | .vis (.inr (.inl e)) k =>
    cont (k PUnit.unit) (tr ++ [⟨.inr (.inl e), PUnit.unit⟩])
  | .vis (.inr (.inr _)) _ => False

/-- Structural `Prop`-valued call-free trace evaluator over `SymTree MirStepNode`. -/
def evalSymNodeTreeTraceNoCall
    (cont : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (tr : List (Event MirEffect)) :
    SymTree MirStepNode → Prop
  | .leaf (.ret out) => post tr out
  | .leaf (.tau st') => cont st' tr
  | .leaf (.vis (.inl _) _) => False
  | .leaf (.vis (.inr (.inl e)) k) =>
    cont (k PUnit.unit) (tr ++ [⟨.inr (.inl e), PUnit.unit⟩])
  | .leaf (.vis (.inr (.inr _)) _) => False
  | .branch c t1 t2 =>
    match c with
    | true => evalSymNodeTreeTraceNoCall cont post tr t1
    | false => evalSymNodeTreeTraceNoCall cont post tr t2

theorem evalSymNodeTreeTraceNoCall_eq
    (cont : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop)
    (tr : List (Event MirEffect))
    (t : SymTree MirStepNode) :
    evalSymNodeTreeTraceNoCall cont post tr t =
      evalNodeTraceNoCallWP cont post tr t.eval := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => rfl
    | tau _ => rfl
    | vis i _ =>
      rcases i with f | (e | c) <;> rfl
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2
    · exact ih1

theorem evalSymNodeTreeTrace_of_evalSymNodeTreeTraceNoCall
    {cont : MirExecState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    {tr : List (Event MirEffect)}
    {t : SymTree MirStepNode}
    (h : evalSymNodeTreeTraceNoCall cont post tr t) :
    evalSymNodeTreeTrace cont post tr t := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => exact h
    | tau _ => exact h
    | vis i _ =>
      rcases i with f | (e | c)
      · exact False.elim h
      · exact h
      · exact False.elim h
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2 h
    · exact ih1 h

theorem evalSymNodeTreeTraceNoCall_mono
    {cont₁ cont₂ : MirExecState → List (Event MirEffect) → Prop}
    {post₁ post₂ : List (Event MirEffect) → MirOutcome → Prop}
    {tr : List (Event MirEffect)}
    (h_cont : ∀ st' tr', cont₁ st' tr' → cont₂ st' tr')
    (h_post : ∀ tr' out, post₁ tr' out → post₂ tr' out)
    {t : SymTree MirStepNode}
    (h : evalSymNodeTreeTraceNoCall cont₁ post₁ tr t) :
    evalSymNodeTreeTraceNoCall cont₂ post₂ tr t := by
  induction t with
  | leaf node =>
    cases node with
    | ret out => exact h_post tr out h
    | tau st' => exact h_cont st' tr h
    | vis i k =>
      rcases i with f | (e | c)
      · exact False.elim h
      · exact h_cont (k PUnit.unit) _ h
      · exact False.elim h
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2 h
    · exact ih1 h

theorem evalSymNodeTreeTraceNoCall_exists_fuel
    {cont : Nat → MirExecState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    {tr : List (Event MirEffect)}
    (t : SymTree MirStepNode)
    (h : evalSymNodeTreeTraceNoCall (fun st' tr' => ∃ f, cont f st' tr') post tr t) :
    ∃ f : Nat, evalSymNodeTreeTraceNoCall (cont f) post tr t := by
  induction t with
  | leaf node =>
    cases node with
    | ret _ => exact ⟨0, h⟩
    | tau _ => exact h
    | vis i _ =>
      rcases i with f | (e | c)
      · exact False.elim h
      · exact h
      · exact False.elim h
  | branch c _ _ ih1 ih2 =>
    cases c
    · exact ih2 h
    · exact ih1 h

/--
Single-pass fuel-bounded trace-accumulating state-to-state stepper over
`MirExecState`.
-/
def wpMirExecTraceStepsSym
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (tr : List (Event MirEffect))
    (mid : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop) : Prop :=
  match fuel with
  | 0 => mid st tr
  | fuel' + 1 =>
    evalSymNodeTreeTraceNoCall
      (fun st' tr' => wpMirExecTraceStepsSym fuel' body st' tr' mid post)
      post tr
      (stepMirExecSymTree body st)

/--
Single-pass fuel-bounded trace-accumulating state-to-state stepper over
`MachineState`.
-/
def wpMirTraceStepsSym
    (fuel : Nat) (body : CapturedMir) (s : MachineState)
    (mid : MachineState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop := fun _ _ => False) : Prop :=
  wpMirExecTraceStepsSym fuel body (.running s) []
    (fun
      | .running s', tr => mid s' tr
      | .halted out, tr => post tr out
      | .faulted _, _ => False)
    post

/--
Fuel-free trace-accumulating intermediate state convergence over `MachineState`.
-/
def MirTraceStepsConverges
    (body : CapturedMir) (s : MachineState)
    (mid : MachineState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop := fun _ _ => False) : Prop :=
  ∃ fuel : Nat, wpMirTraceStepsSym fuel body s mid post

/-- Lift a bounded `wpMirTraceStepsSym` proof into `MirTraceStepsConverges`. -/
theorem MirTraceStepsConverges.of_wpMirTraceStepsSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {mid : MachineState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : wpMirTraceStepsSym fuel body s mid post) :
    MirTraceStepsConverges body s mid post :=
  ⟨fuel, h⟩

/-- Zero-step reflexivity for `MirTraceStepsConverges`. -/
theorem MirTraceStepsConverges.refl
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : mid s []) :
    MirTraceStepsConverges body s mid post :=
  ⟨0, h⟩

/-- Monotonicity of `MirTraceStepsConverges` in `mid` and `post`. -/
theorem MirTraceStepsConverges.mono
    {body : CapturedMir} {s : MachineState}
    {mid₁ mid₂ : MachineState → List (Event MirEffect) → Prop}
    {post₁ post₂ : List (Event MirEffect) → MirOutcome → Prop}
    (h_mid : ∀ s' tr, mid₁ s' tr → mid₂ s' tr)
    (h_post : ∀ tr out, post₁ tr out → post₂ tr out)
    (h : MirTraceStepsConverges body s mid₁ post₁) :
    MirTraceStepsConverges body s mid₂ post₂ := by
  rcases h with ⟨fuel, hf⟩
  refine ⟨fuel, ?_⟩
  suffices ∀ (st : MirExecState) (tr : List (Event MirEffect)),
      wpMirExecTraceStepsSym fuel body st tr
        (fun
          | .running s', tr' => mid₁ s' tr'
          | .halted out, tr' => post₁ tr' out
          | .faulted _, _ => False)
        post₁ →
      wpMirExecTraceStepsSym fuel body st tr
        (fun
          | .running s', tr' => mid₂ s' tr'
          | .halted out, tr' => post₂ tr' out
          | .faulted _, _ => False)
        post₂ from
    this (.running s) [] hf
  clear hf
  induction fuel with
  | zero =>
    intro st tr h_st
    cases st with
    | running s' => exact h_mid s' tr h_st
    | halted out => exact h_post tr out h_st
    | faulted _ => exact False.elim h_st
  | succ fuel' ih =>
    intro st tr h_st
    unfold wpMirExecTraceStepsSym at h_st ⊢
    exact evalSymNodeTreeTraceNoCall_mono ih h_post h_st

/--
Lift any trace-agnostic `MirStepsConverges` proof into `MirTraceStepsConverges`.
-/
theorem MirTraceStepsConverges.of_stepsConverges
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop} {post : MirOutcome → Prop}
    (h : MirStepsConverges body s mid post) :
    MirTraceStepsConverges body s
      (fun s' _ => mid s')
      (fun _ out => post out) := by
  rcases h with ⟨fuel, hf⟩
  refine ⟨fuel, ?_⟩
  suffices ∀ (st : MirExecState) (tr : List (Event MirEffect)),
      wpMirExecStepsSym fuel body st
        (fun
          | .running s' => mid s'
          | .halted out => post out
          | .faulted _ => False)
        post →
      wpMirExecTraceStepsSym fuel body st tr
        (fun
          | .running s', _ => mid s'
          | .halted out, _ => post out
          | .faulted _, _ => False)
        (fun _ out => post out) from
    this (.running s) [] hf
  clear hf
  induction fuel with
  | zero =>
    intro st _ h_st
    cases st <;> exact h_st
  | succ fuel' ih =>
    intro st tr h_st
    unfold wpMirExecStepsSym at h_st
    unfold wpMirExecTraceStepsSym
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st
    rw [evalSymNodeTreeTraceNoCall_eq, stepMirExecSymTree_eval]
    cases h_step : stepMirState body st with
    | ret out =>
      simp only [h_step] at h_st ⊢
      exact h_st
    | tau st' =>
      simp only [h_step] at h_st ⊢
      exact ih st' tr h_st
    | vis i k =>
      simp only [h_step] at h_st ⊢
      rcases i with f | (e | c)
      · exact False.elim h_st
      · cases e
        exact ih (k PUnit.unit) _ h_st
      · exact False.elim h_st

/--
Trace-prefix shift invariance for `wpMirExecTraceStepsSym`: starting at trace
`tr₁ ++ tr₂` is equivalent to starting at `tr₂` with shifted intermediate and
final trace predicates.
-/
theorem wpMirExecTraceStepsSym_append
    (fuel : Nat) (body : CapturedMir) (st : MirExecState)
    (tr₁ tr₂ : List (Event MirEffect))
    (mid : MirExecState → List (Event MirEffect) → Prop)
    (post : List (Event MirEffect) → MirOutcome → Prop) :
    wpMirExecTraceStepsSym fuel body st (tr₁ ++ tr₂) mid post ↔
      wpMirExecTraceStepsSym fuel body st tr₂
        (fun st' tr => mid st' (tr₁ ++ tr))
        (fun tr out => post (tr₁ ++ tr) out) := by
  induction fuel generalizing st tr₂ with
  | zero => exact Iff.rfl
  | succ fuel' ih =>
    unfold wpMirExecTraceStepsSym
    rw [evalSymNodeTreeTraceNoCall_eq, evalSymNodeTreeTraceNoCall_eq, stepMirExecSymTree_eval]
    cases stepMirState body st with
    | ret _ => exact Iff.rfl
    | tau st' => exact ih st' tr₂
    | vis i k =>
      rcases i with f | (e | c)
      · exact Iff.rfl
      · cases e
        dsimp [evalNodeTraceNoCallWP]
        rw [List.append_assoc]
        exact ih (k PUnit.unit) _
      · exact Iff.rfl

/--
Fuel-free transitivity of `MirTraceStepsConverges` across multi-stage
trace-accumulating executions.
-/
theorem MirTraceStepsConverges.trans
    {body : CapturedMir} {s : MachineState}
    {mid₁ mid₂ : MachineState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h₁ : MirTraceStepsConverges body s mid₁ post)
    (h₂ :
      ∀ s' tr₁,
        mid₁ s' tr₁ →
        MirTraceStepsConverges body s'
          (fun s'' tr₂ => mid₂ s'' (tr₁ ++ tr₂))
          (fun tr₂ out => post (tr₁ ++ tr₂) out)) :
    MirTraceStepsConverges body s mid₂ post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  suffices ∀ (st : MirExecState) (tr : List (Event MirEffect)),
      wpMirExecTraceStepsSym f₁ body st tr
        (fun
          | .running s', tr' => mid₁ s' tr'
          | .halted out, tr' => post tr' out
          | .faulted _, _ => False)
        post →
      ∃ f : Nat,
        wpMirExecTraceStepsSym f body st tr
          (fun
            | .running s', tr' => mid₂ s' tr'
            | .halted out, tr' => post tr' out
            | .faulted _, _ => False)
          post from
    this (.running s) [] hf₁
  clear hf₁
  induction f₁ with
  | zero =>
    intro st tr h_st
    cases st with
    | running s' =>
      rcases h₂ s' tr h_st with ⟨f₂, hf₂⟩
      refine ⟨f₂, ?_⟩
      have h_mid_eq :
          (fun (st' : MirExecState) (tr₁ : List (Event MirEffect)) =>
            (fun
              | MirExecState.running s'', tr' => mid₂ s'' tr'
              | MirExecState.halted out, tr' => post tr' out
              | MirExecState.faulted _, _ => False) st' (tr ++ tr₁)) =
          (fun
            | MirExecState.running s'', tr₁ => mid₂ s'' (tr ++ tr₁)
            | MirExecState.halted out, tr₁ => post (tr ++ tr₁) out
            | MirExecState.faulted _, _ => False) := by
        funext st' tr₁
        cases st' <;> rfl
      have h_app :=
        (wpMirExecTraceStepsSym_append f₂ body (.running s') tr []
          (fun
            | .running s'', tr' => mid₂ s'' tr'
            | .halted out, tr' => post tr' out
            | .faulted _, _ => False)
          post).2 (h_mid_eq.symm ▸ hf₂)
      simpa only [List.append_nil] using h_app
    | halted out => exact ⟨0, h_st⟩
    | faulted _ => exact False.elim h_st
  | succ f₁' ih =>
    intro st tr h_st
    unfold wpMirExecTraceStepsSym at h_st
    have h_ex :
        evalSymNodeTreeTraceNoCall
          (fun st' tr' =>
            ∃ f,
              wpMirExecTraceStepsSym f body st' tr'
                (fun
                  | .running s', tr'' => mid₂ s' tr''
                  | .halted out, tr'' => post tr'' out
                  | .faulted _, _ => False)
                post)
          post tr
          (stepMirExecSymTree body st) := by
      refine evalSymNodeTreeTraceNoCall_mono ?_ (fun _ _ hp => hp) h_st
      intro st' tr' h_st'
      exact ih st' tr' h_st'
    rcases evalSymNodeTreeTraceNoCall_exists_fuel (stepMirExecSymTree body st) h_ex with
      ⟨f₂, hf₂⟩
    exact ⟨f₂ + 1, hf₂⟩

/--
Single-step symbolic unfolding rule for `MirTraceStepsConverges`.
-/
theorem MirTraceStepsConverges.step
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h :
      evalSymNodeTreeTraceNoCall
        (fun
          | .running s', tr₁ =>
            MirTraceStepsConverges body s'
              (fun s'' tr₂ => mid s'' (tr₁ ++ tr₂))
              (fun tr₂ out => post (tr₁ ++ tr₂) out)
          | .halted out, tr₁ => post tr₁ out
          | .faulted _, _ => False)
        post []
        (stepMirSymTree body s)) :
    MirTraceStepsConverges body s mid post :=
  MirTraceStepsConverges.trans
    (mid₁ := fun s' tr₁ =>
      MirTraceStepsConverges body s'
        (fun s'' tr₂ => mid s'' (tr₁ ++ tr₂))
        (fun tr₂ out => post (tr₁ ++ tr₂) out))
    ⟨1, h⟩
    (fun _ _ h_next => h_next)

/-- Single-step silent `.tau` transition rule for `MirTraceStepsConverges`. -/
theorem MirTraceStepsConverges.step_tau
    {body : CapturedMir} {s s' : MachineState}
    {mid : MachineState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h_step : stepMirFn body s = .tau (.running s'))
    (h_next : MirTraceStepsConverges body s' mid post) :
    MirTraceStepsConverges body s mid post := by
  rcases h_next with ⟨fuel, h_wp⟩
  refine ⟨fuel + 1, ?_⟩
  unfold wpMirTraceStepsSym wpMirExecTraceStepsSym
  rw [evalSymNodeTreeTraceNoCall_eq, stepMirExecSymTree_eval]
  dsimp only [stepMirState]
  rw [h_step]
  exact h_wp

/-- Single-step `MirObs.event` emission rule for `MirTraceStepsConverges`. -/
theorem MirTraceStepsConverges.step_emit
    {body : CapturedMir} {s s' : MachineState} {ev : Nat}
    {mid : MachineState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h_step : stepMirFn body s = MirStepNode.emitStep (.event ev) s')
    (h_next :
      MirTraceStepsConverges body s'
        (fun s'' tr₂ =>
          mid s'' ([⟨.inr (.inl (.emit (.event ev))), PUnit.unit⟩] ++ tr₂))
        (fun tr₂ out =>
          post ([⟨.inr (.inl (.emit (.event ev))), PUnit.unit⟩] ++ tr₂) out)) :
    MirTraceStepsConverges body s mid post := by
  refine MirTraceStepsConverges.step ?_
  rw [evalSymNodeTreeTraceNoCall_eq, stepMirSymTree_eval, h_step]
  dsimp [MirStepNode.emitStep]
  exact h_next

/--
Every `runMirTauToBlock fuel body targetBlock s = some s'` execution witnesses
`MirTraceStepsConverges body s (fun s₁ tr => s₁ = s' ∧ tr = []) post`.
-/
theorem MirTraceStepsConverges.of_runMirTauToBlock
    {fuel : Nat} {body : CapturedMir} {targetBlock : BasicBlockIdx}
    {s s' : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : runMirTauToBlock fuel body targetBlock s = some s') :
    MirTraceStepsConverges body s (fun s₁ tr => s₁ = s' ∧ tr = []) post := by
  induction fuel generalizing s with
  | zero => nomatch h
  | succ fuel' ih =>
    unfold runMirTauToBlock at h
    split at h
    · injection h with h_eq
      subst h_eq
      exact ⟨0, rfl, rfl⟩
    · cases h_step : stepMirFn body s with
      | ret _ => simp only [h_step] at h; nomatch h
      | vis _ _ => simp only [h_step] at h; nomatch h
      | tau execNext =>
        simp only [h_step] at h
        cases execNext with
        | running s₁ =>
          exact MirTraceStepsConverges.step_tau h_step (ih h)
        | halted _ => nomatch h
        | faulted _ => nomatch h

/--
Fuel-free trace-aware weakest precondition over `MachineState`.
-/
def MirTraceWpConverges
    (body : CapturedMir) (s : MachineState)
    (post : List (Event MirEffect) → MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirTraceBounded fuel body s post

/--
Equivalence between `MirTraceWpConverges` and `∃ fuel, wpMirTraceSym fuel`.
-/
theorem MirTraceWpConverges.iff_exists_wpMirTraceSym
    (body : CapturedMir) (s : MachineState)
    (post : List (Event MirEffect) → MirOutcome → Prop) :
    MirTraceWpConverges body s post ↔
      ∃ fuel : Nat, wpMirTraceSym fuel body s post :=
  exists_congr (fun fuel => (wpMirTraceSym_iff_wpMirTraceBounded fuel body s post).symm)

/-- Lift a bounded `wpMirTraceSym` proof into `MirTraceWpConverges`. -/
theorem MirTraceWpConverges.of_wpMirTraceSym
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : wpMirTraceSym fuel body s post) :
    MirTraceWpConverges body s post :=
  ⟨fuel, (wpMirTraceSym_iff_wpMirTraceBounded fuel body s post).1 h⟩

/-- Lift a bounded `wpMirTraceBounded` proof into `MirTraceWpConverges`. -/
theorem MirTraceWpConverges.of_wpMirTraceBounded
    {fuel : Nat} {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : wpMirTraceBounded fuel body s post) :
    MirTraceWpConverges body s post :=
  ⟨fuel, h⟩

/--
Every `MirWpConverges body s post` proof implies `MirTraceWpConverges` when the
postcondition does not constrain the trace.
-/
theorem MirTraceWpConverges.of_mirWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirWpConverges body s post) :
    MirTraceWpConverges body s (fun _ out => post out) := by
  rcases h with ⟨fuel, h_wp⟩
  exact MirTraceWpConverges.of_wpMirTraceSym
    (wpMirExecTraceSym_of_wpMirExecSym h_wp)

/--
Every `MirNoCallWpConverges body s post` proof implies `MirTraceWpConverges`
when the postcondition does not constrain the trace.
-/
theorem MirTraceWpConverges.of_noCall
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirNoCallWpConverges body s post) :
    MirTraceWpConverges body s (fun _ out => post out) :=
  MirTraceWpConverges.of_mirWpConverges (MirWpConverges.of_noCall h)

/-- Postcondition monotonicity for `MirTraceWpConverges`. -/
theorem MirTraceWpConverges.mono
    {body : CapturedMir} {s : MachineState}
    {P Q : List (Event MirEffect) → MirOutcome → Prop}
    (h_imp : ∀ tr out, P tr out → Q tr out)
    (h : MirTraceWpConverges body s P) :
    MirTraceWpConverges body s Q := by
  rcases h with ⟨fuel, h_wp⟩
  refine ⟨fuel, ?_⟩
  exact wpCoalBounded_mono_both (Nat.le_refl fuel)
    (fun out tr hp => h_imp tr out hp) h_wp

/--
Conjunction of two fuel-free `MirTraceWpConverges` proofs by aligning fuel to
`max f₁ f₂`.
-/
theorem MirTraceWpConverges.conj
    {body : CapturedMir} {s : MachineState}
    {P Q : List (Event MirEffect) → MirOutcome → Prop}
    (hP : MirTraceWpConverges body s P)
    (hQ : MirTraceWpConverges body s Q) :
    MirTraceWpConverges body s (fun tr out => P tr out ∧ Q tr out) := by
  rcases hP with ⟨f₁, h₁⟩
  rcases hQ with ⟨f₂, h₂⟩
  exact ⟨max f₁ f₂,
    wpCoalBounded_conj
      (wpMirTraceBounded_mono (Nat.le_max_left f₁ f₂) h₁)
      (wpMirTraceBounded_mono (Nat.le_max_right f₁ f₂) h₂)⟩

/--
Fuel-free sequential composition (`MirTraceWpConverges.bind`) composing a
trace-accumulating first stage `MirTraceStepsConverges body s mid post` with a
continuation `∀ s' tr₁, mid s' tr₁ → MirTraceWpConverges body s' (fun tr₂ out => post (tr₁ ++ tr₂) out)`
without exposing fuel.
-/
theorem MirTraceWpConverges.bind
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → List (Event MirEffect) → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h₁ : MirTraceStepsConverges body s mid post)
    (h₂ :
      ∀ s' tr₁,
        mid s' tr₁ →
        MirTraceWpConverges body s' (fun tr₂ out => post (tr₁ ++ tr₂) out)) :
    MirTraceWpConverges body s post := by
  rw [MirTraceWpConverges.iff_exists_wpMirTraceSym]
  rcases h₁ with ⟨f₁, hf₁⟩
  suffices ∀ (st : MirExecState) (tr : List (Event MirEffect)),
      wpMirExecTraceStepsSym f₁ body st tr
        (fun
          | .running s', tr' => mid s' tr'
          | .halted out, tr' => post tr' out
          | .faulted _, _ => False)
        post →
      ∃ f : Nat, wpMirExecTraceSym f body st tr post from
    this (.running s) [] hf₁
  clear hf₁
  induction f₁ with
  | zero =>
    intro st tr h_st
    cases st with
    | running s' =>
      rcases (MirTraceWpConverges.iff_exists_wpMirTraceSym body s' _).1 (h₂ s' tr h_st) with
        ⟨f₂, hf₂⟩
      refine ⟨f₂, ?_⟩
      have h_app :=
        (wpMirExecTraceSym_append f₂ body (.running s') tr [] post).2 hf₂
      simpa only [List.append_nil] using h_app
    | halted out => exact ⟨1, h_st⟩
    | faulted _ => exact False.elim h_st
  | succ f₁' ih =>
    intro st tr h_st
    unfold wpMirExecTraceStepsSym at h_st
    have h_ex :
        evalSymNodeTreeTraceNoCall
          (fun st' tr' => ∃ f, wpMirExecTraceSym f body st' tr' post)
          post tr
          (stepMirExecSymTree body st) := by
      refine evalSymNodeTreeTraceNoCall_mono ?_ (fun _ _ hp => hp) h_st
      intro st' tr' h_st'
      exact ih st' tr' h_st'
    rcases evalSymNodeTreeTraceNoCall_exists_fuel (stepMirExecSymTree body st) h_ex with
      ⟨f₂, hf₂⟩
    exact ⟨f₂ + 1, evalSymNodeTreeTrace_of_evalSymNodeTreeTraceNoCall hf₂⟩

/--
Silent-prefix specialization of `MirTraceWpConverges.bind` when the first stage
reaches `mid s'` with empty emitted trace `tr = []`.
-/
theorem MirTraceWpConverges.bind_silent
    {body : CapturedMir} {s : MachineState}
    {mid : MachineState → Prop}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h₁ : MirTraceStepsConverges body s (fun s' tr => mid s' ∧ tr = []) post)
    (h₂ : ∀ s', mid s' → MirTraceWpConverges body s' post) :
    MirTraceWpConverges body s post :=
  MirTraceWpConverges.bind h₁ (fun s' tr ⟨h_mid, h_tr⟩ => by
    subst h_tr
    exact h₂ s' h_mid)

/--
Fuel-free single-step symbolic unfolding rule for `MirTraceWpConverges`.
-/
theorem MirTraceWpConverges.step
    {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h :
      evalSymNodeTreeTraceNoCall
        (fun
          | .running s', tr₁ =>
            MirTraceWpConverges body s' (fun tr₂ out => post (tr₁ ++ tr₂) out)
          | .halted out, tr₁ => post tr₁ out
          | .faulted _, _ => False)
        post []
        (stepMirSymTree body s)) :
    MirTraceWpConverges body s post :=
  MirTraceWpConverges.bind
    (mid := fun s' tr₁ =>
      MirTraceWpConverges body s' (fun tr₂ out => post (tr₁ ++ tr₂) out))
    ⟨1, h⟩
    (fun _ _ h_next => h_next)

/-- Total-correctness (`DWP mirTraceWP`) soundness of `MirTraceWpConverges`. -/
theorem dwp_of_mirTraceWpConverges
    {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : MirTraceWpConverges body s post) :
    DWP mirTraceWP (mirTree body s) (fun out tr => post tr out) [] := by
  rcases h with ⟨fuel, h_wp⟩
  exact dwp_cofix_of_wpCoalBounded fuel h_wp

/-- Partial-correctness (`DWLP mirTraceWP`) soundness of `MirTraceWpConverges`. -/
theorem dwlp_of_mirTraceWpConverges
    {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : MirTraceWpConverges body s post) :
    DWLP mirTraceWP (mirTree body s) (fun out tr => post tr out) [] :=
  (dwp_of_mirTraceWpConverges h).toDWLP

/--
Every `runMirTauToRet fuel body s = some out` execution witnesses
`MirTraceWpConverges body s (fun tr out' => tr = [] ∧ out' = out)`.
-/
theorem MirTraceWpConverges.of_runMirTauToRet
    {fuel : Nat} {body : CapturedMir} {s : MachineState} {out : MirOutcome}
    (h_run : runMirTauToRet fuel body s = some out) :
    MirTraceWpConverges body s (fun tr out' => tr = [] ∧ out' = out) := by
  induction fuel generalizing s with
  | zero => nomatch h_run
  | succ fuel' ih =>
    unfold runMirTauToRet at h_run
    cases h_step : stepMirFn body s with
    | ret out₀ =>
      simp only [h_step] at h_run
      injection h_run with h_eq
      subst h_eq
      refine MirTraceWpConverges.of_wpMirTraceSym (fuel := 1) ?_
      unfold wpMirTraceSym wpMirExecTraceSym
      rw [evalSymNodeTreeTrace_eq, stepMirExecSymTree_eval]
      dsimp only [stepMirState]
      rw [h_step]
      exact ⟨rfl, rfl⟩
    | vis _ _ =>
      simp only [h_step] at h_run; nomatch h_run
    | tau execNext =>
      simp only [h_step] at h_run
      cases execNext with
      | running s' =>
        exact MirTraceWpConverges.bind_silent
          (MirTraceStepsConverges.step_tau h_step
            (MirTraceStepsConverges.refl ⟨rfl, rfl⟩))
          (fun _ h_eq => h_eq ▸ ih h_run)
      | halted out₀ =>
        injection h_run with h_eq
        subst h_eq
        refine MirTraceWpConverges.of_wpMirTraceSym (fuel := 2) ?_
        unfold wpMirTraceSym wpMirExecTraceSym
        rw [evalSymNodeTreeTrace_eq, stepMirExecSymTree_eval]
        dsimp only [stepMirState]
        rw [h_step]
        dsimp only [evalNodeTraceWP]
        unfold wpMirExecTraceSym
        rw [evalSymNodeTreeTrace_eq, stepMirExecSymTree_eval]
        exact ⟨rfl, rfl⟩
      | faulted _ => nomatch h_run

/--
Fuel-free discharge of `TraceVerificationResult c` from `MirTraceWpConverges`.
-/
theorem verifyTraceMir_of_wpConverges
    (c : TraceClaim)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirTraceWpConverges c.body
          (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees)
          (fun tr out => c.post args mem tr out)) :
    TraceVerificationResult c :=
  verifyTraceByDWLP c (fun args mem h_pre =>
    dwlp_of_mirTraceWpConverges (h_wp args mem h_pre))

/--
Fuel-free discharge of a stateless `VerificationResult c` when `c.pre args`
pins `args` to `expectedArgs`.
-/
theorem dischargeStatelessEq_of_wpConverges
    (c : Claim)
    (expectedArgs : List Value)
    (h_pre : ∀ args : List Value, c.pre args → args = expectedArgs)
    (h_eval :
      MirWpConverges c.body
        (initMachineStateWithCallees c.body expectedArgs c.callees)
        (mirNormalPost (fun retVal _ => c.post expectedArgs retVal))) :
    VerificationResult c :=
  verifyMirNoPanic_of_wpConverges c (fun args hp => by
    rw [h_pre args hp]
    exact h_eval)

/--
Fuel-free discharge of a stateful `StatefulVerificationResult c` when
`c.pre args mem` pins `(args, mem)` to `(expectedArgs, expectedMem)`.
-/
theorem dischargeStatefulEq_of_wpConverges
    (c : StatefulClaim)
    (expectedArgs : List Value)
    (expectedMem : Memory)
    (h_pre :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem → args = expectedArgs ∧ mem = expectedMem)
    (h_eval :
      MirWpConverges c.body
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body expectedArgs expectedMem c.callees)
        (mirNormalPost (c.post expectedArgs expectedMem))) :
    StatefulVerificationResult c :=
  verifyStatefulMirNoPanic_of_wpConverges c (fun args mem hp => by
    rcases h_pre args mem hp with ⟨rfl, rfl⟩
    exact h_eval)

/--
Fuel-free verification of a 1-argument scalar function across all canonical
`width`-byte inputs.
-/
theorem verifyWellTypedScalarArg1_of_wpConverges
    (c : Claim) (width : Nat)
    (h_pre : ∀ args : List Value, c.pre args → WellTypedScalarArg1 width args)
    (h_sym :
      ∀ b : Nat,
        b < scalarModulus width →
        c.pre [.scalar { bits := b, sizeBytes := width }] →
        MirWpConverges c.body
          (initMachineStateWithCallees c.body
            [.scalar { bits := b, sizeBytes := width }] c.callees)
          (mirNormalPost
            (fun retVal _ =>
              c.post [.scalar { bits := b, sizeBytes := width }] retVal))) :
    VerificationResult c :=
  verifyMirNoPanic_of_wpConverges c (fun args hp => by
    rcases h_pre args hp with ⟨b, hb, rfl⟩
    exact h_sym b hb hp)

/-- Safe-panic fuel-free variant of `verifyWellTypedScalarArg1_of_wpConverges`. -/
theorem verifyWellTypedSafeScalarArg1_of_wpConverges
    (c : Claim) (width : Nat)
    (h_pre : ∀ args : List Value, c.pre args → WellTypedScalarArg1 width args)
    (h_sym :
      ∀ b : Nat,
        b < scalarModulus width →
        c.pre [.scalar { bits := b, sizeBytes := width }] →
        MirWpConverges c.body
          (initMachineStateWithCallees c.body
            [.scalar { bits := b, sizeBytes := width }] c.callees)
          (mirSafePost
            (fun retVal _ =>
              c.post [.scalar { bits := b, sizeBytes := width }] retVal))) :
    VerificationResult c :=
  verifyMirSafe_of_wpConverges c (fun args hp => by
    rcases h_pre args hp with ⟨b, hb, rfl⟩
    exact h_sym b hb hp)

/--
Fuel-free verification of a 2-argument scalar function across all canonical
`(w1, w2)`-byte inputs.
-/
theorem verifyWellTypedScalarArg2_of_wpConverges
    (c : Claim) (w1 w2 : Nat)
    (h_pre : ∀ args : List Value, c.pre args → WellTypedScalarArg2 w1 w2 args)
    (h_sym :
      ∀ b1 b2 : Nat,
        b1 < scalarModulus w1 →
        b2 < scalarModulus w2 →
        c.pre
          [ .scalar { bits := b1, sizeBytes := w1 }
          , .scalar { bits := b2, sizeBytes := w2 } ] →
        MirWpConverges c.body
          (initMachineStateWithCallees c.body
            [ .scalar { bits := b1, sizeBytes := w1 }
            , .scalar { bits := b2, sizeBytes := w2 } ] c.callees)
          (mirNormalPost
            (fun retVal _ =>
              c.post
                [ .scalar { bits := b1, sizeBytes := w1 }
                , .scalar { bits := b2, sizeBytes := w2 } ]
                retVal))) :
    VerificationResult c :=
  verifyMirNoPanic_of_wpConverges c (fun args hp => by
    rcases h_pre args hp with ⟨b1, b2, hb1, hb2, rfl⟩
    exact h_sym b1 b2 hb1 hb2 hp)

/-- Safe-panic fuel-free variant of `verifyWellTypedScalarArg2_of_wpConverges`. -/
theorem verifyWellTypedSafeScalarArg2_of_wpConverges
    (c : Claim) (w1 w2 : Nat)
    (h_pre : ∀ args : List Value, c.pre args → WellTypedScalarArg2 w1 w2 args)
    (h_sym :
      ∀ b1 b2 : Nat,
        b1 < scalarModulus w1 →
        b2 < scalarModulus w2 →
        c.pre
          [ .scalar { bits := b1, sizeBytes := w1 }
          , .scalar { bits := b2, sizeBytes := w2 } ] →
        MirWpConverges c.body
          (initMachineStateWithCallees c.body
            [ .scalar { bits := b1, sizeBytes := w1 }
            , .scalar { bits := b2, sizeBytes := w2 } ] c.callees)
          (mirSafePost
            (fun retVal _ =>
              c.post
                [ .scalar { bits := b1, sizeBytes := w1 }
                , .scalar { bits := b2, sizeBytes := w2 } ]
                retVal))) :
    VerificationResult c :=
  verifyMirSafe_of_wpConverges c (fun args hp => by
    rcases h_pre args hp with ⟨b1, b2, hb1, hb2, rfl⟩
    exact h_sym b1 b2 hb1 hb2 hp)

/-! ## 8. Concrete Multi-Block Fuel-Free Verification Witnesses -/

section ConcreteWitnesses

/-- Standard 4-byte `u32` `TypeLayout` entry for concrete test witnesses. -/
def u32Layout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr :=
      .scalar
        (.initialized (.int 32 false)
          { start := 0, end_ := 4294967295 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Standard 4-byte `u32` `Ty` referencing index `0` of `[u32Layout]`. -/
@[reducible, simp]
def u32Ty : Ty :=
  { kind := .uint .u32, layoutIdx := 0 }

/--
Concrete 3-block `CapturedMir` pipeline (`bb0 -> bb1 -> bb2`) taking one `u32`
argument (`_1`), copying `_1` into temporary `_2` in `bb0`, moving `_2` into the
return slot `_0` in `bb1`, and returning in `bb2`.
-/
def multiBlockPipelineBody : CapturedMir :=
  { defPath := "Anneal::MirFuelFree::multiBlockPipeline"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := u32Ty, debugName := some "_0" }
      , { mutability := .not, ty := u32Ty, debugName := some "x" }
      , { mutability := .mut, ty := u32Ty, debugName := some "tmp" } ]
    basicBlocks :=
      [ { statements :=
            [ { kind := .storageLive 2, span := "MirFuelFree.lean:bb0:0_storage_live" }
            , { kind :=
                  .assign
                    { local_ := 2, projection := [] }
                    (.use (.copy { local_ := 1, projection := [] }))
                span := "MirFuelFree.lean:bb0:0" } ]
          terminator := { kind := .goto 1, span := "MirFuelFree.lean:bb0:1" }
          isCleanup := false }
      , { statements :=
            [ { kind :=
                  .assign
                    { local_ := 0, projection := [] }
                    (.use (.move { local_ := 2, projection := [] }))
                span := "MirFuelFree.lean:bb1:0" } ]
          terminator := { kind := .goto 2, span := "MirFuelFree.lean:bb1:1" }
          isCleanup := false }
      , { statements := []
          terminator := { kind := .return_, span := "MirFuelFree.lean:bb2:0" }
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := u32Layout, mode := .direct }]
        ret := { layout := u32Layout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts :=
      { pointerBits := 64
        isLittleEndian := true
        entries := [u32Layout] }
    allocations := [] }

/-- Intermediate `MachineState` at the entry of `bb1` for `multiBlockPipelineBody`. -/
def multiBlockMidState (b : Nat) (mem : Memory) : MachineState :=
  { frame :=
      { blockIdx := 1
        stmtIdx := 0
        locals :=
          [ .uninit
          , .init (.scalar { bits := b, sizeBytes := 4 })
          , .init (.scalar { bits := b, sizeBytes := 4 }) ] }
    memory := mem }

/--
Stage 1 (`bb0 -> bb1`): `multiBlockPipelineBody` steps from its initial state on
`[.scalar ⟨b, 4⟩]` and any root-activation `mem : Memory` (`RootActiveMemory mem`,
preserving arbitrary heap allocations, tag counters, and `callees` tables) to
`multiBlockMidState b mem`.
-/
theorem multiBlockPipeline_stage1_converges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirStepsConverges multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (· = multiBlockMidState b mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨3, rfl⟩

/--
Stage 2 (`bb1 -> bb2 -> return`): from `multiBlockMidState b mem`,
`multiBlockPipelineBody` converges to normal return `.scalar ⟨b, 4⟩` with
unchanged `mem` for any `RootActiveMemory mem`.
-/
theorem multiBlockPipeline_stage2_converges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirWpConverges multiBlockPipelineBody
      (multiBlockMidState b mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨3, rfl, rfl⟩

/--
Fuel-free sequential composition of Stage 1 and Stage 2 via
`MirWpConverges.bind` without exposing any fuel constant in the theorem
signature, valid across arbitrary `mem : Memory` with `RootActiveMemory mem`.
-/
theorem multiBlockPipeline_wpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirWpConverges multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) :=
  MirWpConverges.bind
    (multiBlockPipeline_stage1_converges b mem h_root)
    (fun _ h_eq => h_eq ▸ multiBlockPipeline_stage2_converges b mem h_root)

/--
Deterministic outcome convergence (`MirConverges`) for `multiBlockPipelineBody`
across any `RootActiveMemory mem`.
-/
theorem multiBlockPipeline_converges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirConverges multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (.normal (.scalar { bits := b, sizeBytes := 4 }, mem)) := by
  refine MirWpConverges.mono ?_ (multiBlockPipeline_wpConverges b mem h_root)
  intro out h_post
  cases out with
  | normal rv =>
    rcases rv with ⟨retVal, mem'⟩
    rcases h_post with ⟨rfl, rfl⟩
    rfl
  | panic => exact False.elim h_post
  | abort => exact False.elim h_post

/--
Callee-populated (`BRIEF-3.2`) fuel-free convergence for
`initMachineStateWithMemoryAndCallees` across arbitrary `callees : List CapturedMir`
and any `RootActiveMemory mem`.
-/
theorem multiBlockPipeline_withMemoryAndCallees_wpConverges
    (b : Nat) (mem : Memory) (callees : List CapturedMir)
    (h_root : RootActiveMemory mem) :
    MirWpConverges multiBlockPipelineBody
      (initMachineStateWithMemoryAndCallees multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem callees)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧
          mem' = Memory.withDefaultCallees mem callees)) :=
  multiBlockPipeline_wpConverges b
    (Memory.withDefaultCallees mem callees)
    ((rootActiveMemory_withDefaultCallees mem callees).2 h_root)

/--
Callee-populated (`BRIEF-3.2`) fuel-free convergence for
`initMachineStateWithCallees` across arbitrary `callees : List CapturedMir`.
-/
theorem multiBlockPipeline_withCallees_wpConverges
    (b : Nat) (callees : List CapturedMir) :
    MirWpConverges multiBlockPipelineBody
      (initMachineStateWithCallees multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] callees)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧
          mem' =
            (initMachineStateWithCallees multiBlockPipelineBody
              [.scalar { bits := b, sizeBytes := 4 }] callees).memory)) := by
  have h := multiBlockPipeline_wpConverges b
    (initMachineStateWithCallees multiBlockPipelineBody
      [.scalar { bits := b, sizeBytes := 4 }] callees).memory
    (rootActiveMemory_initMachineStateWithCallees _ _ callees)
  rwa [← initMachineStateWithCallees_eq_withMemory] at h

/-- Stateless `Claim` for `multiBlockPipelineBody`. -/
def multiBlockPipelineClaim : Claim where
  body := multiBlockPipelineBody
  pre args := WellTypedScalarArg1 4 args
  post args retVal := args = [retVal]

/-- Non-vacuity witness for `multiBlockPipelineClaim.pre`. -/
theorem multiBlockPipelineClaim_nonVacuous :
    ∃ args : List Value, multiBlockPipelineClaim.pre args :=
  proveNonVacuousPre
    [.scalar { bits := 42, sizeBytes := 4 }]
    ⟨42, by decide, rfl⟩

/--
Fuel-free discharge of `VerificationResult multiBlockPipelineClaim` using
`verifyMirNoPanic_of_wpConverges` and `MirWpConverges.bind`.
-/
theorem verify_multiBlockPipelineClaim :
    VerificationResult multiBlockPipelineClaim := by
  refine verifyMirNoPanic_of_wpConverges multiBlockPipelineClaim ?_
  intro args h_pre
  rcases h_pre with ⟨b, _, rfl⟩
  exact MirWpConverges.mono
    (fun out ho => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases ho with ⟨h_rv, _⟩
        dsimp [mirNormalPost, multiBlockPipelineClaim]
        exact by rw [h_rv]
      | panic => exact False.elim ho
      | abort => exact False.elim ho)
    (multiBlockPipeline_wpConverges b _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

/--
Stateful `StatefulClaim` for `multiBlockPipelineBody` over any root-activation
`mem : Memory` (allowing arbitrary heap allocations, tag counters, and callee
tables).
-/
def multiBlockPipelineStatefulClaim : StatefulClaim where
  body := multiBlockPipelineBody
  pre args mem := WellTypedScalarArg1 4 args ∧ RootActiveMemory mem
  post args mem retVal mem' := args = [retVal] ∧ mem' = mem

/-- Non-vacuity witness for `multiBlockPipelineStatefulClaim.pre`. -/
theorem multiBlockPipelineStatefulClaim_nonVacuous :
    ∃ (args : List Value) (mem : Memory),
      multiBlockPipelineStatefulClaim.pre args mem :=
  proveNonVacuousStatefulPre
    [.scalar { bits := 42, sizeBytes := 4 }]
    (initMachineStateWithCallees multiBlockPipelineBody
      [.scalar { bits := 42, sizeBytes := 4 }] [multiBlockPipelineBody]).memory
    ⟨⟨42, by decide, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/--
Fuel-free discharge of `StatefulVerificationResult multiBlockPipelineStatefulClaim`
using `verifyStatefulMirNoPanic_of_wpConverges` and `MirWpConverges.bind`.
-/
theorem verify_multiBlockPipelineStatefulClaim :
    StatefulVerificationResult multiBlockPipelineStatefulClaim := by
  refine verifyStatefulMirNoPanic_of_wpConverges multiBlockPipelineStatefulClaim ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
  exact MirWpConverges.mono
    (fun out ho => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases ho with ⟨h_rv, h_mem_eq⟩
        dsimp [mirNormalPost, multiBlockPipelineStatefulClaim]
        exact ⟨by rw [h_rv], h_mem_eq⟩
      | panic => exact False.elim ho
      | abort => exact False.elim ho)
    (multiBlockPipeline_wpConverges b mem h_root)

/--
Total-correctness `TotalClaim` for `multiBlockPipelineBody` over any
root-activation `mem : Memory`.
-/
def multiBlockPipelineTotalClaim : TotalClaim where
  body := multiBlockPipelineBody
  pre args mem := WellTypedScalarArg1 4 args ∧ RootActiveMemory mem
  post args mem retVal mem' := args = [retVal] ∧ mem' = mem

/-- Non-vacuity witness for `multiBlockPipelineTotalClaim.pre`. -/
theorem multiBlockPipelineTotalClaim_nonVacuous :
    ∃ args mem,
      multiBlockPipelineTotalClaim.pre args mem :=
  proveNonVacuousStatefulPre
    [.scalar { bits := 42, sizeBytes := 4 }]
    (initMachineStateWithCallees multiBlockPipelineBody
      [.scalar { bits := 42, sizeBytes := 4 }] [multiBlockPipelineBody]).memory
    ⟨⟨42, by decide, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/--
Fuel-free discharge of `TotalVerificationResult multiBlockPipelineTotalClaim`
using `verifyTotalMir_of_wpConverges` and `MirWpConverges.bind`.
-/
theorem verify_multiBlockPipelineTotalClaim :
    TotalVerificationResult multiBlockPipelineTotalClaim := by
  refine verifyTotalMir_of_wpConverges multiBlockPipelineTotalClaim ?_
  intro args mem h_pre
  rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
  exact MirWpConverges.mono
    (fun out ho => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases ho with ⟨h_rv, h_mem_eq⟩
        dsimp [mirNormalPost, multiBlockPipelineTotalClaim]
        exact ⟨by rw [h_rv], h_mem_eq⟩
      | panic => exact False.elim ho
      | abort => exact False.elim ho)
    (multiBlockPipeline_wpConverges b mem h_root)

/--
Stage 2 call-free convergence (`MirNoCallWpConverges`) for
`multiBlockPipelineBody` from `multiBlockMidState b mem`.
-/
theorem multiBlockPipeline_stage2_noCallWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirNoCallWpConverges multiBlockPipelineBody
      (multiBlockMidState b mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨3, rfl, rfl⟩

/--
Fuel-free call-forbidding sequential composition (`MirNoCallWpConverges.bind`)
of Stage 1 and Stage 2 for `multiBlockPipelineBody`.
-/
theorem multiBlockPipeline_noCallWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirNoCallWpConverges multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) :=
  MirNoCallWpConverges.bind
    (multiBlockPipeline_stage1_converges b mem h_root)
    (fun _ h_eq => h_eq ▸ multiBlockPipeline_stage2_noCallWpConverges b mem h_root)

/--
Relational `StatefulEquivClaim` for `multiBlockPipelineBody` over any
`RootActiveMemory mem`.
-/
def multiBlockPipelineEquivClaim : StatefulEquivClaim where
  implBody := multiBlockPipelineBody
  specBody := multiBlockPipelineBody
  pre args mem := WellTypedScalarArg1 4 args ∧ RootActiveMemory mem
  post args mem retVal mem' := args = [retVal] ∧ mem' = mem

/-- Non-vacuity witness for `multiBlockPipelineEquivClaim.pre`. -/
theorem multiBlockPipelineEquivClaim_nonVacuous :
    ∃ (args : List Value) (mem : Memory),
      multiBlockPipelineEquivClaim.pre args mem :=
  multiBlockPipelineStatefulClaim_nonVacuous

/--
Fuel-free discharge of `StatefulEquivVerificationResult multiBlockPipelineEquivClaim`
using `verifyStatefulEquivMir_of_wpConverges` and `MirNoCallWpConverges.bind`.
-/
theorem verify_multiBlockPipelineEquivClaim :
    StatefulEquivVerificationResult multiBlockPipelineEquivClaim := by
  refine verifyStatefulEquivMir_of_wpConverges
    multiBlockPipelineEquivClaim
    (fun args mem => (args.headD .unit, mem))
    (fun args mem h_pre => ?_)
    (fun args mem h_pre => ?_)
  · rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
    refine MirNoCallWpConverges.mono ?_
      (multiBlockPipeline_noCallWpConverges b mem h_root)
    intro out ho
    cases out with
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases ho with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    | panic => exact False.elim ho
    | abort => exact False.elim ho
  · rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
    refine MirNoCallWpConverges.mono ?_
      (multiBlockPipeline_noCallWpConverges b mem h_root)
    intro out ho
    cases out with
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases ho with ⟨rfl, rfl⟩
      rfl
    | panic => exact False.elim ho
    | abort => exact False.elim ho


/--
Stage 2 UB-waived convergence (`MirUbWaivedWpConverges`) for
`multiBlockPipelineBody` from `multiBlockMidState b mem`.
-/
theorem multiBlockPipeline_stage2_ubWaivedWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirUbWaivedWpConverges multiBlockPipelineBody
      (multiBlockMidState b mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨3, rfl, rfl⟩

/--
Fuel-free UB-waived sequential composition (`MirUbWaivedWpConverges.bind`) of
Stage 1 (`multiBlockPipeline_stage1_converges`) and Stage 2
(`multiBlockPipeline_stage2_ubWaivedWpConverges`).
-/
theorem multiBlockPipeline_ubWaivedWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirUbWaivedWpConverges multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) :=
  MirUbWaivedWpConverges.bind
    (multiBlockPipeline_stage1_converges b mem h_root)
    (fun _ h_eq => h_eq ▸ multiBlockPipeline_stage2_ubWaivedWpConverges b mem h_root)

/--
Scoped `UbExceptionClaim` for `multiBlockPipelineBody`, where `strictSafetyPre`
(`mem.callees = []`) is a proper subdomain of `pre` (`WellTypedScalarArg1 4 args ∧ RootActiveMemory mem`).
-/
def multiBlockPipelineUbExceptionClaim : UbExceptionClaim where
  body := multiBlockPipelineBody
  pre args mem := WellTypedScalarArg1 4 args ∧ RootActiveMemory mem
  strictSafetyPre _ mem := mem.callees = []
  post args mem retVal mem' := args = [retVal] ∧ mem' = mem

/-- Non-vacuity witness for `multiBlockPipelineUbExceptionClaim.pre`. -/
theorem multiBlockPipelineUbExceptionClaim_nonVacuous :
    ∃ args mem, multiBlockPipelineUbExceptionClaim.pre args mem :=
  multiBlockPipelineStatefulClaim_nonVacuous

/--
Non-vacuity witness for the strict safety subdomain
`multiBlockPipelineUbExceptionClaim.pre ∧ multiBlockPipelineUbExceptionClaim.strictSafetyPre`.
-/
theorem multiBlockPipelineUbExceptionClaim_strictDomain_nonVacuous :
    ∃ args mem,
      multiBlockPipelineUbExceptionClaim.pre args mem ∧
      multiBlockPipelineUbExceptionClaim.strictSafetyPre args mem :=
  ⟨[.scalar { bits := 42, sizeBytes := 4 }],
   (initMachineState multiBlockPipelineBody
     [.scalar { bits := 42, sizeBytes := 4 }]).memory,
   ⟨⟨42, by decide, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩,
   rfl⟩

/--
Non-vacuity witness for the UB-waived complement subdomain
`multiBlockPipelineUbExceptionClaim.pre ∧ ¬ multiBlockPipelineUbExceptionClaim.strictSafetyPre`.
-/
theorem multiBlockPipelineUbExceptionClaim_waivedDomain_nonVacuous :
    ∃ args mem,
      multiBlockPipelineUbExceptionClaim.pre args mem ∧
      ¬ multiBlockPipelineUbExceptionClaim.strictSafetyPre args mem :=
  ⟨[.scalar { bits := 42, sizeBytes := 4 }],
   (initMachineStateWithCallees multiBlockPipelineBody
     [.scalar { bits := 42, sizeBytes := 4 }] [multiBlockPipelineBody]).memory,
   ⟨⟨42, by decide, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩,
   fun h => nomatch h⟩

/--
Fuel-free discharge of `UbExceptionVerificationResult multiBlockPipelineUbExceptionClaim`
using `verifyUbExceptionMir_of_wpConverges`, `MirWpConverges.bind`, and
`MirUbWaivedWpConverges.bind`.
-/
theorem verify_multiBlockPipelineUbExceptionClaim :
    UbExceptionVerificationResult multiBlockPipelineUbExceptionClaim := by
  refine verifyUbExceptionMir_of_wpConverges
    multiBlockPipelineUbExceptionClaim
    (fun args mem h_pre _ => ?_)
    (fun args mem h_pre => ?_)
  · rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
    refine MirWpConverges.mono ?_
      (multiBlockPipeline_wpConverges b mem h_root)
    intro out ho
    cases out with
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases ho with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | panic => exact False.elim ho
    | abort => exact False.elim ho
  · rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
    refine MirUbWaivedWpConverges.mono ?_
      (multiBlockPipeline_ubWaivedWpConverges b mem h_root)
    intro out ho
    cases out with
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases ho with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | panic => exact False.elim ho
    | abort => exact False.elim ho

/--
Stage 2 modular call-contract convergence (`MirModularWpConverges`) for
`multiBlockPipelineBody` from `multiBlockMidState b mem` under any
`contract : MirCallContract`.
-/
theorem multiBlockPipeline_stage2_modularWpConverges
    (contract : MirCallContract)
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirModularWpConverges contract multiBlockPipelineBody
      (multiBlockMidState b mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) :=
  MirModularWpConverges.of_noCall
    (multiBlockPipeline_stage2_noCallWpConverges b mem h_root)

/--
Fuel-free modular sequential composition (`MirModularWpConverges.bind`) of
Stage 1 (`multiBlockPipeline_stage1_converges`) and Stage 2
(`multiBlockPipeline_stage2_modularWpConverges`) under any `contract : MirCallContract`.
-/
theorem multiBlockPipeline_modularWpConverges
    (contract : MirCallContract)
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirModularWpConverges contract multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (mirNormalPost
        (fun retVal mem' =>
          retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)) :=
  MirModularWpConverges.bind
    (multiBlockPipeline_stage1_converges b mem h_root)
    (fun _ h_eq =>
      h_eq ▸ multiBlockPipeline_stage2_modularWpConverges contract b mem h_root)

/-- Default call contract for concrete modular verification witnesses. -/
def dummyContract : MirCallContract where
  pre _ := True
  post _ _ := True

/-- `ModularClaim` for `multiBlockPipelineBody` under `dummyContract`. -/
def multiBlockPipelineModularClaim : ModularClaim :=
  { body := multiBlockPipelineBody
    envAssumed := dummyContract.holdsOn
    pre := multiBlockPipelineEquivClaim.pre
    post := multiBlockPipelineEquivClaim.post }

/-- Non-vacuity witness for `multiBlockPipelineModularClaim.pre`. -/
theorem multiBlockPipelineModularClaim_nonVacuous :
    ∃ args mem, multiBlockPipelineModularClaim.pre args mem :=
  multiBlockPipelineStatefulClaim_nonVacuous

/--
Fuel-free discharge of `ModularVerificationResult` for `multiBlockPipelineBody`
under any `contract : MirCallContract` using `verifyModularContractMir_of_wpConverges`
and `MirModularWpConverges.bind`.
-/
theorem verify_multiBlockPipelineModularClaim_any
    (contract : MirCallContract) :
    ModularVerificationResult
      { body := multiBlockPipelineBody
        envAssumed := contract.holdsOn
        pre := multiBlockPipelineEquivClaim.pre
        post := multiBlockPipelineEquivClaim.post } := by
  refine verifyModularContractMir_of_wpConverges
    contract multiBlockPipelineBody
    multiBlockPipelineEquivClaim.pre multiBlockPipelineEquivClaim.post
    (fun args mem h_pre => ?_)
  rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
  refine MirModularWpConverges.mono ?_
    (multiBlockPipeline_modularWpConverges contract b mem h_root)
  intro out ho
  cases out with
  | normal rv =>
    rcases rv with ⟨retVal, mem'⟩
    rcases ho with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | panic => exact False.elim ho
  | abort => exact False.elim ho

/--
Fuel-free discharge of `ModularVerificationResult multiBlockPipelineModularClaim`
using `verifyModularContractMir_of_wpConverges` and `MirModularWpConverges.bind`.
-/
theorem verify_multiBlockPipelineModularClaim :
    ModularVerificationResult multiBlockPipelineModularClaim :=
  verify_multiBlockPipelineModularClaim_any dummyContract

/--
Stage 1 (`bb0 -> bb1`) trace-accumulating convergence (`MirTraceStepsConverges`)
for `multiBlockPipelineBody`, reaching `multiBlockMidState b mem` with empty
emitted trace `tr = []`.
-/
theorem multiBlockPipeline_stage1_traceStepsConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirTraceStepsConverges multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (fun s' tr => s' = multiBlockMidState b mem ∧ tr = [])
      (fun tr out =>
        tr = [] ∧
        mirNormalPost
          (fun retVal mem' =>
            retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)
          out) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨3, rfl, rfl⟩

/--
Stage 2 (`bb1 -> bb2 -> return`) trace-aware convergence (`MirTraceWpConverges`)
for `multiBlockPipelineBody` from `multiBlockMidState b mem`, halting with empty
emitted trace `tr = []`.
-/
theorem multiBlockPipeline_stage2_traceWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirTraceWpConverges multiBlockPipelineBody
      (multiBlockMidState b mem)
      (fun tr out =>
        tr = [] ∧
        mirNormalPost
          (fun retVal mem' =>
            retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)
          out) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨3, rfl, rfl, rfl⟩

/--
Fuel-free trace-aware sequential composition (`MirTraceWpConverges.bind_silent`)
of Stage 1 (`multiBlockPipeline_stage1_traceStepsConverges`) and Stage 2
(`multiBlockPipeline_stage2_traceWpConverges`).
-/
theorem multiBlockPipeline_traceWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirTraceWpConverges multiBlockPipelineBody
      (initMachineStateWithMemory multiBlockPipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (fun tr out =>
        tr = [] ∧
        mirNormalPost
          (fun retVal mem' =>
            retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)
          out) :=
  MirTraceWpConverges.bind_silent
    (multiBlockPipeline_stage1_traceStepsConverges b mem h_root)
    (fun _ h_eq => h_eq ▸ multiBlockPipeline_stage2_traceWpConverges b mem h_root)

/--
Trace-aware `TraceClaim` for `multiBlockPipelineBody` certifying that every
execution under `WellTypedScalarArg1 4 args ∧ RootActiveMemory mem` emits an
empty event trace (`tr = []`) and halts normally with `args = [retVal]` and
`mem' = mem`.
-/
def multiBlockPipelineTraceClaim : TraceClaim where
  body := multiBlockPipelineBody
  pre args mem := WellTypedScalarArg1 4 args ∧ RootActiveMemory mem
  post args mem tr out :=
    tr = [] ∧
    mirNormalPost (fun retVal mem' => args = [retVal] ∧ mem' = mem) out

/-- Non-vacuity witness for `multiBlockPipelineTraceClaim.pre`. -/
theorem multiBlockPipelineTraceClaim_nonVacuous :
    ∃ args mem, multiBlockPipelineTraceClaim.pre args mem :=
  multiBlockPipelineStatefulClaim_nonVacuous

/--
Fuel-free discharge of `TraceVerificationResult multiBlockPipelineTraceClaim`
using `verifyTraceMir_of_wpConverges` and `MirTraceWpConverges.bind_silent`.
-/
theorem verify_multiBlockPipelineTraceClaim :
    TraceVerificationResult multiBlockPipelineTraceClaim := by
  refine verifyTraceMir_of_wpConverges multiBlockPipelineTraceClaim
    (fun args mem h_pre => ?_)
  rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
  refine MirTraceWpConverges.mono ?_
    (multiBlockPipeline_traceWpConverges b mem h_root)
  intro tr out ⟨h_tr, h_out⟩
  refine ⟨h_tr, ?_⟩
  cases out with
  | normal rv =>
    rcases rv with ⟨retVal, mem'⟩
    rcases h_out with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

/--
Concrete 3-block branching `CapturedMir` pipeline (`bb0 -> bb1 -> bb2`) whose
`bb0` terminator is a `switchInt` on `_1`, emitting a non-empty `MirObsE`
branch observation event `⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩` in
Stage 1 before moving `_1` into `_0` in `bb1` and returning in `bb2`.
-/
def branchingTracePipelineBody : CapturedMir :=
  { defPath := "Anneal::MirFuelFree::branchingTracePipeline"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 1
    localDecls :=
      [ { mutability := .mut, ty := u32Ty, debugName := some "_0" }
      , { mutability := .not, ty := u32Ty, debugName := some "x" } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            { kind :=
                .switchInt
                  (.copy { local_ := 1, projection := [] })
                  { branches := [], otherwise := 1 }
              span := "MirFuelFree.lean:branch:bb0:0" }
          isCleanup := false }
      , { statements :=
            [ { kind :=
                  .assign
                    { local_ := 0, projection := [] }
                    (.use (.move { local_ := 1, projection := [] }))
                span := "MirFuelFree.lean:branch:bb1:0" } ]
          terminator := { kind := .goto 2, span := "MirFuelFree.lean:branch:bb1:1" }
          isCleanup := false }
      , { statements := []
          terminator := { kind := .return_, span := "MirFuelFree.lean:branch:bb2:0" }
          isCleanup := false } ]
    fnAbi :=
      { args := [{ layout := u32Layout, mode := .direct }]
        ret := { layout := u32Layout, mode := .direct }
        conv := .rust
        canUnwind := true }
    layouts :=
      { pointerBits := 64
        isLittleEndian := true
        entries := [u32Layout] }
    allocations := [] }

/-- Intermediate `MachineState` at `bb1` for `branchingTracePipelineBody`. -/
def branchingTraceMidState (b : Nat) (mem : Memory) : MachineState :=
  { frame :=
      { blockIdx := 1
        stmtIdx := 0
        locals :=
          [ .uninit
          , .init (.scalar { bits := b, sizeBytes := 4 }) ] }
    memory := mem }

/--
Stage 1 (`bb0 -> bb1`) of `branchingTracePipelineBody`: executes `.switchInt`
on `_1`, reaching `branchingTraceMidState b mem` while emitting the non-empty
trace `[⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩]`.
-/
theorem branchingTracePipeline_stage1_traceStepsConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirTraceStepsConverges branchingTracePipelineBody
      (initMachineStateWithMemory branchingTracePipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (fun s' tr =>
        s' = branchingTraceMidState b mem ∧
        tr = [⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩])
      (fun tr out =>
        tr = [⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩] ∧
        mirNormalPost
          (fun retVal mem' =>
            retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)
          out) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨1, rfl, rfl⟩

/--
Stage 2 (`bb1 -> bb2 -> return`) of `branchingTracePipelineBody` from
`branchingTraceMidState b mem`.
-/
theorem branchingTracePipeline_stage2_traceWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirTraceWpConverges branchingTracePipelineBody
      (branchingTraceMidState b mem)
      (fun tr₂ out =>
        tr₂ = [] ∧
        mirNormalPost
          (fun retVal mem' =>
            retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)
          out) := by
  rcases mem with
    ⟨nextAllocId, globals, borrows, nextTag, callees, callStack,
     activeCallee, activeProtectors, nextProtector, callerLocals⟩
  rcases h_root with ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨3, rfl, rfl, rfl⟩

/--
Fuel-free non-empty trace composition (`MirTraceWpConverges.bind`) chaining
Stage 1 (`tr₁ = [⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩]`) with Stage 2
(`tr₂ = []`) into `tr = [⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩]`.
-/
theorem branchingTracePipeline_traceWpConverges
    (b : Nat) (mem : Memory) (h_root : RootActiveMemory mem) :
    MirTraceWpConverges branchingTracePipelineBody
      (initMachineStateWithMemory branchingTracePipelineBody
        [.scalar { bits := b, sizeBytes := 4 }] mem)
      (fun tr out =>
        tr = [⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩] ∧
        mirNormalPost
          (fun retVal mem' =>
            retVal = .scalar { bits := b, sizeBytes := 4 } ∧ mem' = mem)
          out) := by
  refine MirTraceWpConverges.bind
    (branchingTracePipeline_stage1_traceStepsConverges b mem h_root)
    (fun s' tr₁ ⟨h_s', h_tr₁⟩ => ?_)
  subst h_s' h_tr₁
  refine MirTraceWpConverges.mono ?_
    (branchingTracePipeline_stage2_traceWpConverges b mem h_root)
  intro tr₂ out ⟨h_tr₂, h_out⟩
  subst h_tr₂
  exact ⟨rfl, h_out⟩

/--
Non-empty event-emitting `TraceClaim` for `branchingTracePipelineBody`.
-/
def branchingTracePipelineTraceClaim : TraceClaim where
  body := branchingTracePipelineBody
  pre args mem := WellTypedScalarArg1 4 args ∧ RootActiveMemory mem
  post args mem tr out :=
    (∃ b : Nat,
      args = [.scalar { bits := b, sizeBytes := 4 }] ∧
      tr = [⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩]) ∧
    mirNormalPost (fun retVal mem' => args = [retVal] ∧ mem' = mem) out

/-- Non-vacuity witness for `branchingTracePipelineTraceClaim.pre`. -/
theorem branchingTracePipelineTraceClaim_nonVacuous :
    ∃ args mem, branchingTracePipelineTraceClaim.pre args mem :=
  multiBlockPipelineStatefulClaim_nonVacuous

/--
Fuel-free discharge of `TraceVerificationResult branchingTracePipelineTraceClaim`
via `verifyTraceMir_of_wpConverges` and `MirTraceWpConverges.bind`.
-/
theorem verify_branchingTracePipelineTraceClaim :
    TraceVerificationResult branchingTracePipelineTraceClaim := by
  refine verifyTraceMir_of_wpConverges branchingTracePipelineTraceClaim
    (fun args mem h_pre => ?_)
  rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
  refine MirTraceWpConverges.mono ?_
    (branchingTracePipeline_traceWpConverges b mem h_root)
  intro tr out ⟨h_tr, h_out⟩
  refine ⟨⟨b, rfl, h_tr⟩, ?_⟩
  cases out with
  | normal rv =>
    rcases rv with ⟨retVal, mem'⟩
    rcases h_out with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

end ConcreteWitnesses

end Anneal.MirFuelFree


section MovedPureMirExecPrefix
set_option maxRecDepth 2048

namespace Anneal.PureMirExec

open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval

/-!
# Tier 1 Pure MIR Execution & Alias Erasure (`Anneal.PureMirExec`)

This module implements Tier 1 local-value / alias erasure for pure Rust MIR
functions (`FF-2.1`), modeled on `Py/PureExec.lean`:

1. **Alias-Erased State (`PureState`) & `SlotState`**:
   Erases the 10-field `Memory` record (`nextAllocId`, `globals`, `borrows`,
   `nextTag`, `callees`, `callStack`, `activeCallee`, `activeProtectors`,
   `nextProtector`, `callerLocals`), retaining only the active basic-block
   index `bb : BasicBlockIdx`, statement index `stmtIdx : Nat`, and local value
   environment `env : List SlotState` where every initialized slot holds a pure
   `Value` (`SlotState.val v`).
2. **Frame Simulation (`MirFrameSim`)**:
   Relates `ps : PureState` to `ms : MachineState` at an arbitrary initial
   memory `mem₀ : Memory`, asserting exact agreement on `bb`, `stmtIdx`, and
   `env` together with `ms.memory = mem₀` (all 10 fields of `Memory`
   definitionally equal to `mem₀`, including when `mem₀.callees` is populated
   by `initMachineStateWithCallees` or `initMachineStateWithMemoryAndCallees`).
3. **Computable Syntactic Purity Checker (`checkPureMir : CapturedMir → Bool`)**:
   Verifies in $O(|\text{MIR}|)$ time (discharged by `decide` or `rfl`) that no
   statement, rvalue, operand, or terminator in `body` creates a local address
   (`Rvalue.ref`, `Rvalue.rawPtr`), dereferences a pointer
   (`ProjectionElem.deref`), reads indirect global memory, or mutates heap/borrow
   state, while permitting arbitrary value projections (`.field`, `.downcast`,
   `.index`, `.constantIndex`, `.subslice`), local statements
   (`storageLive`, `storageDead`, `assign`, `setDiscriminant`, `nop`, `deinit`,
   `placeMention`), and control-flow terminators (`return_`, `goto`,
   `switchInt`, `assert`, `drop`, `unreachable`).
4. **Once-and-for-All Alias-Erasure Soundness (`mirWpConverges_of_pureExec`)**:
   Proves that whenever `checkPureMir body = true` and
   `PureMirConverges body (initPureState body args) post`, the full stateful
   interaction tree converges (`MirWpConverges`) from
   `initMachineStateWithMemory body args mem₀` to
   `mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)` without ever
   destructuring the 10-field `Memory` record in user proofs.
-/

/-! ## 1. Alias-Erased State (`SlotState`, `PureState`) & Simulation (`MirFrameSim`) -/

/--
Alias-erased local slot state in `PureState` (`LocalSlot`: `.uninit`, `.init v`,
`.dead`), where every initialized slot holds a pure `Value` directly (never a
heap or borrow allocation address).
-/
abbrev SlotState : Type := LocalSlot

/-- Initialized value slot constructor (`LocalSlot.init`). -/
abbrev SlotState.val : Value → SlotState := LocalSlot.init

/-- Uninitialized slot constructor (`LocalSlot.uninit`). -/
abbrev SlotState.uninit : SlotState := LocalSlot.uninit

/-- Dead storage slot constructor (`LocalSlot.dead`). -/
abbrev SlotState.dead : SlotState := LocalSlot.dead

/-- Basic-block index accessor on `MachineState` (`ms.frame.blockIdx`). -/
abbrev _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MachineState.bb
    (ms : MachineState) : BasicBlockIdx :=
  ms.frame.blockIdx

/-- Statement index accessor on `MachineState` (`ms.frame.stmtIdx`). -/
abbrev _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MachineState.stmtIdx
    (ms : MachineState) : Nat :=
  ms.frame.stmtIdx

/-- Local slot environment accessor on `MachineState` (`ms.frame.locals`). -/
abbrev _root_.Trusted.Rustc.V2026_06_01.MirSemantics.MachineState.locals
    (ms : MachineState) : List LocalSlot :=
  ms.frame.locals

/--
Alias-erased execution state for Tier 1 pure MIR functions (`PureState`),
containing only the active basic-block index `bb`, statement index `stmtIdx`,
and local slot environment `env`.
-/
structure PureState : Type where
  /-- Active basic block index (`0` at function entry). -/
  bb : BasicBlockIdx
  /-- Active statement index within `bb` (`0` at basic block entry). -/
  stmtIdx : Nat := 0
  /-- Local slot environment (`_0` return slot followed by arguments and locals). -/
  env : List SlotState

/--
Default empty `Memory` state used as the canonical erased reference memory for
`PureState` evaluation (`emptyMemory`).
-/
abbrev dummyMem : Memory := emptyMemory

/--
Initialize `PureState` for `body` with argument values `args` at basic block `0`
and statement `0`.
-/
def initPureState (body : CapturedMir) (args : List Value) : PureState :=
  { bb := 0, stmtIdx := 0, env := initLocals body args }

/--
Embed `ps : PureState` into a full `MachineState` with memory `mem` (defaulting
to `emptyMemory`).
-/
def PureState.toMachineState
    (ps : PureState) (mem : Memory := emptyMemory) : MachineState :=
  { frame := { blockIdx := ps.bb, stmtIdx := ps.stmtIdx, locals := ps.env }
    memory := mem }

/--
Project the stack frame of `ms : MachineState` to `PureState`, erasing
`ms.memory`.
-/
def PureState.ofMachineState (ms : MachineState) : PureState :=
  { bb := ms.frame.blockIdx, stmtIdx := ms.frame.stmtIdx, env := ms.frame.locals }

@[simp]
theorem PureState.ofMachineState_toMachineState
    (ps : PureState) (mem : Memory) :
    PureState.ofMachineState (ps.toMachineState mem) = ps :=
  rfl

@[simp]
theorem PureState.toMachineState_ofMachineState
    (ms : MachineState) (mem : Memory) :
    (PureState.ofMachineState ms).toMachineState mem =
      { ms with memory := mem } :=
  rfl

@[simp]
theorem initPureState_toMachineState
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    (initPureState body args).toMachineState mem =
      initMachineStateWithMemory body args mem :=
  rfl

@[simp]
theorem initPureState_toMachineState_init
    (body : CapturedMir) (args : List Value) :
    (initPureState body args).toMachineState
        (initMachineState body args).memory =
      initMachineState body args :=
  rfl

@[simp]
theorem initPureState_toMachineState_withCallees
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    (initPureState body args).toMachineState
        (initMachineStateWithCallees body args callees).memory =
      initMachineStateWithCallees body args callees := by
  cases callees <;> rfl

@[simp]
theorem initPureState_toMachineState_withMemoryAndCallees
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) :
    (initPureState body args).toMachineState
        (MirFuelFree.Memory.withDefaultCallees mem callees) =
      MirFuelFree.initMachineStateWithMemoryAndCallees body args mem callees :=
  rfl

/--
Frame simulation relation between alias-erased `ps : PureState` and full
`ms : MachineState` at initial memory `mem₀ : Memory`.

Asserts `ms.bb = ps.bb`, `ms.stmtIdx = ps.stmtIdx`, exact slot-by-slot local
environment correspondence (`ms.locals = ps.env`), and `ms.memory = mem₀` (all
10 fields of `Memory` definitionally equal to `mem₀`, including when
`mem₀.callees` is populated by `initMachineStateWithCallees` or
`initMachineStateWithMemoryAndCallees`).
-/
def MirFrameSim
    (_body : CapturedMir)
    (mem₀ : Memory)
    (ps : PureState)
    (ms : MachineState) : Prop :=
  ms.frame.blockIdx = ps.bb ∧
  ms.frame.stmtIdx = ps.stmtIdx ∧
  ms.frame.locals = ps.env ∧
  ms.memory = mem₀

/--
`MirFrameSim body mem₀ ps ms` holds if and only if `ms` is definitionally
`ps.toMachineState mem₀`.
-/
theorem mirFrameSim_iff_eq_toMachineState
    (body : CapturedMir) (mem₀ : Memory) (ps : PureState) (ms : MachineState) :
    MirFrameSim body mem₀ ps ms ↔ ms = ps.toMachineState mem₀ := by
  rcases ms with ⟨⟨bb, stmtIdx, locals⟩, memory⟩
  rcases ps with ⟨pbb, pstmtIdx, penv⟩
  simp [MirFrameSim, PureState.toMachineState, and_assoc]

@[simp]
theorem mirFrameSim_toMachineState
    (body : CapturedMir) (mem₀ : Memory) (ps : PureState) :
    MirFrameSim body mem₀ ps (ps.toMachineState mem₀) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineStateWithMemory body args mem₀` for arbitrary `mem₀ : Memory`.
-/
@[simp]
theorem mirFrameSim_initMachineStateWithMemory
    (body : CapturedMir) (args : List Value) (mem₀ : Memory) :
    MirFrameSim body mem₀
      (initPureState body args)
      (initMachineStateWithMemory body args mem₀) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineState body args`.
-/
@[simp]
theorem mirFrameSim_initMachineState
    (body : CapturedMir) (args : List Value) :
    MirFrameSim body (initMachineState body args).memory
      (initPureState body args)
      (initMachineState body args) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineStateWithCallees body args callees`.
-/
@[simp]
theorem mirFrameSim_initMachineStateWithCallees
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    MirFrameSim body (initMachineStateWithCallees body args callees).memory
      (initPureState body args)
      (initMachineStateWithCallees body args callees) := by
  cases callees <;> exact ⟨rfl, rfl, rfl, rfl⟩

/--
Initial frame simulation between `initPureState body args` and
`initMachineStateWithMemoryAndCallees body args mem₀ callees`, preserving
`Memory.withDefaultCallees mem₀ callees`.
-/
@[simp]
theorem mirFrameSim_initMachineStateWithMemoryAndCallees
    (body : CapturedMir) (args : List Value) (mem₀ : Memory)
    (callees : List CapturedMir) :
    MirFrameSim body (MirFuelFree.Memory.withDefaultCallees mem₀ callees)
      (initPureState body args)
      (MirFuelFree.initMachineStateWithMemoryAndCallees body args mem₀ callees) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Extract `ms.memory = mem₀` from `MirFrameSim`. -/
theorem MirFrameSim.memory_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.memory = mem₀ :=
  h.2.2.2

/-- Extract `ms.bb = ps.bb` from `MirFrameSim`. -/
theorem MirFrameSim.bb_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.bb = ps.bb :=
  h.1

/-- Extract `ms.stmtIdx = ps.stmtIdx` from `MirFrameSim`. -/
theorem MirFrameSim.stmtIdx_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.stmtIdx = ps.stmtIdx :=
  h.2.1

/-- Extract `ms.locals = ps.env` from `MirFrameSim`. -/
theorem MirFrameSim.locals_eq
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    ms.locals = ps.env :=
  h.2.2.1

/-! ## 2. Computable Syntactic Purity Checker (`checkPureMir`) -/

/--
Syntactic purity check on a `ConstValue`: accepts inline constants that do not
inspect global memory allocations (`mem.globals`), while rejecting `.indirect`
and pointer-backed `.slice` constants.
-/
def isPureConstValue : ConstValue → Bool
  | .zeroSized => true
  | .scalar _ => true
  | .slice (.int _) _ => true
  | .slice (.ptr _ _) _ => false
  | .indirect _ _ => false
  | .unevaluated _ => true

/--
Syntactic purity check on a `ProjectionElem`: allows arbitrary value projections
(`.field`, `.downcast`, `.index`, `.constantIndex`, `.subslice`) while rejecting
pointer dereferences (`.deref`) and the type-changing projections
`.unwrapUnsafeBinder` and `.opaqueCast`.

`.opaqueCast` is outside the pure fragment because a place that starts with an
opaque cast is dispatched on the projections below the cast chain
(`DIV-TR-OPAQUECAST-ROOT-DISPATCH`: `Trusted`'s `stripLeadingOpaqueCast` makes
`(_l as T)` a whole-local place), which the projected-place equations of this
fragment do not describe. `Runtime` MIR, the phase this library lifts, never
contains the projection (`rustc_middle::mir::RuntimePhase::Initial` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: "beginning with this phase, the
following variants are disallowed: ... [`PlaceElem::OpaqueCast`]").
-/
def isPureProjElem : ProjectionElem → Bool
  | .deref => false
  | .field _ _ => true
  | .index _ => true
  | .constantIndex .. => true
  | .subslice .. => true
  | .downcast _ _ => true
  | .opaqueCast _ => false
  | .unwrapUnsafeBinder _ => false

/-- Syntactic purity check on a `Place`: every projection element is pure. -/
def isPurePlace (p : Place) : Bool :=
  p.projection.all isPureProjElem

/--
Syntactic purity check on an `Operand`: `.copy` and `.move` access pure places,
and `.constant` carries a pure `ConstValue`.
-/
def isPureOperand : Operand → Bool
  | .copy p => isPurePlace p
  | .move p => isPurePlace p
  | .constant c => isPureConstValue c.val

/--
Syntactic purity check on a `BinOp`: every operator except `BinOp.offset`,
whose pointer case (`evalPtrOffsetBinOp`) reads `mem.borrows` to bound the
offset.
-/
def isPureBinOp : BinOp → Bool
  | .offset => false
  | _ => true

/--
Syntactic purity check on an `Rvalue`: allows value operations on pure places
and operands while rejecting address/borrow creation (`.ref`, `.rawPtr`,
`.threadLocalRef`, `.shallowInitBox`).
-/
def isPureRvalue : Rvalue → Bool
  | .use op => isPureOperand op
  | .repeat op _ => isPureOperand op
  | .ref .. => false
  | .rawPtr .. => false
  | .threadLocalRef _ => false
  | .len p => isPurePlace p
  | .cast ck op _ => match ck with
    | .pointerCoercion _ => false
    | .fnPtrToPtr => false
    -- `ptrToPtr` reads `mem.borrows` and may push a fresh element borrow
    -- (`deriveStackElemThinPtr`), so it is not memory-independent.
    | .ptrToPtr => false
    | .pointerExposeProvenance => false
    | .pointerWithExposedProvenance => false
    | _ => isPureOperand op
  | .binaryOp op lhs rhs => isPureBinOp op && (isPureOperand lhs && isPureOperand rhs)
  | .nullaryOp _ _ => true
  | .unaryOp _ op => isPureOperand op
  | .discriminant p => isPurePlace p
  | .aggregate _ ops => ops.all isPureOperand
  | .shallowInitBox _ _ => false
  | .copyForDeref _p => false
  | .wrapUnsafeBinder op _ => isPureOperand op

/--
Syntactic purity check on a `StatementKind`: allows `.assign`,
`.setDiscriminant`, `.storageLive`, `.storageDead`, `.nop`, `.coverage`,
`.constEvalCounter`, `.placeMention`, `.deinit`, and `.intrinsic (.assume op)`
when all referenced places/operands are pure.
-/
def isPureStatement : StatementKind → Bool
  | .assign p r => isPurePlace p && isPureRvalue r
  | .setDiscriminant p _ => isPurePlace p
  | .storageLive _ => true
  | .storageDead _ => true
  | .nop => true
  | .coverage => true
  | .constEvalCounter => true
  | .placeMention p => isPurePlace p
  | .deinit p => isPurePlace p
  | .intrinsic (.assume op) => isPureOperand op
  | _ => false

/--
Syntactic purity check on a `TerminatorKind`: allows `.goto`, `.switchInt`,
`.return_`, `.assert`, `.drop`, and `.unreachable` when all referenced
places/operands are pure.
-/
def isPureTerminator : TerminatorKind → Bool
  | .goto _ => true
  | .switchInt discr _ => isPureOperand discr
  | .return_ => true
  | .assert cond _ _ _ => isPureOperand cond
  | .drop p _ _ => isPurePlace p
  | .unreachable => true
  | .unwindResume => true
  | .unwindTerminate => true
  | .inlineAsm .. => false
  | _ => false

/--
Strengthened syntactic purity check on an `Rvalue` in the presence of active
borrows (`mem.borrows ≠ []`): in addition to `isPureRvalue rv`, rejects
relational `BinOp`s whose LHS operand is pointer-typed or untyped in
`localDecls`, because pointer relational comparisons consult `mem.borrows` via
`ptrAddressScalar?`.
-/
def isBorrowFreePureRvalue
    (localDecls : List LocalDecl) (layouts : LayoutTable) (rv : Rvalue) : Bool :=
  isPureRvalue rv &&
  match rv with
  | .binaryOp op lhs _ =>
    Bool.not (Bool.and (isRelationalBinOp op) (isPtrOrUntypedOperand localDecls layouts lhs))
  | _ => true

/--
Strengthened syntactic purity check on a `StatementKind` in the presence of
active borrows (`mem.borrows ≠ []`).
-/
def isBorrowFreePureStatement
    (localDecls : List LocalDecl) (layouts : LayoutTable) : StatementKind → Bool
  | .assign p r => isPurePlace p && isBorrowFreePureRvalue localDecls layouts r
  | sk => isPureStatement sk

theorem isPureRvalue_of_isBorrowFreePureRvalue
    {localDecls : List LocalDecl} {layouts : LayoutTable} {rv : Rvalue}
    (h : isBorrowFreePureRvalue localDecls layouts rv = true) :
    isPureRvalue rv = true :=
  (Bool.and_eq_true_iff.mp h).1

theorem isPureStatement_of_isBorrowFreePureStatement
    {localDecls : List LocalDecl} {layouts : LayoutTable} {sk : StatementKind}
    (h : isBorrowFreePureStatement localDecls layouts sk = true) :
    isPureStatement sk = true := by
  cases sk with
  | assign p r =>
    simp only [isBorrowFreePureStatement, isPureStatement, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, isPureRvalue_of_isBorrowFreePureRvalue h.2⟩
  | _ => exact h

/--
Computable $O(|\text{MIR}|)$ syntactic purity checker on a `CapturedMir` body,
discharged by `decide` or `rfl`.
-/
def checkPureMir (body : CapturedMir) : Bool :=
  body.basicBlocks.all (fun block =>
    block.statements.all (fun stmt =>
      isBorrowFreePureStatement body.localDecls body.layouts stmt.kind) &&
    isPureTerminator block.terminator.kind)

/-! ## 3. Pure Memory-Independence & Step Simulation Lemmas -/

/-- Look up an element of `xs` via `Trusted.Sequence.get?` preserves `List.all`. -/
theorem list_all_of_get?
    {α : Type} {p : α → Bool} {xs : List α} {idx : Nat} {x : α}
    (h_all : xs.all p = true)
    (h_get : get? xs idx = some x) :
    p x = true := by
  induction xs generalizing idx with
  | nil => cases h_get
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h_all
    cases idx with
    | zero =>
      cases h_get
      exact h_all.1
    | succ idx' =>
      exact ih h_all.2 h_get

theorem list_all_mono {α : Type} {p q : α → Bool} {xs : List α}
    (h_imp : ∀ x, p x = true → q x = true)
    (h : xs.all p = true) :
    xs.all q = true := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨h_imp hd h.1, ih h.2⟩

/--
If `checkPureMir body = true`, every basic block in `body.basicBlocks` has pure
statements and a pure terminator.
-/
theorem checkPureMir_block
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    (h_pure : checkPureMir body = true)
    (h_bb : get? body.basicBlocks bbIdx = some bb) :
    bb.statements.all (fun stmt => isPureStatement stmt.kind) = true ∧
    isPureTerminator bb.terminator.kind = true := by
  have h_raw :
      (bb.statements.all (fun stmt =>
        isBorrowFreePureStatement body.localDecls body.layouts stmt.kind) &&
       isPureTerminator bb.terminator.kind) = true :=
    list_all_of_get? (xs := body.basicBlocks) (idx := (bbIdx : Nat)) h_pure h_bb
  have h := Bool.and_eq_true_iff.mp h_raw
  exact ⟨list_all_mono (fun _ hs => isPureStatement_of_isBorrowFreePureStatement hs) h.1, h.2⟩

/--
Evaluating a pure `Operand` is completely independent of `borrows`, `globals`,
`callerLocals`, and the suspended-frame `callStack` (a pure operand never
dereferences a pointer, so it never resolves a frame-qualified borrow target).
-/
theorem evalOperand_pure_eq
    (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    {localDecls : List LocalDecl} {callStack : List SavedCallerFrame}
    (h_pure : isPureOperand op = true) :
    evalOperand locals op borrows globals layouts callerLocals localDecls callStack =
      evalOperand locals op [] [] layouts [] localDecls := by
  cases op with
  | constant c =>
    rcases c with ⟨ty, val⟩
    cases val with
    | zeroSized => rfl
    | scalar sc => cases sc <;> rfl
    | slice sc lenMeta =>
      cases sc with
      | int _ => rfl
      | ptr _ _ => cases h_pure
    | indirect _ _ => cases h_pure
    | unevaluated _ => rfl
  | copy p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd tl =>
      simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
      cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
  | move p =>
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil => rfl
    | cons hd tl =>
      simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
      cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)

/--
A pure operand never moves out of a place that starts with an opaque cast, so
terminator operand evaluation (`evalOperandWithBodyCast`,
`DIV-TR-OPAQUECAST-ROOT-DISPATCH`) is the declaration-erased `evalOperand`.
-/
theorem operandIsLeadingOpaqueCastMove_eq_false_of_isPureOperand
    {op : Operand} (h : isPureOperand op = true) :
    operandIsLeadingOpaqueCastMove op = false := by
  cases op with
  | constant c => rfl
  | copy p => rfl
  | move p =>
    rcases p with ⟨loc, _ | ⟨hd, tl⟩⟩
    · rfl
    · cases hd with
      | opaqueCast castTy => exact False.elim (Bool.false_ne_true h)
      | _ => rfl

/--
Terminator operand evaluation of a pure operand (`evalOperandWithBodyCast`) is
independent of the memory-derived arguments and of the active body's
declarations.
-/
theorem evalOperandWithBodyCast_pure_eq
    (locals : List LocalSlot) (op : Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl) (callStack : List SavedCallerFrame)
    (h_pure : isPureOperand op = true) :
    evalOperandWithBodyCast locals op borrows globals layouts callerLocals
        bodyLocalDecls callStack =
      evalOperand locals op [] [] layouts [] := by
  rw [evalOperandWithBodyCast_eq_evalOperand _ _ _ _ _ _ _ _
    (operandIsLeadingOpaqueCastMove_eq_false_of_isPureOperand h_pure)]
  exact evalOperand_pure_eq locals op borrows globals layouts callerLocals h_pure

/--
Evaluating a list of pure `Operand`s is completely independent of `borrows`,
`globals`, `callerLocals`, and the suspended-frame `callStack`.
-/
theorem evalOperands_pure_eq
    (locals : List LocalSlot) (ops : List Operand)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    {localDecls : List LocalDecl} {callStack : List SavedCallerFrame}
    (h_pure : ops.all isPureOperand = true) :
    evalOperands locals ops borrows globals layouts callerLocals localDecls callStack =
      evalOperands locals ops [] [] layouts [] localDecls := by
  induction ops generalizing locals with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h_pure
    unfold evalOperands
    rw [evalOperand_pure_eq locals op borrows globals layouts callerLocals
      (callStack := callStack) h_pure.1]
    cases evalOperand locals op [] [] layouts [] localDecls with
    | ub => rfl
    | unsupported => rfl
    | ok v locals₁ =>
      dsimp only
      rw [ih locals₁ h_pure.2]

/--
Writing to a pure `Place` via `writePlaceValue` is completely independent of
`borrows` and of the suspended-frame `callStack`.
-/
theorem writePlaceValue_pure_eq
    (locals : List LocalSlot) (borrows : List BorrowEntry)
    (dst : Place) (val : Value)
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {callStack : List SavedCallerFrame}
    (h_pure : isPurePlace dst = true) :
    writePlaceValue locals borrows dst val localDecls layouts callStack =
      writePlaceValue locals [] dst val localDecls layouts := by
  rcases dst with ⟨loc, proj⟩
  cases proj with
  | nil => rfl
  | cons hd tl =>
    simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
    cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)

theorem writeIntrinsicReturn_pure_eq
    (s : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value)
    (h_pure : isPurePlace destination = true) :
    writeIntrinsicReturn s locals' destination targetBb retVal =
      match writePlaceValue locals' [] destination retVal with
      | .ok updatedLocals =>
        MirStepNode.step {
          frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
          memory := invalidateDirectDestWriteBorrows s.memory locals' destination
        }
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  have h_w :
      writePlaceValue locals' s.memory.borrows destination retVal (callStack := s.memory.callStack) =
        writePlaceValue locals' [] destination retVal := by
    have h_cs :
        writePlaceValue locals' s.memory.borrows destination retVal (callStack := s.memory.callStack) =
          writePlaceValue locals' s.memory.borrows destination retVal := by
      rcases destination with ⟨loc, _ | ⟨hd, tl⟩⟩
      · rfl
      · simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
        cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
    exact h_cs.trans (writePlaceValue_pure_eq locals' s.memory.borrows destination retVal h_pure)
  rcases destination with ⟨loc, _ | ⟨hd, tl⟩⟩
  · unfold writeIntrinsicReturn; dsimp only; rw [h_w]; rfl
  · simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
    cases hd <;>
      first
      | exact False.elim (Bool.false_ne_true h_pure.1)
      | (unfold writeIntrinsicReturn; dsimp only; rw [h_w]; rfl)

theorem resumeExternalCall_pure_returned_eq
    (s : MachineState) (localsAfterArgs : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (retVal : Value) (retMem : Memory)
    (h_pure : isPurePlace destination = true)
    (h_ap : retMem.activeProtectors = []) :
    resumeExternalCall s localsAfterArgs destination targetBb unwind (.returned retVal retMem) =
      match writePlaceValue localsAfterArgs [] destination retVal with
      | .ok updatedLocals =>
        .running {
          frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
          memory :=
            invalidateDirectDestWriteBorrows
              { retMem with rootUnwindCeiling := s.memory.rootUnwindCeiling }
              localsAfterArgs destination
        }
      | .ub => .faulted .ub
      | .unsupported => .faulted .unsupported := by
  have h_w :
      writePlaceValue localsAfterArgs retMem.borrows destination retVal [] emptyLayoutTable retMem.callStack =
        writePlaceValue localsAfterArgs [] destination retVal := by
    have h_cs :
        writePlaceValue localsAfterArgs retMem.borrows destination retVal [] emptyLayoutTable retMem.callStack =
          writePlaceValue localsAfterArgs retMem.borrows destination retVal := by
      rcases destination with ⟨loc, _ | ⟨hd, tl⟩⟩
      · rfl
      · simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
        cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
    exact h_cs.trans (writePlaceValue_pure_eq localsAfterArgs retMem.borrows destination retVal h_pure)
  have h_mem_eta :
      ({ retMem with
         borrows :=
           (invalidateDirectDestWriteBorrows
              { retMem with rootUnwindCeiling := s.memory.rootUnwindCeiling }
              localsAfterArgs destination).borrows
         rootUnwindCeiling := s.memory.rootUnwindCeiling } : Memory) =
        invalidateDirectDestWriteBorrows
          { retMem with rootUnwindCeiling := s.memory.rootUnwindCeiling }
          localsAfterArgs destination := by
    rcases retMem with ⟨nA, gl, _ | ⟨bHd, bTl⟩, nT, cal, tr, cs, ac, ap, nP, cl, fp, ex, ru⟩
    · rfl
    · unfold invalidateDirectDestWriteBorrows
      rcases destination with ⟨loc, _ | ⟨hd, tl⟩⟩
      · rfl
      · cases hd <;> rfl
  rcases destination with ⟨loc, _ | ⟨hd, tl⟩⟩
  · unfold resumeExternalCall; dsimp only; rw [h_mem_eta, h_ap]; dsimp only [evalPlaceWrite]; rw [h_w]; rfl
  · simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
    cases hd <;>
      first
      | exact False.elim (Bool.false_ne_true h_pure.1)
      | (unfold resumeExternalCall; dsimp only; rw [h_mem_eta, h_ap]; dsimp only [evalPlaceWrite]; rw [h_w]; rfl)

/-- Replace the `Memory` in an `RvalueEvalResult` with `mem`. -/
def RvalueEvalResult.withMem (mem : Memory) : RvalueEvalResult → RvalueEvalResult
  | .ok v locals' _ => .ok v locals' mem
  | .ub => .ub
  | .unsupported => .unsupported

theorem rval_withMem_ub {mem : Memory} :
    RvalueEvalResult.ub = RvalueEvalResult.withMem mem RvalueEvalResult.ub := rfl

theorem rval_withMem_unsupported {mem : Memory} :
    RvalueEvalResult.unsupported = RvalueEvalResult.withMem mem RvalueEvalResult.unsupported := rfl

theorem rval_withMem_ok {v : Value} {l : List LocalSlot} {m₀ mem : Memory} :
    RvalueEvalResult.ok v l mem = RvalueEvalResult.withMem mem (RvalueEvalResult.ok v l m₀) := rfl


@[simp]
theorem evalSignedDiv_eq_withMem
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedDiv a b sz locals mem =
      RvalueEvalResult.withMem mem (evalSignedDiv a b sz locals emptyMemory) := by
  unfold evalSignedDiv
  dsimp only
  cases Bool.and (Nat.beq (wrapScalarBits a (scalarModulus sz)) (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz)) (Nat.sub (scalarModulus sz) 1)) <;> rfl

@[simp]
theorem evalSignedRem_eq_withMem
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedRem a b sz locals mem =
      RvalueEvalResult.withMem mem (evalSignedRem a b sz locals emptyMemory) := by
  unfold evalSignedRem
  dsimp only
  cases Bool.and (Nat.beq (wrapScalarBits a (scalarModulus sz)) (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz)) (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalScalarBinOp_eq_withMem
    (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp op lhs rhs locals mem isSigned =
      RvalueEvalResult.withMem mem
        (evalScalarBinOp op lhs rhs locals emptyMemory isSigned) := by
  unfold evalScalarBinOp
  cases Nat.beq lhs.sizeBytes 0 with
  | true => rfl
  | false =>
    dsimp only
    cases op with
    | shl | shr =>
      dsimp only
      cases Nat.beq rhs.sizeBytes 0 <;> rfl
    | shlUnchecked | shrUnchecked =>
      dsimp only
      cases Nat.beq rhs.sizeBytes 0 with
      | true => rfl
      | false =>
        dsimp only
        cases Nat.ble (Nat.mul lhs.sizeBytes 8) rhs.bits <;> rfl
    | add | addWithOverflow | mul | mulWithOverflow
    | bitAnd | bitOr | bitXor | eq | ne | lt | le | gt | ge | offset =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes <;> rfl
    | addUnchecked =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.add lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowAdd lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | sub =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.ble rhs.bits lhs.bits <;> rfl
    | subUnchecked =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble rhs.bits lhs.bits with
          | false => rfl
          | true =>
            dsimp only
            cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.sub lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowSub lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | subWithOverflow =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble rhs.bits lhs.bits <;> rfl
        | true => rfl
    | mulUnchecked =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.ble (scalarModulus lhs.sizeBytes) (Nat.mul lhs.bits rhs.bits) <;> rfl
        | true =>
          dsimp only
          cases signedOverflowMul lhs.bits rhs.bits lhs.sizeBytes <;> rfl
    | div =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.beq rhs.bits 0 with
        | true => rfl
        | false =>
          dsimp only
          cases isSigned with
          | false => rfl
          | true => exact evalSignedDiv_eq_withMem ..
    | rem =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.beq rhs.bits 0 with
        | true => rfl
        | false =>
          dsimp only
          cases isSigned with
          | false => rfl
          | true => exact evalSignedRem_eq_withMem ..
    | cmp =>
      dsimp only
      cases Nat.beq lhs.sizeBytes rhs.sizeBytes with
      | false => rfl
      | true =>
        dsimp only
        cases isSigned with
        | false =>
          dsimp only
          cases Nat.beq lhs.bits rhs.bits with
          | true => rfl
          | false =>
            dsimp only
            cases Nat.ble lhs.bits rhs.bits <;> rfl
        | true =>
          dsimp only
          cases Nat.beq (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
              (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) with
          | true => rfl
          | false =>
            dsimp only
            cases signedLt (wrapScalarBits lhs.bits (scalarModulus lhs.sizeBytes))
                (wrapScalarBits rhs.bits (scalarModulus lhs.sizeBytes)) lhs.sizeBytes <;> rfl

theorem evalUnaryNot_eq_withMem
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalUnaryNot sc optTy locals mem =
      RvalueEvalResult.withMem mem
        (evalUnaryNot sc optTy locals emptyMemory) := by
  unfold evalUnaryNot
  repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)

theorem evalFloatUnaryNeg_eq_withMem
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalFloatUnaryNeg sc optTy locals mem =
      RvalueEvalResult.withMem mem
        (evalFloatUnaryNeg sc optTy locals emptyMemory) := by
  unfold evalFloatUnaryNeg
  repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)

theorem evalFloatScalarBinOp_eq_withMem
    (op : BinOp) (lhs rhs : ScalarInt) (lhsTy? rhsTy? : Option Ty)
    (locals : List LocalSlot) (mem : Memory) :
    evalFloatScalarBinOp op lhs rhs lhsTy? rhsTy? locals mem =
      RvalueEvalResult.withMem mem
        (evalFloatScalarBinOp op lhs rhs lhsTy? rhsTy? locals emptyMemory) := by
  unfold evalFloatScalarBinOp
  cases lhsTy? with
  | none => rfl
  | some lTy =>
    cases rhsTy? with
    | none => rfl
    | some rTy =>
      dsimp only
      cases ieeeFormatOfTy? lTy with
      | none => rfl
      | some fL =>
        cases ieeeFormatOfTy? rTy with
        | none => rfl
        | some fR =>
          dsimp only
          cases
            Bool.and
              (match fL, fR with
               | .binary32, .binary32 => true
               | .binary64, .binary64 => true
               | _, _ => false)
              (Bool.and (Nat.beq lhs.sizeBytes fL.byteWidth) (Nat.beq rhs.sizeBytes fL.byteWidth))
          with
          | false => rfl
          | true =>
            dsimp only
            cases evalFloatBinOp op fL lhs.bits rhs.bits <;> rfl

private def evalByteCastBody
    (op : Operand) (targetTy : Ty) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot) (mem : Memory) : RvalueEvalResult :=
  let rTargetTy := resolveTyWithLocalDecls localDecls layouts targetTy
  match tyByteSize localDecls layouts rTargetTy with
  | .none => .unsupported
  | .some dstSize =>
    match operandTy localDecls layouts op with
    | .some srcTy =>
      match resolveByteCastSrcTyAndSize localDecls layouts op srcTy with
      | .none => .unsupported
      | .some (rSrcTy, srcSize) =>
        match Nat.beq srcSize dstSize with
        | false => .unsupported
        | true =>
          let encodedOpt : Option (List AbstractByte) :=
            encodeByteCastSourceBytes layouts rSrcTy v
          match encodedOpt with
          | .none => .ub
          | .some bs =>
            match Nat.beq (length bs) dstSize with
            | false => .ub
            | true =>
              match decodeTypedValueFromBytes defaultCodecFuel layouts rTargetTy bs with
              | .some v' => .ok v' locals' mem
              | .none => .ub
    | .none =>
      match encodeUntypedValueToBytes defaultCodecFuel v with
      | .none => .unsupported
      | .some bs =>
        match Nat.beq (length bs) dstSize with
        | false => .unsupported
        | true =>
          match decodeTypedValueFromBytes defaultCodecFuel layouts rTargetTy bs with
          | .some v' => .ok v' locals' mem
          | .none => .ub

theorem evalByteCast_ub_of_load
    {locals : List LocalSlot} {op : Operand} {targetTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ub) :
    evalByteCast locals op targetTy mem localDecls layouts = .ub := by
  unfold evalByteCast; rw [h]

theorem evalByteCast_unsupported_of_load
    {locals : List LocalSlot} {op : Operand} {targetTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .unsupported) :
    evalByteCast locals op targetTy mem localDecls layouts = .unsupported := by
  unfold evalByteCast; rw [h]

theorem evalByteCast_ok_of_load
    {locals : List LocalSlot} {op : Operand} {targetTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {v : Value} {locals' : List LocalSlot}
    (h : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack = .ok v locals') :
    evalByteCast locals op targetTy mem localDecls layouts =
      evalByteCastBody op targetTy localDecls layouts v locals' mem := by
  unfold evalByteCast; rw [h]; rfl

theorem evalByteCastBody_shape
    (op : Operand) (targetTy : Ty) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot) :
    (∀ mem, evalByteCastBody op targetTy localDecls layouts v locals' mem = .ub) ∨
    (∀ mem, evalByteCastBody op targetTy localDecls layouts v locals' mem = .unsupported) ∨
    (∃ v', ∀ mem, evalByteCastBody op targetTy localDecls layouts v locals' mem =
      .ok v' locals' mem) := by
  unfold evalByteCastBody
  dsimp only
  cases tyByteSize localDecls layouts (resolveTyWithLocalDecls localDecls layouts targetTy) with
  | none => exact Or.inr (Or.inl fun _ => rfl)
  | some dstSize =>
    dsimp only
    cases operandTy localDecls layouts op with
    | some srcTy =>
      dsimp only
      cases resolveByteCastSrcTyAndSize localDecls layouts op srcTy with
      | none => exact Or.inr (Or.inl fun _ => rfl)
      | some p =>
        rcases p with ⟨rSrcTy, srcSize⟩
        dsimp only
        cases Nat.beq srcSize dstSize with
        | false => exact Or.inr (Or.inl fun _ => rfl)
        | true =>
          dsimp only
          cases encodeByteCastSourceBytes layouts rSrcTy v with
          | none => exact Or.inl fun _ => rfl
          | some bs =>
            dsimp only
            cases Nat.beq (length bs) dstSize with
            | false => exact Or.inl fun _ => rfl
            | true =>
              dsimp only
              cases decodeTypedValueFromBytes defaultCodecFuel layouts
                  (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
              | some v' => exact Or.inr (Or.inr ⟨v', fun _ => rfl⟩)
              | none => exact Or.inl fun _ => rfl
    | none =>
      dsimp only
      cases encodeUntypedValueToBytes defaultCodecFuel v with
      | none => exact Or.inr (Or.inl fun _ => rfl)
      | some bs =>
        dsimp only
        cases Nat.beq (length bs) dstSize with
        | false => exact Or.inr (Or.inl fun _ => rfl)
        | true =>
          dsimp only
          cases decodeTypedValueFromBytes defaultCodecFuel layouts
              (resolveTyWithLocalDecls localDecls layouts targetTy) bs with
          | some v' => exact Or.inr (Or.inr ⟨v', fun _ => rfl⟩)
          | none => exact Or.inl fun _ => rfl

theorem evalNullaryOp_shape
    (locals : List LocalSlot) (op : NullOp) (argTy : Ty)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    (∀ mem, evalNullaryOp locals op argTy mem localDecls layouts = .unsupported) ∨
    (∃ sc, ∀ mem, evalNullaryOp locals op argTy mem localDecls layouts =
      .ok (.scalar sc) locals mem) := by
  unfold evalNullaryOp
  dsimp only
  cases op with
  | sizeOf =>
    dsimp only
    cases intrinsicRigidTyByteSize localDecls layouts argTy.kind with
    | none => exact Or.inl fun _ => rfl
    | some sz =>
      dsimp only
      cases Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1) with
      | true => exact Or.inr ⟨_, fun _ => rfl⟩
      | false => exact Or.inl fun _ => rfl
  | alignOf =>
    dsimp only
    cases intrinsicRigidTyByteSize localDecls layouts argTy.kind with
    | none => exact Or.inl fun _ => rfl
    | some sz =>
      cases intrinsicRigidTyAlign localDecls layouts argTy.kind with
      | none => exact Or.inl fun _ => rfl
      | some align =>
        dsimp only
        cases Bool.and (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
            (Bool.and (Align.isPowerOfTwoBytes ⟨align⟩)
              (Nat.blt align (scalarModulus (layoutPointerBytes layouts)))) with
        | true => exact Or.inr ⟨_, fun _ => rfl⟩
        | false => exact Or.inl fun _ => rfl
  | offsetOf fields =>
    dsimp only
    cases intrinsicRigidTyByteSize localDecls layouts argTy.kind with
    | none => exact Or.inl fun _ => rfl
    | some sz =>
      dsimp only
      cases resolveOffsetOfPath layouts
          (intrinsicRigidTyByteSize localDecls layouts)
          (intrinsicRigidTyAlign localDecls layouts)
          (findDeclLayoutForRigidTy localDecls layouts)
          (.some argTy.kind)
          (findDeclLayoutForRigidTy localDecls layouts argTy.kind)
          fields with
      | none => exact Or.inl fun _ => rfl
      | some offset =>
        dsimp only
        cases Bool.and (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
            (Nat.ble offset sz) with
        | true => exact Or.inr ⟨_, fun _ => rfl⟩
        | false => exact Or.inl fun _ => rfl
  | ubChecks =>
    dsimp only
    cases argTy.kind <;> first | exact Or.inr ⟨_, fun _ => rfl⟩ | exact Or.inl fun _ => rfl
  | contractChecks =>
    exact Or.inl fun _ => rfl

private def evalShallowInitBoxBody
    (op : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot) (mem' : Memory) : RvalueEvalResult :=
  let operandIsRawPtr : Bool :=
    match operandTy localDecls layouts op with
    | .some { kind := .rawPtr _ _, .. } => true
    | .some _ => false
    | .none => true
  match operandIsRawPtr, v with
  | true, .ptr p sz =>
    match Nat.beq sz (layoutPointerBytes layouts) with
    | true => .ok (.ptr p sz) locals' mem'
    | false => .unsupported
  | _, _ => .unsupported

theorem evalShallowInitBox_ub_of_use
    {locals : List LocalSlot} {op : Operand} {contentTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : evalUseRvalue locals op mem localDecls layouts = .ub) :
    evalShallowInitBox locals op contentTy mem localDecls layouts = .ub := by
  unfold evalShallowInitBox; rw [h]

theorem evalShallowInitBox_unsupported_of_use
    {locals : List LocalSlot} {op : Operand} {contentTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : evalUseRvalue locals op mem localDecls layouts = .unsupported) :
    evalShallowInitBox locals op contentTy mem localDecls layouts = .unsupported := by
  unfold evalShallowInitBox; rw [h]

theorem evalShallowInitBox_ok_of_use
    {locals : List LocalSlot} {op : Operand} {contentTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {v : Value} {locals' : List LocalSlot} {mem' : Memory}
    (h : evalUseRvalue locals op mem localDecls layouts = .ok v locals' mem') :
    evalShallowInitBox locals op contentTy mem localDecls layouts =
      evalShallowInitBoxBody op localDecls layouts v locals' mem' := by
  unfold evalShallowInitBox; rw [h]; rfl

theorem evalShallowInitBoxBody_shape
    (op : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot) :
    (∀ mem', evalShallowInitBoxBody op localDecls layouts v locals' mem' = .unsupported) ∨
    (∃ p sz, ∀ mem', evalShallowInitBoxBody op localDecls layouts v locals' mem' =
      .ok (.ptr p sz) locals' mem') := by
  unfold evalShallowInitBoxBody
  dsimp only
  cases (match operandTy localDecls layouts op with
    | .some { kind := .rawPtr _ _, .. } => true
    | .some _ => false
    | .none => true) with
  | false =>
    cases v <;> exact Or.inl fun _ => rfl
  | true =>
    cases v with
    | ptr p sz =>
      dsimp only
      cases Nat.beq sz (layoutPointerBytes layouts) with
      | true => exact Or.inr ⟨p, sz, fun _ => rfl⟩
      | false => exact Or.inl fun _ => rfl
    | _ => exact Or.inl fun _ => rfl

private def evalWrapUnsafeBinderBody
    (op : Operand) (targetTy : Ty) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot) (mem' : Memory) : RvalueEvalResult :=
  match binderStructLayout? localDecls layouts targetTy with
  | .some l =>
    match operandTy localDecls layouts op with
    | .some opTy =>
      match scalarValidRangeOk l v with
      | false => .ub
      | true =>
        match rigidTyEq opTy.kind targetTy.kind with
        | true => .ok v locals' mem'
        | false => .ok (.aggregate 0 (v :: .nil)) locals' mem'
    | .none => .unsupported
  | .none =>
    let targetRangeOk : Bool :=
      match resolvedTyLayout? localDecls layouts targetTy with
      | .some l => scalarValidRangeOk l v
      | .none => true
    match targetRangeOk with
    | false => .ub
    | true => .ok v locals' mem'

theorem evalWrapUnsafeBinder_ub_of_use
    {locals : List LocalSlot} {op : Operand} {targetTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : evalUseRvalue locals op mem localDecls layouts = .ub) :
    evalWrapUnsafeBinder locals op targetTy mem localDecls layouts = .ub := by
  unfold evalWrapUnsafeBinder; rw [h]

theorem evalWrapUnsafeBinder_unsupported_of_use
    {locals : List LocalSlot} {op : Operand} {targetTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h : evalUseRvalue locals op mem localDecls layouts = .unsupported) :
    evalWrapUnsafeBinder locals op targetTy mem localDecls layouts = .unsupported := by
  unfold evalWrapUnsafeBinder; rw [h]

theorem evalWrapUnsafeBinder_ok_of_use
    {locals : List LocalSlot} {op : Operand} {targetTy : Ty} {mem : Memory}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {v : Value} {locals' : List LocalSlot} {mem' : Memory}
    (h : evalUseRvalue locals op mem localDecls layouts = .ok v locals' mem') :
    evalWrapUnsafeBinder locals op targetTy mem localDecls layouts =
      evalWrapUnsafeBinderBody op targetTy localDecls layouts v locals' mem' := by
  unfold evalWrapUnsafeBinder; rw [h]; rfl

theorem evalWrapUnsafeBinderBody_shape
    (op : Operand) (targetTy : Ty) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (v : Value) (locals' : List LocalSlot) :
    (∀ mem', evalWrapUnsafeBinderBody op targetTy localDecls layouts v locals' mem' = .ub) ∨
    (∀ mem', evalWrapUnsafeBinderBody op targetTy localDecls layouts v locals' mem' =
      .unsupported) ∨
    (∃ outVal, ∀ mem', evalWrapUnsafeBinderBody op targetTy localDecls layouts v locals' mem' =
      .ok outVal locals' mem') := by
  unfold evalWrapUnsafeBinderBody
  dsimp only
  cases binderStructLayout? localDecls layouts targetTy with
  | some l =>
    dsimp only
    cases operandTy localDecls layouts op with
    | none => exact Or.inr (Or.inl fun _ => rfl)
    | some opTy =>
      dsimp only
      cases scalarValidRangeOk l v with
      | false => exact Or.inl fun _ => rfl
      | true =>
        dsimp only
        cases rigidTyEq opTy.kind targetTy.kind with
        | true => exact Or.inr (Or.inr ⟨v, fun _ => rfl⟩)
        | false => exact Or.inr (Or.inr ⟨.aggregate 0 [v], fun _ => rfl⟩)
  | none =>
    dsimp only
    cases (match resolvedTyLayout? localDecls layouts targetTy with
      | .some l => scalarValidRangeOk l v
      | .none => true) with
    | false => exact Or.inl fun _ => rfl
    | true => exact Or.inr (Or.inr ⟨v, fun _ => rfl⟩)

theorem evalByteCast_pure_eq_withMem
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureOperand op = true) :
    evalByteCast locals op targetTy mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalByteCast locals op targetTy emptyMemory localDecls layouts) := by
  have h1 := evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals
    (localDecls := localDecls) (callStack := mem.callStack) h_pure
  have h2 := evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts
    emptyMemory.callerLocals (localDecls := localDecls) (callStack := emptyMemory.callStack) h_pure
  cases h0 : evalOperand locals op [] [] layouts [] localDecls with
  | ub =>
    rw [evalByteCast_ub_of_load (h1.trans h0), evalByteCast_ub_of_load (h2.trans h0)]
    rfl
  | unsupported =>
    rw [evalByteCast_unsupported_of_load (h1.trans h0),
        evalByteCast_unsupported_of_load (h2.trans h0)]
    rfl
  | ok v locals' =>
    rw [evalByteCast_ok_of_load (h1.trans h0), evalByteCast_ok_of_load (h2.trans h0)]
    rcases evalByteCastBody_shape op targetTy localDecls layouts v locals' with
      h_ub | h_un | ⟨v', h_ok⟩
    · rw [h_ub mem, h_ub emptyMemory]; rfl
    · rw [h_un mem, h_un emptyMemory]; rfl
    · rw [h_ok mem, h_ok emptyMemory]; rfl

/-- A pure projection path contains no `.deref`, so `splitLastDeref?` finds none. -/
theorem splitLastDeref?_eq_none_of_pure :
    ∀ (proj : List ProjectionElem), proj.all isPureProjElem = true →
      splitLastDeref? proj = none
  | [], _ => rfl
  | hd :: tl, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := splitLastDeref?_eq_none_of_pure tl h.2
    cases hd <;> simp_all [isPureProjElem, splitLastDeref?]

/--
Reading a pure place is independent of `borrows`, `globals`, `callerLocals`,
and the suspended-frame `callStack`.
-/
theorem evalPlaceRead_pure_eq
    (locals : List LocalSlot) (p : Place)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl) {callStack : List SavedCallerFrame}
    (h_pure : isPurePlace p = true) :
    evalPlaceRead locals p borrows globals layouts callerLocals localDecls callStack =
      evalPlaceRead locals p [] [] layouts [] localDecls := by
  rcases p with ⟨loc, proj⟩
  cases proj with
  | nil => rfl
  | cons hd tl =>
    simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
    cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)

/-- `Rvalue.len` of a pure place is independent of `mem` and leaves it unchanged. -/
theorem evalPlaceLen_pure_eq_withMem
    (locals : List LocalSlot) (p : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPurePlace p = true) :
    evalPlaceLen locals p mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalPlaceLen locals p emptyMemory localDecls layouts) := by
  have h_split : splitLastDeref? p.projection = none :=
    splitLastDeref?_eq_none_of_pure p.projection h_pure
  unfold evalPlaceLen
  simp only [h_split]
  rw [evalPlaceRead_pure_eq locals p mem.borrows mem.globals layouts
      mem.callerLocals localDecls h_pure,
    evalPlaceRead_pure_eq locals p emptyMemory.borrows emptyMemory.globals
      layouts emptyMemory.callerLocals localDecls h_pure]
  repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)

/-- `evalPlaceDiscriminant` only threads `mem` through to its result. -/
theorem evalPlaceDiscriminant_eq_withMem
    (val : Value) (locals' : List LocalSlot) (mem : Memory) (p : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceDiscriminant val locals' mem p localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalPlaceDiscriminant val locals' emptyMemory p localDecls layouts) := by
  unfold evalPlaceDiscriminant
  dsimp only
  repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)

theorem ptrAddressScalar?_nil_borrows
    (locals : List LocalSlot) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ptrBytes : Nat) (p : ProvenancePtr) (sz : Nat)
    {callStack : List SavedCallerFrame} :
    ptrAddressScalar? locals [] callerLocals localDecls layouts ptrBytes p sz callStack =
      .some (ptrToAddrScalar p sz) :=
  rfl

theorem resolveWideWordScalar?_nil_borrows
    (word : Value) (locals : List LocalSlot) (callerLocals : List LocalSlot)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (ptrBytes : Nat)
    {callStack : List SavedCallerFrame} :
    resolveWideWordScalar? word locals [] callerLocals localDecls layouts ptrBytes callStack =
      resolveWideWordScalar? word locals [] [] localDecls layouts ptrBytes := by
  unfold resolveWideWordScalar?
  simp only [ptrAddressScalar?_nil_borrows]

theorem isPtrRelationalBinOp_eq_false_of_nonptr
    {op : BinOp} {localDecls : List LocalDecl} {layouts : LayoutTable}
    {lhs rhs : Operand}
    (h : Bool.not (Bool.and (isRelationalBinOp op) (isPtrOrUntypedOperand localDecls layouts lhs)) = true) :
    isPtrRelationalBinOp op localDecls layouts lhs rhs = false := by
  unfold isPtrRelationalBinOp
  cases h1 : isRelationalBinOp op <;> cases h2 : isPtrOrUntypedOperand localDecls layouts lhs
  · rfl
  · rfl
  · rfl
  · rw [h1, h2] at h; cases h

private theorem evalFloatCastRvalue_pure_eq_withMem
    (locals : List LocalSlot) (ck : CastKind) (op : Operand)
    (targetTy : Ty) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (h_pure : isPureOperand op = true) :
    evalFloatCastRvalue locals ck op targetTy mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalFloatCastRvalue locals ck op targetTy emptyMemory localDecls layouts) := by
  unfold evalFloatCastRvalue
  rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure,
      evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
  cases evalOperand locals op [] [] layouts [] localDecls with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    dsimp only
    cases evalFloatCast ck (operandTy localDecls layouts op) targetTy layouts v <;> rfl

private theorem evalRvalue_binaryOp_pure_eq_withMem
    (locals : List LocalSlot) (op : BinOp) (lhs rhs : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_op : isPureBinOp op = true)
    (h_lhs : isPureOperand lhs = true)
    (h_rhs : isPureOperand rhs = true)
    (h_bor_or_np :
      mem.borrows = [] ∨
      Bool.not (Bool.and (isRelationalBinOp op) (isPtrOrUntypedOperand localDecls layouts lhs)) = true) :
    evalRvalue locals (.binaryOp op lhs rhs) mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalRvalue locals (.binaryOp op lhs rhs) emptyMemory localDecls layouts) := by
  dsimp only [evalRvalue]
  rw [evalOperand_pure_eq locals lhs mem.borrows mem.globals layouts mem.callerLocals h_lhs,
      evalOperand_pure_eq locals lhs emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_lhs]
  cases evalOperand locals lhs [] [] layouts [] localDecls with
  | ub => rfl
  | unsupported => rfl
  | ok lhsVal locals₁ =>
    dsimp only
    rw [evalOperand_pure_eq locals₁ rhs mem.borrows mem.globals layouts mem.callerLocals h_rhs,
        evalOperand_pure_eq locals₁ rhs emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_rhs]
    cases evalOperand locals₁ rhs [] [] layouts [] localDecls with
    | ub => rfl
    | unsupported => rfl
    | ok rhsVal locals₂ =>
      dsimp only
      cases lhsVal with
      | scalar lhsSc =>
        cases rhsVal with
        | scalar rhsSc =>
          cases op with
          | offset => exact absurd h_op (by decide)
          | _ =>
            cases Bool.or (isFloatOptTy (operandTy localDecls layouts lhs))
                (isFloatOptTy (operandTy localDecls layouts rhs)) with
            | true => exact evalFloatScalarBinOp_eq_withMem _ lhsSc rhsSc _ _ locals₂ mem
            | false => exact evalScalarBinOp_eq_withMem _ lhsSc rhsSc locals₂ mem _
        | ptr ptrVal sz =>
          rcases h_bor_or_np with h_borrows | h_np
          · cases isPtrRelationalBinOp op localDecls layouts lhs rhs with
            | false => rfl
            | true =>
              dsimp only [emptyMemory]
              rw [h_borrows, ptrAddressScalar?_nil_borrows, ptrAddressScalar?_nil_borrows]
              exact evalScalarBinOp_eq_withMem op lhsSc (ptrToAddrScalar ptrVal sz) locals₂ mem false
          · rw [isPtrRelationalBinOp_eq_false_of_nonptr h_np]; rfl
        | _ => rfl
      | ptr ptrVal sz =>
        cases rhsVal with
        | scalar rhsSc =>
          cases op with
          | offset => exact absurd h_op (by decide)
          | _ =>
            rcases h_bor_or_np with h_borrows | h_np
            · cases isPtrRelationalBinOp _ localDecls layouts lhs rhs with
              | false => rfl
              | true =>
                dsimp only [emptyMemory]
                rw [h_borrows, ptrAddressScalar?_nil_borrows, ptrAddressScalar?_nil_borrows]
                exact evalScalarBinOp_eq_withMem _ (ptrToAddrScalar ptrVal sz) rhsSc locals₂ mem false
            · rw [isPtrRelationalBinOp_eq_false_of_nonptr h_np]; rfl
        | ptr rhsPtr rhsSz =>
          rcases h_bor_or_np with h_borrows | h_np
          · cases isPtrRelationalBinOp op localDecls layouts lhs rhs with
            | false => rfl
            | true =>
              dsimp only [emptyMemory]
              rw [h_borrows,
                  ptrAddressScalar?_nil_borrows, ptrAddressScalar?_nil_borrows,
                  ptrAddressScalar?_nil_borrows, ptrAddressScalar?_nil_borrows]
              exact evalScalarBinOp_eq_withMem op (ptrToAddrScalar ptrVal sz) (ptrToAddrScalar rhsPtr rhsSz) locals₂ mem false
          · rw [isPtrRelationalBinOp_eq_false_of_nonptr h_np]; rfl
        | _ => rfl
      | aggregate lhsVar lhsFields =>
        cases rhsVal with
        | aggregate rhsVar rhsFields =>
          rcases h_bor_or_np with h_borrows | h_np
          · dsimp only [evalWidePtrAggregateRelBinOp, evalWidePtrRelBinOp, emptyMemory]
            rw [h_borrows]
            simp only [resolveWideWordScalar?_nil_borrows]
            repeat' (first
              | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok
              | exact evalScalarBinOp_eq_withMem ..
              | split)
          · dsimp only [evalWidePtrAggregateRelBinOp]
            cases h1 : isRelationalBinOp op <;> cases h2 : isPtrOrUntypedOperand localDecls layouts lhs
            · repeat' (first | rfl | split)
            · repeat' (first | rfl | split)
            · repeat' (first | rfl | split)
            · rw [h1, h2] at h_np; cases h_np
        | _ => rfl
      | _ => rfl

/-- The operand load `evalUseRvalue` of a pure operand depends on memory only through the memory it
returns. -/
theorem evalUseRvalue_pure_eq_withMem
    (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureOperand op = true) :
    evalUseRvalue locals op mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalUseRvalue locals op emptyMemory localDecls layouts) := by
  dsimp only [evalUseRvalue]
  rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
  rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
  cases evalOperand locals op [] [] layouts [] localDecls with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    dsimp only
    cases validateLoadedValue layouts localDecls op v with
    | false => rfl
    | true =>
      cases op with
      | constant _ => rfl
      | copy p | move p =>
        rcases p with ⟨loc, proj⟩
        cases proj with
        | nil => rfl
        | cons hd tl =>
          simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
          cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)

theorem evalRvalue_pure_eq_withMem_core
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureRvalue rv = true)
    (h_bor_or_nonptr :
      mem.borrows = [] ∨
      ∀ op lhs rhs, rv = .binaryOp op lhs rhs →
        Bool.not (Bool.and (isRelationalBinOp op) (isPtrOrUntypedOperand localDecls layouts lhs)) = true) :
    evalRvalue locals rv mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalRvalue locals rv emptyMemory localDecls layouts) := by
  cases rv with
  | use op =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    cases evalOperand locals op [] [] layouts [] localDecls with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      dsimp only
      cases validateLoadedValue layouts localDecls op v with
      | false => rfl
      | true =>
        cases op with
        | constant _ => rfl
        | copy p | move p =>
          rcases p with ⟨loc, proj⟩
          cases proj with
          | nil => rfl
          | cons hd tl =>
            simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
            cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
  | wrapUnsafeBinder op targetTy =>
    dsimp only [isPureRvalue] at h_pure
    show evalWrapUnsafeBinder locals op targetTy mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalWrapUnsafeBinder locals op targetTy emptyMemory localDecls layouts)
    have h_u := evalUseRvalue_pure_eq_withMem locals op mem localDecls layouts h_pure
    cases h0 : evalUseRvalue locals op emptyMemory localDecls layouts with
    | ub =>
      rw [h0] at h_u
      rw [evalWrapUnsafeBinder_ub_of_use h_u, evalWrapUnsafeBinder_ub_of_use h0]
      rfl
    | unsupported =>
      rw [h0] at h_u
      rw [evalWrapUnsafeBinder_unsupported_of_use h_u,
          evalWrapUnsafeBinder_unsupported_of_use h0]
      rfl
    | ok v l m =>
      rw [h0] at h_u
      rw [evalWrapUnsafeBinder_ok_of_use h_u, evalWrapUnsafeBinder_ok_of_use h0]
      rcases evalWrapUnsafeBinderBody_shape op targetTy localDecls layouts v l with
        h_ub | h_un | ⟨outVal, h_ok⟩
      · rw [h_ub mem, h_ub m]; rfl
      · rw [h_un mem, h_un m]; rfl
      · rw [h_ok mem, h_ok m]; rfl
  | «repeat» op count =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    cases evalOperand locals op [] [] layouts [] localDecls with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases op with
      | constant _ => rfl
      | copy p | move p =>
        rcases p with ⟨loc, proj⟩
        cases proj with
        | nil => rfl
        | cons hd tl =>
          simp only [isPureOperand, isPurePlace, List.all_cons, Bool.and_eq_true] at h_pure
          cases hd <;> first | rfl | exact False.elim (Bool.false_ne_true h_pure.1)
  | ref _ _ => cases h_pure
  | threadLocalRef _ => cases h_pure
  | rawPtr _ _ => cases h_pure
  | len p =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    exact evalPlaceLen_pure_eq_withMem locals p mem localDecls layouts h_pure
  | cast ck op targetTy =>
    dsimp only [isPureRvalue] at h_pure
    cases ck with
    | pointerCoercion _ => cases h_pure
    | fnPtrToPtr => cases h_pure
    | ptrToPtr => cases h_pure
    | pointerExposeProvenance => cases h_pure
    | pointerWithExposedProvenance => cases h_pure
    | transmute => exact evalByteCast_pure_eq_withMem locals op targetTy mem localDecls layouts h_pure
    | subtype => exact evalByteCast_pure_eq_withMem locals op targetTy mem localDecls layouts h_pure
    | floatToInt | intToFloat | floatToFloat =>
      exact evalFloatCastRvalue_pure_eq_withMem locals _ op targetTy mem localDecls layouts h_pure
    | _ =>
      dsimp only [evalRvalue]
      try rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      try rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      try cases evalOperand locals op [] [] layouts [] localDecls
      try cases evalOperand locals op [] [] layouts []
      repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)
      all_goals try dsimp (config := { zeta := true })
      repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)
      all_goals try rfl
  | binaryOp op lhs rhs =>
    have h_bor_or_np := h_bor_or_nonptr.imp id (fun f => f op lhs rhs rfl)
    simp only [isPureRvalue, Bool.and_eq_true] at h_pure
    exact evalRvalue_binaryOp_pure_eq_withMem locals op lhs rhs mem localDecls layouts
      h_pure.1 h_pure.2.1 h_pure.2.2 h_bor_or_np
  | nullaryOp op ty =>
    show evalNullaryOp locals op ty mem localDecls layouts =
      RvalueEvalResult.withMem mem (evalNullaryOp locals op ty emptyMemory localDecls layouts)
    rcases evalNullaryOp_shape locals op ty localDecls layouts with h_un | ⟨sc, h_ok⟩
    · rw [h_un mem, h_un emptyMemory]; rfl
    · rw [h_ok mem, h_ok emptyMemory]; rfl
  | unaryOp uop op =>
    dsimp only [isPureRvalue] at h_pure
    cases uop with
    | not =>
      dsimp only [evalRvalue]
      rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      cases evalOperand locals op [] [] layouts [] localDecls with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        cases v with
        | scalar sc => exact evalUnaryNot_eq_withMem sc _ locals' mem
        | _ => rfl
    | neg =>
      dsimp only [evalRvalue]
      rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first
        | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok
        | exact evalFloatUnaryNeg_eq_withMem .. | split)
    | ptrMetadata =>
      dsimp only [evalRvalue, evalUnaryPtrMetadata]
      rw [evalOperand_pure_eq locals op mem.borrows mem.globals layouts mem.callerLocals h_pure]
      rw [evalOperand_pure_eq locals op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)
  | discriminant p =>
    dsimp only [isPureRvalue] at h_pure
    dsimp only [evalRvalue]
    rw [evalOperand_pure_eq locals (.copy p) mem.borrows mem.globals layouts mem.callerLocals h_pure]
    rw [evalOperand_pure_eq locals (.copy p) emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
    repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | exact evalPlaceDiscriminant_eq_withMem .. | split)
  | aggregate kind ops =>
    dsimp only [isPureRvalue] at h_pure
    cases kind with
    | rawPtr pt mutab =>
      dsimp only [evalRvalue, evalAggregateRawPtr]
      rw [evalOperands_pure_eq locals ops mem.borrows mem.globals layouts mem.callerLocals h_pure,
          evalOperands_pure_eq locals ops emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)
    | adt dp vi af =>
      dsimp only [evalRvalue, evalAggregateAdt]
      rw [evalOperands_pure_eq locals ops mem.borrows mem.globals layouts mem.callerLocals h_pure,
          evalOperands_pure_eq locals ops emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      cases evalOperands locals ops [] [] layouts [] localDecls with
      | ub => rfl
      | unsupported => rfl
      | ok _ _ =>
        dsimp only
        repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)
    | _ =>
      dsimp only [evalRvalue]
      try rw [evalOperands_pure_eq locals ops mem.borrows mem.globals layouts mem.callerLocals h_pure]
      try rw [evalOperands_pure_eq locals ops emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | exact rval_withMem_ub | exact rval_withMem_unsupported | exact rval_withMem_ok | split)
  | shallowInitBox _ _ => cases h_pure
  | copyForDeref _ => cases h_pure

/--
Evaluating a pure `Rvalue` at `mem : Memory` with `mem.borrows = []` produces
the exact same value and local-slot updates as evaluating at `emptyMemory`,
leaving `mem` completely unchanged.
-/
theorem evalRvalue_pure_eq_withMem
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureRvalue rv = true)
    (h_borrows : mem.borrows = []) :
    evalRvalue locals rv mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalRvalue locals rv emptyMemory localDecls layouts) :=
  evalRvalue_pure_eq_withMem_core locals rv mem localDecls layouts h_pure (Or.inl h_borrows)

/--
Evaluating a borrow-free pure `Rvalue` (`isBorrowFreePureRvalue`) at ANY
`mem : Memory` (even when `mem.borrows ≠ []`) produces the exact same value and
local-slot updates as evaluating at `emptyMemory`, leaving `mem` unchanged.
-/
theorem evalRvalue_borrowFree_pure_eq_withMem
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isBorrowFreePureRvalue localDecls layouts rv = true) :
    evalRvalue locals rv mem localDecls layouts =
      RvalueEvalResult.withMem mem
        (evalRvalue locals rv emptyMemory localDecls layouts) := by
  have ⟨h_p, h_np⟩ := Bool.and_eq_true_iff.mp h_pure
  refine evalRvalue_pure_eq_withMem_core locals rv mem localDecls layouts h_p (Or.inr ?_)
  intro op lhs rhs h_eq
  subst h_eq
  exact h_np

/-- Replace the `Memory` in a normal `MirOutcome` with `mem`. -/
def MirOutcome.withMem (mem : Memory) : MirOutcome → MirOutcome
  | .normal retPair => .normal (retPair.1, mem)
  | .panic => .panic
  | .abort => .abort

/-- Replace the `Memory` in a `MirExecState` with `mem`. -/
def MirExecState.withMem (mem : Memory) : MirExecState → MirExecState
  | .running s => .running { s with memory := mem }
  | .halted out => .halted (MirOutcome.withMem mem out)
  | .faulted fk => .faulted fk

/--
Replace the `Memory` in a `MirStepNode` with `mem`, leaving `MirFailE` fault
nodes untouched so `MirStepNode.withMem mem (MirStepNode.fail fk)` is
definitionally equal (`rfl`) to `MirStepNode.fail fk`.
-/
def MirStepNode.withMem (mem : Memory) : MirStepNode → MirStepNode
  | .ret out => .ret (MirOutcome.withMem mem out)
  | .tau st => .tau (MirExecState.withMem mem st)
  | .vis (.inl f) k => .vis (.inl f) k
  | .vis (.inr e) k => .vis (.inr e) (fun o => MirExecState.withMem mem (k o))

@[simp]
theorem MirStepNode.withMem_fail (mem : Memory) (fk : FailureKind) :
    MirStepNode.withMem mem (MirStepNode.fail fk) = MirStepNode.fail fk :=
  rfl

@[simp]
theorem MirStepNode.withMem_unsupported (mem : Memory) :
    MirStepNode.withMem mem MirStepNode.unsupported = MirStepNode.unsupported :=
  rfl

theorem memory_with_borrows_nil_eq {mem : Memory} (h : mem.borrows = []) :
    { mem with borrows := [] } = mem := by
  cases mem
  simp only at h
  subst h
  rfl

def evalAssignNonDeref
    (s : MachineState) (dstLoc : Local) (proj : List ProjectionElem)
    (val : Value) (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  let decls' := eraseLeadingOpaqueCastDecls localDecls layouts dstLoc proj
  match get? locals₁ dstLoc with
  | .some (.init rootVal) =>
    match
      ensureNestedFieldShells
        rootVal
        proj
        decls'
        layouts
        (placeTy decls' layouts { local_ := dstLoc, projection := .nil })
    with
    | .none => MirStepNode.fail .ub
    | .some shelledRoot =>
      match
        writeProjectedForLocal
          locals₁
          decls'
          layouts
          dstLoc
          shelledRoot
          proj
          val
      with
      | .ok rootVal' =>
        match set? locals₁ dstLoc (.init rootVal') with
        | .some locals₂ =>
          let resolvedLocalProj :=
            resolveBorrowWriteLocalProj decls' layouts locals₁ dstLoc proj
          match mem₁.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
                (length mem₁.callStack)
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
  | .some .uninit =>
    match (match proj with
       | hd :: tl => uninitFieldWriteShell? localDecls layouts dstLoc hd tl
       | .nil => .none) with
    | .some rootVal =>
      match writeProjectedForLocal locals₁ decls' layouts dstLoc rootVal proj val with
      | .ok rootVal' =>
        match set? locals₁ dstLoc (.init rootVal') with
        | .some locals₂ =>
          let resolvedLocalProj :=
            resolveBorrowWriteLocalProj
              decls'
              layouts
              locals₁
              dstLoc
              proj
          match mem₁.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                mem₁.borrows (protHead :: protTail) dstLoc .none resolvedLocalProj 0 0
                (length mem₁.callStack)
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  mem₁.borrows dstLoc .none resolvedLocalProj 0 0 (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
    | .none => MirStepNode.fail .ub
  | .some .dead => MirStepNode.fail .ub
  | .none => MirStepNode.fail .ub

def evalAssignDst
    (s : MachineState) (dst : Place) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match dst.projection, stripLeadingOpaqueCast dst.projection with
  | .nil, _ =>
    match get? locals₁ dst.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dst.local_ (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dst.local_ .none .nil 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deref :: restProj, _ =>
    match
      evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors localDecls layouts
        mem₁.callStack
    with
    | .ok locals₂ =>
      match
        Bool.or
          (derefWriteTreeUB locals₁ mem₁.borrows dst)
          (derefWriteUnionProtectorUB
            localDecls layouts locals₁ mem₁.borrows mem₁.activeProtectors dst restProj
            mem₁.callStack)
      with
      | true => MirStepNode.fail .ub
      | false =>
        let borrows' :=
          invalidateDerefWriteBorrowsWithLayouts
            localDecls layouts locals₁ mem₁.borrows dst restProj mem₁.callStack
        MirStepNode.step (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
    | .ub =>
      match mem₁.callStack with
      | .nil =>
        match mem₁.callerLocals with
        | .nil => MirStepNode.fail .ub
        | _ :: _ =>
          match
            evalCallerPlaceWrite
              locals₁ mem₁.callerLocals mem₁.borrows dst val mem₁.activeProtectors
          with
          | .ok callerLocals' =>
            match derefWriteTreeUB locals₁ mem₁.borrows dst with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateDerefWriteBorrows
                  locals₁ mem₁.borrows dst restProj mem₁.callerLocals
              MirStepNode.step
                (advanceStmt s locals₁
                  { mem₁ with borrows := borrows', callerLocals := callerLocals' })
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
      | _ :: _ =>
        evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts
    | .unsupported => MirStepNode.unsupported
  | .opaqueCast _ :: _, .nil =>
    match get? locals₁ dst.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? locals₁ dst.local_ (.init val) with
      | .some locals₂ =>
        match mem₁.activeProtectors with
        | .nil =>
          let borrows' :=
            invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict
              mem₁.borrows (protHead :: protTail) dst.local_ .none .nil 0 0
              (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateConflictingBorrows mem₁.borrows dst.local_ .none (length mem₁.callStack)
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | hd :: tl, _ =>
    evalAssignNonDeref s dst.local_ (hd :: tl) val locals₁ mem₁ localDecls layouts

theorem evalStmt_assign_eq
    (s : MachineState) (dst : Place) (rv : Rvalue) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt s ⟨.assign dst rv, span⟩ localDecls layouts =
      match evalRvalue s.frame.locals rv s.memory localDecls layouts with
      | .ok val locals₁ mem₁ => evalAssignDst s dst val locals₁ mem₁ localDecls layouts
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalStmt
  dsimp only
  cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
  | ub => rfl
  | unsupported => rfl
  | ok val locals₁ mem₁ =>
    rcases dst with ⟨dstLoc, dstProj⟩
    cases dstProj with
    | nil => rfl
    | cons hd tl => cases hd <;> rfl

/--
A projection list whose head is not an opaque cast is not a pure opaque-cast
chain, so `Trusted`'s `DIV-TR-OPAQUECAST-ROOT-DISPATCH` place dispatch
(`stripLeadingOpaqueCast`) treats the place as projected.
-/
theorem stripLeadingOpaqueCast_cons_ne_nil_of_ne_opaqueCast
    {hd : ProjectionElem} {tl : List ProjectionElem}
    (h : ∀ (castTy : Ty), hd ≠ .opaqueCast castTy) :
    stripLeadingOpaqueCast (hd :: tl) ≠ [] := by
  cases hd with
  | opaqueCast castTy => exact False.elim (h castTy rfl)
  | _ => intro h_eq; cases h_eq

theorem ne_deref_of_isPureProjElem
    {hd : ProjectionElem} (h : isPureProjElem hd = true) : hd ≠ .deref := by
  intro h_eq; subst h_eq; cases h

/-- A pure projection element is not an opaque cast (`DIV-TR-OPAQUECAST-ROOT-DISPATCH`). -/
theorem ne_opaqueCast_of_isPureProjElem
    {hd : ProjectionElem} (h : isPureProjElem hd = true) :
    ∀ (castTy : Ty), hd ≠ .opaqueCast castTy := by
  intro castTy h_eq; subst h_eq; cases h

/-- A projection list with a pure head is dispatched as a projected place. -/
theorem stripLeadingOpaqueCast_cons_ne_nil_of_isPureProjElem
    {hd : ProjectionElem} {tl : List ProjectionElem}
    (h : isPureProjElem hd = true) :
    stripLeadingOpaqueCast (hd :: tl) ≠ [] :=
  stripLeadingOpaqueCast_cons_ne_nil_of_ne_opaqueCast (ne_opaqueCast_of_isPureProjElem h)

/--
A pure place is either the whole local or dispatched as a projected place: it
is never a non-empty pure opaque-cast chain.
-/
theorem isPurePlace_nil_or_strip_ne_nil
    {p : Place} (h : isPurePlace p = true) :
    p.projection = [] ∨ stripLeadingOpaqueCast p.projection ≠ [] := by
  rcases p with ⟨loc, _ | ⟨hd, tl⟩⟩
  · exact Or.inl rfl
  · refine Or.inr (stripLeadingOpaqueCast_cons_ne_nil_of_isPureProjElem ?_)
    simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h
    exact h.1

/-- Case split on `Trusted`'s `DIV-TR-OPAQUECAST-ROOT-DISPATCH` place dispatch. -/
theorem stripLeadingOpaqueCast_eq_nil_or_ne_nil (proj : List ProjectionElem) :
    stripLeadingOpaqueCast proj = [] ∨ stripLeadingOpaqueCast proj ≠ [] := by
  cases stripLeadingOpaqueCast proj with
  | nil => exact Or.inl rfl
  | cons a b => exact Or.inr (List.cons_ne_nil a b)

theorem evalAssignDst_nonDeref
    (s : MachineState) (dstLoc : Local) (hd : ProjectionElem)
    (tl : List ProjectionElem) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_nd : hd ≠ .deref)
    (h_nr : stripLeadingOpaqueCast (hd :: tl) ≠ []) :
    evalAssignDst s ⟨dstLoc, hd :: tl⟩ val locals₁ mem₁ localDecls layouts =
      evalAssignNonDeref s dstLoc (hd :: tl) val locals₁ mem₁ localDecls layouts := by
  unfold evalAssignDst
  dsimp only
  split
  · rename_i h; cases h
  · rename_i h; cases h; exact False.elim (h_nd rfl)
  · rename_i _ h; exact False.elim (h_nr h)
  · rename_i h _; cases h; rfl

/--
Assignment to a pure opaque-cast chain over a local (`(_l as T) = v`) is the
whole-local assignment `_l = v` (`DIV-TR-OPAQUECAST-ROOT-DISPATCH`).
-/
theorem evalAssignDst_castRoot
    (s : MachineState) (dstLoc : Local) (hd : ProjectionElem)
    (tl : List ProjectionElem) (val : Value)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_root : stripLeadingOpaqueCast (List.cons hd tl) = .nil) :
    evalAssignDst s ⟨dstLoc, hd :: tl⟩ val locals₁ mem₁ localDecls layouts =
      evalAssignDst s ⟨dstLoc, []⟩ val locals₁ mem₁ localDecls layouts := by
  cases hd with
  | opaqueCast castTy =>
    unfold evalAssignDst
    dsimp only
    rw [h_root]
  | _ => cases h_root

/--
`Deinit` of a pure opaque-cast chain over a local is the whole-local `Deinit`
(`DIV-TR-OPAQUECAST-ROOT-DISPATCH`).
-/
theorem evalStmt_deinit_castRoot
    (s : MachineState) (loc : Local) (hd : ProjectionElem) (tl : List ProjectionElem)
    (sp : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_root : stripLeadingOpaqueCast (List.cons hd tl) = .nil) :
    evalStmt s { kind := .deinit ⟨loc, hd :: tl⟩, span := sp } localDecls layouts =
      evalStmt s { kind := .deinit ⟨loc, []⟩, span := sp } localDecls layouts := by
  cases hd with
  | opaqueCast castTy =>
    unfold evalStmt
    dsimp only
    rw [h_root]
  | _ => cases h_root

/--
`SetDiscriminant` on a pure opaque-cast chain over a local is the whole-local
`SetDiscriminant` evaluated against the cast-erased declarations
(`eraseLeadingOpaqueCastDecls`, `DIV-TR-OPAQUECAST-ROOT-DISPATCH`).
-/
theorem evalStmt_setDiscriminant_castRoot
    (s : MachineState) (loc : Local) (hd : ProjectionElem) (tl : List ProjectionElem)
    (variantIdx : Nat) (sp : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_root : stripLeadingOpaqueCast (List.cons hd tl) = .nil) :
    evalStmt s { kind := .setDiscriminant ⟨loc, hd :: tl⟩ variantIdx, span := sp }
        localDecls layouts =
      evalStmt s { kind := .setDiscriminant ⟨loc, []⟩ variantIdx, span := sp }
        (eraseLeadingOpaqueCastDecls localDecls layouts loc (hd :: tl)) layouts := by
  cases hd with
  | opaqueCast castTy =>
    unfold evalStmt
    dsimp only
    rw [h_root]
  | _ => cases h_root

/--
`Drop` of a pure opaque-cast chain over a local is the whole-local `Drop`
(`DIV-TR-OPAQUECAST-ROOT-DISPATCH`).
-/
theorem evalTerminator_drop_castRoot
    (s : MachineState) (loc : Local) (hd : ProjectionElem) (tl : List ProjectionElem)
    (target : BasicBlockIdx) (unwind : UnwindAction) (sp : String)
    (curBodyOpt : Option CapturedMir)
    (h_root : stripLeadingOpaqueCast (List.cons hd tl) = .nil) :
    evalTerminator s { kind := .drop ⟨loc, hd :: tl⟩ target unwind, span := sp } curBodyOpt =
      evalTerminator s { kind := .drop ⟨loc, []⟩ target unwind, span := sp } curBodyOpt := by
  cases hd with
  | opaqueCast castTy =>
    unfold evalTerminator
    dsimp only
    rw [h_root]
  | _ => cases h_root

def isOtherPhase : MirPhaseTag → Bool
  | .other _ => true
  | _ => false

theorem stepMirFn_eq_ite (body : CapturedMir) (s : MachineState) :
    stepMirFn body s =
      let currentBody := s.memory.activeCallee.getD body
      if isOtherPhase currentBody.phase then
        MirStepNode.unsupported
      else
        match get? currentBody.basicBlocks s.frame.blockIdx with
        | none => MirStepNode.fail .ub
        | some bb =>
          match get? bb.statements s.frame.stmtIdx with
          | some stmt => evalStmt s stmt currentBody.localDecls currentBody.layouts
          | none =>
            if s.frame.stmtIdx == length bb.statements then
              evalTerminator s bb.terminator (some currentBody)
            else
              MirStepNode.fail .ub := by
  unfold stepMirFn
  dsimp only
  cases (s.memory.activeCallee.getD body).phase <;> rfl

theorem isOtherPhase_eq_false {ph : MirPhaseTag}
    (h : ∀ tag, ph ≠ .other tag) : isOtherPhase ph = false := by
  cases ph with
  | other tag => exact False.elim (h tag rfl)
  | _ => rfl

theorem isOtherPhase_eq_true_iff {ph : MirPhaseTag} :
    isOtherPhase ph = true → ∃ tag, ph = .other tag := by
  cases ph with
  | other tag => intro _; exact ⟨tag, rfl⟩
  | _ => intro h; cases h

theorem evalStmt_setDiscriminant_nonDeref
    (s : MachineState) (loc : Local) (hd : ProjectionElem)
    (tl : List ProjectionElem) (variantIdx : Nat) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_nd : hd ≠ .deref)
    (h_nr : stripLeadingOpaqueCast (hd :: tl) ≠ []) :
    evalStmt s ⟨.setDiscriminant ⟨loc, hd :: tl⟩ variantIdx, span⟩ localDecls layouts =
      match
        evalOperand s.frame.locals (.copy ⟨loc, hd :: tl⟩) s.memory.borrows
          s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack
      with
      | .ok (.aggregate _ fields) locals₁ =>
        match padSetDiscriminantInitFields? localDecls layouts ⟨loc, hd :: tl⟩ variantIdx fields with
        | .none => MirStepNode.fail .ub
        | .some fields' =>
          let newVal : Value := .aggregate variantIdx fields'
          let depth := length s.memory.callStack
          let resolvedLocalProj :=
            resolveBorrowWriteLocalProj localDecls layouts locals₁ loc (hd :: tl)
          match
            hasProtectedWriteConflict s.memory.borrows s.memory.activeProtectors
              loc .none resolvedLocalProj 0 0 depth
          with
          | true => MirStepNode.fail .ub
          | false =>
            match
              writePlaceValue locals₁ s.memory.borrows ⟨loc, hd :: tl⟩ newVal
                localDecls layouts s.memory.callStack
            with
            | .ok locals₂ =>
              MirStepNode.step
                (advanceStmt s locals₂
                  { s.memory with
                    borrows :=
                      invalidateConflictingBorrowsAtProj s.memory.borrows loc .none
                        resolvedLocalProj 0 0 depth })
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
      | .ok _ _ => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold evalStmt
  dsimp only
  split
  · rename_i h; cases h
  · rename_i _ h; exact False.elim (h_nr h)
  · rename_i h _
    cases h
    cases evalOperand s.frame.locals (.copy ⟨loc, hd :: tl⟩) s.memory.borrows
        s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
    | ub =>
      cases hd with
      | deref => exact False.elim (h_nd rfl)
      | _ => rfl
    | unsupported => rfl
    | ok v l1 =>
      cases v with
      | aggregate _ fields =>
        dsimp only
        cases padSetDiscriminantInitFields? localDecls layouts ⟨loc, hd :: tl⟩ variantIdx fields with
        | none => rfl
        | some _ =>
          cases hd with
          | deref => exact False.elim (h_nd rfl)
          | _ => rfl
      | _ => rfl

/--
Evaluating a pure `Statement` from `ps.toMachineState mem₀` produces the exact
same transition as evaluating from `ps.toMachineState emptyMemory` and
restoring `mem₀`, provided `mem₀` has no live borrows and no active
function-entry protectors.

Pure statements read and write only the frame's locals; the only memory fields
they consult are the borrow table (invalidated on every local write) and the
protector stack (checked for protected-write conflicts). In particular, the
call stack and the active callee are irrelevant, so the lemma also applies to
callee frames and to caller frames resumed after a return.
-/
def evalDeinitBorrowsNil
    (s : MachineState) (p : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) : MirStepNode :=
  match p.projection with
  | .nil =>
    match get? s.frame.locals p.local_ with
    | .some .dead => MirStepNode.fail .ub
    | .some _ =>
      match set? s.frame.locals p.local_ .uninit with
      | .some locals' => MirStepNode.step (advanceStmt s locals' s.memory)
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | proj :: rest =>
    match get? s.frame.locals p.local_ with
    | .some (.init rootVal) =>
      match deinitProjectedForLocal s.frame.locals localDecls layouts p.local_ rootVal (proj :: rest) with
      | .ok rootVal' =>
        match set? s.frame.locals p.local_ (.init rootVal') with
        | .some locals' => MirStepNode.step (advanceStmt s locals' s.memory)
        | .none => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
    | .some .uninit =>
      match deinitTailOk s.frame.locals localDecls layouts
          (placeTy localDecls layouts { local_ := p.local_, projection := .nil })
          (proj :: rest) with
      | true => MirStepNode.step (advanceStmt s s.frame.locals s.memory)
      | false =>
        match projectionHasDeref (proj :: rest) with
        | true => MirStepNode.unsupported
        | false => MirStepNode.fail .ub
    | .some .dead => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub

theorem evalStmt_deinit_borrows_nil
    {s : MachineState} {p : Place} {sp : String}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    (h_bor : s.memory.borrows = [])
    (h_nr : p.projection = [] ∨ stripLeadingOpaqueCast p.projection ≠ []) :
    evalStmt s { kind := .deinit p, span := sp } localDecls layouts =
      evalDeinitBorrowsNil s p localDecls layouts := by
  rcases s with ⟨sFr, ⟨nA, gl, bor, nT, cal, tr, cs, ac, ap, nP, cl, fp, ex, ru⟩⟩
  dsimp only at h_bor
  subst h_bor
  unfold evalStmt evalDeinitBorrowsNil
  rcases p with ⟨loc, proj⟩
  dsimp only at h_nr ⊢
  split
  · try dsimp only
    cases get? sFr.locals loc with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | uninit | init _ =>
        dsimp only
        cases set? sFr.locals loc .uninit with
        | none => rfl
        | some _ => cases ap <;> rfl
  · rename_i h
    rcases h_nr with h_nil | h_ne
    · cases h_nil
    · exact False.elim (h_ne h)
  · rename_i phd ptl _
    try dsimp only
    cases get? sFr.locals loc with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | uninit =>
        dsimp only
        cases deinitTailOk sFr.locals localDecls layouts
            (placeTy localDecls layouts { local_ := loc, projection := .nil })
            (phd :: ptl) with
        | false => dsimp only; cases projectionHasDeref (phd :: ptl) <;> rfl
        | true => cases ap <;> rfl
      | init rv =>
        dsimp only
        cases deinitProjectedForLocal sFr.locals localDecls layouts loc rv (phd :: ptl) with
        | ub => rfl
        | unsupported => rfl
        | ok rv' =>
          dsimp only
          cases set? sFr.locals loc (.init rv') with
          | none => rfl
          | some _ => cases ap <;> rfl

theorem evalStmt_toMachineState_eq_withMem_of_frameFree
    (ps : PureState) (mem₀ : Memory) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureStatement stmt.kind = true)
    (h_borrows : mem₀.borrows = [])
    (h_prot : mem₀.activeProtectors = []) :
    evalStmt (ps.toMachineState mem₀) stmt localDecls layouts =
      MirStepNode.withMem mem₀
        (evalStmt (ps.toMachineState emptyMemory) stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop => rfl
  | coverage => rfl
  | constEvalCounter => rfl
  | storageLive loc =>
    cases mem₀
    dsimp only at h_borrows h_prot
    subst h_borrows h_prot
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | storageDead loc =>
    cases mem₀
    dsimp only at h_borrows h_prot
    subst h_borrows h_prot
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | placeMention p =>
    unfold evalStmt
    dsimp only [PureState.toMachineState]
    repeat' (first | rfl | split)
  | deinit p =>
    have h_nr := isPurePlace_nil_or_strip_ne_nil (p := p) h_pure
    rw [evalStmt_deinit_borrows_nil h_borrows h_nr,
        evalStmt_deinit_borrows_nil (s := ps.toMachineState emptyMemory) rfl h_nr]
    unfold evalDeinitBorrowsNil
    rcases p with ⟨loc, _ | ⟨phd, ptl⟩⟩
    · dsimp only [PureState.toMachineState]
      cases get? ps.env loc with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | uninit | init _ =>
          dsimp only
          cases set? ps.env loc .uninit <;> rfl
    · dsimp only [PureState.toMachineState]
      cases get? ps.env loc with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | uninit =>
          dsimp only
          cases deinitTailOk ps.env localDecls layouts
              (placeTy localDecls layouts { local_ := loc, projection := .nil })
              (phd :: ptl) with
          | true => rfl
          | false => dsimp only; cases projectionHasDeref (phd :: ptl) <;> rfl
        | init rv =>
          dsimp only
          cases deinitProjectedForLocal ps.env localDecls layouts loc rv (phd :: ptl) with
          | ub | unsupported => rfl
          | ok rv' => dsimp only; cases set? ps.env loc (.init rv') <;> rfl
  | intrinsic intr =>
    cases intr with
    | assume op =>
      dsimp only [isPureStatement] at h_pure
      unfold evalStmt
      dsimp only [PureState.toMachineState]
      rw [evalOperand_pure_eq ps.env op mem₀.borrows mem₀.globals layouts mem₀.callerLocals h_pure]
      rw [evalOperand_pure_eq ps.env op emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_pure]
      repeat' (first | rfl | split)
    | copyNonOverlapping _ _ _ => cases h_pure
  | retag _ _ => cases h_pure
  | backwardIncompatibleDropHint _ => cases h_pure
  | setDiscriminant p variantIdx =>
    dsimp only [isPureStatement] at h_pure
    have h_op : isPureOperand (.copy p) = true := h_pure
    have h_pp : isPurePlace p = true := h_pure
    rcases mem₀ with ⟨nA, gl, bor, nT, cal, tr, cs, ac, ap, nP, cl, fp, ex⟩
    dsimp only at h_borrows h_prot
    subst h_borrows h_prot
    rcases p with ⟨loc, proj⟩
    cases proj with
    | nil =>
      unfold evalStmt
      dsimp only [PureState.toMachineState, evalSetDiscriminantLocal]
      cases get? ps.env loc with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | uninit =>
          dsimp only
          cases setDiscriminantUninitDeclOk localDecls loc with
          | false => rfl
          | true =>
            dsimp only
            cases setDiscriminantUninitPayload? localDecls layouts loc variantIdx with
            | none => rfl
            | some uf => dsimp only; cases set? ps.env loc (.init (.aggregate variantIdx uf)) <;> rfl
        | init v =>
          cases v with
          | aggregate _ fields =>
            dsimp only
            cases padSetDiscriminantInitFields? localDecls layouts ⟨loc, .nil⟩ variantIdx fields with
            | none => rfl
            | some fields' => dsimp only; cases set? ps.env loc (.init (.aggregate variantIdx fields')) <;> rfl
          | _ => rfl
    | cons hd tl =>
      have h_hd : isPureProjElem hd = true := by
        simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_pp
        exact h_pp.1
      have h_nd := ne_deref_of_isPureProjElem h_hd
      have h_nr := stripLeadingOpaqueCast_cons_ne_nil_of_isPureProjElem (tl := tl) h_hd
      rw [evalStmt_setDiscriminant_nonDeref _ _ _ _ _ _ _ _ h_nd h_nr,
          evalStmt_setDiscriminant_nonDeref _ _ _ _ _ _ _ _ h_nd h_nr]
      dsimp only [PureState.toMachineState]
      rw [evalOperand_pure_eq ps.env (.copy { local_ := loc, projection := hd :: tl })
        [] gl layouts cl h_op]
      rw [evalOperand_pure_eq ps.env (.copy { local_ := loc, projection := hd :: tl })
        emptyMemory.borrows emptyMemory.globals layouts emptyMemory.callerLocals h_op]
      cases evalOperand ps.env (.copy { local_ := loc, projection := hd :: tl }) [] [] layouts [] localDecls with
      | ub => rfl
      | unsupported => rfl
      | ok v locals₁ =>
        cases v with
        | aggregate oldVar fields =>
          dsimp only
          cases padSetDiscriminantInitFields? localDecls layouts ⟨loc, hd :: tl⟩ variantIdx fields with
          | none => rfl
          | some fields' =>
            dsimp only [hasProtectedWriteConflict, emptyMemory, invalidateConflictingBorrowsAtProj]
            rw [writePlaceValue_pure_eq locals₁ [] _ (.aggregate variantIdx fields') h_pp]
            cases writePlaceValue locals₁ [] _ (.aggregate variantIdx fields')
              localDecls layouts <;> rfl
        | _ => rfl
  | assign dst rv =>
    simp only [isPureStatement, Bool.and_eq_true] at h_pure
    rcases h_pure with ⟨h_dst, h_rv⟩
    rw [evalStmt_assign_eq, evalStmt_assign_eq]
    dsimp only [PureState.toMachineState]
    rw [evalRvalue_pure_eq_withMem ps.env rv mem₀ localDecls layouts h_rv h_borrows]
    have h_emp := evalRvalue_pure_eq_withMem ps.env rv emptyMemory localDecls layouts h_rv rfl
    cases h_res : evalRvalue ps.env rv emptyMemory localDecls layouts with
    | ub => rfl
    | unsupported => rfl
    | ok val locals₁ mem₁ =>
      have h_mem₁ : mem₁ = emptyMemory := by
        rw [h_res] at h_emp
        dsimp only [RvalueEvalResult.withMem] at h_emp
        injection h_emp
      subst h_mem₁
      dsimp only [RvalueEvalResult.withMem]
      rcases dst with ⟨dstLoc, dstProj⟩
      cases dstProj with
      | nil =>
        unfold evalAssignDst
        dsimp only
        cases get? locals₁ dstLoc with
        | none => rw [MirStepNode.withMem_fail]
        | some slot =>
          cases slot with
          | dead => rfl
          | uninit =>
            dsimp only
            cases set? locals₁ dstLoc (.init val) with
            | none => rw [MirStepNode.withMem_fail]
            | some locals₂ =>
              try rw [h_prot, h_borrows]
              try rfl
              dsimp only [emptyMemory, invalidateConflictingBorrows,
                MirStepNode.step, advanceStmt, MirStepNode.withMem,
                MirExecState.withMem]
              cases mem₀
              subst h_borrows
              subst h_prot
              rfl
          | init _ =>
            dsimp only
            cases set? locals₁ dstLoc (.init val) with
            | none => rw [MirStepNode.withMem_fail]
            | some locals₂ =>
              try rw [h_prot, h_borrows]
              try rfl
              dsimp only [emptyMemory, invalidateConflictingBorrows,
                MirStepNode.step, advanceStmt, MirStepNode.withMem,
                MirExecState.withMem]
              cases mem₀
              subst h_borrows
              subst h_prot
              rfl
      | cons hd tl =>
        simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_dst
        have h_nd := ne_deref_of_isPureProjElem h_dst.1
        have h_nr := stripLeadingOpaqueCast_cons_ne_nil_of_isPureProjElem (tl := tl) h_dst.1
        rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_nd h_nr,
            evalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_nd h_nr]
        unfold evalAssignNonDeref
        dsimp only
        let decls' := eraseLeadingOpaqueCastDecls localDecls layouts dstLoc (hd :: tl)
        cases get? locals₁ dstLoc with
        | none => rw [MirStepNode.withMem_fail]
        | some slot =>
          cases slot with
          | uninit =>
            dsimp only
            cases uninitFieldWriteShell? localDecls layouts dstLoc hd tl with
            | none => rfl
            | some rootVal =>
              dsimp only
              cases writeProjectedForLocal locals₁ decls' layouts dstLoc rootVal _ val with
              | ub => rfl
              | unsupported => rfl
              | ok rootVal' =>
                dsimp only
                cases set? locals₁ dstLoc (.init rootVal') with
                | none => rw [MirStepNode.withMem_fail]
                | some locals₂ =>
                  try rw [h_prot, h_borrows]
                  try rfl
                  dsimp only [emptyMemory, invalidateConflictingBorrowsAtProj,
                    MirStepNode.step, advanceStmt, MirStepNode.withMem,
                    MirExecState.withMem]
                  cases mem₀
                  subst h_borrows
                  subst h_prot
                  rfl
          | dead => rfl
          | init rootVal =>
            dsimp only
            cases ensureNestedFieldShells rootVal (hd :: tl) decls' layouts
                (placeTy decls' layouts { local_ := dstLoc, projection := .nil }) with
            | none => rw [MirStepNode.withMem_fail]
            | some shelledRoot =>
              dsimp only
              cases writeProjectedForLocal locals₁ decls' layouts dstLoc shelledRoot _ val with
              | ub => rfl
              | unsupported => rfl
              | ok rootVal' =>
                dsimp only
                cases set? locals₁ dstLoc (.init rootVal') with
                | none => rw [MirStepNode.withMem_fail]
                | some locals₂ =>
                  try rw [h_prot, h_borrows]
                  try rfl
                  dsimp only [emptyMemory, invalidateConflictingBorrowsAtProj,
                    MirStepNode.step, advanceStmt, MirStepNode.withMem,
                    MirExecState.withMem]
                  cases mem₀
                  subst h_borrows
                  subst h_prot
                  rfl

/--
Evaluating a pure `Statement` from `ps.toMachineState mem₀` under
`RootActiveMemory mem₀` produces the exact same transition as evaluating from
`ps.toMachineState emptyMemory` and restoring `mem₀`.
-/
theorem evalStmt_toMachineState_eq_withMem
    (ps : PureState) (mem₀ : Memory) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_pure : isPureStatement stmt.kind = true)
    (h_root : RootActiveMemory mem₀) :
    evalStmt (ps.toMachineState mem₀) stmt localDecls layouts =
      MirStepNode.withMem mem₀
        (evalStmt (ps.toMachineState emptyMemory) stmt localDecls layouts) :=
  evalStmt_toMachineState_eq_withMem_of_frameFree ps mem₀ stmt localDecls layouts
    h_pure h_root.1 h_root.2.2.2.1

/--
Evaluating a pure `Terminator` from `ps.toMachineState mem₀` under
`RootActiveMemory mem₀` produces the exact same transition as evaluating from
`ps.toMachineState emptyMemory` and restoring `mem₀`.
-/
def evalDropBorrowsNil
    (s : MachineState) (place : Place) (target : BasicBlockIdx)
    (curBodyOpt : Option CapturedMir) : MirStepNode :=
  let bodyLocalDecls := bodyLocalDeclsOf curBodyOpt
  let bodyLayouts : LayoutTable :=
    match curBodyOpt with
    | .some b => b.layouts
    | .none => emptyLayoutTable
  match get? s.frame.locals place.local_ with
  | .none => MirStepNode.fail .ub
  | .some .dead => MirStepNode.fail .ub
  | .some slot =>
    match place.projection with
    | .nil =>
      match set? s.frame.locals place.local_ .uninit with
      | .some locals' =>
        MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
      | .none => MirStepNode.fail .ub
    | proj :: rest =>
      match slot with
      | .init rootVal =>
        match deinitProjectedForLocal s.frame.locals bodyLocalDecls bodyLayouts place.local_ rootVal (proj :: rest) with
        | .ok rootVal' =>
          match set? s.frame.locals place.local_ (.init rootVal') with
          | .some locals' =>
            MirStepNode.step { s with frame := { blockIdx := target, stmtIdx := 0, locals := locals' } }
          | .none => MirStepNode.fail .ub
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | .uninit =>
        match deinitTailOk s.frame.locals bodyLocalDecls bodyLayouts
            (placeTy bodyLocalDecls bodyLayouts { local_ := place.local_, projection := .nil })
            (proj :: rest) with
        | true =>
          MirStepNode.step { s with frame := { s.frame with blockIdx := target, stmtIdx := 0 } }
        | false =>
          match projectionHasDeref (proj :: rest) with
          | true => MirStepNode.unsupported
          | false => MirStepNode.fail .ub
      | .dead => MirStepNode.fail .ub

theorem evalTerminator_drop_borrows_nil
    {s : MachineState} {place : Place} {target : BasicBlockIdx}
    {unwind : UnwindAction} {sp : String}
    {curBodyOpt : Option CapturedMir}
    (h_bor : s.memory.borrows = [])
    (h_nr : place.projection = [] ∨ stripLeadingOpaqueCast place.projection ≠ []) :
    evalTerminator s { kind := .drop place target unwind, span := sp } curBodyOpt =
      evalDropBorrowsNil s place target curBodyOpt := by
  rcases s with ⟨sFr, ⟨nA, gl, bor, nT, cal, tr, cs, ac, ap, nP, cl, fp, ex, ru⟩⟩
  dsimp only at h_bor
  subst h_bor
  unfold evalTerminator evalDropBorrowsNil
  rcases place with ⟨loc, proj⟩
  dsimp only at h_nr
  cases curBodyOpt <;>
  · dsimp only
    cases get? sFr.locals loc with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | uninit =>
        dsimp only
        split
        · try dsimp only
          cases set? sFr.locals loc .uninit with
          | none => rfl
          | some _ => cases ap <;> rfl
        · rename_i h
          rcases h_nr with h_nil | h_ne
          · cases h_nil
          · exact False.elim (h_ne h)
        · rename_i phd ptl _
          try dsimp only
          cases deinitTailOk sFr.locals _ _ _ (phd :: ptl) with
          | false => dsimp only; cases projectionHasDeref (phd :: ptl) <;> rfl
          | true => cases ap <;> rfl
      | init rv =>
        dsimp only
        split
        · try dsimp only
          cases set? sFr.locals loc .uninit with
          | none => rfl
          | some _ => cases ap <;> rfl
        · rename_i h
          rcases h_nr with h_nil | h_ne
          · cases h_nil
          · exact False.elim (h_ne h)
        · rename_i phd ptl _
          try dsimp only
          cases deinitProjectedForLocal sFr.locals _ _ loc rv (phd :: ptl) with
          | ub => rfl
          | unsupported => rfl
          | ok rv' =>
            dsimp only
            cases set? sFr.locals loc (.init rv') with
            | none => rfl
            | some _ => cases ap <;> rfl

theorem evalTerminator_toMachineState_eq_withMem
    (ps : PureState) (mem₀ : Memory) (term : Terminator) (body : CapturedMir)
    (h_pure : isPureTerminator term.kind = true)
    (h_root : RootActiveMemory mem₀) :
    evalTerminator (ps.toMachineState mem₀) term (some body) =
      MirStepNode.withMem mem₀
        (evalTerminator (ps.toMachineState emptyMemory) term (some body)) := by
  rcases term with ⟨kind, span⟩
  rcases h_root with ⟨h_bor, h_stack, _, h_prot, h_ceil⟩
  cases kind with
  | goto target => rfl
  | unreachable => rfl
  | return_ =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    cases get? ps.env 0 with
    | none => rw [MirStepNode.withMem_fail]
    | some slot =>
      cases slot with
      | uninit => rfl
      | dead => rfl
      | init retVal =>
        dsimp only
        rcases mem₀ with ⟨nA, gl, bor, nT, cal, tr, cs, ac, ap, nP, cl, fp, ex, ru⟩
        dsimp only at h_bor h_stack h_prot
        subst h_bor h_stack h_prot
        cases valueContainsUninit retVal <;> rfl
  | drop p target unwind =>
    have h_nr := isPurePlace_nil_or_strip_ne_nil (p := p) h_pure
    rw [evalTerminator_drop_borrows_nil (s := ps.toMachineState mem₀) h_bor h_nr,
        evalTerminator_drop_borrows_nil (s := ps.toMachineState emptyMemory) rfl h_nr]
    unfold evalDropBorrowsNil
    rcases p with ⟨loc, proj⟩
    dsimp only [PureState.toMachineState]
    cases get? ps.env loc with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | uninit =>
        dsimp only
        cases proj with
        | nil => dsimp only; cases set? ps.env loc .uninit <;> rfl
        | cons hd tl =>
          dsimp only
          cases deinitTailOk ps.env _ _ _ (hd :: tl) with
          | true => rfl
          | false => dsimp only; cases projectionHasDeref (hd :: tl) <;> rfl
      | init rv =>
        dsimp only
        cases proj with
        | nil => dsimp only; cases set? ps.env loc .uninit <;> rfl
        | cons hd tl =>
          dsimp only
          cases deinitProjectedForLocal ps.env _ _ loc rv (hd :: tl) with
          | ub | unsupported => rfl
          | ok rv' => dsimp only; cases set? ps.env loc (.init rv') <;> rfl
  | switchInt discr targets =>
    dsimp only [isPureTerminator] at h_pure
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [evalOperandWithBodyCast_pure_eq ps.env discr mem₀.borrows mem₀.globals body.layouts
      mem₀.callerLocals _ _ h_pure]
    rw [evalOperandWithBodyCast_pure_eq ps.env discr emptyMemory.borrows emptyMemory.globals
      body.layouts emptyMemory.callerLocals _ _ h_pure]
    cases evalOperand ps.env discr [] [] body.layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases v <;> rfl
  | assert cond expected target unwind =>
    dsimp only [isPureTerminator] at h_pure
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [evalOperandWithBodyCast_pure_eq ps.env cond mem₀.borrows mem₀.globals body.layouts
      mem₀.callerLocals _ _ h_pure]
    rw [evalOperandWithBodyCast_pure_eq ps.env cond emptyMemory.borrows emptyMemory.globals
      body.layouts emptyMemory.callerLocals _ _ h_pure]
    cases evalOperand ps.env cond [] [] body.layouts [] with
    | ub => rfl
    | unsupported => rfl
    | ok v locals' =>
      cases v with
      | scalar sc =>
        cases expected
        · dsimp only
          cases Nat.beq sc.bits 0 with
          | true => rfl
          | false =>
            dsimp only [applyUnwindAction]
            cases unwind <;> (try rw [h_stack]) <;>
              (try (dsimp only [unwindFromCallStack]; rw [h_ceil])) <;> rfl
        · dsimp only
          cases Nat.beq sc.bits 1 with
          | true => rfl
          | false =>
            dsimp only [applyUnwindAction]
            cases unwind <;> (try rw [h_stack]) <;>
              (try (dsimp only [unwindFromCallStack]; rw [h_ceil])) <;> rfl
      | _ => rfl
  | call _ _ _ _ _ => cases h_pure
  | tailCall _ _ => cases h_pure
  | unwindResume =>
    unfold evalTerminator
    dsimp only [PureState.toMachineState]
    rw [h_stack]
    dsimp only [unwindFromCallStack]
    rw [h_ceil]
    rfl
  | unwindTerminate => rfl
  | inlineAsm => rfl

/--
One-step simulation theorem for `stepMirFn`: under `checkPureMir body = true`
and `RootActiveMemory mem₀`, stepping `ps.toMachineState mem₀` equals stepping
`ps.toMachineState emptyMemory` and restoring `mem₀` via
`MirStepNode.withMem mem₀`.
-/
theorem stepMirFn_toMachineState_eq_withMem
    {body : CapturedMir} {mem₀ : Memory} (ps : PureState)
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀) :
    stepMirFn body (ps.toMachineState mem₀) =
      MirStepNode.withMem mem₀ (stepMirFn body (ps.toMachineState emptyMemory)) := by
  have h_act : (ps.toMachineState mem₀).memory.activeCallee = none := h_root.2.2.1
  have h_emp_act : (ps.toMachineState emptyMemory).memory.activeCallee = none := rfl
  unfold stepMirFn
  rw [h_act, h_emp_act]
  dsimp only [Option.getD, PureState.toMachineState]
  cases body.phase with
  | other _ => rw [MirStepNode.withMem_unsupported]
  | _ =>
    all_goals
      dsimp only
      cases h_bb : Trusted.Sequence.get? body.basicBlocks (ps.bb : Nat) with
      | none => rw [MirStepNode.withMem_fail]
      | some bb =>
        dsimp only
        have ⟨h_stmts, h_term⟩ := checkPureMir_block h_pure h_bb
        cases h_stmt : get? bb.statements ps.stmtIdx with
        | some stmt =>
          have h_s := list_all_of_get? h_stmts h_stmt
          exact evalStmt_toMachineState_eq_withMem ps mem₀ stmt
            body.localDecls body.layouts h_s h_root
        | none =>
          dsimp only
          by_cases h_eq : (ps.stmtIdx == length bb.statements) = true
          · simp only [h_eq, ite_true]
            exact evalTerminator_toMachineState_eq_withMem ps mem₀ bb.terminator body h_term h_root
          · simp only [h_eq]
            rfl

/-! ## 4. Pure Execution Predicates (`wpPureMirExec`, `PureMirConverges`) & Soundness -/

/--
Pure operand evaluation on an alias-erased local slot environment `env`
(referencing no `Memory` state).
-/
def evalPureOperand
    (env : List SlotState)
    (op : Operand)
    (layouts : LayoutTable := emptyLayoutTable) : PlaceReadResult :=
  evalOperand env op [] [] layouts []

/--
Pure operand-list evaluation on an alias-erased local slot environment `env`
(referencing no `Memory` state).
-/
def evalPureOperands
    (env : List SlotState)
    (ops : List Operand)
    (layouts : LayoutTable := emptyLayoutTable) : OperandsEvalResult :=
  evalOperands env ops [] [] layouts []

/--
Pure place write on an alias-erased local slot environment `env` (referencing
no `BorrowEntry` table).
-/
def writePurePlaceValue
    (env : List SlotState)
    (dst : Place)
    (val : Value) : PlaceWriteResult :=
  writePlaceValue env [] dst val

/--
Fuel-bounded symbolic weakest precondition over alias-erased `PureState`
(`mirNormalPost`: requires normal return satisfying `post retVal` and forbids
UB, panics, and aborts).
-/
def wpPureMirExec
    (fuel : Nat) (body : CapturedMir) (ps : PureState)
    (post : Value → Prop) : Prop :=
  wpMirExecSym fuel body (.running (ps.toMachineState emptyMemory))
    (mirNormalPost (fun retVal _ => post retVal))

/--
Fuel-bounded partial-correctness symbolic weakest precondition over `PureState`
(`mirSafePost`: forbids UB; if execution returns normally with `retVal`, then
`post retVal` holds).
-/
def wpPureMirSafeExec
    (fuel : Nat) (body : CapturedMir) (ps : PureState)
    (post : Value → Prop) : Prop :=
  wpMirExecSym fuel body (.running (ps.toMachineState emptyMemory))
    (mirSafePost (fun retVal _ => post retVal))

/--
Fuel-bounded state-to-state symbolic stepper over `PureState`.
-/
def wpPureMirSteps
    (fuel : Nat) (body : CapturedMir) (ps : PureState)
    (mid : PureState → Prop)
    (post : Value → Prop := fun _ => False) : Prop :=
  wpMirStepsSym fuel body (ps.toMachineState emptyMemory)
    (fun ms' => mid (PureState.ofMachineState ms'))
    (mirNormalPost (fun retVal _ => post retVal))

/--
Fuel-free total-correctness convergence over alias-erased `PureState`.
-/
def PureMirConverges
    (body : CapturedMir) (ps : PureState) (post : Value → Prop) : Prop :=
  ∃ fuel : Nat, wpPureMirExec fuel body ps post

/--
Fuel-free partial-correctness (`mirSafePost`) convergence over alias-erased
`PureState`.
-/
def PureMirSafeConverges
    (body : CapturedMir) (ps : PureState) (post : Value → Prop) : Prop :=
  ∃ fuel : Nat, wpPureMirSafeExec fuel body ps post

/--
Fuel-free intermediate state convergence over alias-erased `PureState`.
-/
def PureMirStepsConverges
    (body : CapturedMir) (ps : PureState)
    (mid : PureState → Prop)
    (post : Value → Prop := fun _ => False) : Prop :=
  ∃ fuel : Nat, wpPureMirSteps fuel body ps mid post

/-- Postcondition monotonicity for `PureMirConverges`. -/
theorem PureMirConverges.mono
    {body : CapturedMir} {ps : PureState} {P Q : Value → Prop}
    (h_imp : ∀ v, P v → Q v)
    (h : PureMirConverges body ps P) :
    PureMirConverges body ps Q := by
  rcases h with ⟨fuel, h_wp⟩
  refine ⟨fuel, wpMirExecSym_mono_post ?_ h_wp⟩
  intro out h_out
  cases out with
  | normal rv => exact h_imp rv.1 h_out
  | panic => exact False.elim h_out
  | abort => exact False.elim h_out

/-- Every `PureMirConverges` proof implies `PureMirSafeConverges`. -/
theorem PureMirSafeConverges.of_pureMirConverges
    {body : CapturedMir} {ps : PureState} {post : Value → Prop}
    (h : PureMirConverges body ps post) :
    PureMirSafeConverges body ps post := by
  rcases h with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_mono_post (fun _ => mirNormalPost_imp_mirSafePost) h_wp⟩

/-- Postcondition monotonicity for `PureMirSafeConverges`. -/
theorem PureMirSafeConverges.mono
    {body : CapturedMir} {ps : PureState} {P Q : Value → Prop}
    (h_imp : ∀ v, P v → Q v)
    (h : PureMirSafeConverges body ps P) :
    PureMirSafeConverges body ps Q := by
  rcases h with ⟨fuel, h_wp⟩
  refine ⟨fuel, wpMirExecSym_mono_post ?_ h_wp⟩
  intro out h_out
  cases out with
  | normal rv => exact h_imp rv.1 h_out
  | panic => trivial
  | abort => trivial

/-- Zero-step reflexivity for `PureMirStepsConverges`. -/
theorem PureMirStepsConverges.refl
    {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h : mid ps) :
    PureMirStepsConverges body ps mid post :=
  ⟨0, h⟩

/-- Root-active memory witness for `emptyMemory`. -/
@[simp]
theorem rootActiveMemory_emptyMemory : RootActiveMemory emptyMemory :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Fuel-free sequential composition (`PureMirConverges.bind`) over `PureState`. -/
theorem PureMirConverges.bind
    {body : CapturedMir} {ps : PureState}
    {mid : PureState → Prop} {post : Value → Prop}
    (h₁ : PureMirStepsConverges body ps mid post)
    (h₂ : ∀ ps', mid ps' → PureMirConverges body ps' post)
    (h_pure : checkPureMir body = true) :
    PureMirConverges body ps post := by
  rcases h₁ with ⟨f₁, hf₁⟩
  have h_steps :
      MirStepsConverges body (ps.toMachineState emptyMemory)
        (fun ms' =>
          mid (PureState.ofMachineState ms') ∧
          ms' = (PureState.ofMachineState ms').toMachineState emptyMemory)
        (mirNormalPost (fun retVal _ => post retVal)) := by
    suffices ∀ (f : Nat) (st : MirExecState),
        wpMirExecStepsSym f body (MirExecState.withMem emptyMemory st)
          (fun
            | .running s' => mid (PureState.ofMachineState s')
            | .halted out => mirNormalPost (fun retVal _ => post retVal) out
            | .faulted _ => False)
          (mirNormalPost (fun retVal _ => post retVal)) →
        wpMirExecStepsSym f body (MirExecState.withMem emptyMemory st)
          (fun
            | .running s' =>
              mid (PureState.ofMachineState s') ∧
              s' = (PureState.ofMachineState s').toMachineState emptyMemory
            | .halted out => mirNormalPost (fun retVal _ => post retVal) out
            | .faulted _ => False)
          (mirNormalPost (fun retVal _ => post retVal)) from
      ⟨f₁, this f₁ (.running (ps.toMachineState emptyMemory)) hf₁⟩
    intro f
    induction f with
    | zero =>
      intro st h_st
      cases st with
      | running s' => exact ⟨h_st, rfl⟩
      | halted out => exact h_st
      | faulted _ => exact False.elim h_st
    | succ f' ih =>
      intro st h_st
      cases st with
      | halted out =>
        unfold wpMirExecStepsSym at h_st ⊢
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
        cases out with
        | normal retPair => exact h_st
        | panic => exact h_st
        | abort => exact h_st
      | faulted fk =>
        unfold wpMirExecStepsSym at h_st
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st
        exact False.elim h_st
      | running s =>
        unfold wpMirExecStepsSym at h_st ⊢
        rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
        dsimp only [MirExecState.withMem, stepMirState] at h_st ⊢
        have h_eq :=
          stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
            (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
        dsimp only [PureState.toMachineState_ofMachineState] at h_eq
        rw [h_eq] at h_st ⊢
        cases h_step : stepMirFn body { s with memory := emptyMemory } with
        | ret out =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          exact h_st
        | tau st' =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          exact ih st' h_st
        | vis i k =>
          rw [h_step] at h_st
          dsimp only [MirStepNode.withMem] at h_st
          cases i with
          | inl _ => exact False.elim h_st
          | inr i2 => cases i2 with
            | inl _ => exact ih (k PUnit.unit) h_st
            | inr _ => exact False.elim h_st
  exact MirWpConverges.bind h_steps (fun ms' ⟨h_mid, h_eq⟩ => by
    rw [h_eq]
    exact h₂ (PureState.ofMachineState ms') h_mid)

/--
Core inductive simulation theorem lifting `wpMirExecSym` from `emptyMemory` to
any `mem₀ : Memory` satisfying `RootActiveMemory mem₀`.
-/
theorem wpMirExecSym_withMem_of_emptyMemory
    {fuel : Nat} {body : CapturedMir} {mem₀ : Memory} (st : MirExecState)
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀)
    (h_wp :
      wpMirExecSym fuel body (MirExecState.withMem emptyMemory st)
        (mirNormalPost (fun retVal _ => post retVal))) :
    wpMirExecSym fuel body (MirExecState.withMem mem₀ st)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecSym at h_wp ⊢
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h_wp ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeWP] at h_wp ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_wp⟩
      | panic => exact False.elim h_wp
      | abort => exact False.elim h_wp
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeWP] at h_wp
      exact False.elim h_wp
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_wp ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_wp
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_wp⟩
        | panic => trivial
        | abort => trivial
      | tau st' =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        exact ih st' h_wp
      | vis i k =>
        rw [h_step] at h_wp
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp
          exact False.elim h_wp
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            exact ih (k PUnit.unit) h_wp
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            intro ans
            exact ih (k ans) (h_wp ans)

/--
Core inductive simulation theorem for `mirSafePost` lifting `wpMirExecSym` from
`emptyMemory` to any `mem₀ : Memory` satisfying `RootActiveMemory mem₀`.
-/
theorem wpMirExecSym_safe_withMem_of_emptyMemory
    {fuel : Nat} {body : CapturedMir} {mem₀ : Memory} (st : MirExecState)
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀)
    (h_wp :
      wpMirExecSym fuel body (MirExecState.withMem emptyMemory st)
        (mirSafePost (fun retVal _ => post retVal))) :
    wpMirExecSym fuel body (MirExecState.withMem mem₀ st)
      (mirSafePost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecSym at h_wp ⊢
    rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h_wp ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeWP] at h_wp ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_wp⟩
      | panic => trivial
      | abort => trivial
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeWP] at h_wp
      exact False.elim h_wp
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_wp ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_wp
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_wp⟩
        | panic => trivial
        | abort => trivial
      | tau st' =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
        exact ih st' h_wp
      | vis i k =>
        rw [h_step] at h_wp
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp
          exact False.elim h_wp
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            exact ih (k PUnit.unit) h_wp
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeWP] at h_wp ⊢
            intro ans
            exact ih (k ans) (h_wp ans)

/--
Core inductive simulation theorem for call-forbidding `wpMirExecNoCallSym`
lifting from `emptyMemory` to `mem₀`.
-/
theorem wpMirExecNoCallSym_withMem_of_emptyMemory
    {fuel : Nat} {body : CapturedMir} {mem₀ : Memory} (st : MirExecState)
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_root : RootActiveMemory mem₀)
    (h_wp :
      wpMirExecNoCallSym fuel body (MirExecState.withMem emptyMemory st)
        (mirNormalPost (fun retVal _ => post retVal))) :
    wpMirExecNoCallSym fuel body (MirExecState.withMem mem₀ st)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  induction fuel generalizing st with
  | zero => exact False.elim h_wp
  | succ fuel' ih =>
    unfold wpMirExecNoCallSym at h_wp ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_wp ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeNoCallWP] at h_wp ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_wp⟩
      | panic => exact False.elim h_wp
      | abort => exact False.elim h_wp
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeNoCallWP] at h_wp
      exact False.elim h_wp
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_wp ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_wp
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_wp⟩
        | panic => exact False.elim h_wp
        | abort => exact False.elim h_wp
      | tau st' =>
        rw [h_step] at h_wp
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp ⊢
        exact ih st' h_wp
      | vis i k =>
        rw [h_step] at h_wp
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp
          exact False.elim h_wp
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp ⊢
            exact ih (k PUnit.unit) h_wp
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_wp
            exact False.elim h_wp

/--
Simulation theorem from any intermediate `(ps, ms)` satisfying
`MirFrameSim body mem₀ ps ms`: `PureMirConverges body ps post` implies
`MirWpConverges body ms (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal))`.
-/
theorem mirWpConverges_of_pureExec_sim
    {body : CapturedMir} {ps : PureState} {ms : MachineState}
    {post : Value → Prop} {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_sim : MirFrameSim body mem₀ ps ms)
    (h_conv : PureMirConverges body ps post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body ms
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  have h_ms := (mirFrameSim_iff_eq_toMachineState body mem₀ ps ms).mp h_sim
  subst h_ms
  rcases h_conv with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_withMem_of_emptyMemory
    (.running (ps.toMachineState emptyMemory)) h_pure h_root h_wp⟩

/--
Once-and-for-All Tier 1 Alias-Erasure Theorem (`mirWpConverges_of_pureExec`):
Whenever `checkPureMir body = true` and
`PureMirConverges body (initPureState body args) post`, the full stateful
machine state `initMachineStateWithMemory body args mem₀` converges
(`MirWpConverges`) to `mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)`
for any root-active `mem₀ : Memory` (discharged automatically for concrete
initial memories and local `RootActiveMemory` hypotheses).
-/
theorem mirWpConverges_of_pureExec
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) :=
  mirWpConverges_of_pureExec_sim h_pure
    (mirFrameSim_initMachineStateWithMemory body args mem₀)
    h_conv
    h_root

/--
Specialization of `mirWpConverges_of_pureExec` to `initMachineState body args`
(where `RootActiveMemory` holds definitionally by `rfl`).
-/
theorem mirWpConverges_of_pureExec_init
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post) :
    MirWpConverges body (initMachineState body args)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = (initMachineState body args).memory ∧ post retVal)) :=
  mirWpConverges_of_pureExec h_pure h_conv (h_root := ⟨rfl, rfl, rfl, rfl, rfl⟩)

/--
Specialization of `mirWpConverges_of_pureExec` to
`initMachineStateWithCallees body args callees`, preserving the populated
callee table `callees` in `(initMachineStateWithCallees body args callees).memory`.
-/
theorem mirWpConverges_of_pureExec_withCallees
    {body : CapturedMir} {args : List Value} {callees : List CapturedMir}
    {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post) :
    MirWpConverges body (initMachineStateWithCallees body args callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = (initMachineStateWithCallees body args callees).memory ∧
          post retVal)) := by
  have h := mirWpConverges_of_pureExec
    (mem₀ := (initMachineStateWithCallees body args callees).memory)
    h_pure h_conv (rootActiveMemory_initMachineStateWithCallees body args callees)
  rwa [← initMachineStateWithCallees_eq_withMemory] at h

/--
Specialization of `mirWpConverges_of_pureExec` to
`initMachineStateWithMemoryAndCallees body args mem₀ callees`, preserving
`Memory.withDefaultCallees mem₀ callees` across arbitrary `mem₀` and `callees`.
-/
theorem mirWpConverges_of_pureExec_withMemoryAndCallees
    {body : CapturedMir} {args : List Value} {mem₀ : Memory}
    {callees : List CapturedMir} {post : Value → Prop}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body
      (MirFuelFree.initMachineStateWithMemoryAndCallees body args mem₀ callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = MirFuelFree.Memory.withDefaultCallees mem₀ callees ∧ post retVal)) :=
  mirWpConverges_of_pureExec h_pure h_conv (h_root := ((rootActiveMemory_withDefaultCallees mem₀ callees).mpr h_root))

/--
Call-forbidding (`MirNoCallWpConverges`) alias-erasure theorem from
`PureMirConverges`.
-/
theorem mirNoCallWpConverges_of_pureExec
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirNoCallWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  rcases h_conv with ⟨fuel, h_wp⟩
  have h_nc :
      wpMirExecNoCallSym fuel body
        (MirExecState.withMem emptyMemory
          (.running ((initPureState body args).toMachineState emptyMemory)))
        (mirNormalPost (fun retVal _ => post retVal)) := by
    suffices ∀ (f : Nat) (st : MirExecState),
        wpMirExecSym f body (MirExecState.withMem emptyMemory st)
          (mirNormalPost (fun retVal _ => post retVal)) →
        wpMirExecNoCallSym f body (MirExecState.withMem emptyMemory st)
          (mirNormalPost (fun retVal _ => post retVal)) from
      this fuel (.running ((initPureState body args).toMachineState emptyMemory)) h_wp
    intro f
    induction f with
    | zero =>
      intro st h_st
      exact False.elim h_st
    | succ f' ih =>
      intro st h_st
      unfold wpMirExecSym at h_st
      unfold wpMirExecNoCallSym
      rw [evalSymNodeTree_eq, stepMirExecSymTree_eval, evalNodeWP_eq] at h_st
      rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq]
      cases st with
      | halted out => exact h_st
      | faulted fk => exact False.elim h_st
      | running s =>
        dsimp only [MirExecState.withMem, stepMirState] at h_st ⊢
        have h_emp :=
          stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
            (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
        dsimp only [PureState.toMachineState_ofMachineState] at h_emp
        rw [h_emp] at h_st ⊢
        cases h_step : stepMirFn body { s with memory := emptyMemory } with
        | ret out =>
          rw [h_step] at h_st
          exact h_st
        | tau st' =>
          rw [h_step] at h_st
          exact ih st' h_st
        | vis i k =>
          rw [h_step] at h_st
          cases i with
          | inl _ => exact False.elim h_st
          | inr i2 => cases i2 with
            | inl _ => exact ih (k PUnit.unit) h_st
            | inr _ =>
              exfalso
              have h_ac : ({ s with memory := emptyMemory } : MachineState).memory.activeCallee = none := rfl
              unfold stepMirFn at h_step
              rw [h_ac] at h_step
              dsimp only [Option.getD] at h_step
              cases h_ph : body.phase with
              | other _ =>
                rw [h_ph] at h_step
                cases h_step
              | _ =>
                all_goals
                  rw [h_ph] at h_step
                  dsimp only at h_step
                cases h_bb : Trusted.Sequence.get? body.basicBlocks (s.frame.blockIdx : Nat) with
                | none =>
                  rw [h_bb] at h_step
                  cases h_step
                | some bb =>
                  rw [h_bb] at h_step
                  dsimp only at h_step
                  have ⟨h_stmts, h_term⟩ := checkPureMir_block h_pure h_bb
                  cases h_stmt : get? bb.statements (s.frame.stmtIdx : Nat) with
                  | some stmt =>
                    rw [h_stmt] at h_step
                    dsimp only at h_step
                    have h_s := list_all_of_get? h_stmts h_stmt
                    rcases stmt with ⟨skind, sspan⟩
                    cases skind with
                    | nop | coverage | constEvalCounter =>
                      dsimp only [evalStmt] at h_step; cases h_step
                    | backwardIncompatibleDropHint _ | retag _ _ =>
                      exact False.elim (Bool.false_ne_true h_s)
                    | storageLive loc =>
                      dsimp only [evalStmt, emptyMemory] at h_step
                      cases h1 : get? s.frame.locals loc <;> rw [h1] at h_step
                      · cases h_step
                      · rename_i sl; cases sl <;> dsimp only at h_step <;>
                          (try cases h_step) <;>
                          (cases h2 : set? s.frame.locals loc .uninit <;> rw [h2] at h_step <;> cases h_step)
                    | storageDead loc =>
                      dsimp only [evalStmt, emptyMemory] at h_step
                      cases h1 : get? s.frame.locals loc <;> rw [h1] at h_step
                      · cases h_step
                      · rename_i sl; cases sl <;> dsimp only at h_step <;>
                          (try cases h_step) <;>
                          (cases h2 : set? s.frame.locals loc .dead <;> rw [h2] at h_step <;> cases h_step)
                    | placeMention p =>
                      dsimp only [evalStmt] at h_step
                      repeat' (first | cases h_step | split at h_step)
                    | deinit p =>
                      rw [evalStmt_deinit_borrows_nil (s := { s with memory := emptyMemory }) rfl
                        (isPurePlace_nil_or_strip_ne_nil (p := p) h_s)] at h_step
                      unfold evalDeinitBorrowsNil at h_step
                      rcases p with ⟨loc, _ | ⟨phd, ptl⟩⟩
                      · dsimp only at h_step
                        cases h1 : get? s.frame.locals loc with
                        | none => rw [h1] at h_step; cases h_step
                        | some sl =>
                          rw [h1] at h_step
                          cases sl with
                          | dead => cases h_step
                          | uninit | init _ =>
                            dsimp only at h_step
                            cases h2 : set? s.frame.locals loc .uninit <;> rw [h2] at h_step <;> cases h_step
                      · dsimp only at h_step
                        cases h1 : get? s.frame.locals loc with
                        | none => rw [h1] at h_step; cases h_step
                        | some sl =>
                          rw [h1] at h_step
                          cases sl with
                          | dead => cases h_step
                          | uninit =>
                            dsimp only at h_step
                            cases h2 : deinitTailOk s.frame.locals body.localDecls body.layouts
                                (placeTy body.localDecls body.layouts { local_ := loc, projection := .nil })
                                (phd :: ptl) <;> rw [h2] at h_step
                            · dsimp only at h_step
                              cases h3 : projectionHasDeref (phd :: ptl) <;> rw [h3] at h_step <;> cases h_step
                            · cases h_step
                          | init rv =>
                            dsimp only at h_step
                            cases h2 : deinitProjectedForLocal s.frame.locals body.localDecls body.layouts loc rv (phd :: ptl) <;>
                                rw [h2] at h_step
                            · dsimp only at h_step
                              cases h3 : set? s.frame.locals loc _ <;> rw [h3] at h_step <;> cases h_step
                            · cases h_step
                            · cases h_step
                    | intrinsic i =>
                      cases i with
                      | copyNonOverlapping _ _ _ => exact False.elim (Bool.false_ne_true h_s)
                      | assume op =>
                        dsimp only [evalStmt] at h_step
                        cases h1 : evalOperand s.frame.locals op _ _ _ _ _ _ <;> rw [h1] at h_step
                        · rename_i v _; cases v <;> try dsimp only at h_step
                          · cases h_step
                          · rename_i sc
                            cases h2 : Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) <;>
                              rw [h2] at h_step <;> cases h_step
                          · cases h_step
                          · cases h_step
                          · cases h_step
                        · cases h_step
                        · cases h_step
                    | setDiscriminant p vi =>
                      simp only [isPureStatement] at h_s
                      rcases p with ⟨loc, _ | ⟨phd, ptl⟩⟩
                      · dsimp only [evalStmt, evalSetDiscriminantLocal, emptyMemory] at h_step
                        cases h1 : get? s.frame.locals loc with
                        | none => rw [h1] at h_step; cases h_step
                        | some sl =>
                          rw [h1] at h_step
                          cases sl with
                          | dead => cases h_step
                          | uninit =>
                            dsimp only at h_step
                            cases h2 : setDiscriminantUninitDeclOk body.localDecls loc <;> rw [h2] at h_step
                            · cases h_step
                            · dsimp only at h_step
                              cases h3 : setDiscriminantUninitPayload? body.localDecls body.layouts loc vi <;>
                                  rw [h3] at h_step
                              · cases h_step
                              · dsimp only at h_step
                                cases h4 : set? s.frame.locals loc _ <;> rw [h4] at h_step <;> cases h_step
                          | init rv =>
                            cases rv with
                            | aggregate _ fields =>
                              dsimp only at h_step
                              cases h2 : padSetDiscriminantInitFields? body.localDecls body.layouts ⟨loc, .nil⟩ vi fields <;>
                                  rw [h2] at h_step
                              · cases h_step
                              · dsimp only at h_step
                                cases h3 : set? s.frame.locals loc _ <;> rw [h3] at h_step <;> cases h_step
                            | _ => cases h_step
                      · simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_s
                        have h_nd := ne_deref_of_isPureProjElem h_s.1
                        rw [evalStmt_setDiscriminant_nonDeref _ _ _ _ _ _ _ _ h_nd
                          (stripLeadingOpaqueCast_cons_ne_nil_of_isPureProjElem h_s.1)] at h_step
                        dsimp only [emptyMemory] at h_step
                        cases h1 : evalOperand s.frame.locals _ _ _ _ _ _ _ <;> rw [h1] at h_step
                        · rename_i rv _
                          cases rv with
                          | aggregate _ fields =>
                            dsimp only at h_step
                            cases h2 : padSetDiscriminantInitFields? body.localDecls body.layouts _ vi fields <;>
                                rw [h2] at h_step
                            · cases h_step
                            · dsimp only at h_step
                              cases h3 : writePlaceValue _ _ _ _ _ _ _ <;> rw [h3] at h_step <;> cases h_step
                          | _ => cases h_step
                        · cases h_step
                        · cases h_step
                    | assign dst rv =>
                      simp only [isPureStatement, Bool.and_eq_true] at h_s
                      rw [evalStmt_assign_eq] at h_step
                      cases h1 : evalRvalue s.frame.locals rv emptyMemory body.localDecls body.layouts <;>
                          rw [h1] at h_step
                      · dsimp only at h_step
                        rcases dst with ⟨dLoc, _ | ⟨dhd, dtl⟩⟩
                        · unfold evalAssignDst at h_step; dsimp only at h_step
                          repeat' (first | cases h_step | split at h_step)
                        · have h_dst := h_s.1
                          simp only [isPurePlace, List.all_cons, Bool.and_eq_true] at h_dst
                          have h_nd := ne_deref_of_isPureProjElem h_dst.1
                          rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_nd
                            (stripLeadingOpaqueCast_cons_ne_nil_of_isPureProjElem h_dst.1)] at h_step
                          unfold evalAssignNonDeref at h_step; dsimp only at h_step
                          repeat' (first | cases h_step | split at h_step)
                      · cases h_step
                      · cases h_step
                  | none =>
                    rw [h_stmt] at h_step
                    dsimp only at h_step
                    split at h_step
                    · rcases bb with ⟨_, ⟨tkind, tspan⟩, _⟩
                      cases tkind with
                      | drop p target _ =>
                        rw [evalTerminator_drop_borrows_nil (s := { s with memory := emptyMemory }) rfl
                          (isPurePlace_nil_or_strip_ne_nil (p := p) h_term)] at h_step
                        unfold evalDropBorrowsNil at h_step
                        dsimp only at h_step
                        cases h1 : get? s.frame.locals p.local_ with
                        | none => rw [h1] at h_step; cases h_step
                        | some sl =>
                          rw [h1] at h_step
                          cases sl with
                          | dead => cases h_step
                          | uninit =>
                            dsimp only at h_step
                            cases h2 : p.projection with
                            | nil =>
                              rw [h2] at h_step; dsimp only at h_step
                              cases h3 : set? s.frame.locals p.local_ .uninit <;> rw [h3] at h_step <;> cases h_step
                            | cons phd ptl =>
                              rw [h2] at h_step; dsimp only at h_step
                              cases h3 : deinitTailOk s.frame.locals _ _ _ (phd :: ptl) <;> rw [h3] at h_step
                              · dsimp only at h_step
                                cases h4 : projectionHasDeref (phd :: ptl) <;> rw [h4] at h_step <;> cases h_step
                              · cases h_step
                          | init rv =>
                            dsimp only at h_step
                            cases h2 : p.projection with
                            | nil =>
                              rw [h2] at h_step; dsimp only at h_step
                              cases h3 : set? s.frame.locals p.local_ .uninit <;> rw [h3] at h_step <;> cases h_step
                            | cons phd ptl =>
                              rw [h2] at h_step; dsimp only at h_step
                              cases h3 : deinitProjectedForLocal s.frame.locals _ _ p.local_ rv (phd :: ptl) <;>
                                  rw [h3] at h_step
                              · dsimp only at h_step
                                cases h4 : set? s.frame.locals p.local_ _ <;> rw [h4] at h_step <;> cases h_step
                              · cases h_step
                              · cases h_step
                      | _ =>
                        first
                        | exact False.elim (Bool.false_ne_true h_term)
                        | (dsimp only [evalTerminator] at h_step
                           repeat' (first | cases h_step | split at h_step))
                    · cases h_step
  exact ⟨fuel, wpMirExecNoCallSym_withMem_of_emptyMemory
    (.running ((initPureState body args).toMachineState emptyMemory))
    h_pure h_root h_nc⟩

/--
Partial-correctness (`mirSafePost`) alias-erasure theorem from
`PureMirSafeConverges`.
-/
theorem mirSafeWpConverges_of_pureExec
    {body : CapturedMir} {args : List Value} {post : Value → Prop}
    {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_conv : PureMirSafeConverges body (initPureState body args) post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirWpConverges body (initMachineStateWithMemory body args mem₀)
      (mirSafePost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  rcases h_conv with ⟨fuel, h_wp⟩
  exact ⟨fuel, wpMirExecSym_safe_withMem_of_emptyMemory
    (.running ((initPureState body args).toMachineState emptyMemory))
    h_pure h_root h_wp⟩

/--
Intermediate state-to-state simulation lifting `PureMirStepsConverges` to
`MirStepsConverges` while preserving `MirFrameSim body mem₀ ps' ms'`.
-/
theorem mirStepsConverges_of_pureExec_sim
    {body : CapturedMir} {ps : PureState} {ms : MachineState}
    {mid : PureState → Prop} {post : Value → Prop} {mem₀ : Memory}
    (h_pure : checkPureMir body = true)
    (h_sim : MirFrameSim body mem₀ ps ms)
    (h_steps : PureMirStepsConverges body ps mid post)
    (h_root : RootActiveMemory mem₀ := by
      first
      | assumption
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [RootActiveMemory])) :
    MirStepsConverges body ms
      (fun ms' =>
        ∃ ps' : PureState, mid ps' ∧ MirFrameSim body mem₀ ps' ms')
      (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) := by
  have h_ms := (mirFrameSim_iff_eq_toMachineState body mem₀ ps ms).mp h_sim
  subst h_ms
  rcases h_steps with ⟨fuel, h_wp⟩
  refine ⟨fuel, ?_⟩
  suffices ∀ st : MirExecState,
      wpMirExecStepsSym fuel body (MirExecState.withMem emptyMemory st)
        (fun
          | .running s' => mid (PureState.ofMachineState s')
          | .halted out => mirNormalPost (fun retVal _ => post retVal) out
          | .faulted _ => False)
        (mirNormalPost (fun retVal _ => post retVal)) →
      wpMirExecStepsSym fuel body (MirExecState.withMem mem₀ st)
        (fun
          | .running ms' =>
            ∃ ps' : PureState, mid ps' ∧ MirFrameSim body mem₀ ps' ms'
          | .halted out =>
            mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal) out
          | .faulted _ => False)
        (mirNormalPost (fun retVal mem' => mem' = mem₀ ∧ post retVal)) from
    this (.running (ps.toMachineState emptyMemory)) h_wp
  clear h_wp
  induction fuel with
  | zero =>
    intro st h_st
    cases st with
    | running s' =>
      exact ⟨PureState.ofMachineState s', h_st, ⟨rfl, rfl, rfl, rfl⟩⟩
    | halted out =>
      cases out with
      | normal retPair => exact ⟨rfl, h_st⟩
      | panic => exact False.elim h_st
      | abort => exact False.elim h_st
    | faulted _ => exact False.elim h_st
  | succ fuel' ih =>
    intro st h_st
    unfold wpMirExecStepsSym at h_st ⊢
    rw [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval, evalNodeNoCallWP_eq] at h_st ⊢
    cases st with
    | halted out =>
      dsimp only [MirExecState.withMem, stepMirState, evalNodeNoCallWP] at h_st ⊢
      cases out with
      | normal retPair => exact ⟨rfl, h_st⟩
      | panic => exact False.elim h_st
      | abort => exact False.elim h_st
    | faulted fk =>
      dsimp only [MirExecState.withMem, stepMirState, MirStepNode.fail, evalNodeNoCallWP] at h_st
      exact False.elim h_st
    | running s =>
      dsimp only [MirExecState.withMem, stepMirState] at h_st ⊢
      have h_emp :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := emptyMemory)
          (PureState.ofMachineState s) h_pure rootActiveMemory_emptyMemory
      have h_mem :=
        stepMirFn_toMachineState_eq_withMem (mem₀ := mem₀)
          (PureState.ofMachineState s) h_pure h_root
      dsimp only [PureState.toMachineState_ofMachineState] at h_emp h_mem
      rw [h_emp] at h_st
      rw [h_mem]
      cases h_step : stepMirFn body { s with memory := emptyMemory } with
      | ret out =>
        rw [h_step] at h_st
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st ⊢
        cases out with
        | normal retPair => exact ⟨rfl, h_st⟩
        | panic => exact False.elim h_st
        | abort => exact False.elim h_st
      | tau st' =>
        rw [h_step] at h_st
        dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st ⊢
        exact ih st' h_st
      | vis i k =>
        rw [h_step] at h_st
        cases i with
        | inl fk =>
          dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st
          exact False.elim h_st
        | inr i2 => cases i2 with
          | inl obs =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st ⊢
            exact ih (k PUnit.unit) h_st
          | inr req =>
            dsimp only [MirStepNode.withMem, evalNodeNoCallWP] at h_st
            exact False.elim h_st

/-! ## 5. Verification Gate Bridges (`VerificationResult`, `StatefulVerificationResult`, `TotalVerificationResult`) -/

/--
The trusted callee-aware stateful initial state is `initMachineStateWithMemory`
over its own initial memory, which seeds `Memory.callees` and
`Memory.traitImpls` only when the callee table is non-empty.
-/
theorem trustedInitWithMemoryAndCallees_eq_withMemory
    (body : CapturedMir) (args : List Value) (mem : Memory)
    (callees : List CapturedMir) :
    Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body args mem callees =
      initMachineStateWithMemory body args
        (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          body args mem callees).memory :=
  rfl

/--
Seeding the callee and trait-implementation tables preserves
`RootActiveMemory`: neither table is a root-activation field.
-/
theorem rootActiveMemory_trustedInitWithMemoryAndCallees
    {body : CapturedMir} {args : List Value} {mem : Memory}
    {callees : List CapturedMir}
    (h_root : RootActiveMemory mem) :
    RootActiveMemory
      (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
        body args mem callees).memory := by
  cases callees with
  | nil => exact h_root
  | cons _ _ => exact h_root

section ConstructiveVerificationResult

open Trusted.ITree
open Anneal.EffectWP
open Anneal.ITreeWP
open Anneal.Rustc.V2026_06_01.Lower

/--
Constructive all-prefix fault-freedom (`¬ FaultNow`) from `wpCoalBounded` over
`stepMirState body` (avoiding `Classical.choice` from `DWLP` coinduction).
-/
theorem not_faultNow_of_wpCoalBounded
    (body : CapturedMir) (post : MirOutcome → Prop) :
    ∀ (fuel : Nat) (st : MirExecState),
      wpCoalBounded fuel mirDefaultWP (stepMirState body) (fun out _ => post out) st PUnit.unit →
      ¬ FaultNow (ITree.cofix (stepMirState body) st)
  | 0, _, h_wp => False.elim h_wp
  | fuel' + 1, st, h_wp => by
    unfold wpCoalBounded at h_wp
    rintro ⟨t', i, k, h_tau, h_vis, h_fault⟩
    cases h_tau with
    | refl =>
      rw [ITree.observe_cofix] at h_vis
      cases h_step : stepMirState body st with
      | ret out =>
        rw [h_step] at h_vis
        nomatch h_vis
      | tau st' =>
        rw [h_step] at h_vis
        nomatch h_vis
      | vis i₀ k₀ =>
        rw [h_step] at h_wp h_vis
        dsimp [ITreeF.map] at h_vis
        injection h_vis with h_i _
        subst h_i
        cases i₀ with
        | inl fk =>
          cases fk <;> exact h_wp
        | inr i₂ =>
          cases i₂ with
          | inl _ => exact h_fault
          | inr _ => exact h_fault
    | @step _ t₁ _ h_obs h_tau' =>
      rw [ITree.observe_cofix] at h_obs
      cases h_step : stepMirState body st with
      | ret out =>
        rw [h_step] at h_obs
        nomatch h_obs
      | tau st' =>
        rw [h_step] at h_wp h_obs
        dsimp [ITreeF.map] at h_obs
        injection h_obs with h_t₁
        subst h_t₁
        exact not_faultNow_of_wpCoalBounded body post fuel' st' h_wp ⟨t', i, k, h_tau', h_vis, h_fault⟩
      | vis _ _ =>
        rw [h_step] at h_obs
        nomatch h_obs

/--
Constructive preservation of `wpCoalBounded` along finite labeled `Reaches`
transitions on `ITree.cofix (stepMirState body) st`.
-/
theorem reaches_wpCoalBounded
    (body : CapturedMir) (post : MirOutcome → Prop)
    {t u : ITree MirEffect MirOutcome} {tr : List (Event MirEffect)}
    (h_reach : Reaches t tr u) :
    ∀ (fuel : Nat) (st : MirExecState),
      t = ITree.cofix (stepMirState body) st →
      wpCoalBounded fuel mirDefaultWP (stepMirState body) (fun out _ => post out) st PUnit.unit →
      ∃ (fuel' : Nat) (st' : MirExecState),
        u = ITree.cofix (stepMirState body) st' ∧
        wpCoalBounded fuel' mirDefaultWP (stepMirState body) (fun out _ => post out) st' PUnit.unit := by
  induction h_reach with
  | refl t₀ =>
    intro fuel st h_eq h_wp
    exact ⟨fuel, st, h_eq, h_wp⟩
  | @tau t₀ t₁ u₀ tr₀ h_obs _ ih =>
    intro fuel st h_eq h_wp
    cases fuel with
    | zero => exact False.elim h_wp
    | succ fuel' =>
      subst h_eq
      rw [ITree.observe_cofix] at h_obs
      unfold wpCoalBounded at h_wp
      cases h_step : stepMirState body st with
      | ret _ => rw [h_step] at h_obs; nomatch h_obs
      | tau st' =>
        rw [h_step] at h_obs h_wp
        dsimp [ITreeF.map] at h_obs
        injection h_obs with h_t₁
        exact ih fuel' st' h_t₁.symm h_wp
      | vis _ _ => rw [h_step] at h_obs; nomatch h_obs
  | @vis t₀ u₀ i k tr₀ h_obs _ o _ ih =>
    intro fuel st h_eq h_wp
    cases fuel with
    | zero => exact False.elim h_wp
    | succ fuel' =>
      subst h_eq
      rw [ITree.observe_cofix] at h_obs
      unfold wpCoalBounded at h_wp
      cases h_step : stepMirState body st with
      | ret _ => rw [h_step] at h_obs; nomatch h_obs
      | tau _ => rw [h_step] at h_obs; nomatch h_obs
      | vis i₀ k₀ =>
        rw [h_step] at h_obs h_wp
        dsimp [ITreeF.map] at h_obs
        injection h_obs with h_i h_k
        subst h_i
        have h_ko : k o = ITree.cofix (stepMirState body) (k₀ o) := by
          have := congrFun (eq_of_heq h_k) o
          exact this.symm
        cases i₀ with
        | inl fk =>
          cases fk <;> exact False.elim h_wp
        | inr i₂ =>
          cases i₂ with
          | inl obs =>
            cases obs
            exact ih fuel' (k₀ o) h_ko h_wp
          | inr req =>
            cases req
            exact ih fuel' (k₀ o) h_ko (h_wp o)

/--
Constructive adequacy of `MirWpConverges` (`⊆ {propext, Quot.sound}`):
establishes `TreeSafe (mirTree body s)` and `ReachesRet (mirTree body s) tr out → post out`
by structural induction on `Reaches` and `TauStar` without `DWLP` coinduction.
-/
theorem treeSafe_and_ret_of_mirWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirWpConverges body s post) :
    TreeSafe (mirTree body s) ∧
      ∀ tr out, ReachesRet (mirTree body s) tr out → post out := by
  rcases h with ⟨fuel, h_sym⟩
  have h_wp : wpCoalBounded fuel mirDefaultWP (stepMirState body) (fun out _ => post out) (.running s) PUnit.unit := by
    rwa [← wpMirExecSym_eq_wpCoalBounded]
  refine ⟨?_, ?_⟩
  · intro tr u h_reach
    obtain ⟨f', st', rfl, h_wp'⟩ := reaches_wpCoalBounded body post h_reach fuel (.running s) rfl h_wp
    exact not_faultNow_of_wpCoalBounded body post f' st' h_wp'
  · rintro tr out ⟨u, h_reach, h_ret⟩
    obtain ⟨f', st', rfl, h_wp'⟩ := reaches_wpCoalBounded body post h_reach fuel (.running s) rfl h_wp
    cases f' with
    | zero => exact False.elim h_wp'
    | succ f'' =>
      unfold wpCoalBounded at h_wp'
      rw [ITree.observe_cofix] at h_ret
      cases h_step : stepMirState body st' with
      | ret out' =>
        rw [h_step] at h_ret h_wp'
        dsimp [ITreeF.map] at h_ret
        injection h_ret with h_out
        subst h_out
        exact h_wp'
      | tau _ => rw [h_step] at h_ret; nomatch h_ret
      | vis _ _ => rw [h_step] at h_ret; nomatch h_ret

end ConstructiveVerificationResult

/--
Discharge a stateless `VerificationResult c` from panic-forbidding pure
execution (`PureMirConverges`).
-/
theorem verifyMirNoPanic_of_pureExec
    (c : Claim)
    (h_pure : checkPureMir c.body = true)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        PureMirConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c := by
  refine ⟨fun args h_pre => ?_⟩
  have ⟨h_safe, h_ret⟩ :=
    treeSafe_and_ret_of_mirWpConverges
      (mirWpConverges_of_pureExec_withCallees (callees := c.callees) h_pure (h_wp args h_pre))
  exact ⟨h_safe, fun outPair h_r _ retVal mem' h_out => by
    have h_post := h_ret outPair.1 outPair.2 h_r
    rw [h_out] at h_post
    exact h_post.2⟩

/--
Discharge a stateless `VerificationResult c` from partial-correctness pure
execution (`PureMirSafeConverges`).
-/
theorem verifyMirSafe_of_pureExec
    (c : Claim)
    (h_pure : checkPureMir c.body = true)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        PureMirSafeConverges c.body (initPureState c.body args) (c.post args)) :
    VerificationResult c := by
  refine ⟨fun args h_pre => ?_⟩
  have h := mirSafeWpConverges_of_pureExec
    (mem₀ := (initMachineStateWithCallees c.body args c.callees).memory)
    h_pure (h_wp args h_pre)
    (rootActiveMemory_initMachineStateWithCallees c.body args c.callees)
  rw [← initMachineStateWithCallees_eq_withMemory] at h
  have ⟨h_safe, h_ret⟩ := treeSafe_and_ret_of_mirWpConverges h
  exact ⟨h_safe, fun outPair h_r _ retVal mem' h_out => by
    have h_post := h_ret outPair.1 outPair.2 h_r
    rw [h_out] at h_post
    exact h_post.2⟩

/-- Primary alias for stateless pure verification (`verifyMirNoPanic_of_pureExec`). -/
abbrev verifyMir_of_pureExec := @verifyMirNoPanic_of_pureExec

/--
Discharge a stateful `StatefulVerificationResult c` from panic-forbidding pure
execution (`PureMirConverges`), automatically supplying `mem' = mem` alongside
`post retVal` without any manual `Memory` destructuring.
-/
theorem verifyStatefulMirNoPanic_of_pureExec
    (c : StatefulClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConverges c.body (initPureState c.body args)
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)) :
    StatefulVerificationResult c := by
  refine ⟨fun args mem h_pre => ?_⟩
  have ⟨h_safe, h_ret⟩ :=
    treeSafe_and_ret_of_mirWpConverges
      (mirWpConverges_of_pureExec
        (mem₀ := (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees).memory)
        h_pure (h_wp args mem h_pre)
        (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre)))
  exact ⟨h_safe, fun outPair h_r _ retVal mem' h_out => by
    have h_post := h_ret outPair.1 outPair.2 h_r
    rw [h_out] at h_post
    rcases h_post with ⟨rfl, hp⟩
    exact hp⟩

/--
Discharge a stateful `StatefulVerificationResult c` from partial-correctness
pure execution (`PureMirSafeConverges`).
-/
theorem verifyStatefulMirSafe_of_pureExec
    (c : StatefulClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirSafeConverges c.body (initPureState c.body args)
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)) :
    StatefulVerificationResult c := by
  refine ⟨fun args mem h_pre => ?_⟩
  have ⟨h_safe, h_ret⟩ :=
    treeSafe_and_ret_of_mirWpConverges
      (mirSafeWpConverges_of_pureExec
        (mem₀ := (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
            c.body args mem c.callees).memory)
        h_pure (h_wp args mem h_pre)
        (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre)))
  exact ⟨h_safe, fun outPair h_r _ retVal mem' h_out => by
    have h_post := h_ret outPair.1 outPair.2 h_r
    rw [h_out] at h_post
    rcases h_post with ⟨rfl, hp⟩
    exact hp⟩

/-- Primary alias for stateful pure verification (`verifyStatefulMirNoPanic_of_pureExec`). -/
abbrev verifyStatefulMir_of_pureExec := @verifyStatefulMirNoPanic_of_pureExec

/--
Discharge a total-correctness `TotalVerificationResult c` from pure execution
(`PureMirConverges`).
-/
theorem verifyTotalMir_of_pureExec
    (c : TotalClaim)
    (h_pure : checkPureMir c.body = true)
    (h_root : ∀ args mem, c.pre args mem → RootActiveMemory mem)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        PureMirConverges c.body (initPureState c.body args)
          (fun retVal =>
            c.post args mem retVal
              (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
                c.body args mem c.callees).memory)) :
    TotalVerificationResult c := by
  refine verifyTotalMir_of_wpConverges c (fun args mem h_pre => ?_)
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases h_out with ⟨rfl, h_post⟩
        exact h_post
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec
      (mem₀ := (Trusted.VerificationResult.initMachineStateWithMemoryAndCallees
          c.body args mem c.callees).memory)
      h_pure (h_wp args mem h_pre)
      (rootActiveMemory_trustedInitWithMemoryAndCallees (h_root args mem h_pre)))

/--
Discharge `MirBoolPredicateHolds specBody args` from `PureMirConverges`.
-/
theorem mirBoolPredicateHolds_of_pureExec
    (specBody : CapturedMir) (args : List Value)
    (h_pure : checkPureMir specBody = true)
    (h_conv :
      PureMirConverges specBody (initPureState specBody args)
        (· = .scalar { bits := 1, sizeBytes := 1 })) :
    MirBoolPredicateHolds specBody args := by
  refine mirBoolPredicateHolds_of_wpConverges specBody args ?_
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec_init h_pure h_conv)

/--
Discharge `MirBoolPredicateHoldsWithCallees specBody callees args` from
`PureMirConverges`.
-/
theorem mirBoolPredicateHoldsWithCallees_of_pureExec
    (specBody : CapturedMir) (callees : List CapturedMir) (args : List Value)
    (h_pure : checkPureMir specBody = true)
    (h_conv :
      PureMirConverges specBody (initPureState specBody args)
        (· = .scalar { bits := 1, sizeBytes := 1 })) :
    MirFuelFree.MirBoolPredicateHoldsWithCallees specBody callees args := by
  refine mirBoolPredicateHoldsWithCallees_of_wpConverges specBody callees args ?_
  exact MirWpConverges.mono
    (fun out h_out => by
      cases out with
      | normal rv => exact h_out.2
      | panic => exact False.elim h_out
      | abort => exact False.elim h_out)
    (mirWpConverges_of_pureExec_withCallees h_pure h_conv)

/-! ## 6. Concrete Multi-Block Struct/Tuple/Enum Witness (`pureAdtMultiBlockBody`) -/

/-- Synthetic source span for `pureAdtMultiBlockBody`. -/
def pureAdtSpan : String := "PureMirExec.lean"

/-- `u32` type (`4` bytes). -/
def pureU32Ty : Ty :=
  { kind := .uint .u32, layoutIdx := 0 }

/-- Tuple type `(u32, u32)`. -/
def purePairTy : Ty :=
  { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }

/--
Two-variant enum/ADT type `Mode` (`variant 0 = KeepFirst`, `variant 1 = KeepSecond`).

Its `layoutIdx` (`1`) has no entry in `pureAdtMultiBlockBody.layouts`, so
`evalPlaceDiscriminant` reads the raw variant index. Index `0` would alias
`u32Layout`, whose `.single 0` variants make every nonzero variant UB.
-/
def pureModeEnumTy : Ty :=
  { kind := .adt "demo::Mode" [], layoutIdx := 1 }

/--
Multi-block MIR function `pureAdtMultiBlockBody` operating on structs/tuples
and enums across 4 basic blocks (`bb0`, `bb1`, `bb2`, `bb3`):
- Incoming arguments:
  - `_1` (`purePairTy`): tuple/struct pair `(x, y)` of two `u32` scalars
  - `_2` (`pureModeEnumTy`): enum value with variant `0` or `1` and payload `[tag]`
- Locals:
  - `_0`: return slot (`u32`)
  - `_3`: temporary tuple `(x, y)` constructed via `Rvalue.aggregate .tuple`
    and projected at fields `0` and `1`
  - `_4`: discriminant of enum `_2` extracted via `Rvalue.discriminant`
- Control flow:
  - `bb0`: `StorageLive(_3)`, `StorageLive(_4)`, extract `x = _1.0` and
    `y = _1.1` into tuple `_3`, compute `_4 = discriminant(_2)`, and branch via
    `switchInt(_4)` to `bb1` (when variant == 0) or `bb2` (otherwise).
  - `bb1`: project `_0 = _3.0` and `goto bb3`.
  - `bb2`: project `_0 = _3.1` and `goto bb3`.
  - `bb3`: `StorageDead(_4)`, `StorageDead(_3)`, `return`.
-/
def pureAdtMultiBlockBody : CapturedMir where
  defPath := "demo::select_pair_by_mode"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := pureU32Ty, debugName := some "_0" },
    { mutability := .not, ty := purePairTy, debugName := some "pair" },
    { mutability := .not, ty := pureModeEnumTy, debugName := some "mode" },
    { mutability := .mut, ty := purePairTy, debugName := some "tmp_pair" },
    { mutability := .mut, ty := { kind := .uint .usize, layoutIdx := 0 }, debugName := some "discr" }
  ]
  basicBlocks := [
    -- bb0: construct tuple _3 from (_1.0, _1.1), read discriminant(_2) into _4, switchInt
    { statements := [
        { kind := .storageLive 3, span := pureAdtSpan },
        { kind := .storageLive 4, span := pureAdtSpan },
        { kind := .assign
            { local_ := 3, projection := [] }
            (.aggregate .tuple [
              .copy { local_ := 1, projection := [.field 0 pureU32Ty] },
              .copy { local_ := 1, projection := [.field 1 pureU32Ty] }
            ])
          span := pureAdtSpan },
        { kind := .assign
            { local_ := 4, projection := [] }
            (.discriminant { local_ := 2, projection := [] })
          span := pureAdtSpan }
      ]
      terminator := {
        kind := .switchInt
          (.copy { local_ := 4, projection := [] })
          { branches := [(0, 1)], otherwise := 2 }
        span := pureAdtSpan
      }
      isCleanup := false
    },
    -- bb1: variant 0 branch -> _0 = _3.0; goto bb3
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.use (.copy { local_ := 3, projection := [.field 0 pureU32Ty] }))
          span := pureAdtSpan }
      ]
      terminator := { kind := .goto 3, span := pureAdtSpan }
      isCleanup := false
    },
    -- bb2: non-zero variant branch -> _0 = _3.1; goto bb3
    { statements := [
        { kind := .assign
            { local_ := 0, projection := [] }
            (.use (.copy { local_ := 3, projection := [.field 1 pureU32Ty] }))
          span := pureAdtSpan }
      ]
      terminator := { kind := .goto 3, span := pureAdtSpan }
      isCleanup := false
    },
    -- bb3: StorageDead(_4); StorageDead(_3); return
    { statements := [
        { kind := .storageDead 4, span := pureAdtSpan },
        { kind := .storageDead 3, span := pureAdtSpan }
      ]
      terminator := { kind := .return_, span := pureAdtSpan }
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32Layout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := u32Layout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [u32Layout]
  }
  allocations := []

/--
`checkPureMir pureAdtMultiBlockBody = true` holds by `decide` / `rfl`.
-/
theorem checkPureMir_pureAdtMultiBlockBody :
    checkPureMir pureAdtMultiBlockBody = true := by
  decide

/--
Expected pure specification of `pureAdtMultiBlockBody` on scalar fields `x`, `y`
and enum variant index `variantIdx`.
-/
def pureAdtExpected (x y variantIdx : Nat) : Value :=
  .scalar { bits := if variantIdx == 0 then x else y, sizeBytes := 4 }

/--
Fuel-free pure execution convergence (`PureMirConverges`) for
`pureAdtMultiBlockBody` on `initPureState`, proved purely over `PureState`
without touching any `Memory` fields.
-/
theorem pureAdtMultiBlock_pureConverges
    (x y variantIdx : Nat) (payload : List Value)
    (h_init : valueListContainsUninit payload = false := by rfl) :
    PureMirConverges pureAdtMultiBlockBody
      (initPureState pureAdtMultiBlockBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ])
      (· = pureAdtExpected x y variantIdx) := by
  refine ⟨12, ?_⟩
  let env3 : List LocalSlot :=
    [ .uninit
    , .init (.aggregate 0 [.scalar { bits := x, sizeBytes := 4 }, .scalar { bits := y, sizeBytes := 4 }])
    , .init (.aggregate variantIdx payload)
    , .init (.aggregate 0 [.scalar { bits := x, sizeBytes := 4 }, .scalar { bits := y, sizeBytes := 4 }])
    , .uninit ]
  let env4 : List LocalSlot :=
    [ .uninit
    , .init (.aggregate 0 [.scalar { bits := x, sizeBytes := 4 }, .scalar { bits := y, sizeBytes := 4 }])
    , .init (.aggregate variantIdx payload)
    , .init (.aggregate 0 [.scalar { bits := x, sizeBytes := 4 }, .scalar { bits := y, sizeBytes := 4 }])
    , .init (.scalar { bits := variantIdx, sizeBytes := 8 }) ]
  change
    wpMirExecSym 9 pureAdtMultiBlockBody
      (.running (PureState.toMachineState { bb := 0, stmtIdx := 3, env := env3 } emptyMemory))
      (mirNormalPost (fun retVal _ => retVal = pureAdtExpected x y variantIdx))
  have hStep3 :
      evalStmt
        (PureState.toMachineState { bb := 0, stmtIdx := 3, env := env3 } emptyMemory)
        { kind := .assign { local_ := 4, projection := [] } (.discriminant { local_ := 2, projection := [] })
          span := pureAdtSpan }
        pureAdtMultiBlockBody.localDecls pureAdtMultiBlockBody.layouts =
      MirStepNode.step
        (PureState.toMachineState { bb := 0, stmtIdx := 4, env := env4 } emptyMemory) := by
    unfold evalStmt evalRvalue evalPlaceDiscriminant
    simp only [env3, env4, PureState.toMachineState, pureAdtMultiBlockBody, emptyMemory, get?, set?,
      advanceStmt, h_init, List.getElem?_cons_succ, List.getElem?_cons_zero]
    rfl
  unfold wpMirExecSym
  rw [evalSymNodeTree_eq, stepMirExecSymTree_eval]
  change
    evalNodeWP
      (fun st' =>
        wpMirExecSym 8 pureAdtMultiBlockBody st'
          (mirNormalPost (fun retVal _ => retVal = pureAdtExpected x y variantIdx)))
      (mirNormalPost (fun retVal _ => retVal = pureAdtExpected x y variantIdx))
      (evalStmt
        (PureState.toMachineState { bb := 0, stmtIdx := 3, env := env3 } emptyMemory)
        { kind := .assign { local_ := 4, projection := [] } (.discriminant { local_ := 2, projection := [] })
          span := pureAdtSpan }
        pureAdtMultiBlockBody.localDecls pureAdtMultiBlockBody.layouts)
  rw [hStep3]
  cases variantIdx with
  | zero =>
    change Value.scalar { bits := x, sizeBytes := 4 } = pureAdtExpected x y 0
    rfl
  | succ n =>
    change Value.scalar { bits := y, sizeBytes := 4 } = pureAdtExpected x y (n + 1)
    rfl

/--
1-step stateful `MirWpConverges` proof for `pureAdtMultiBlockBody` at arbitrary
root-active `mem₀ : Memory`, discharged directly via `mirWpConverges_of_pureExec`
without ever mentioning `allocs`, `borrows`, or `provenanceMap`.
-/
theorem pureAdtMultiBlock_wpConverges
    (x y variantIdx : Nat) (payload : List Value)
    (mem₀ : Memory) (h_root : RootActiveMemory mem₀)
    (h_init : valueListContainsUninit payload = false := by rfl) :
    MirWpConverges pureAdtMultiBlockBody
      (initMachineStateWithMemory pureAdtMultiBlockBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ] mem₀)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = mem₀ ∧ retVal = pureAdtExpected x y variantIdx)) :=
  mirWpConverges_of_pureExec
    checkPureMir_pureAdtMultiBlockBody
    (pureAdtMultiBlock_pureConverges x y variantIdx payload h_init)
    h_root

/--
1-step stateful `MirWpConverges` proof for `pureAdtMultiBlockBody` when
`mem₀.callees` is populated by `initMachineStateWithMemoryAndCallees`.
-/
theorem pureAdtMultiBlock_wpConverges_withCallees
    (x y variantIdx : Nat) (payload : List Value)
    (mem₀ : Memory) (callees : List CapturedMir)
    (h_root : RootActiveMemory mem₀)
    (h_init : valueListContainsUninit payload = false := by rfl) :
    MirWpConverges pureAdtMultiBlockBody
      (MirFuelFree.initMachineStateWithMemoryAndCallees pureAdtMultiBlockBody [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ] mem₀ callees)
      (mirNormalPost
        (fun retVal mem' =>
          mem' = MirFuelFree.Memory.withDefaultCallees mem₀ callees ∧
          retVal = pureAdtExpected x y variantIdx)) :=
  mirWpConverges_of_pureExec_withMemoryAndCallees
    checkPureMir_pureAdtMultiBlockBody
    (pureAdtMultiBlock_pureConverges x y variantIdx payload h_init)
    h_root

/--
Stateful claim for `pureAdtMultiBlockBody` requiring exact memory preservation
(`mem' = mem₀`) across arbitrary heap allocations and callee tables.
-/
def pureAdtMultiBlockStatefulClaim : StatefulClaim where
  body := pureAdtMultiBlockBody
  pre args mem₀ :=
    (∃ (x y variantIdx : Nat) (payload : List Value),
      valueListContainsUninit payload = false ∧
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ]) ∧
    RootActiveMemory mem₀
  post args mem₀ retVal mem' :=
    mem' = mem₀ ∧
    ∀ (x y variantIdx : Nat) (payload : List Value),
      args = [
        .aggregate 0 [
          .scalar { bits := x, sizeBytes := 4 },
          .scalar { bits := y, sizeBytes := 4 }
        ],
        .aggregate variantIdx payload
      ] →
      retVal = pureAdtExpected x y variantIdx

/-- Non-vacuity witness for `pureAdtMultiBlockStatefulClaim.pre`. -/
theorem pureAdtMultiBlockStatefulClaim_nonVacuous :
    ∃ (args : List Value) (mem₀ : Memory),
      pureAdtMultiBlockStatefulClaim.pre args mem₀ :=
  ⟨[
      .aggregate 0 [
        .scalar { bits := 10, sizeBytes := 4 },
        .scalar { bits := 20, sizeBytes := 4 }
      ],
      .aggregate 1 []
    ],
    (initMachineStateWithCallees pureAdtMultiBlockBody [] [pureAdtMultiBlockBody]).memory,
    ⟨⟨10, 20, 1, [], rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩⟩

/--
Concrete `StatefulVerificationResult` discharge for `pureAdtMultiBlockStatefulClaim`
where the postcondition requires `mem' = mem₀`, proved via
`verifyStatefulMirNoPanic_of_pureExec` (`mirWpConverges_of_pureExec`) without
ever mentioning `allocs`, `borrows`, or `provenanceMap`.
-/
theorem verify_pureAdtMultiBlockStatefulClaim :
    StatefulVerificationResult pureAdtMultiBlockStatefulClaim := by
  refine verifyStatefulMirNoPanic_of_pureExec
    pureAdtMultiBlockStatefulClaim
    checkPureMir_pureAdtMultiBlockBody
    (fun _ _ h_pre => h_pre.2)
    (fun args _ h_pre => ?_)
  rcases h_pre.1 with ⟨x, y, variantIdx, payload, h_init, rfl⟩
  exact PureMirConverges.mono
    (fun retVal h_ret =>
      ⟨rfl, fun x' y' v' p' h_eq => by
        injection h_eq with h_hd h_tl
        injection h_tl with h_snd _
        injection h_hd with _ h_fields
        injection h_fields with h_x h_rest
        injection h_rest with h_y _
        injection h_x with h_sc_x
        injection h_y with h_sc_y
        injection h_sc_x with h_bx _
        injection h_sc_y with h_by _
        injection h_snd with h_var _
        subst h_bx h_by h_var
        exact h_ret⟩)
    (pureAdtMultiBlock_pureConverges x y variantIdx payload h_init)


/-! ## 7. Root-Active Callee Memory (`ActiveRootMemory`) & Stack-Suffix Simulation -/

/--
Memory frame relation between an initial root memory `mem₀` and the memory `mem`
observed when a root caller `body` returns across zero or more inlined
`s.memory.callees` calls or root `TerminatorKind.tailCall` transitions (`FF-2.2`).

Before any inlined call or tail call occurs, `mem = mem₀` (`mem.activeCallee =
mem₀.activeCallee`); once an inlined callee returns to `body` or `body` enters a
tail callee `activeBody`, `mem = { mem₀ with activeCallee := some activeBody }`,
leaving every other field of `mem₀` (`borrows`, `globals`, `callStack`,
`activeProtectors`, `callees`, `traitImpls`, `nextAllocId`, `nextTag`,
`nextProtector`, `callerLocals`, `fnPtrs`) untouched.
-/
def ActiveRootMemory (_body : CapturedMir) (mem₀ mem : Memory) : Prop :=
  mem = mem₀ ∨
  ∃ (activeBody : CapturedMir) (ruc : Bool),
    mem = { mem₀ with activeCallee := some activeBody, rootUnwindCeiling := ruc }

@[simp]
theorem ActiveRootMemory.refl (body : CapturedMir) (mem₀ : Memory) :
    ActiveRootMemory body mem₀ mem₀ :=
  Or.inl rfl

theorem ActiveRootMemory.of_eq
    {body : CapturedMir} {mem₀ mem : Memory} (h : mem = mem₀) :
    ActiveRootMemory body mem₀ mem :=
  h ▸ Or.inl rfl

theorem ActiveRootMemory.with_some
    (body activeBody : CapturedMir) (mem₀ : Memory) :
    ActiveRootMemory body mem₀ { mem₀ with activeCallee := some activeBody } :=
  Or.inr ⟨activeBody, mem₀.rootUnwindCeiling, rfl⟩

theorem ActiveRootMemory.with_some_body
    (body : CapturedMir) (mem₀ : Memory) :
    ActiveRootMemory body mem₀ { mem₀ with activeCallee := some body } :=
  Or.inr ⟨body, mem₀.rootUnwindCeiling, rfl⟩

theorem ActiveRootMemory.trans_with_some_body
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    ActiveRootMemory body mem₀ { mem with activeCallee := some body } := by
  rcases h with rfl | ⟨_, ruc, rfl⟩
  · exact Or.inr ⟨body, mem.rootUnwindCeiling, rfl⟩
  · exact Or.inr ⟨body, ruc, rfl⟩

theorem ActiveRootMemory.activeCallee_getD
    {body : CapturedMir} {mem₀ mem : Memory}
    (h_act : mem = mem₀ ∨ mem = { mem₀ with activeCallee := some body })
    (h_init : mem₀.activeCallee = none ∨ mem₀.activeCallee = some body) :
    mem.activeCallee.getD body = body := by
  rcases h_act with rfl | rfl
  · rcases h_init with h0 | h0 <;> simp [h0]
  · rfl

theorem ActiveRootMemory.borrows_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.borrows = mem₀.borrows := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.callStack_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.callStack = mem₀.callStack := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.activeProtectors_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.activeProtectors = mem₀.activeProtectors := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.callees_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.callees = mem₀.callees := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.traitImpls_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.traitImpls = mem₀.traitImpls := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.globals_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.globals = mem₀.globals := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.nextAllocId_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.nextAllocId = mem₀.nextAllocId := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.callerLocals_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.callerLocals = mem₀.callerLocals := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.fnPtrs_eq
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    mem.fnPtrs = mem₀.fnPtrs := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem ActiveRootMemory.restore_activeCallee
    {body : CapturedMir} {mem₀ mem : Memory}
    (h : ActiveRootMemory body mem₀ mem) :
    { mem with activeCallee := mem₀.activeCallee, rootUnwindCeiling := mem₀.rootUnwindCeiling } = mem₀ := by
  cases mem₀
  rcases h with rfl | ⟨_, _, rfl⟩ <;> rfl

/--
Callee-aware frame simulation between alias-erased `ps : PureState` and full
`ms : MachineState` at root memory `mem₀`, allowing `ms.memory` to satisfy
`ActiveRootMemory body mem₀ ms.memory` after inlined callee returns.
-/
def MirCalleeFrameSim
    (body : CapturedMir)
    (mem₀ : Memory)
    (ps : PureState)
    (ms : MachineState) : Prop :=
  ms.frame.blockIdx = ps.bb ∧
  ms.frame.stmtIdx = ps.stmtIdx ∧
  ms.frame.locals = ps.env ∧
  ActiveRootMemory body mem₀ ms.memory

theorem MirCalleeFrameSim.of_mirFrameSim
    {body : CapturedMir} {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (h : MirFrameSim body mem₀ ps ms) :
    MirCalleeFrameSim body mem₀ ps ms :=
  ⟨h.1, h.2.1, h.2.2.1, Or.inl h.2.2.2⟩

/--
Append `baseStack` beneath `m.callStack` and normalize `m.activeCallee` to
`some (m.activeCallee.getD calleeBody)` so an unstacked execution of
`calleeBody` lifts directly onto a caller's suspended `callStack`.

The empty base stack is special-cased so that `Memory.pushBaseStack c [] m`
leaves `m.callStack` definitionally unchanged (only `activeCallee` is
normalized): under the frame-qualified borrow semantics
(`BorrowEntry.targetFrameDepth`, `DIV-MR-CALL-TARGET-LOCAL`) evaluation reads
`mem.callStack` (frame depth and suspended-frame lookups), so the generic
`*_pushBaseStack` commutation lemmas below hold only for the empty base stack,
and they are proved by unfolding against this definitional equation.
-/
def Memory.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame)
    (m : Memory) : Memory :=
  { m with
    callStack :=
      match baseStack with
      | [] => m.callStack
      | b :: bs => m.callStack ++ narrowCallStackForTailCallee (b :: bs) m.rootUnwindCeiling
    activeCallee := some (m.activeCallee.getD calleeBody)
    rootUnwindCeiling :=
      match baseStack with
      | [] => m.rootUnwindCeiling
      | _ :: _ => true }

/-- Lift `Memory.pushBaseStack` to `MachineState`. -/
def MachineState.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame)
    (ms : MachineState) : MachineState :=
  { ms with memory := Memory.pushBaseStack calleeBody baseStack ms.memory }

/-- Lift `Memory.pushBaseStack` to `RvalueEvalResult`. -/
def RvalueEvalResult.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    RvalueEvalResult → RvalueEvalResult
  | .ok v locals' m => .ok v locals' (Memory.pushBaseStack calleeBody baseStack m)
  | .ub => .ub
  | .unsupported => .unsupported

/-- Lift `Memory.pushBaseStack` to `MirOutcome`. -/
def MirOutcome.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    MirOutcome → MirOutcome
  | .normal (v, m) => .normal (v, Memory.pushBaseStack calleeBody baseStack m)
  | .panic => .panic
  | .abort => .abort

/-- Lift `Memory.pushBaseStack` to `MirExecState`. -/
def MirExecState.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    MirExecState → MirExecState
  | .running ms => .running (MachineState.pushBaseStack calleeBody baseStack ms)
  | .halted out => .halted (MirOutcome.pushBaseStack calleeBody baseStack out)
  | .faulted fk => .faulted fk

/-- Lift `Memory.pushBaseStack` to `MirStepNode` (preserving faults and observations). -/
def MirStepNode.pushBaseStack
    (calleeBody : CapturedMir)
    (baseStack : List SavedCallerFrame) :
    MirStepNode → MirStepNode
  | .ret out => .ret (MirOutcome.pushBaseStack calleeBody baseStack out)
  | .tau st => .tau (MirExecState.pushBaseStack calleeBody baseStack st)
  | .vis (.inl fk) k => .vis (.inl fk) k
  | .vis (.inr (.inl obs)) k =>
    .vis (.inr (.inl obs))
      (fun u => MirExecState.pushBaseStack calleeBody baseStack (k u))
  | .vis (.inr (.inr req)) k =>
    .vis (.inr (.inr req))
      (fun ans => MirExecState.pushBaseStack calleeBody baseStack (k ans))

@[simp]
theorem MirStepNode.pushBaseStack_fail
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (fk : FailureKind) :
    MirStepNode.pushBaseStack calleeBody baseStack (MirStepNode.fail fk) =
      MirStepNode.fail fk :=
  rfl

@[simp]
theorem MirStepNode.pushBaseStack_unsupported
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame) :
    MirStepNode.pushBaseStack calleeBody baseStack MirStepNode.unsupported =
      MirStepNode.unsupported :=
  rfl

theorem rval_push_ub {c : CapturedMir} {b : List SavedCallerFrame} :
    RvalueEvalResult.ub = RvalueEvalResult.pushBaseStack c b RvalueEvalResult.ub := rfl

theorem rval_push_unsupported {c : CapturedMir} {b : List SavedCallerFrame} :
    RvalueEvalResult.unsupported =
      RvalueEvalResult.pushBaseStack c b RvalueEvalResult.unsupported := rfl

theorem rval_push_ok
    {c : CapturedMir} {b : List SavedCallerFrame}
    {v : Value} {l : List LocalSlot} {m₁ m₂ : Memory}
    (h : m₁ = Memory.pushBaseStack c b m₂) :
    RvalueEvalResult.ok v l m₁ =
      RvalueEvalResult.pushBaseStack c b (RvalueEvalResult.ok v l m₂) :=
  h ▸ rfl


theorem step_push_fail {c : CapturedMir} {b : List SavedCallerFrame} {fk : FailureKind} :
    MirStepNode.fail fk = MirStepNode.pushBaseStack c b (MirStepNode.fail fk) := rfl

theorem step_push_unsupported {c : CapturedMir} {b : List SavedCallerFrame} :
    MirStepNode.unsupported = MirStepNode.pushBaseStack c b MirStepNode.unsupported := rfl

theorem step_push_step
    {c : CapturedMir} {b : List SavedCallerFrame} {s₁ s₂ : MachineState}
    (h : s₁ = MachineState.pushBaseStack c b s₂) :
    MirStepNode.step s₁ = MirStepNode.pushBaseStack c b (MirStepNode.step s₂) :=
  h ▸ rfl


theorem internFnPtr_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) (defPath : DefPath) (typeArgs : List RigidTy)
    (fnSig : Option RigidTy) :
    internFnPtr (Memory.pushBaseStack calleeBody baseStack mem)
        defPath typeArgs fnSig =
      let (allocId, mem') := internFnPtr mem defPath typeArgs fnSig
      (allocId, Memory.pushBaseStack calleeBody baseStack mem') := by
  unfold internFnPtr
  dsimp only [Memory.pushBaseStack]
  cases findFnPtrEntry? mem.fnPtrs defPath typeArgs fnSig <;> rfl

theorem evalUnsafeFnPointer_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsafeFnPointer locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalUnsafeFnPointer locals op targetTy mem localDecls layouts) := by
  unfold evalUnsafeFnPointer
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem deriveStackElemThinPtr_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (mem : Memory) (ptrVal : ProvenancePtr)
    (parentEntry : BorrowEntry) (elemCountOpt : Option Nat)
    (ptrBytes : Nat) :
    deriveStackElemThinPtr locals (Memory.pushBaseStack calleeBody [] mem)
        ptrVal parentEntry elemCountOpt ptrBytes =
      RvalueEvalResult.pushBaseStack calleeBody []
        (deriveStackElemThinPtr locals mem ptrVal parentEntry elemCountOpt ptrBytes) := by
  unfold deriveStackElemThinPtr
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalUnsizeCoercion_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUnsizeCoercion locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalUnsizeCoercion locals op targetTy mem localDecls layouts) := by
  unfold evalUnsizeCoercion
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalSliceFatPtrDerefBorrow_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (mem : Memory) (parentPtr : ProvenancePtr)
    (ptrSz : Nat) (lenSc : ScalarInt) (restProj : List ProjectionElem)
    (perm : TreeBorrowPerm) (isMut : Bool) (pointeeTyOpt : Option Ty)
    (layouts : LayoutTable) (checkPerm : Bool)
    (localDecls : List LocalDecl) (fullPlaceTyOpt : Option Ty)
    (checkRefElemAlign : Bool) :
    evalSliceFatPtrDerefBorrow locals
        (Memory.pushBaseStack calleeBody [] mem)
        parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts checkPerm
        localDecls fullPlaceTyOpt checkRefElemAlign =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalSliceFatPtrDerefBorrow locals mem
          parentPtr ptrSz lenSc restProj perm isMut pointeeTyOpt layouts checkPerm
          localDecls fullPlaceTyOpt checkRefElemAlign) := by
  unfold evalSliceFatPtrDerefBorrow
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalGlobalThinPtrDerefBorrow_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (mem : Memory) (alloc : CapturedAllocation)
    (parentPtr : ProvenancePtr) (ptrSz : Nat) (restProj : List ProjectionElem)
    (isMut : Bool) (pointeeTyOpt : Option Ty) (layouts : LayoutTable)
    (localDecls : List LocalDecl) (rawPtrMode : Bool)
    (fullPlaceTyOpt : Option Ty) :
    evalGlobalThinPtrDerefBorrow locals
        (Memory.pushBaseStack calleeBody baseStack mem)
        alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts localDecls rawPtrMode
        fullPlaceTyOpt =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalGlobalThinPtrDerefBorrow locals mem
          alloc parentPtr ptrSz restProj isMut pointeeTyOpt layouts localDecls rawPtrMode
          fullPlaceTyOpt) := by
  unfold evalGlobalThinPtrDerefBorrow
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalScalarSliceFatPtrDerefRaw_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals : List LocalSlot) (mem : Memory) (addrSc lenSc : ScalarInt)
    (restProj : List ProjectionElem) (pointeeTyOpt : Option Ty)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalScalarSliceFatPtrDerefRaw locals
        (Memory.pushBaseStack calleeBody baseStack mem)
        addrSc lenSc restProj pointeeTyOpt localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalScalarSliceFatPtrDerefRaw locals mem
          addrSc lenSc restProj pointeeTyOpt localDecls layouts) := by
  unfold evalScalarSliceFatPtrDerefRaw
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalScalarPtrOffsetBinOp_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (lhs rhs : ScalarInt) :
    evalScalarPtrOffsetBinOp locals₂
        (Memory.pushBaseStack calleeBody baseStack mem)
        localDecls layouts lhsOp lhs rhs =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalScalarPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp lhs rhs) := by
  unfold evalScalarPtrOffsetBinOp
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalPtrOffsetBinOp_pushBaseStack
    (calleeBody : CapturedMir)
    (locals₂ : List LocalSlot) (mem : Memory) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (lhsOp : Operand) (ptrVal : ProvenancePtr)
    (sz : Nat) (offsetSc : ScalarInt) :
    evalPtrOffsetBinOp locals₂ (Memory.pushBaseStack calleeBody [] mem)
        localDecls layouts lhsOp ptrVal sz offsetSc =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalPtrOffsetBinOp locals₂ mem localDecls layouts lhsOp ptrVal sz
          offsetSc) := by
  unfold evalPtrOffsetBinOp ptrAllocByteBound?
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalPlaceLen_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (place : Place) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceLen locals place (Memory.pushBaseStack calleeBody [] mem)
        localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalPlaceLen locals place mem localDecls layouts) := by
  unfold evalPlaceLen
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalPlaceDiscriminant_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (val : Value) (locals' : List LocalSlot) (mem : Memory) (place : Place)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPlaceDiscriminant val locals'
        (Memory.pushBaseStack calleeBody baseStack mem) place localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalPlaceDiscriminant val locals' mem place localDecls layouts) := by
  unfold evalPlaceDiscriminant
  dsimp only
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalReifyFnPointer_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (coercionKind : String) :
    evalReifyFnPointer locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem)
        localDecls layouts coercionKind =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalReifyFnPointer locals op targetTy mem
          localDecls layouts coercionKind) := by
  unfold evalReifyFnPointer
  cases isReifyFnPointerCoercion coercionKind with
  | false =>
    dsimp only [Memory.pushBaseStack]
    repeat' (first
      | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
      | exact evalUnsizeCoercion_pushBaseStack calleeBody ..
      | exact deriveStackElemThinPtr_pushBaseStack calleeBody ..
      | split)
  | true =>
    cases stringEq coercionKind "UnsafeFnPointer" with
    | true =>
      exact evalUnsafeFnPointer_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts
    | false =>
      dsimp only
      dsimp only [Memory.pushBaseStack]
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals [] mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        dsimp only
        repeat' (first
          | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
          | (rw [internFnPtr_pushBaseStack]; rfl)
          | split)

theorem evalFnPtrToPtr_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalFnPtrToPtr locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalFnPtrToPtr locals op targetTy mem localDecls layouts) := by
  unfold evalFnPtrToPtr
  dsimp only [Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalByteCast_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalByteCast locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalByteCast locals op targetTy mem localDecls layouts) := by
  have h_op :
      evalOperand locals op (Memory.pushBaseStack calleeBody [] mem).borrows
        (Memory.pushBaseStack calleeBody [] mem).globals layouts
        (Memory.pushBaseStack calleeBody [] mem).callerLocals localDecls
        (Memory.pushBaseStack calleeBody [] mem).callStack =
      evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
        mem.callStack := by
    dsimp only [Memory.pushBaseStack]
  cases h0 : evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls
      mem.callStack with
  | ub =>
    rw [evalByteCast_ub_of_load (h_op.trans h0), evalByteCast_ub_of_load h0]; rfl
  | unsupported =>
    rw [evalByteCast_unsupported_of_load (h_op.trans h0),
        evalByteCast_unsupported_of_load h0]; rfl
  | ok v locals' =>
    rw [evalByteCast_ok_of_load (h_op.trans h0), evalByteCast_ok_of_load h0]
    rcases evalByteCastBody_shape op targetTy localDecls layouts v locals' with
      h_ub | h_un | ⟨v', h_ok⟩
    · rw [h_ub _, h_ub mem]; rfl
    · rw [h_un _, h_un mem]; rfl
    · rw [h_ok _, h_ok mem]; rfl

theorem evalSignedDiv_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedDiv a b sz locals (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalSignedDiv a b sz locals mem) := by
  unfold evalSignedDiv
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalSignedRem_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (a b sz : Nat) (locals : List LocalSlot) (mem : Memory) :
    evalSignedRem a b sz locals (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalSignedRem a b sz locals mem) := by
  unfold evalSignedRem
  dsimp only
  cases Bool.and
    (Nat.beq (wrapScalarBits a (scalarModulus sz))
      (scalarPow2 (Nat.sub (Nat.mul sz 8) 1)))
    (Nat.beq (wrapScalarBits b (scalarModulus sz))
      (Nat.sub (scalarModulus sz) 1)) <;> rfl

theorem evalScalarBinOp_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (op : BinOp) (lhs rhs : ScalarInt) (locals : List LocalSlot)
    (mem : Memory) (isSigned : Bool) :
    evalScalarBinOp op lhs rhs locals
        (Memory.pushBaseStack calleeBody baseStack mem) isSigned =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalScalarBinOp op lhs rhs locals mem isSigned) := by
  rw [evalScalarBinOp_eq_withMem _ _ _ _ (Memory.pushBaseStack calleeBody baseStack mem),
      evalScalarBinOp_eq_withMem _ _ _ _ mem]
  cases evalScalarBinOp op lhs rhs locals emptyMemory isSigned <;> rfl

theorem evalUnaryNot_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalUnaryNot sc optTy locals
        (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalUnaryNot sc optTy locals mem) := by
  rw [evalUnaryNot_eq_withMem _ _ _ (Memory.pushBaseStack calleeBody baseStack mem),
      evalUnaryNot_eq_withMem _ _ _ mem]
  cases evalUnaryNot sc optTy locals emptyMemory <;> rfl

theorem evalFloatUnaryNeg_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (sc : ScalarInt) (optTy : Option Ty) (locals : List LocalSlot)
    (mem : Memory) :
    evalFloatUnaryNeg sc optTy locals
        (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalFloatUnaryNeg sc optTy locals mem) := by
  rw [evalFloatUnaryNeg_eq_withMem _ _ _ (Memory.pushBaseStack calleeBody baseStack mem),
      evalFloatUnaryNeg_eq_withMem _ _ _ mem]
  cases evalFloatUnaryNeg sc optTy locals emptyMemory <;> rfl

theorem evalFloatScalarBinOp_pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (op : BinOp) (lhs rhs : ScalarInt) (lhsTy? rhsTy? : Option Ty)
    (locals : List LocalSlot) (mem : Memory) :
    evalFloatScalarBinOp op lhs rhs lhsTy? rhsTy? locals
        (Memory.pushBaseStack calleeBody baseStack mem) =
      RvalueEvalResult.pushBaseStack calleeBody baseStack
        (evalFloatScalarBinOp op lhs rhs lhsTy? rhsTy? locals mem) := by
  rw [evalFloatScalarBinOp_eq_withMem _ _ _ _ _ _ (Memory.pushBaseStack calleeBody baseStack mem),
      evalFloatScalarBinOp_eq_withMem _ _ _ _ _ _ mem]
  cases evalFloatScalarBinOp op lhs rhs lhsTy? rhsTy? locals emptyMemory <;> rfl

theorem evalRvalueRefDeref_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (borrowKind : BorrowKind) (place : Place)
    (restProj : List ProjectionElem) (perm : TreeBorrowPerm) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalueRefDeref locals borrowKind place restProj perm
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalRvalueRefDeref locals borrowKind place restProj perm mem localDecls layouts) := by
  dsimp only [evalRvalueRefDeref, Memory.pushBaseStack]
  repeat' (first
    | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
    | exact evalSliceFatPtrDerefBorrow_pushBaseStack calleeBody ..
    | exact evalGlobalThinPtrDerefBorrow_pushBaseStack calleeBody [] ..
    | split)

theorem evalRvalueRawPtr_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (mutability : Mutability) (place : Place)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalueRawPtr locals mutability place
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalRvalueRawPtr locals mutability place mem localDecls layouts) := by
  rcases place with ⟨pLoc, _ | ⟨phd, restProj⟩⟩
  · dsimp only [evalRvalueRawPtr, Memory.pushBaseStack]
    cases get? locals pLoc with
    | none => rfl
    | some sl => cases sl <;> rfl
  · cases phd with
    | deref =>
      dsimp only [evalRvalueRawPtr, Memory.pushBaseStack]
      repeat' (first
        | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
        | exact evalSliceFatPtrDerefBorrow_pushBaseStack calleeBody ..
        | exact evalGlobalThinPtrDerefBorrow_pushBaseStack calleeBody [] ..
        | exact evalScalarSliceFatPtrDerefRaw_pushBaseStack calleeBody [] ..
        | split)
    | _ =>
      dsimp only [evalRvalueRawPtr, Memory.pushBaseStack]
      cases get? locals pLoc with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | uninit | init _ =>
          dsimp only
          cases resolveBorrowProjectionElems locals _ with
          | none => rfl
          | some rp =>
            dsimp only
            cases projHasSubslice rp with
            | false => rfl
            | true => dsimp only; cases validateNonDerefSubslices locals localDecls layouts pLoc _ rp <;> rfl

theorem evalCastPtrToPtr_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalCastPtrToPtr locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalCastPtrToPtr locals op targetTy mem localDecls layouts) := by
  dsimp only [evalCastPtrToPtr, Memory.pushBaseStack]
  repeat' (first
    | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
    | exact deriveStackElemThinPtr_pushBaseStack calleeBody ..
    | split)

theorem evalPointerExposeProvenance_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPointerExposeProvenance locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalPointerExposeProvenance locals op targetTy mem localDecls layouts) := by
  dsimp only [evalPointerExposeProvenance, Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalPointerWithExposedProvenance_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (op : Operand) (targetTy : Ty)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalPointerWithExposedProvenance locals op targetTy
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalPointerWithExposedProvenance locals op targetTy mem localDecls layouts) := by
  dsimp only [evalPointerWithExposedProvenance, Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalAggregateRawPtr_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (pointeeTy : Ty) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalAggregateRawPtr locals pointeeTy ops
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalAggregateRawPtr locals pointeeTy ops mem localDecls layouts) := by
  dsimp only [evalAggregateRawPtr, Memory.pushBaseStack]
  repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

theorem evalAggregateAdt_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (defPath : DefPath) (variantIdx : VariantIdx)
    (activeField : Option FieldIdx) (ops : List Operand)
    (mem : Memory) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalAggregateAdt locals defPath variantIdx activeField ops
        (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalAggregateAdt locals defPath variantIdx activeField ops mem localDecls layouts) := by
  unfold evalAggregateAdt
  dsimp only [Memory.pushBaseStack]
  cases evalOperands locals ops mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => rfl
  | unsupported => rfl
  | ok vals locals' =>
    dsimp only
    repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)

private theorem evalFloatCastRvalue_pushBaseStack
    (calleeBody : CapturedMir) (locals : List LocalSlot) (ck : CastKind)
    (op : Operand) (targetTy : Ty) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalFloatCastRvalue locals ck op targetTy (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalFloatCastRvalue locals ck op targetTy mem localDecls layouts) := by
  unfold evalFloatCastRvalue
  dsimp only [Memory.pushBaseStack]
  cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    dsimp only
    cases evalFloatCast ck (operandTy localDecls layouts op) targetTy layouts v <;> rfl

/-- The operand load `evalUseRvalue` commutes with `Memory.pushBaseStack` (`[]` base stack). -/
theorem evalUseRvalue_pushBaseStack
    (calleeBody : CapturedMir) (locals : List LocalSlot) (op : Operand) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalUseRvalue locals op (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalUseRvalue locals op mem localDecls layouts) := by
  rcases mem with ⟨nA, gl, bor, nT, cal, tr, cs, ac, ap, nP, cl, fp, ex⟩
  unfold evalUseRvalue
  dsimp only [Memory.pushBaseStack]
  cases evalOperand locals op bor gl layouts cl localDecls cs with
  | ub => rfl
  | unsupported => rfl
  | ok v locals' =>
    dsimp only
    cases validateLoadedValue layouts localDecls op v with
    | false => rfl
    | true =>
      dsimp only
      rcases op with ⟨loc, _ | ⟨hd, tl⟩⟩ | ⟨loc, _ | ⟨hd, tl⟩⟩ | _
      · rfl
      · cases hd <;> try rfl
        rcases bor with _ | ⟨b₁, _ | ⟨b₂, rest⟩⟩
        · rfl
        · rfl
        · dsimp only
          cases derefReadTreeUB locals loc tl (b₁ :: b₂ :: rest) ap <;> rfl
      · rfl
      · cases hd <;> try rfl
        rcases bor with _ | ⟨b₁, _ | ⟨b₂, rest⟩⟩
        · rfl
        · rfl
        · dsimp only
          cases derefReadTreeUB locals loc tl (b₁ :: b₂ :: rest) ap <;> rfl
      · rfl

/--
`evalRvalue` is completely independent of `Memory.callStack` and
`Memory.activeCallee`, commuting unconditionally with `Memory.pushBaseStack`.
-/
theorem evalRvalue_pushBaseStack
    (calleeBody : CapturedMir)
    (locals : List LocalSlot) (rv : Rvalue) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalRvalue locals rv (Memory.pushBaseStack calleeBody [] mem)
        localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalRvalue locals rv mem localDecls layouts) := by
  cases rv with
  | use op =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.pushBaseStack]; repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split))
  | «repeat» op count =>
    cases op
    all_goals (dsimp only [evalRvalue, Memory.pushBaseStack]; repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split))
  | ref bk place =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    repeat' (first
      | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
      | exact evalRvalueRefDeref_pushBaseStack calleeBody ..
      | split)
  | threadLocalRef _ => rfl
  | rawPtr mutab place =>
    exact evalRvalueRawPtr_pushBaseStack calleeBody locals mutab place mem localDecls layouts
  | len place =>
    dsimp only [evalRvalue]
    exact evalPlaceLen_pushBaseStack calleeBody locals place mem
      localDecls layouts
  | cast ck op targetTy =>
    cases ck with
    | pointerCoercion ckStr =>
      exact evalReifyFnPointer_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts ckStr
    | fnPtrToPtr =>
      exact evalFnPtrToPtr_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts
    | ptrToPtr =>
      exact evalCastPtrToPtr_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts
    | pointerExposeProvenance =>
      exact evalPointerExposeProvenance_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts
    | pointerWithExposedProvenance =>
      exact evalPointerWithExposedProvenance_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts
    | transmute =>
      exact evalByteCast_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts
    | subtype =>
      exact evalByteCast_pushBaseStack calleeBody
        locals op targetTy mem localDecls layouts
    | floatToInt | intToFloat | floatToFloat =>
      exact evalFloatCastRvalue_pushBaseStack calleeBody
        locals _ op targetTy mem localDecls layouts
    | _ =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      repeat' (first
        | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
        | split)
  | binaryOp op lhsOp rhsOp =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    cases evalOperand locals lhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok lhsVal locals₁ =>
      dsimp only
      cases evalOperand locals₁ rhsOp mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok rhsVal locals₂ =>
        dsimp only
        cases lhsVal with
        | scalar lhsSc =>
          cases rhsVal with
          | scalar rhsSc =>
            cases op with
            | offset =>
              exact evalScalarPtrOffsetBinOp_pushBaseStack calleeBody []
                locals₂ mem localDecls layouts lhsOp lhsSc rhsSc
            | _ =>
              cases Bool.or (isFloatOptTy (operandTy localDecls layouts lhsOp))
                  (isFloatOptTy (operandTy localDecls layouts rhsOp)) with
              | true =>
                exact evalFloatScalarBinOp_pushBaseStack calleeBody []
                  _ lhsSc rhsSc _ _ locals₂ mem
              | false =>
                exact evalScalarBinOp_pushBaseStack calleeBody []
                  _ lhsSc rhsSc locals₂ mem _
          | ptr ptrVal sz =>
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => rfl
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none => rfl
              | some rhsAddrSc =>
                exact evalScalarBinOp_pushBaseStack calleeBody [] op lhsSc rhsAddrSc locals₂ mem false
          | _ => rfl
        | ptr ptrVal sz =>
          cases rhsVal with
          | scalar rhsSc =>
            cases op with
            | offset =>
              exact evalPtrOffsetBinOp_pushBaseStack calleeBody
                locals₂ mem localDecls layouts lhsOp ptrVal sz rhsSc
            | _ =>
              cases isPtrRelationalBinOp _ localDecls layouts lhsOp rhsOp with
              | false => rfl
              | true =>
                dsimp only
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
                | none => rfl
                | some lhsAddrSc =>
                  exact evalScalarBinOp_pushBaseStack calleeBody [] _ lhsAddrSc rhsSc locals₂ mem false
          | ptr rhsPtr rhsSz =>
            cases isPtrRelationalBinOp op localDecls layouts lhsOp rhsOp with
            | false => rfl
            | true =>
              dsimp only
              cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) ptrVal sz mem.callStack with
              | none =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack <;> rfl
              | some lhsAddrSc =>
                cases ptrAddressScalar? locals₂ mem.borrows mem.callerLocals localDecls layouts (layoutPointerBytes layouts) rhsPtr rhsSz mem.callStack with
                | none => rfl
                | some rhsAddrSc =>
                  exact evalScalarBinOp_pushBaseStack calleeBody [] op lhsAddrSc rhsAddrSc locals₂ mem false
          | _ => rfl
        | aggregate lhsVar lhsFields =>
          cases rhsVal with
          | aggregate rhsVar rhsFields =>
            dsimp only [evalWidePtrAggregateRelBinOp, evalWidePtrRelBinOp, Memory.pushBaseStack]
            repeat' (first
              | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
              | exact evalScalarBinOp_pushBaseStack calleeBody [] ..
              | split)
          | _ => rfl
        | _ => rfl
  | nullaryOp op ty =>
    show evalNullaryOp locals op ty (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalNullaryOp locals op ty mem localDecls layouts)
    rcases evalNullaryOp_shape locals op ty localDecls layouts with h_un | ⟨sc, h_ok⟩
    · rw [h_un _, h_un mem]; rfl
    · rw [h_ok _, h_ok mem]; rfl
  | unaryOp uop op =>
    cases uop with
    | not =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      cases evalOperand locals op mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok v locals' =>
        cases v with
        | scalar sc =>
          exact evalUnaryNot_pushBaseStack calleeBody [] sc _ locals' mem
        | _ => rfl
    | neg =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      repeat' (first
        | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
        | exact evalFloatUnaryNeg_pushBaseStack calleeBody [] .. | split)
    | ptrMetadata =>
      dsimp only [evalRvalue, evalUnaryPtrMetadata, Memory.pushBaseStack]
      repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)
  | discriminant place =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    repeat' (first
      | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl
      | exact evalPlaceDiscriminant_pushBaseStack calleeBody [] ..
      | split)
  | aggregate kind ops =>
    cases kind with
    | rawPtr pointeeTy _ =>
      exact evalAggregateRawPtr_pushBaseStack calleeBody locals pointeeTy ops mem localDecls layouts
    | adt defPath variantIdx activeField =>
      exact evalAggregateAdt_pushBaseStack calleeBody locals defPath variantIdx activeField ops mem localDecls layouts
    | _ =>
      dsimp only [evalRvalue, Memory.pushBaseStack]
      repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)
  | shallowInitBox op ty =>
    show evalShallowInitBox locals op ty (Memory.pushBaseStack calleeBody [] mem) localDecls layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalShallowInitBox locals op ty mem localDecls layouts)
    have h_u := evalUseRvalue_pushBaseStack calleeBody locals op mem localDecls layouts
    cases h0 : evalUseRvalue locals op mem localDecls layouts with
    | ub =>
      rw [h0] at h_u
      rw [evalShallowInitBox_ub_of_use h_u, evalShallowInitBox_ub_of_use h0]; rfl
    | unsupported =>
      rw [h0] at h_u
      rw [evalShallowInitBox_unsupported_of_use h_u, evalShallowInitBox_unsupported_of_use h0]; rfl
    | ok v l m =>
      rw [h0] at h_u
      rw [evalShallowInitBox_ok_of_use h_u, evalShallowInitBox_ok_of_use h0]
      rcases evalShallowInitBoxBody_shape op localDecls layouts v l with h_un | ⟨p, sz, h_ok⟩
      · rw [h_un _, h_un m]; rfl
      · rw [h_ok _, h_ok m]; rfl
  | copyForDeref place =>
    dsimp only [evalRvalue, Memory.pushBaseStack]
    cases evalOperand locals (.copy place) mem.borrows mem.globals layouts mem.callerLocals localDecls mem.callStack <;> repeat' (first | exact rval_push_ub | exact rval_push_unsupported | exact rval_push_ok rfl | split)
  | wrapUnsafeBinder op ty =>
    show evalWrapUnsafeBinder locals op ty (Memory.pushBaseStack calleeBody [] mem) localDecls
        layouts =
      RvalueEvalResult.pushBaseStack calleeBody []
        (evalWrapUnsafeBinder locals op ty mem localDecls layouts)
    have h_u := evalUseRvalue_pushBaseStack calleeBody locals op mem localDecls layouts
    cases h0 : evalUseRvalue locals op mem localDecls layouts with
    | ub =>
      rw [h0] at h_u
      rw [evalWrapUnsafeBinder_ub_of_use h_u, evalWrapUnsafeBinder_ub_of_use h0]; rfl
    | unsupported =>
      rw [h0] at h_u
      rw [evalWrapUnsafeBinder_unsupported_of_use h_u,
          evalWrapUnsafeBinder_unsupported_of_use h0]; rfl
    | ok v l m =>
      rw [h0] at h_u
      rw [evalWrapUnsafeBinder_ok_of_use h_u, evalWrapUnsafeBinder_ok_of_use h0]
      rcases evalWrapUnsafeBinderBody_shape op ty localDecls layouts v l with
        h_ub | h_un | ⟨outVal, h_ok⟩
      · rw [h_ub _, h_ub m]; rfl
      · rw [h_un _, h_un m]; rfl
      · rw [h_ok _, h_ok m]; rfl

theorem evalCopySingleDirect_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    evalCopySingleDirect
        (MachineState.pushBaseStack calleeBody [] s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃ =
      MirStepNode.pushBaseStack calleeBody []
        (evalCopySingleDirect
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃) := by
  unfold evalCopySingleDirect
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
  all_goals try dsimp (config := { zeta := true })
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
  all_goals try rfl

@[simp]
theorem Memory.pushBaseStack_borrows
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).borrows = mem.borrows :=
  rfl

@[simp]
theorem Memory.pushBaseStack_callerLocals
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).callerLocals =
      mem.callerLocals :=
  rfl

@[simp]
theorem Memory.pushBaseStack_globals
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).globals = mem.globals :=
  rfl

@[simp]
theorem Memory.pushBaseStack_callees
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).callees = mem.callees :=
  rfl

@[simp]
theorem Memory.pushBaseStack_traitImpls
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).traitImpls =
      mem.traitImpls :=
  rfl

@[simp]
theorem Memory.pushBaseStack_activeProtectors
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).activeProtectors =
      mem.activeProtectors :=
  rfl

@[simp]
theorem Memory.pushBaseStack_exposedAllocIds
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).exposedAllocIds =
      mem.exposedAllocIds :=
  rfl

theorem Memory.pushBaseStack_callStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (mem : Memory) :
    (Memory.pushBaseStack calleeBody baseStack mem).callStack =
      mem.callStack ++ narrowCallStackForTailCallee baseStack mem.rootUnwindCeiling := by
  cases baseStack with
  | nil => cases mem.rootUnwindCeiling <;> exact (List.append_nil mem.callStack).symm
  | cons _ _ => rfl

@[simp]
theorem Memory.pushBaseStack_nil_callStack
    (calleeBody : CapturedMir) (mem : Memory) :
    (Memory.pushBaseStack calleeBody [] mem).callStack = mem.callStack :=
  rfl

@[simp]
theorem MachineState.pushBaseStack_frame
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) :
    (MachineState.pushBaseStack calleeBody baseStack s).frame = s.frame :=
  rfl

@[simp]
theorem MachineState.pushBaseStack_memory
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) :
    (MachineState.pushBaseStack calleeBody baseStack s).memory =
      Memory.pushBaseStack calleeBody baseStack s.memory :=
  rfl

@[simp]
theorem MirStepNode.pushBaseStack_step
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (ms : MachineState) :
    MirStepNode.pushBaseStack calleeBody baseStack (MirStepNode.step ms) =
      MirStepNode.step (MachineState.pushBaseStack calleeBody baseStack ms) :=
  rfl

theorem advanceStmt_pushBaseStack_borrows
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (locs : List LocalSlot) (bs : List BorrowEntry) :
    advanceStmt (MachineState.pushBaseStack calleeBody baseStack s) locs
        { Memory.pushBaseStack calleeBody baseStack s.memory with
          borrows := bs } =
      MachineState.pushBaseStack calleeBody baseStack
        (advanceStmt s locs { s.memory with borrows := bs }) :=
  rfl

theorem advanceStmt_pushBaseStack_borrows_callerLocals
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (locs : List LocalSlot)
    (bs : List BorrowEntry) (cl : List LocalSlot) :
    advanceStmt (MachineState.pushBaseStack calleeBody baseStack s) locs
        { Memory.pushBaseStack calleeBody baseStack s.memory with
          borrows := bs
          callerLocals := cl } =
      MachineState.pushBaseStack calleeBody baseStack
        (advanceStmt s locs { s.memory with borrows := bs, callerLocals := cl }) :=
  rfl

def IsStmtNode (n : MirStepNode) : Prop :=
  (∃ nextSt : MachineState, n = MirStepNode.step nextSt) ∨
  (∃ fk : FailureKind, n = MirStepNode.fail fk) ∨
  n = MirStepNode.unsupported

def copyWriteDstVal
    (s : MachineState) (locals₃ : List LocalSlot) (dstPlace : Place)
    (dstLoc : Local) (dstTag : Nat) (newVal : Value)
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match writePlaceValue locals₃ s.memory.borrows dstPlace newVal localDecls layouts with
  | .ok locals₄ =>
    let borrows' := invalidateConflictingBorrows s.memory.borrows dstLoc (.some dstTag) (length s.memory.callStack)
    MirStepNode.step (advanceStmt s locals₄ { s.memory with borrows := borrows' })
  | .unsupported => MirStepNode.unsupported
  | .ub =>
    match get? locals₃ dstPlace.local_ with
    | .some _ => MirStepNode.fail .ub
    | .none =>
      let callerIdx :=
        match get? s.memory.callerLocals dstPlace.local_ with
        | .some _ => dstPlace.local_
        | .none => Nat.sub dstPlace.local_ (length locals₃)
      let callerWriteRes : PlaceWriteResult :=
        match dstPlace.projection with
        | .nil =>
          match get? s.memory.callerLocals callerIdx with
          | .some .dead => .ub
          | .some _ =>
            match set? s.memory.callerLocals callerIdx (.init newVal) with
            | .some callerLocals' => .ok callerLocals'
            | .none => .ub
          | .none => .ub
        | .deref :: _ => .ub
        | proj :: rest =>
          match get? s.memory.callerLocals callerIdx with
          | .some (.init rootVal) =>
            match writeProjectedValue locals₃ rootVal (proj :: rest) newVal with
            | .ok rootVal' =>
              match set? s.memory.callerLocals callerIdx (.init rootVal') with
              | .some callerLocals' => .ok callerLocals'
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _ => .ub
      match callerWriteRes with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callerLocals' =>
        let borrows' := invalidateConflictingBorrows s.memory.borrows dstLoc (.some dstTag) 0
        MirStepNode.step
          (advanceStmt s locals₃
            { s.memory with borrows := borrows', callerLocals := callerLocals' })

def evalCopyNonOverlappingPermOk
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) : MirStepNode :=
  let n := countBits
  let srcStart := srcPtr.offsetBytes
  let dstStart := dstPtr.offsetBytes
  let srcUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ srcEntry
  let dstUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ dstEntry
  let hasUnionEndpoint :=
    match srcUnionOpt, dstUnionOpt with
    | .none, .none => false
    | _, _ => true
  match hasUnionEndpoint with
  | true =>
    evalCopyUnionBytes
      s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
      srcUnionOpt dstUnionOpt n locals₃
  | false =>
    let isSingleDirect :=
      Bool.and (Nat.beq n 1) (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0))
    match isSingleDirect with
    | true =>
      evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃
    | false =>
      evalCopySubplaceMulti s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry n locals₃

theorem evalCopyNonOverlappingWithCountNonZero_eq
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCountNonZero s src dst localDecls layouts srcVal dstVal countBits
        locals₃ =
        match srcVal, dstVal with
        | .ptr srcPtr _, .ptr dstPtr _ =>
          match lookupBorrow s.memory.borrows srcPtr.tag, lookupBorrow s.memory.borrows dstPtr.tag with
          | .some srcEntry, .some dstEntry =>
            match srcEntry.perm, dstEntry.perm with
            | .disabled, _ => MirStepNode.fail .ub
            | _, .frozen => MirStepNode.fail .ub
            | _, .disabled => MirStepNode.fail .ub
            | _, _ =>
              match copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry with
              | false =>
                evalForeignFrameCopySingleDirect s src dst localDecls layouts srcPtr dstPtr
                  srcEntry dstEntry countBits locals₃
              | true =>
                evalCopyNonOverlappingPermOk s src dst localDecls layouts srcPtr dstPtr
                  srcEntry dstEntry countBits locals₃
          | _, _ => MirStepNode.fail .ub
        | _, _ => MirStepNode.fail .ub := by
  unfold evalCopyNonOverlappingWithCountNonZero
  cases srcVal with
  | ptr srcPtr _ =>
    cases dstVal with
    | ptr dstPtr _ =>
      dsimp only
      cases lookupBorrow s.memory.borrows srcPtr.tag with
      | none => rfl
      | some srcEntry =>
        cases lookupBorrow s.memory.borrows dstPtr.tag with
        | none => rfl
        | some dstEntry =>
          dsimp only
          have h_ok :
              _root_.Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyNonOverlappingPermOk
                s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
              evalCopyNonOverlappingPermOk
                s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ :=
            rfl
          rw [h_ok]
          cases srcEntry.perm <;> cases dstEntry.perm <;> rfl
    | _ => rfl
  | _ => rfl

theorem copyWriteDstVal_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (locals₃ : List LocalSlot) (dstPlace : Place)
    (dstLoc : Local) (dstTag : Nat) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    copyWriteDstVal (MachineState.pushBaseStack calleeBody [] s)
        locals₃ dstPlace dstLoc dstTag newVal localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (copyWriteDstVal s locals₃ dstPlace dstLoc dstTag newVal localDecls layouts) := by
  unfold copyWriteDstVal
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

theorem copyWriteDstVal_isStmtNode
    (s : MachineState) (locals₃ : List LocalSlot) (dstPlace : Place)
    (dstLoc : Local) (dstTag : Nat) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (copyWriteDstVal s locals₃ dstPlace dstLoc dstTag newVal localDecls layouts) := by
  unfold copyWriteDstVal
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

/-- `Trusted`'s destination write `commitCopyDstPlaceWrite` (shared by the statement and call
forms of `copy_nonoverlapping` and by call-form `write_bytes`) is `copyWriteDstVal`. -/
theorem commitCopyDstPlaceWrite_eq_copyWriteDstVal
    (s : MachineState) (dstPlace : Place) (dstLoc : Local) (dstTag : Nat)
    (locals₃ : List LocalSlot) (newVal : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    commitCopyDstPlaceWrite s dstPlace dstLoc dstTag locals₃ newVal localDecls layouts =
      copyWriteDstVal s locals₃ dstPlace dstLoc dstTag newVal localDecls layouts :=
  rfl

theorem commitCopyDstPlaceWriteWithBorrows_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (dstPlace : Place) (locals₃ : List LocalSlot) (newVal : Value)
    (borrows' : List BorrowEntry) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    commitCopyDstPlaceWriteWithBorrows (MachineState.pushBaseStack calleeBody [] s)
        dstPlace locals₃ newVal borrows' localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (commitCopyDstPlaceWriteWithBorrows s dstPlace locals₃ newVal borrows' localDecls
          layouts) := by
  unfold commitCopyDstPlaceWriteWithBorrows
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

theorem commitCopyDstPlaceWriteWithBorrows_isStmtNode
    (s : MachineState) (dstPlace : Place) (locals₃ : List LocalSlot) (newVal : Value)
    (borrows' : List BorrowEntry) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode
      (commitCopyDstPlaceWriteWithBorrows s dstPlace locals₃ newVal borrows' localDecls
        layouts) := by
  unfold commitCopyDstPlaceWriteWithBorrows
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

/-- The multi-element / offset sub-place copy (`evalCopySubplaceMulti`) reads the machine state
only through `Memory.borrows`, `Memory.activeProtectors`, `Memory.callerLocals`, and
`Memory.callStack`, so it commutes with pushing an empty base stack. -/
theorem evalCopySubplaceMulti_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) :
    evalCopySubplaceMulti (MachineState.pushBaseStack calleeBody [] s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody []
        (evalCopySubplaceMulti s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
          countBits locals₃) := by
  unfold evalCopySubplaceMulti
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first
    | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl
    | exact commitCopyDstPlaceWriteWithBorrows_pushBaseStack ..
    | split)

theorem evalCopySubplaceMulti_isStmtNode
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (countBits : Nat)
    (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopySubplaceMulti s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        countBits locals₃) := by
  unfold evalCopySubplaceMulti
  repeat' (first
    | exact commitCopyDstPlaceWriteWithBorrows_isStmtNode ..
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalCopySingleDirect_isStmtNode
    (s : MachineState) (src dst : Operand) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry) (locals₃ : List LocalSlot) :
    IsStmtNode (evalCopySingleDirect s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry locals₃) := by
  unfold evalCopySingleDirect
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalCopyUnionBytes_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat) (locals₃ : List LocalSlot) :
    evalCopyUnionBytes
        (MachineState.pushBaseStack calleeBody [] s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃ =
      MirStepNode.pushBaseStack calleeBody []
        (evalCopyUnionBytes
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
          srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | exact copyWriteDstVal_pushBaseStack .. | split)

theorem evalCopyUnionBytes_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat) (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopyUnionBytes
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry
        srcUnionOpt dstUnionOpt n locals₃) := by
  unfold evalCopyUnionBytes
  dsimp only
  repeat' (first
    | exact copyWriteDstVal_isStmtNode ..
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalCopyNonOverlappingPermOk_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingPermOk
        (MachineState.pushBaseStack calleeBody [] s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody []
        (evalCopyNonOverlappingPermOk
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalCopyNonOverlappingPermOk
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first
    | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl
    | exact evalCopyUnionBytes_pushBaseStack ..
    | exact evalCopySingleDirect_pushBaseStack ..
    | exact evalCopySubplaceMulti_pushBaseStack ..
    | exact copyWriteDstVal_pushBaseStack ..
    | split)

theorem evalCopyNonOverlappingPermOk_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopyNonOverlappingPermOk
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalCopyNonOverlappingPermOk
  dsimp only
  repeat' (first
    | exact evalCopyUnionBytes_isStmtNode ..
    | exact evalCopySingleDirect_isStmtNode ..
    | exact evalCopySubplaceMulti_isStmtNode ..
    | exact copyWriteDstVal_isStmtNode ..
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalForeignFrameCopySingleDirect_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    evalForeignFrameCopySingleDirect
        (MachineState.pushBaseStack calleeBody [] s)
        src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody []
        (evalForeignFrameCopySingleDirect
          s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalForeignFrameCopySingleDirect
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

theorem evalForeignFrameCopySingleDirect_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr) (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat) (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalForeignFrameCopySingleDirect
        s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃) := by
  unfold evalForeignFrameCopySingleDirect
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalCopyNonOverlappingWithCountNonZero_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCountNonZero
        (MachineState.pushBaseStack calleeBody [] s)
        src dst localDecls layouts srcVal dstVal countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody []
        (evalCopyNonOverlappingWithCountNonZero
          s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  rw [evalCopyNonOverlappingWithCountNonZero_eq, evalCopyNonOverlappingWithCountNonZero_eq]
  cases srcVal with
  | ptr srcPtr _ =>
    cases dstVal with
    | ptr dstPtr _ =>
      dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
      cases lookupBorrow s.memory.borrows srcPtr.tag with
      | none => rfl
      | some srcEntry =>
        cases lookupBorrow s.memory.borrows dstPtr.tag with
        | none => rfl
        | some dstEntry =>
          dsimp only
          cases srcEntry.perm <;> cases dstEntry.perm <;>
            first
            | rfl
            | (cases copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry with
               | false =>
                 exact evalForeignFrameCopySingleDirect_pushBaseStack calleeBody
                   s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃
               | true =>
                 exact evalCopyNonOverlappingPermOk_pushBaseStack calleeBody
                   s src dst localDecls layouts srcPtr dstPtr srcEntry dstEntry countBits locals₃)
    | _ => rfl
  | _ => rfl

/-- The zero-byte `copy_nonoverlapping` precondition never reads `Memory.activeCallee`, so it is
invariant under `MachineState.pushBaseStack` with an empty base stack. -/
theorem zeroByteCopyPrecheck_pushBaseStack
    (calleeBody : CapturedMir) (s : MachineState) (locals₃ : List LocalSlot)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (elemAlign : Nat)
    (srcVal dstVal : Value) :
    zeroByteCopyPrecheck (MachineState.pushBaseStack calleeBody [] s) locals₃ localDecls layouts
        elemAlign srcVal dstVal =
      zeroByteCopyPrecheck s locals₃ localDecls layouts elemAlign srcVal dstVal := rfl

/-- With no Tree Borrows entries, the zero-byte `copy_nonoverlapping` precondition reads neither
`Memory.callStack` nor `Memory.activeCallee` (no stack-borrow resolution happens), so it is
invariant under `MachineState.pushBaseStack` for every base stack. -/
theorem zeroByteCopyPrecheck_pushBaseStack_of_borrows_nil
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame) (s : MachineState)
    (locals₃ : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemAlign : Nat) (srcVal dstVal : Value) (h_nil : s.memory.borrows = []) :
    zeroByteCopyPrecheck (MachineState.pushBaseStack calleeBody baseStack s) locals₃ localDecls
        layouts elemAlign srcVal dstVal =
      zeroByteCopyPrecheck s locals₃ localDecls layouts elemAlign srcVal dstVal := by
  have hc : ∀ v, checkZeroCountCopyPtr (MachineState.pushBaseStack calleeBody baseStack s) locals₃
      localDecls layouts elemAlign v =
      checkZeroCountCopyPtr s locals₃ localDecls layouts elemAlign v := by
    intro v
    unfold checkZeroCountCopyPtr
    cases v <;> simp [MachineState.pushBaseStack, Memory.pushBaseStack, h_nil, lookupBorrow]
  unfold zeroByteCopyPrecheck
  rw [hc, hc]

theorem evalCopyNonOverlappingWithCount_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCount
        (MachineState.pushBaseStack calleeBody [] s)
        src dst localDecls layouts srcVal dstVal countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody []
        (evalCopyNonOverlappingWithCount
          s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  unfold evalCopyNonOverlappingWithCount
  simp only [zeroByteCopyPrecheck_pushBaseStack, evalCopyNonOverlappingWithCountNonZero_pushBaseStack]
  repeat' (first | rfl | exact step_push_fail | exact step_push_unsupported | (dsimp only) | split)

theorem evalCopyNonOverlappingWithCountNonZero_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopyNonOverlappingWithCountNonZero
        s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  rw [evalCopyNonOverlappingWithCountNonZero_eq]
  cases srcVal with
  | ptr srcPtr _ =>
    cases dstVal with
    | ptr dstPtr _ =>
      dsimp only
      cases lookupBorrow s.memory.borrows srcPtr.tag with
      | none => exact Or.inr (Or.inl ⟨_, rfl⟩)
      | some srcEntry =>
        cases lookupBorrow s.memory.borrows dstPtr.tag with
        | none => exact Or.inr (Or.inl ⟨_, rfl⟩)
        | some dstEntry =>
          dsimp only
          cases srcEntry.perm <;> cases dstEntry.perm <;>
            first
            | exact Or.inr (Or.inl ⟨_, rfl⟩)
            | (cases copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry with
               | false => exact evalForeignFrameCopySingleDirect_isStmtNode ..
               | true => exact evalCopyNonOverlappingPermOk_isStmtNode ..)
    | _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | _ => exact Or.inr (Or.inl ⟨_, rfl⟩)

theorem evalCopyNonOverlappingWithCount_isStmtNode
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot) :
    IsStmtNode
      (evalCopyNonOverlappingWithCount
        s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  have hNZ := evalCopyNonOverlappingWithCountNonZero_isStmtNode s src dst localDecls layouts
    srcVal dstVal countBits locals₃
  unfold evalCopyNonOverlappingWithCount
  dsimp only
  repeat' (first
    | (dsimp only)
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | exact hNZ
    | split)

/-- With no Tree Borrows entries, the statement-form `copy_nonoverlapping` core either copies
nothing (a zero-byte copy: it only advances), fails closed, or faults (no borrow entry for a
pointer argument of a non-zero-byte copy). -/
theorem evalCopyNonOverlappingWithCount_borrows_nil
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot)
    (h_nil : s.memory.borrows = []) :
    evalCopyNonOverlappingWithCount
        s src dst localDecls layouts srcVal dstVal countBits locals₃ =
      MirStepNode.step (advanceStmt s locals₃) ∨
    evalCopyNonOverlappingWithCount
        s src dst localDecls layouts srcVal dstVal countBits locals₃ =
      MirStepNode.unsupported ∨
    ∃ fk : FailureKind,
      evalCopyNonOverlappingWithCount
          s src dst localDecls layouts srcVal dstVal countBits locals₃ =
        MirStepNode.fail fk := by
  have hNZ : ∃ fk : FailureKind,
      evalCopyNonOverlappingWithCountNonZero s src dst localDecls layouts srcVal dstVal countBits
        locals₃ = MirStepNode.fail fk := by
    rw [evalCopyNonOverlappingWithCountNonZero_eq]
    cases srcVal with
    | ptr srcPtr _ =>
      cases dstVal with
      | ptr dstPtr _ =>
        dsimp only
        rw [h_nil]
        exact ⟨_, rfl⟩
      | _ => exact ⟨_, rfl⟩
    | _ => exact ⟨_, rfl⟩
  unfold evalCopyNonOverlappingWithCount
  dsimp only
  repeat' (first
    | (dsimp only)
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr ⟨_, rfl⟩)
    | exact Or.inr (Or.inr hNZ)
    | split)

/-- With no Tree Borrows entries, the statement-form `copy_nonoverlapping` core commutes with
`MachineState.pushBaseStack` for every base stack. -/
theorem evalCopyNonOverlappingWithCount_pushBaseStack_of_borrows_nil
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcVal dstVal : Value) (countBits : Nat) (locals₃ : List LocalSlot)
    (h_nil : s.memory.borrows = []) :
    evalCopyNonOverlappingWithCount
        (MachineState.pushBaseStack calleeBody baseStack s)
        src dst localDecls layouts srcVal dstVal countBits locals₃ =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalCopyNonOverlappingWithCount
          s src dst localDecls layouts srcVal dstVal countBits locals₃) := by
  have hNZ : ∀ (s' : MachineState), s'.memory.borrows = [] →
      evalCopyNonOverlappingWithCountNonZero s' src dst localDecls layouts srcVal dstVal
        countBits locals₃ = MirStepNode.fail .ub := by
    intro s' h'
    rw [evalCopyNonOverlappingWithCountNonZero_eq]
    cases srcVal with
    | ptr srcPtr _ =>
      cases dstVal with
      | ptr dstPtr _ =>
        dsimp only
        rw [h']
        rfl
      | _ => rfl
    | _ => rfl
  have h₁ := hNZ (MachineState.pushBaseStack calleeBody baseStack s) h_nil
  have h₂ := hNZ s h_nil
  unfold evalCopyNonOverlappingWithCount
  simp only [zeroByteCopyPrecheck_pushBaseStack_of_borrows_nil calleeBody baseStack s locals₃
    localDecls layouts _ srcVal dstVal h_nil, h₁, h₂]
  repeat' (first | rfl | exact step_push_fail | exact step_push_unsupported | (dsimp only) | split)

theorem evalCopyNonOverlapping_isStmtNode
    (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  cases evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
  | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | unsupported => exact Or.inr (Or.inr rfl)
  | ok srcVal locals₁ =>
    dsimp only
    cases evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
    | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | unsupported => exact Or.inr (Or.inr rfl)
    | ok dstVal locals₂ =>
      dsimp only
      cases evalOperand locals₂ count s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
      | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
      | unsupported => exact Or.inr (Or.inr rfl)
      | ok countVal locals₃ =>
        cases countVal with
        | scalar countSc =>
          dsimp only
          cases countScalarWellFormed (layoutPointerBytes layouts) countSc with
          | false => exact Or.inr (Or.inl ⟨_, rfl⟩)
          | true =>
            exact evalCopyNonOverlappingWithCount_isStmtNode s src dst localDecls layouts
              srcVal dstVal countSc.bits locals₃
        | _ => exact Or.inr (Or.inl ⟨_, rfl⟩)

theorem evalCopyNonOverlapping_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (src dst count : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalCopyNonOverlapping
        (MachineState.pushBaseStack calleeBody [] s)
        src dst count localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (evalCopyNonOverlapping s src dst count localDecls layouts) := by
  unfold evalCopyNonOverlapping
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  cases evalOperand s.frame.locals src s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
  | ub => rfl
  | unsupported => rfl
  | ok srcVal locals₁ =>
    dsimp only
    cases evalOperand locals₁ dst s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
    | ub => rfl
    | unsupported => rfl
    | ok dstVal locals₂ =>
      dsimp only
      cases evalOperand locals₂ count s.memory.borrows s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
      | ub => rfl
      | unsupported => rfl
      | ok countVal locals₃ =>
        cases countVal with
        | scalar countSc =>
          dsimp only
          cases countScalarWellFormed (layoutPointerBytes layouts) countSc with
          | false => rfl
          | true =>
            exact evalCopyNonOverlappingWithCount_pushBaseStack
              calleeBody s src dst localDecls layouts
              srcVal dstVal countSc.bits locals₃
        | _ => rfl

/--
`evalStmt` is completely independent of `Memory.callStack` and
`Memory.activeCallee`, commuting unconditionally with `MachineState.pushBaseStack`.
-/
def FrameWriteResult.pushBaseStack
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame) :
    FrameWriteResult → FrameWriteResult
  | .ok l m => .ok l (Memory.pushBaseStack calleeBody baseStack m)
  | .ub => .ub
  | .unsupported => .unsupported

theorem fw_push_ub {c : CapturedMir} {b : List SavedCallerFrame} :
    FrameWriteResult.ub = FrameWriteResult.pushBaseStack c b .ub := rfl
theorem fw_push_unsupported {c : CapturedMir} {b : List SavedCallerFrame} :
    FrameWriteResult.unsupported = FrameWriteResult.pushBaseStack c b .unsupported := rfl
theorem fw_push_ok {c : CapturedMir} {b : List SavedCallerFrame}
    {l : List LocalSlot} {m₁ m₂ : Memory} (h : m₁ = Memory.pushBaseStack c b m₂) :
    FrameWriteResult.ok l m₁ = FrameWriteResult.pushBaseStack c b (.ok l m₂) := h ▸ rfl

theorem commitForeignFrameLocals_pushBaseStack
    (calleeBody : CapturedMir) (mem₁ : Memory)
    (target : ForeignFrameTarget) (targetLocals' : List LocalSlot) :
    commitForeignFrameLocals (Memory.pushBaseStack calleeBody [] mem₁) target targetLocals' =
      (commitForeignFrameLocals mem₁ target targetLocals').map
        (Memory.pushBaseStack calleeBody []) := by
  cases target with
  | callerReferent _ => rfl
  | savedFrame idx _ =>
    unfold commitForeignFrameLocals
    dsimp only [Memory.pushBaseStack]
    cases get? mem₁.callStack idx with
    | none => rfl
    | some sf =>
      dsimp only
      cases set? mem₁.callStack idx { sf with frame := { sf.frame with locals := targetLocals' } } <;> rfl

theorem foreignFrameDerefWrite_pushBaseStack
    (calleeBody : CapturedMir)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (dst : Place) (restProj : List ProjectionElem) (val : Value)
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    foreignFrameDerefWrite locals₁
        (Memory.pushBaseStack calleeBody [] mem₁) dst restProj val localDecls layouts =
      FrameWriteResult.pushBaseStack calleeBody []
        (foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold foreignFrameDerefWrite
  simp only [commitForeignFrameLocals_pushBaseStack]
  dsimp only [Memory.pushBaseStack]
  cases get? locals₁ dst.local_ with
  | none => rfl
  | some sl =>
    cases sl with
    | uninit | dead => rfl
    | init pv =>
      dsimp only
      cases extractDerefPtrVal? pv with
      | none => rfl
      | some ptrVal =>
        dsimp only
        cases lookupBorrow mem₁.borrows ptrVal.tag with
        | none => rfl
        | some entry =>
          dsimp only
          cases activeFrameSlot? locals₁ mem₁.callStack entry.targetFrameDepth entry.targetLocal with
          | some _ => rfl
          | none =>
            dsimp only
            cases foreignFrameTarget? mem₁.callStack mem₁.callerLocals entry.targetFrameDepth entry.targetLocal with
            | none => rfl
            | some target =>
              cases target <;>
              ( dsimp only
                cases evalCallerPlaceWrite locals₁ _ mem₁.borrows dst val mem₁.activeProtectors _ _ mem₁.callStack with
                | ub => rfl
                | unsupported => rfl
                | ok tl' =>
                  dsimp only
                  cases foreignFrameDeclsAndLayouts mem₁.callStack layouts entry.targetFrameDepth entry.targetLocal with
                  | mk td tly =>
                    dsimp only
                    cases derefWriteTreeUB locals₁ mem₁.borrows dst ||
                        derefWriteUnionProtectorUB td tly locals₁ mem₁.borrows mem₁.activeProtectors dst restProj mem₁.callStack with
                    | true => rfl
                    | false =>
                      dsimp only
                      cases commitForeignFrameLocals mem₁ _ tl' <;> rfl )

theorem evalForeignFrameDerefWrite_pushBaseStack
    (calleeBody : CapturedMir) (s : MachineState)
    (locals₁ : List LocalSlot) (mem₁ : Memory)
    (dst : Place) (restProj : List ProjectionElem) (val : Value)
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    evalForeignFrameDerefWrite
        (MachineState.pushBaseStack calleeBody [] s)
        locals₁
        (Memory.pushBaseStack calleeBody [] mem₁)
        dst restProj val localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts) := by
  unfold evalForeignFrameDerefWrite
  rw [foreignFrameDerefWrite_pushBaseStack calleeBody locals₁ mem₁ dst restProj val localDecls layouts]
  cases foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts <;> rfl

theorem evalSetDiscriminantDerefWrite_pushBaseStack
    (calleeBody : CapturedMir) (s : MachineState)
    (locals₁ : List LocalSlot) (p : Place) (rest : List ProjectionElem) (newVal : Value)
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    evalSetDiscriminantDerefWrite
        (MachineState.pushBaseStack calleeBody [] s)
        locals₁ p rest newVal localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts) := by
  have h_ff :=
    evalForeignFrameDerefWrite_pushBaseStack calleeBody s locals₁ s.memory p rest newVal localDecls layouts
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack] at h_ff
  unfold evalSetDiscriminantDerefWrite
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | exact h_ff | split)

theorem writeReturnDestination_nonDeref
    (callerLocals : List LocalSlot) (mem : Memory) (loc : Local)
    (hd : ProjectionElem) (tl : List ProjectionElem)
    (retVal : Value) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (h_nd : hd ≠ .deref)
    (h_nr : stripLeadingOpaqueCast (hd :: tl) ≠ []) :
    writeReturnDestination callerLocals mem ⟨loc, hd :: tl⟩ retVal localDecls layouts =
      let depth := length mem.callStack
      let decls' := eraseLeadingOpaqueCastDecls localDecls layouts loc (hd :: tl)
      let resolvedLocalProj :=
        resolveBorrowWriteLocalProj decls' layouts callerLocals loc (hd :: tl)
      match
        hasProtectedWriteConflict mem.borrows mem.activeProtectors loc .none
          resolvedLocalProj 0 0 depth
      with
      | true => .ub
      | false =>
        let rootOpt : Option Value :=
          match get? callerLocals loc with
          | .some (.init rootVal) =>
            ensureNestedFieldShells rootVal (hd :: tl) decls' layouts
              (placeTy decls' layouts { local_ := loc, projection := .nil })
          | .some .uninit => uninitFieldWriteShell? localDecls layouts loc hd tl
          | _ => .none
        match rootOpt with
        | .none => .ub
        | .some rootVal =>
          match writeProjectedForLocal callerLocals decls' layouts loc rootVal (hd :: tl) retVal with
          | .ok rootVal' =>
            match set? callerLocals loc (.init rootVal') with
            | .some locals' =>
              .ok locals'
                { mem with
                  borrows :=
                    invalidateConflictingBorrowsAtProj mem.borrows loc .none
                      resolvedLocalProj 0 0 depth }
            | .none => .ub
          | .ub => .ub
          | .unsupported => .unsupported := by
  unfold writeReturnDestination
  dsimp only
  split
  · rename_i h; cases h
  · rename_i h; cases h; exact False.elim (h_nd rfl)
  · rename_i _ h; exact False.elim (h_nr h)
  · rename_i h _; cases h; rfl

private theorem evalFnEntryRetag_pushBaseStack
    (calleeBody : CapturedMir) (s : MachineState) (ld : List LocalDecl) (ly : LayoutTable)
    (place : Place) (pv : ProvenancePtr) (sz : Nat) (e : BorrowEntry) (l' : List LocalSlot) :
    evalFnEntryRetag (MachineState.pushBaseStack calleeBody [] s) ld ly place pv sz e l' =
      MirStepNode.pushBaseStack calleeBody [] (evalFnEntryRetag s ld ly place pv sz e l') := by
  unfold evalFnEntryRetag
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

private theorem evalNonFnEntryRetag_pushBaseStack
    (calleeBody : CapturedMir) (rk : RetagKind) (s : MachineState) (ld : List LocalDecl) (ly : LayoutTable)
    (place : Place) (pv : ProvenancePtr) (sz : Nat) (e : BorrowEntry) (l' : List LocalSlot) :
    evalNonFnEntryRetag rk (MachineState.pushBaseStack calleeBody [] s) ld ly place pv sz e l' =
      MirStepNode.pushBaseStack calleeBody [] (evalNonFnEntryRetag rk s ld ly place pv sz e l') := by
  unfold evalNonFnEntryRetag
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

private theorem evalStmt_retag_pushBaseStack
    (calleeBody : CapturedMir) (s : MachineState) (rk : RetagKind) (p : Place)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt (MachineState.pushBaseStack calleeBody [] s) ⟨.retag rk p, span⟩ localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (evalStmt s ⟨.retag rk p, span⟩ localDecls layouts) := by
  unfold evalStmt
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first
    | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl
    | exact evalFnEntryRetag_pushBaseStack calleeBody ..
    | exact evalNonFnEntryRetag_pushBaseStack calleeBody ..
    | split)

private theorem evalStmt_setDiscriminant_pushBaseStack
    (calleeBody : CapturedMir) (s : MachineState) (p : Place) (variantIdx : Nat)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt (MachineState.pushBaseStack calleeBody [] s) ⟨.setDiscriminant p variantIdx, span⟩ localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (evalStmt s ⟨.setDiscriminant p variantIdx, span⟩ localDecls layouts) := by
  rcases p with ⟨pLoc, _ | ⟨phd, ptl⟩⟩
  · unfold evalStmt evalSetDiscriminantLocal
    dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
    repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
  · by_cases h_d : phd = .deref
    · subst h_d
      have h_sdw (l₁ : List LocalSlot) (rp : List ProjectionElem) (nv : Value) :=
        evalSetDiscriminantDerefWrite_pushBaseStack calleeBody s l₁ ⟨pLoc, .deref :: rp⟩ rp nv localDecls layouts
      dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack] at h_sdw
      unfold evalStmt
      dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
      cases evalOperand s.frame.locals (.copy ⟨pLoc, .deref :: ptl⟩) s.memory.borrows
          s.memory.globals layouts s.memory.callerLocals localDecls s.memory.callStack with
      | unsupported => rfl
      | ok v l1 =>
        cases v with
        | aggregate _ fields =>
          dsimp only
          cases padSetDiscriminantInitFields? localDecls layouts ⟨pLoc, .deref :: ptl⟩ variantIdx fields with
          | none => rfl
          | some _ => exact h_sdw _ _ _
        | _ => rfl
      | ub =>
        cases ptl with
        | cons _ _ => rfl
        | nil =>
          dsimp only
          repeat' (first
            | exact step_push_fail
            | exact step_push_unsupported
            | exact step_push_step rfl
            | exact h_sdw _ _ _
            | split)
          all_goals
            dsimp only
            repeat' (first
              | exact step_push_fail
              | exact step_push_unsupported
              | exact step_push_step rfl
              | exact h_sdw _ _ _
              | split)
    · rcases stripLeadingOpaqueCast_eq_nil_or_ne_nil (phd :: ptl) with h_s | h_nr
      · rw [evalStmt_setDiscriminant_castRoot _ _ _ _ _ _ _ _ h_s,
            evalStmt_setDiscriminant_castRoot _ _ _ _ _ _ _ _ h_s]
        unfold evalStmt evalSetDiscriminantLocal
        dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
        repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
      · rw [evalStmt_setDiscriminant_nonDeref _ _ _ _ _ _ _ _ h_d h_nr,
            evalStmt_setDiscriminant_nonDeref _ _ _ _ _ _ _ _ h_d h_nr]
        dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
        repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

private theorem evalStmt_deinit_pushBaseStack
    (calleeBody : CapturedMir) (s : MachineState) (p : Place) (span : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt (MachineState.pushBaseStack calleeBody [] s)
        { kind := .deinit p, span := span } localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (evalStmt s { kind := .deinit p, span := span } localDecls layouts) := by
  unfold evalStmt
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

theorem evalTerminator_drop_pushBaseStack_nil
    (calleeBody : CapturedMir) (s : MachineState)
    (place : Place) (target : BasicBlockIdx) (unwind : UnwindAction) (sp : String)
    (curOpt : Option CapturedMir) :
    evalTerminator (MachineState.pushBaseStack calleeBody [] s)
        { kind := .drop place target unwind, span := sp } curOpt =
      MirStepNode.pushBaseStack calleeBody []
        (evalTerminator s { kind := .drop place target unwind, span := sp } curOpt) := by
  unfold evalTerminator
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
  repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

theorem evalTerminator_drop_pushBaseStack_borrows_nil
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame) (s : MachineState)
    (place : Place) (target : BasicBlockIdx) (unwind : UnwindAction) (sp : String)
    (curOpt : Option CapturedMir)
    (h_bor : s.memory.borrows = []) :
    evalTerminator (MachineState.pushBaseStack calleeBody baseStack s)
        { kind := .drop place target unwind, span := sp } curOpt =
      MirStepNode.pushBaseStack calleeBody baseStack
        (evalTerminator s { kind := .drop place target unwind, span := sp } curOpt) := by
  rcases place with ⟨loc, proj⟩
  have h_main : ∀ (proj : List ProjectionElem),
      (proj = [] ∨ stripLeadingOpaqueCast proj ≠ []) →
      evalTerminator (MachineState.pushBaseStack calleeBody baseStack s)
          { kind := .drop ⟨loc, proj⟩ target unwind, span := sp } curOpt =
        MirStepNode.pushBaseStack calleeBody baseStack
          (evalTerminator s { kind := .drop ⟨loc, proj⟩ target unwind, span := sp } curOpt) := by
    intro proj h_nr
    have h_pbs_bor : (MachineState.pushBaseStack calleeBody baseStack s).memory.borrows = [] := h_bor
    rw [evalTerminator_drop_borrows_nil (s := MachineState.pushBaseStack calleeBody baseStack s) h_pbs_bor h_nr,
        evalTerminator_drop_borrows_nil (s := s) h_bor h_nr]
    unfold evalDropBorrowsNil
    dsimp only [MachineState.pushBaseStack]
    cases get? s.frame.locals loc with
    | none => exact step_push_fail
    | some sl =>
      cases sl with
      | dead => exact step_push_fail
      | uninit =>
        dsimp only
        cases proj with
        | nil =>
          dsimp only
          cases set? s.frame.locals loc .uninit with
          | none => exact step_push_fail
          | some _ => exact step_push_step rfl
        | cons phd ptl =>
          dsimp only
          cases deinitTailOk s.frame.locals _ _ _ (phd :: ptl) with
          | true => exact step_push_step rfl
          | false =>
            dsimp only
            cases projectionHasDeref (phd :: ptl) with
            | true => exact step_push_unsupported
            | false => exact step_push_fail
      | init rv =>
        dsimp only
        cases proj with
        | nil =>
          dsimp only
          cases set? s.frame.locals loc .uninit with
          | none => exact step_push_fail
          | some _ => exact step_push_step rfl
        | cons phd ptl =>
          dsimp only
          cases deinitProjectedForLocal s.frame.locals _ _ loc rv (phd :: ptl) with
          | ub => exact step_push_fail
          | unsupported => exact step_push_unsupported
          | ok rv' =>
            dsimp only
            cases set? s.frame.locals loc (.init rv') with
            | none => exact step_push_fail
            | some _ => exact step_push_step rfl
  cases proj with
  | nil => exact h_main [] (Or.inl rfl)
  | cons hd tl =>
    rcases stripLeadingOpaqueCast_eq_nil_or_ne_nil (hd :: tl) with h_s | h_nr
    · rw [evalTerminator_drop_castRoot _ _ _ _ _ _ _ _ h_s,
          evalTerminator_drop_castRoot _ _ _ _ _ _ _ _ h_s]
      exact h_main [] (Or.inl rfl)
    · exact h_main (hd :: tl) (Or.inr h_nr)

theorem evalStmt_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    evalStmt (MachineState.pushBaseStack calleeBody [] s)
        stmt localDecls layouts =
      MirStepNode.pushBaseStack calleeBody []
        (evalStmt s stmt localDecls layouts) := by
  rcases stmt with ⟨kind, span⟩
  cases kind with
  | nop | coverage | constEvalCounter | backwardIncompatibleDropHint _ => rfl
  | placeMention p =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack]
    repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
  | retag rk p =>
    exact evalStmt_retag_pushBaseStack calleeBody s rk p span localDecls layouts
  | storageLive loc | storageDead loc =>
    unfold evalStmt
    dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
    repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
  | deinit p =>
    exact evalStmt_deinit_pushBaseStack calleeBody s p span localDecls layouts
  | intrinsic intr =>
    cases intr with
    | assume op =>
      unfold evalStmt
      dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
      repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
    | copyNonOverlapping src dst count =>
      exact evalCopyNonOverlapping_pushBaseStack calleeBody
        s src dst count localDecls layouts
  | setDiscriminant p variantIdx =>
    exact evalStmt_setDiscriminant_pushBaseStack calleeBody s p variantIdx span localDecls layouts
  | assign dst rv =>
    rw [evalStmt_assign_eq, evalStmt_assign_eq]
    dsimp only [MachineState.pushBaseStack]
    rw [evalRvalue_pushBaseStack calleeBody
      s.frame.locals rv s.memory localDecls layouts]
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub => rfl
    | unsupported => rfl
    | ok val locals₁ mem₁ =>
      dsimp only [RvalueEvalResult.pushBaseStack, Memory.pushBaseStack]
      rcases dst with ⟨dstLoc, dstProj⟩
      cases dstProj with
      | nil =>
        unfold evalAssignDst
        dsimp only [Memory.pushBaseStack]
        repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
      | cons hd tl =>
        by_cases h_d : hd = .deref
        · subst h_d
          have h_ff := evalForeignFrameDerefWrite_pushBaseStack calleeBody s locals₁ mem₁ ⟨dstLoc, .deref :: tl⟩ tl val localDecls layouts
          dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack] at h_ff
          unfold evalAssignDst
          dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]
          repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | exact h_ff | split)
        · rcases stripLeadingOpaqueCast_eq_nil_or_ne_nil (hd :: tl) with h_s | h_nr
          · rw [evalAssignDst_castRoot _ _ _ _ _ _ _ _ _ h_s,
                evalAssignDst_castRoot _ _ _ _ _ _ _ _ _ h_s]
            unfold evalAssignDst
            dsimp only [Memory.pushBaseStack]
            repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)
          · rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_d h_nr,
                evalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_d h_nr]
            unfold evalAssignNonDeref
            dsimp only [Memory.pushBaseStack]
            repeat' (first | exact step_push_fail | exact step_push_unsupported | exact step_push_step rfl | split)

private theorem evalFnEntryRetag_isStmtNode
    (s : MachineState) (ld : List LocalDecl) (ly : LayoutTable)
    (place : Place) (pv : ProvenancePtr) (sz : Nat) (e : BorrowEntry) (l' : List LocalSlot) :
    IsStmtNode (evalFnEntryRetag s ld ly place pv sz e l') := by
  unfold evalFnEntryRetag; dsimp only
  repeat' (first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr rfl) | split)

private theorem evalNonFnEntryRetag_isStmtNode
    (rk : RetagKind) (s : MachineState) (ld : List LocalDecl) (ly : LayoutTable)
    (place : Place) (pv : ProvenancePtr) (sz : Nat) (e : BorrowEntry) (l' : List LocalSlot) :
    IsStmtNode (evalNonFnEntryRetag rk s ld ly place pv sz e l') := by
  unfold evalNonFnEntryRetag; dsimp only
  repeat' (first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr rfl) | split)

private theorem evalStmt_retag_isStmtNode
    (s : MachineState) (rk : RetagKind) (p : Place) (sp : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (evalStmt s ⟨.retag rk p, sp⟩ localDecls layouts) := by
  unfold evalStmt; dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr rfl)
    | exact evalFnEntryRetag_isStmtNode ..
    | exact evalNonFnEntryRetag_isStmtNode ..
    | split)

private theorem evalSetDiscriminantDerefWrite_isStmtNode
    (s : MachineState) (l1 : List LocalSlot) (p : Place) (rest : List ProjectionElem)
    (nv : Value) (ld : List LocalDecl) (ly : LayoutTable) :
    IsStmtNode (evalSetDiscriminantDerefWrite s l1 p rest nv ld ly) := by
  unfold evalSetDiscriminantDerefWrite evalForeignFrameDerefWrite; dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

private theorem evalStmt_setDiscriminant_isStmtNode
    (s : MachineState) (p : Place) (vi : Nat) (sp : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (evalStmt s ⟨.setDiscriminant p vi, sp⟩ localDecls layouts) := by
  rcases p with ⟨pLoc, _ | ⟨phd, ptl⟩⟩
  · unfold evalStmt evalSetDiscriminantLocal; dsimp only
    repeat' (first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr (Or.inl ⟨_, rfl⟩)
      | exact Or.inr (Or.inr rfl)
      | split)
  · by_cases h_d : phd = .deref
    · subst h_d
      unfold evalStmt; dsimp only
      repeat' (first
        | exact Or.inl ⟨_, rfl⟩
        | exact Or.inr (Or.inl ⟨_, rfl⟩)
        | exact Or.inr (Or.inr rfl)
        | exact evalSetDiscriminantDerefWrite_isStmtNode ..
        | split)
    · rcases stripLeadingOpaqueCast_eq_nil_or_ne_nil (phd :: ptl) with h_s | h_nr
      · rw [evalStmt_setDiscriminant_castRoot _ _ _ _ _ _ _ _ h_s]
        unfold evalStmt evalSetDiscriminantLocal; dsimp only
        repeat' (first
          | exact Or.inl ⟨_, rfl⟩
          | exact Or.inr (Or.inl ⟨_, rfl⟩)
          | exact Or.inr (Or.inr rfl)
          | split)
      · rw [evalStmt_setDiscriminant_nonDeref _ _ _ _ _ _ _ _ h_d h_nr]; dsimp only
        repeat' (first
          | exact Or.inl ⟨_, rfl⟩
          | exact Or.inr (Or.inl ⟨_, rfl⟩)
          | exact Or.inr (Or.inr rfl)
          | split)

private theorem evalStmt_deinit_isStmtNode
    (s : MachineState) (p : Place) (sp : String)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (evalStmt s { kind := .deinit p, span := sp } localDecls layouts) := by
  unfold evalStmt
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalTerminator_drop_isStmtNode
    (s : MachineState) (place : Place) (target : BasicBlockIdx)
    (unwind : UnwindAction) (sp : String)
    (curOpt : Option CapturedMir) :
    IsStmtNode (evalTerminator s { kind := .drop place target unwind, span := sp } curOpt) := by
  unfold evalTerminator
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr rfl)
    | split)

theorem evalStmt_isStmtNode
    (s : MachineState) (stmt : Statement)
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    IsStmtNode (evalStmt s stmt localDecls layouts) := by
  have h_ff : ∀ l₁ m₁ dst rp v,
      IsStmtNode (evalForeignFrameDerefWrite s l₁ m₁ dst rp v localDecls layouts) := by
    intro l₁ m₁ dst rp v
    unfold evalForeignFrameDerefWrite
    cases foreignFrameDerefWrite l₁ m₁ dst rp v localDecls layouts with
    | ok _ _ => exact Or.inl ⟨_, rfl⟩
    | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | unsupported => exact Or.inr (Or.inr rfl)
  rcases stmt with ⟨kind, sp⟩
  cases kind with
  | nop | coverage | constEvalCounter | backwardIncompatibleDropHint _ =>
    exact Or.inl ⟨_, rfl⟩
  | placeMention p =>
    unfold evalStmt; dsimp only
    cases get? s.frame.locals p.local_ with
    | none => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | some sl =>
      cases sl with
      | dead => exact Or.inr (Or.inl ⟨_, rfl⟩)
      | uninit | init _ =>
        dsimp only
        cases placeMentionOperandsInit s.frame.locals _ p.projection with
        | true => exact Or.inl ⟨_, rfl⟩
        | false => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | storageLive _ | storageDead _ =>
    unfold evalStmt; dsimp only
    repeat' (first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr (Or.inl ⟨_, rfl⟩)
      | exact Or.inr (Or.inr rfl)
      | split)
  | deinit p =>
    exact evalStmt_deinit_isStmtNode s p sp localDecls layouts
  | retag rk p =>
    exact evalStmt_retag_isStmtNode s rk p sp localDecls layouts
  | setDiscriminant p vi =>
    exact evalStmt_setDiscriminant_isStmtNode s p vi sp localDecls layouts
  | intrinsic intr =>
    cases intr with
    | assume op =>
      unfold evalStmt; dsimp only
      cases evalOperand s.frame.locals op s.memory.borrows s.memory.globals layouts
          s.memory.callerLocals localDecls s.memory.callStack with
      | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
      | unsupported => exact Or.inr (Or.inr rfl)
      | ok v _ =>
        cases v with
        | scalar sc =>
          dsimp only
          cases Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
          | true => exact Or.inl ⟨_, rfl⟩
          | false => exact Or.inr (Or.inl ⟨_, rfl⟩)
        | _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | copyNonOverlapping src dst count =>
      exact evalCopyNonOverlapping_isStmtNode s src dst count localDecls layouts
  | assign dst rv =>
    rw [evalStmt_assign_eq]
    cases evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | unsupported => exact Or.inr (Or.inr rfl)
    | ok val locals₁ mem₁ =>
      dsimp only
      rcases dst with ⟨dstLoc, dstProj⟩
      cases dstProj with
      | nil =>
        unfold evalAssignDst; dsimp only
        cases get? locals₁ dstLoc with
        | none => exact Or.inr (Or.inl ⟨_, rfl⟩)
        | some sl =>
          cases sl with
          | dead => exact Or.inr (Or.inl ⟨_, rfl⟩)
          | uninit | init _ =>
            dsimp only
            cases set? locals₁ dstLoc (.init val) with
            | none => exact Or.inr (Or.inl ⟨_, rfl⟩)
            | some _ =>
              cases mem₁.activeProtectors with
              | nil => exact Or.inl ⟨_, rfl⟩
              | cons ph pt =>
                dsimp only
                cases hasProtectedWriteConflict mem₁.borrows (ph :: pt) dstLoc .none .nil 0 0
                    (length mem₁.callStack) with
                | true => exact Or.inr (Or.inl ⟨_, rfl⟩)
                | false => exact Or.inl ⟨_, rfl⟩
      | cons hd tl =>
        by_cases h_d : hd = .deref
        · subst h_d
          unfold evalAssignDst; dsimp only
          cases evalPlaceWrite locals₁ mem₁.borrows ⟨dstLoc, .deref :: tl⟩ val
              mem₁.activeProtectors localDecls layouts mem₁.callStack with
          | unsupported => exact Or.inr (Or.inr rfl)
          | ok _ =>
            dsimp only
            cases derefWriteTreeUB locals₁ mem₁.borrows ⟨dstLoc, .deref :: tl⟩ ||
                derefWriteUnionProtectorUB localDecls layouts locals₁ mem₁.borrows
                  mem₁.activeProtectors ⟨dstLoc, .deref :: tl⟩ tl mem₁.callStack with
            | true => exact Or.inr (Or.inl ⟨_, rfl⟩)
            | false => exact Or.inl ⟨_, rfl⟩
          | ub =>
            dsimp only
            cases mem₁.callStack with
            | cons _ _ => exact h_ff ..
            | nil =>
              cases mem₁.callerLocals with
              | nil => exact Or.inr (Or.inl ⟨_, rfl⟩)
              | cons _ _ =>
                dsimp only
                cases evalCallerPlaceWrite locals₁ _ mem₁.borrows ⟨dstLoc, .deref :: tl⟩ val
                    mem₁.activeProtectors with
                | ub => exact Or.inr (Or.inl ⟨_, rfl⟩)
                | unsupported => exact Or.inr (Or.inr rfl)
                | ok _ =>
                  dsimp only
                  cases derefWriteTreeUB locals₁ mem₁.borrows ⟨dstLoc, .deref :: tl⟩ with
                  | true => exact Or.inr (Or.inl ⟨_, rfl⟩)
                  | false => exact Or.inl ⟨_, rfl⟩
        · rcases stripLeadingOpaqueCast_eq_nil_or_ne_nil (hd :: tl) with h_s | h_nr
          · rw [evalAssignDst_castRoot _ _ _ _ _ _ _ _ _ h_s]
            unfold evalAssignDst; dsimp only
            repeat' (first
              | exact Or.inl ⟨_, rfl⟩
              | exact Or.inr (Or.inl ⟨_, rfl⟩)
              | exact Or.inr (Or.inr rfl)
              | split)
          · rw [evalAssignDst_nonDeref _ _ _ _ _ _ _ _ _ h_d h_nr]
            unfold evalAssignNonDeref; dsimp only
            repeat' (first
              | exact Or.inl ⟨_, rfl⟩
              | exact Or.inr (Or.inl ⟨_, rfl⟩)
              | exact Or.inr (Or.inr rfl)
              | split)

@[simp]
theorem resolveCallTarget_pushBaseStack
    (calleeBody : CapturedMir)
    (s : MachineState) (func : Operand) (argCount : Nat)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable) :
    resolveCallTarget (MachineState.pushBaseStack calleeBody [] s)
        func argCount bodyLocalDecls bodyLayouts =
      resolveCallTarget s func argCount bodyLocalDecls bodyLayouts := by
  unfold resolveCallTarget
  dsimp only [MachineState.pushBaseStack, Memory.pushBaseStack]

/--
If `unwindFromCallStack stk mem` does not reach the empty stack `.nil` (i.e., it
returns neither `.halted .panic` nor, under a `false` `rootUnwindCeiling`, the
root `.faulted .ub`; a `.faulted .ub` from an `.unreachable` frame commutes
anyway), then appending `baseStack` beneath `stk` commutes via
`MirExecState.pushBaseStack calleeBody baseStack`.
-/
theorem unwindFromCallStack_pushBaseStack_of_ne_panic
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (stk : List SavedCallerFrame) (mem : Memory)
    (h_no_panic : unwindFromCallStack stk mem ≠ .halted .panic)
    (h_no_ub : unwindFromCallStack stk mem ≠ .faulted .ub)
    (h_bor : baseStack = [] ∨ mem.borrows = []) :
    unwindFromCallStack
        (match baseStack with
         | [] => stk
         | b :: bs => stk ++ narrowCallStackForTailCallee (b :: bs) mem.rootUnwindCeiling)
        (Memory.pushBaseStack calleeBody baseStack mem) =
      MirExecState.pushBaseStack calleeBody baseStack
        (unwindFromCallStack stk mem) := by
  induction stk generalizing mem with
  | nil =>
    dsimp only [unwindFromCallStack] at h_no_panic h_no_ub
    cases h_c : mem.rootUnwindCeiling with
    | true => rw [h_c] at h_no_panic; exact False.elim (h_no_panic rfl)
    | false => rw [h_c] at h_no_ub; exact False.elim (h_no_ub rfl)
  | cons caller rest ih =>
    cases baseStack with
    | nil =>
      dsimp only [unwindFromCallStack] at h_no_panic h_no_ub ⊢
      cases h_uw : caller.returnUnwind with
      | unreachable => rfl
      | terminate => rfl
      | cleanup cleanupBb => rfl
      | continue_ =>
        rw [h_uw] at h_no_panic h_no_ub
        dsimp only at h_no_panic h_no_ub
        exact ih _ h_no_panic h_no_ub (Or.inl rfl)
    | cons bHd bTl =>
      rcases h_bor with h_nil | h_mb
      · cases h_nil
      · dsimp only [List.cons_append, unwindFromCallStack] at h_no_panic h_no_ub ⊢
        cases h_uw : caller.returnUnwind with
        | unreachable => rfl
        | terminate => rfl
        | cleanup cleanupBb =>
          dsimp only [MirExecState.pushBaseStack, MachineState.pushBaseStack,
            Memory.pushBaseStack, Option.getD]
          rw [h_mb]
          rfl
        | continue_ =>
          rw [h_uw] at h_no_panic h_no_ub
          dsimp only at h_no_panic h_no_ub
          exact ih _ h_no_panic h_no_ub (Or.inr h_mb)

theorem unwindFromCallStack_ne_normal
    (stk : List SavedCallerFrame) (mem : Memory) (rv : MirReturn) :
    unwindFromCallStack stk mem ≠ .halted (.normal rv) := by
  induction stk generalizing mem with
  | nil =>
    dsimp only [unwindFromCallStack]
    cases mem.rootUnwindCeiling <;> (intro h; cases h)
  | cons hd tl ih =>
    dsimp only [unwindFromCallStack]
    cases hd.returnUnwind with
    | continue_ => exact ih _
    | unreachable => intro h; cases h
    | terminate => intro h; cases h
    | cleanup _ => intro h; cases h

theorem applyUnwindAction_ne_normal
    (s : MachineState) (localsAfterArgs : List LocalSlot)
    (mem : Memory) (unwind : UnwindAction) (rv : MirReturn) :
    applyUnwindAction s localsAfterArgs mem unwind ≠ .halted (.normal rv) := by
  cases unwind with
  | continue_ => exact unwindFromCallStack_ne_normal mem.callStack mem rv
  | unreachable => intro h; cases h
  | terminate => intro h; cases h
  | cleanup _ => intro h; cases h

theorem applyUnwindAction_pushBaseStack_of_ne_panic
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (s : MachineState) (localsAfterArgs : List LocalSlot)
    (unwind : UnwindAction)
    (h_no_panic :
      applyUnwindAction s localsAfterArgs s.memory unwind ≠ .halted .panic)
    (h_no_ub :
      applyUnwindAction s localsAfterArgs s.memory unwind ≠ .faulted .ub)
    (h_bor : baseStack = [] ∨ s.memory.borrows = []) :
    applyUnwindAction
        (MachineState.pushBaseStack calleeBody baseStack s)
        localsAfterArgs
        (Memory.pushBaseStack calleeBody baseStack s.memory)
        unwind =
      MirExecState.pushBaseStack calleeBody baseStack
        (applyUnwindAction s localsAfterArgs s.memory unwind) := by
  cases unwind with
  | unreachable => rfl
  | terminate => rfl
  | cleanup cleanupBb =>
    cases baseStack <;> rfl
  | continue_ =>
    cases baseStack with
    | nil =>
      exact unwindFromCallStack_pushBaseStack_of_ne_panic
        calleeBody [] s.memory.callStack s.memory h_no_panic h_no_ub (Or.inl rfl)
    | cons bHd bTl =>
      exact unwindFromCallStack_pushBaseStack_of_ne_panic
        calleeBody (bHd :: bTl) s.memory.callStack s.memory h_no_panic h_no_ub h_bor

def IsIntrinsicCallFamily
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (f : MachineState → MirStepNode) : Prop :=
  (∃ retVal,
    ∀ s : MachineState,
      f s = writeIntrinsicReturn s locals' destination targetBb retVal) ∨
  (∃ fk, ∀ s : MachineState, f s = MirStepNode.fail fk) ∨
  (∀ s : MachineState, f s = MirStepNode.unsupported)

theorem IsIntrinsicCallFamily.of_eq
    {locals' : List LocalSlot} {destination : Place} {targetBb : BasicBlockIdx}
    {f g : MachineState → MirStepNode}
    (h_eq : ∀ s, f s = g s)
    (h : IsIntrinsicCallFamily locals' destination targetBb g) :
    IsIntrinsicCallFamily locals' destination targetBb f := by
  rcases h with ⟨retVal, hr⟩ | ⟨fk, hf⟩ | hu
  · exact Or.inl ⟨retVal, fun s => (h_eq s).trans (hr s)⟩
  · exact Or.inr (Or.inl ⟨fk, fun s => (h_eq s).trans (hf s)⟩)
  · exact Or.inr (Or.inr fun s => (h_eq s).trans (hu s))

theorem writeIntrinsicScalarResult_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (resOpt : Option ScalarInt) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s => writeIntrinsicScalarResult s locals' destination targetBb resOpt) := by
  cases resOpt with
  | some sc => exact Or.inl ⟨.scalar sc, fun _ => rfl⟩
  | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

theorem intrinsicUnresolvedLayoutStep_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (ty : RigidTy) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ => intrinsicUnresolvedLayoutStep ty) := by
  unfold intrinsicUnresolvedLayoutStep
  cases isUnsizedRigidTy 8 ty with
  | true => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | false => exact Or.inr (Or.inr fun _ => rfl)

theorem intrinsicWidePointeeStep_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (ty : RigidTy) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ => intrinsicWidePointeeStep ty) := by
  unfold intrinsicWidePointeeStep
  cases intrinsicTailMayBeUnsized 8 ty with
  | true => exact Or.inr (Or.inr fun _ => rfl)
  | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

theorem intrinsicMissingPointeeStep_cases
    (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps) := by
  unfold intrinsicMissingPointeeStep
  cases argOps with
  | nil => exact Or.inr (Or.inr fun _ => rfl)
  | cons ptrOp _ =>
    dsimp only
    cases operandTy bodyLocalDecls bodyLayouts ptrOp with
    | some _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | none => exact Or.inr (Or.inr fun _ => rfl)

theorem unaryScalarIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (argVals : List Value) (g : ScalarInt → Option ScalarInt) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .scalar sc :: .nil =>
          writeIntrinsicScalarResult s locals' destination targetBb (g sc)
        | _ => MirStepNode.fail .ub) := by
  rcases argVals with _ | ⟨_ | sc | _ | _, _ | _⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  exact writeIntrinsicScalarResult_cases locals' destination targetBb (g sc)

theorem binaryScalarIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (argVals : List Value)
    (body : ScalarInt → ScalarInt → MachineState → MirStepNode)
    (h : ∀ lhs rhs, IsIntrinsicCallFamily locals' destination targetBb (body lhs rhs)) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .scalar lhs :: .scalar rhs :: .nil => body lhs rhs s
        | _ => MirStepNode.fail .ub) := by
  rcases argVals with _ | ⟨_ | lhs | _ | _, _ | ⟨_ | rhs | _ | _, _ | _⟩⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  exact h lhs rhs

theorem optSignedBinaryScalarIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (argVals : List Value) (optSigned : Option Bool)
    (op : ScalarInt → ScalarInt → Bool → Option ScalarInt) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .scalar lhs :: .scalar rhs :: .nil =>
          match optSigned with
          | .some flag =>
            writeIntrinsicScalarResult s locals' destination targetBb (op lhs rhs flag)
          | .none => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub) := by
  refine binaryScalarIntrinsic_family locals' destination targetBb argVals
    (fun lhs rhs s =>
      match optSigned with
      | .some flag =>
        writeIntrinsicScalarResult s locals' destination targetBb (op lhs rhs flag)
      | .none => MirStepNode.unsupported)
    fun lhs rhs => ?_
  cases optSigned with
  | none => exact Or.inr (Or.inr fun _ => rfl)
  | some flag =>
    exact writeIntrinsicScalarResult_cases locals' destination targetBb (op lhs rhs flag)

theorem arithOffsetIntrinsic_family
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match argVals with
        | .ptr ptrVal ptrSz :: .scalar countSc :: .nil =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true =>
            match resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
            | .some pointeeTy =>
              match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
              | .some elemSz =>
                match evalArithOffset ptrVal ptrSz countSc elemSz with
                | .some retPtrVal =>
                  writeIntrinsicReturn s locals' destination targetBb (.ptr retPtrVal 8)
                | .none => MirStepNode.fail .ub
              | .none => intrinsicUnresolvedLayoutStep pointeeTy
            | .none => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
        | _ => MirStepNode.fail .ub) := by
  rcases argVals with _ | ⟨_ | _ | ⟨ptrVal, ptrSz⟩ | _, _ | ⟨_ | countSc | _ | _, _ | _⟩⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  dsimp only
  cases Nat.beq ptrSz 8 with
  | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | true =>
    dsimp only
    cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
    | none =>
      exact intrinsicMissingPointeeStep_cases locals' destination targetBb
        bodyLocalDecls bodyLayouts argOps
    | some pointeeTy =>
      dsimp only
      cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
      | none =>
        exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb pointeeTy
      | some elemSz =>
        dsimp only
        cases evalArithOffset ptrVal ptrSz countSc elemSz with
        | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
        | some retPtrVal => exact Or.inl ⟨.ptr retPtrVal 8, fun _ => rfl⟩

theorem wideSliceIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptrArgVal : Value) (body : ScalarInt → MachineState → MirStepNode)
    (h : ∀ lenSc, IsIntrinsicCallFamily locals' destination targetBb (body lenSc)) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true => body lenSc s
        | _ => MirStepNode.fail .ub) := by
  cases ptrArgVal with
  | aggregate varIdx flds =>
    cases varIdx with
    | succ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | zero =>
      rcases flds with _ | ⟨_ | _ | ⟨_, ptrSz⟩ | _, _ | ⟨_ | lenSc | _ | _, _ | _⟩⟩ <;>
        try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      simp only [Nat.zero_eq]
      cases Nat.beq ptrSz 8 with
      | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      | true => exact h lenSc
  | _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

theorem wideMetaOnlyIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptrArgVal : Value) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun _ =>
        match ptrArgVal with
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => MirStepNode.unsupported
        | _ => MirStepNode.fail .ub) := by
  cases ptrArgVal with
  | aggregate varIdx flds =>
    cases varIdx with
    | succ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | zero =>
      rcases flds with _ | ⟨_ | _ | ⟨_, ptrSz⟩ | _, _ | ⟨metaVal, _ | _⟩⟩ <;>
        try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      simp only [Nat.zero_eq]
      cases Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      | true => exact Or.inr (Or.inr fun _ => rfl)
  | _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

theorem thinOrWideMetaIntrinsic_family
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptrArgVal : Value)
    (thinBody : MachineState → MirStepNode)
    (wideBody : MachineState → MirStepNode)
    (h_thin : IsIntrinsicCallFamily locals' destination targetBb thinBody)
    (h_wide : IsIntrinsicCallFamily locals' destination targetBb wideBody) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        match ptrArgVal with
        | .ptr _ ptrSz =>
          match Nat.beq ptrSz 8 with
          | false => MirStepNode.fail .ub
          | true => thinBody s
        | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
          match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
          | false => MirStepNode.fail .ub
          | true => wideBody s
        | _ => MirStepNode.fail .ub) := by
  cases ptrArgVal with
  | ptr _ ptrSz =>
    dsimp only
    cases Nat.beq ptrSz 8 with
    | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | true => exact h_thin
  | aggregate varIdx flds =>
    cases varIdx with
    | succ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | zero =>
      rcases flds with _ | ⟨_ | _ | ⟨_, ptrSz⟩ | _, _ | ⟨metaVal, _ | _⟩⟩ <;>
        try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      simp only [Nat.zero_eq]
      cases Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
      | true => exact h_wide
  | _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)

def sizeOfValOneArg
    (s : MachineState) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptOpt : Option RigidTy) : MirStepNode :=
  match ptOpt with
  | .some (.slice elemTy) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
        | .some elemSz =>
          writeIntrinsicScalarResult s locals' destination targetBb
            (evalSliceSizeOfVal elemSz lenSc)
        | .none => intrinsicUnresolvedLayoutStep elemTy
    | _ => MirStepNode.fail .ub
  | .some .str =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        writeIntrinsicScalarResult s locals' destination targetBb
          (evalSliceSizeOfVal 1 lenSc)
    | _ => MirStepNode.fail .ub
  | .some (.dynamic _) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .some pointeeTy =>
    match ptrArgVal with
    | .ptr _ ptrSz =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match intrinsicTailIsExtern 8 pointeeTy with
        | true => MirStepNode.unsupported
        | false =>
          match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
          | .some sz =>
            match Nat.ble (signedHalfModulus 8) sz with
            | true => MirStepNode.fail .ub
            | false =>
              writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩)
          | .none => intrinsicUnresolvedLayoutStep pointeeTy
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => intrinsicWidePointeeStep pointeeTy
    | _ => MirStepNode.fail .ub
  | .none =>
    match isValidIntrinsicPtrArgVal ptrArgVal with
    | false => MirStepNode.fail .ub
    | true => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps

theorem evalSizeOfVal_oneArg_eq
    (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts
        argOps [ptrArgVal] locals' destination targetBb =
      sizeOfValOneArg s bodyLocalDecls bodyLayouts argOps ptrArgVal
        locals' destination targetBb
        (resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps) := by
  unfold evalNonSelectIntrinsicCall sizeOfValOneArg
  dsimp only
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none => rfl
  | some pt => cases pt <;> rfl

theorem evalSizeOfValIntrinsicCall_cases
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        evalNonSelectIntrinsicCall .sizeOfVal s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  rcases argVals with _ | ⟨ptrArgVal, _ | _⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  refine IsIntrinsicCallFamily.of_eq
    (fun s => evalSizeOfVal_oneArg_eq s target bodyLocalDecls bodyLayouts argOps
      ptrArgVal locals' destination targetBb) ?_
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none =>
    unfold sizeOfValOneArg
    cases isValidIntrinsicPtrArgVal ptrArgVal with
    | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | true =>
      exact intrinsicMissingPointeeStep_cases locals' destination targetBb
        bodyLocalDecls bodyLayouts argOps
  | some pointeeTy =>
    by_cases h_sl : ∃ elemTy, pointeeTy = .slice elemTy
    · rcases h_sl with ⟨elemTy, rfl⟩
      unfold sizeOfValOneArg
      refine wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
        (fun lenSc s =>
          match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
          | .some elemSz =>
            writeIntrinsicScalarResult s locals' destination targetBb
              (evalSliceSizeOfVal elemSz lenSc)
          | .none => intrinsicUnresolvedLayoutStep elemTy)
        fun lenSc => ?_
      cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
      | none =>
        exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb elemTy
      | some elemSz =>
        exact writeIntrinsicScalarResult_cases locals' destination targetBb
          (evalSliceSizeOfVal elemSz lenSc)
    · by_cases h_str : pointeeTy = .str
      · subst h_str
        unfold sizeOfValOneArg
        exact wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
          (fun lenSc s =>
            writeIntrinsicScalarResult s locals' destination targetBb
              (evalSliceSizeOfVal 1 lenSc))
          fun lenSc =>
            writeIntrinsicScalarResult_cases locals' destination targetBb
              (evalSliceSizeOfVal 1 lenSc)
      · by_cases h_dyn : ∃ preds, pointeeTy = .dynamic preds
        · rcases h_dyn with ⟨_, rfl⟩
          unfold sizeOfValOneArg
          exact wideMetaOnlyIntrinsic_family locals' destination targetBb ptrArgVal
        · refine IsIntrinsicCallFamily.of_eq (g := fun s =>
            match ptrArgVal with
            | .ptr _ ptrSz =>
              match Nat.beq ptrSz 8 with
              | false => MirStepNode.fail .ub
              | true =>
                match intrinsicTailIsExtern 8 pointeeTy with
                | true => MirStepNode.unsupported
                | false =>
                  match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
                  | .some sz =>
                    match Nat.ble (signedHalfModulus 8) sz with
                    | true => MirStepNode.fail .ub
                    | false =>
                      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨sz, 8⟩)
                  | .none => intrinsicUnresolvedLayoutStep pointeeTy
            | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
              match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
              | false => MirStepNode.fail .ub
              | true => intrinsicWidePointeeStep pointeeTy
            | _ => MirStepNode.fail .ub) (fun s => ?_) ?_
          · unfold sizeOfValOneArg
            cases pointeeTy <;>
              first
              | exact False.elim (h_sl ⟨_, rfl⟩)
              | exact False.elim (h_str rfl)
              | exact False.elim (h_dyn ⟨_, rfl⟩)
              | rfl
          · refine thinOrWideMetaIntrinsic_family locals' destination targetBb ptrArgVal _ _ ?_
              (intrinsicWidePointeeStep_cases locals' destination targetBb pointeeTy)
            cases intrinsicTailIsExtern 8 pointeeTy with
            | true => exact Or.inr (Or.inr fun _ => rfl)
            | false =>
              dsimp only
              cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts pointeeTy with
              | none =>
                exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb pointeeTy
              | some sz =>
                dsimp only
                cases Nat.ble (signedHalfModulus 8) sz with
                | true => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
                | false => exact Or.inl ⟨.scalar ⟨sz, 8⟩, fun _ => rfl⟩

def alignOfValOneArg
    (s : MachineState) (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx)
    (ptOpt : Option RigidTy) : MirStepNode :=
  match ptOpt with
  | .some (.slice elemTy) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match
          intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
          intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
        with
        | .some elemSz, .some alignBytes =>
          match evalSliceSizeOfVal elemSz lenSc with
          | .some _ =>
            writeIntrinsicReturn s locals' destination targetBb
              (.scalar ⟨alignBytes, 8⟩)
          | .none => MirStepNode.fail .ub
        | _, _ => intrinsicUnresolvedLayoutStep elemTy
    | _ => MirStepNode.fail .ub
  | .some .str =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: .scalar lenSc :: .nil) =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match evalSliceSizeOfVal 1 lenSc with
        | .some _ =>
          writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)
        | .none => MirStepNode.fail .ub
    | _ => MirStepNode.fail .ub
  | .some (.dynamic _) =>
    match ptrArgVal with
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => MirStepNode.unsupported
    | _ => MirStepNode.fail .ub
  | .some pointeeTy =>
    match ptrArgVal with
    | .ptr _ ptrSz =>
      match Nat.beq ptrSz 8 with
      | false => MirStepNode.fail .ub
      | true =>
        match intrinsicTailIsExtern 8 pointeeTy with
        | true => MirStepNode.unsupported
        | false =>
          match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
          | .some alignBytes =>
            writeIntrinsicReturn s locals' destination targetBb
              (.scalar ⟨alignBytes, 8⟩)
          | .none => intrinsicUnresolvedLayoutStep pointeeTy
    | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
      match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
      | false => MirStepNode.fail .ub
      | true => intrinsicWidePointeeStep pointeeTy
    | _ => MirStepNode.fail .ub
  | .none =>
    match isValidIntrinsicPtrArgVal ptrArgVal with
    | false => MirStepNode.fail .ub
    | true => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps

theorem evalAlignOfVal_oneArg_eq
    (s : MachineState) (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl) (bodyLayouts : LayoutTable)
    (argOps : List Operand) (ptrArgVal : Value)
    (locals' : List LocalSlot) (destination : Place) (targetBb : BasicBlockIdx) :
    evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts
        argOps [ptrArgVal] locals' destination targetBb =
      alignOfValOneArg s bodyLocalDecls bodyLayouts argOps ptrArgVal
        locals' destination targetBb
        (resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps) := by
  unfold evalNonSelectIntrinsicCall alignOfValOneArg
  dsimp only
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none => rfl
  | some pt => cases pt <;> rfl

theorem evalAlignOfValIntrinsicCall_cases
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    IsIntrinsicCallFamily locals' destination targetBb
      (fun s =>
        evalNonSelectIntrinsicCall .alignOfVal s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb) := by
  rcases argVals with _ | ⟨ptrArgVal, _ | _⟩ <;>
    try exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  refine IsIntrinsicCallFamily.of_eq
    (fun s => evalAlignOfVal_oneArg_eq s target bodyLocalDecls bodyLayouts argOps
      ptrArgVal locals' destination targetBb) ?_
  cases resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps with
  | none =>
    unfold alignOfValOneArg
    cases isValidIntrinsicPtrArgVal ptrArgVal with
    | false => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
    | true =>
      exact intrinsicMissingPointeeStep_cases locals' destination targetBb
        bodyLocalDecls bodyLayouts argOps
  | some pointeeTy =>
    by_cases h_sl : ∃ elemTy, pointeeTy = .slice elemTy
    · rcases h_sl with ⟨elemTy, rfl⟩
      unfold alignOfValOneArg
      refine wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
        (fun lenSc s =>
          match
            intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
            intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
          with
          | .some elemSz, .some alignBytes =>
            match evalSliceSizeOfVal elemSz lenSc with
            | .some _ =>
              writeIntrinsicReturn s locals' destination targetBb
                (.scalar ⟨alignBytes, 8⟩)
            | .none => MirStepNode.fail .ub
          | _, _ => intrinsicUnresolvedLayoutStep elemTy)
        fun lenSc => ?_
      cases intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
      | none =>
        exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb elemTy
      | some elemSz =>
        cases intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy with
        | none =>
          exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb elemTy
        | some alignBytes =>
          dsimp only
          cases evalSliceSizeOfVal elemSz lenSc with
          | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
          | some _ => exact Or.inl ⟨.scalar ⟨alignBytes, 8⟩, fun _ => rfl⟩
    · by_cases h_str : pointeeTy = .str
      · subst h_str
        unfold alignOfValOneArg
        refine wideSliceIntrinsic_family locals' destination targetBb ptrArgVal
          (fun lenSc s =>
            match evalSliceSizeOfVal 1 lenSc with
            | .some _ =>
              writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 8⟩)
            | .none => MirStepNode.fail .ub)
          fun lenSc => ?_
        cases evalSliceSizeOfVal 1 lenSc with
        | none => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
        | some _ => exact Or.inl ⟨.scalar ⟨1, 8⟩, fun _ => rfl⟩
      · by_cases h_dyn : ∃ preds, pointeeTy = .dynamic preds
        · rcases h_dyn with ⟨_, rfl⟩
          unfold alignOfValOneArg
          exact wideMetaOnlyIntrinsic_family locals' destination targetBb ptrArgVal
        · refine IsIntrinsicCallFamily.of_eq (g := fun s =>
            match ptrArgVal with
            | .ptr _ ptrSz =>
              match Nat.beq ptrSz 8 with
              | false => MirStepNode.fail .ub
              | true =>
                match intrinsicTailIsExtern 8 pointeeTy with
                | true => MirStepNode.unsupported
                | false =>
                  match intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
                  | .some alignBytes =>
                    writeIntrinsicReturn s locals' destination targetBb
                      (.scalar ⟨alignBytes, 8⟩)
                  | .none => intrinsicUnresolvedLayoutStep pointeeTy
            | .aggregate 0 (.ptr _ ptrSz :: metaVal :: .nil) =>
              match Bool.and (Nat.beq ptrSz 8) (isValidWidePtrMetaVal metaVal) with
              | false => MirStepNode.fail .ub
              | true => intrinsicWidePointeeStep pointeeTy
            | _ => MirStepNode.fail .ub) (fun s => ?_) ?_
          · unfold alignOfValOneArg
            cases pointeeTy <;>
              first
              | exact False.elim (h_sl ⟨_, rfl⟩)
              | exact False.elim (h_str rfl)
              | exact False.elim (h_dyn ⟨_, rfl⟩)
              | rfl
          · refine thinOrWideMetaIntrinsic_family locals' destination targetBb ptrArgVal _ _ ?_
              (intrinsicWidePointeeStep_cases locals' destination targetBb pointeeTy)
            cases intrinsicTailIsExtern 8 pointeeTy with
            | true => exact Or.inr (Or.inr fun _ => rfl)
            | false =>
              dsimp only
              cases intrinsicRigidTyAlign bodyLocalDecls bodyLayouts pointeeTy with
              | none =>
                exact intrinsicUnresolvedLayoutStep_cases locals' destination targetBb pointeeTy
              | some alignBytes =>
                exact Or.inl ⟨.scalar ⟨alignBytes, 8⟩, fun _ => rfl⟩

theorem evalNonSelectIntrinsicCall_cases
    (kind : RustIntrinsicKind)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx) :
    (∃ retVal,
      ∀ s : MachineState,
        evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
          argOps argVals locals' destination targetBb =
          writeIntrinsicReturn s locals' destination targetBb retVal) ∨
    (∃ fk, ∀ s : MachineState,
      evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb = MirStepNode.fail fk) ∨
    (∀ s : MachineState,
      evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb = MirStepNode.unsupported) := by
  change IsIntrinsicCallFamily locals' destination targetBb
    (fun s =>
      evalNonSelectIntrinsicCall kind s target bodyLocalDecls bodyLayouts
        argOps argVals locals' destination targetBb)
  cases kind with
  | ubChecks =>
    cases argVals with
    | nil => exact Or.inl ⟨.scalar ⟨1, 1⟩, fun _ => rfl⟩
    | cons _ _ => exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | constEvalSelect =>
    exact Or.inr (Or.inl ⟨.ub, fun _ => rfl⟩)
  | ctlz =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCtlz
  | ctlzNonzero =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCtlzNonzero
  | cttz =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCttz
  | cttzNonzero =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCttzNonzero
  | ctpop =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalCtpop
  | bswap =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalBswap
  | bitreverse =>
    exact unaryScalarIntrinsic_family locals' destination targetBb argVals evalBitreverse
  | wrappingAdd =>
    exact binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingAdd lhs rhs))
      fun lhs rhs =>
        writeIntrinsicScalarResult_cases locals' destination targetBb (evalWrappingAdd lhs rhs)
  | wrappingSub =>
    exact binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingSub lhs rhs))
      fun lhs rhs =>
        writeIntrinsicScalarResult_cases locals' destination targetBb (evalWrappingSub lhs rhs)
  | wrappingMul =>
    exact binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        writeIntrinsicScalarResult s locals' destination targetBb (evalWrappingMul lhs rhs))
      fun lhs rhs =>
        writeIntrinsicScalarResult_cases locals' destination targetBb (evalWrappingMul lhs rhs)
  | saturatingAdd =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => Trusted.Rustc.V2026_06_01.MirSemantics.evalSaturatingAdd lhs rhs flag)
  | saturatingSub =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => Trusted.Rustc.V2026_06_01.MirSemantics.evalSaturatingSub lhs rhs flag)
  | uncheckedShl =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedShl lhs rhs flag)
  | uncheckedShr =>
    refine binaryScalarIntrinsic_family locals' destination targetBb argVals
      (fun lhs rhs s =>
        match
          resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (sameRhsTy := false),
          resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps
        with
        | .some lhsSigned, .some rhsSigned =>
          writeIntrinsicScalarResult s locals' destination targetBb
            (evalUncheckedShr lhs rhs lhsSigned rhsSigned)
        | _, _ => MirStepNode.unsupported)
      fun lhs rhs => ?_
    cases resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (sameRhsTy := false) with
    | none => exact Or.inr (Or.inr fun _ => rfl)
    | some lhsSigned =>
      cases resolveIntrinsicShiftSigned target bodyLocalDecls bodyLayouts argOps with
      | none => exact Or.inr (Or.inr fun _ => rfl)
      | some rhsSigned =>
        exact writeIntrinsicScalarResult_cases locals' destination targetBb
          (evalUncheckedShr lhs rhs lhsSigned rhsSigned)
  | uncheckedAdd =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedAdd lhs rhs flag)
  | uncheckedSub =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedSub lhs rhs flag)
  | uncheckedMul =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedMul lhs rhs flag)
  | uncheckedDiv =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedDiv lhs rhs flag)
  | uncheckedRem =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps)
      (fun lhs rhs flag => evalUncheckedRem lhs rhs flag)
  | threeWayCompare =>
    exact optSignedBinaryScalarIntrinsic_family locals' destination targetBb argVals
      (resolveIntrinsicIsSigned target bodyLocalDecls bodyLayouts argOps (allowChar := true))
      (fun lhs rhs flag => evalThreeWayCompare lhs rhs flag)
  | arithOffset =>
    exact arithOffsetIntrinsic_family target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb
  | sizeOfVal =>
    exact evalSizeOfValIntrinsicCall_cases target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb
  | alignOfVal =>
    exact evalAlignOfValIntrinsicCall_cases target bodyLocalDecls bodyLayouts
      argOps argVals locals' destination targetBb
  | copyNonOverlapping | writeBytes | copy | compareBytes | rawEq
  | typedSwapNonOverlapping | ptrOffsetFrom | ptrOffsetFromUnsigned
  | ptrMask | blackBox =>
    exact Or.inr (Or.inr fun _ => rfl)

theorem writePlaceValue_deref_nil_borrows
    (locals : List LocalSlot) (loc : Local) (tl : List ProjectionElem)
    (val : Value) (ld : List LocalDecl) (ly : LayoutTable)
    (cs : List SavedCallerFrame) :
    writePlaceValue locals [] ⟨loc, .deref :: tl⟩ val ld ly cs = .ub := by
  unfold writePlaceValue
  dsimp only [lookupBorrow]
  cases get? locals loc with
  | none => rfl
  | some sl =>
    cases sl with
    | uninit | dead => rfl
    | init v =>
      cases v with
      | unit | scalar _ | ptr _ _ | uninit => rfl
      | aggregate var fields =>
        cases var with
        | succ _ => rfl
        | zero =>
          cases fields with
          | nil => rfl
          | cons f1 tl1 =>
            cases f1 with
            | unit | scalar _ | aggregate _ _ | uninit => rfl
            | ptr ptrVal ptrSz =>
              cases tl1 with
              | nil => rfl
              | cons f2 tl2 =>
                cases f2 with
                | unit | ptr _ _ | aggregate _ _ | uninit => rfl
                | scalar lenSc =>
                  cases tl2 with
                  | cons _ _ => rfl
                  | nil =>
                    simp only [Nat.zero_eq]
                    split <;> rfl

theorem evalPlaceWrite_deref_nil_borrows
    (locals : List LocalSlot) (loc : Local) (tl : List ProjectionElem)
    (val : Value) (ap : List Nat) (ld : List LocalDecl) (ly : LayoutTable)
    (cs : List SavedCallerFrame) :
    evalPlaceWrite locals [] ⟨loc, .deref :: tl⟩ val ap ld ly cs = .ub := by
  unfold evalPlaceWrite
  have hw := writePlaceValue_deref_nil_borrows locals loc tl val ld ly cs
  cases ap with
  | nil => exact hw
  | cons ph pt =>
    dsimp only [lookupBorrow]
    cases get? locals loc with
    | none => exact hw
    | some sl =>
      cases sl with
      | uninit | dead => exact hw
      | init pv =>
        cases h2 : extractDerefPtrVal? pv <;> (simp only [h2]; exact hw)

theorem writePlaceValue_nil_borrows_callStack
    (locals : List LocalSlot) (dst : Place) (val : Value)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (cs : List SavedCallerFrame) :
    writePlaceValue locals [] dst val localDecls layouts cs =
      writePlaceValue locals [] dst val localDecls layouts [] := by
  rcases dst with ⟨loc, proj⟩
  cases proj with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | deref =>
      rw [writePlaceValue_deref_nil_borrows, writePlaceValue_deref_nil_borrows]
    | _ => rfl

theorem foreignFrameDerefWrite_nil_borrows
    (locals₁ : List LocalSlot) (mem₁ : Memory) (dst : Place)
    (restProj : List ProjectionElem) (val : Value)
    (h_bor : mem₁.borrows = [])
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts = .ub := by
  unfold foreignFrameDerefWrite
  rw [h_bor]
  dsimp only [lookupBorrow]
  cases get? locals₁ dst.local_ with
  | none => rfl
  | some sl =>
    cases sl with
    | uninit | dead => rfl
    | init pv => dsimp only; cases extractDerefPtrVal? pv <;> rfl

private theorem invalidateDirectDestWriteBorrows_pushBaseStack_nil
    (calleeBody : CapturedMir) (mem : Memory) (locals : List LocalSlot) (dst : Place) :
    invalidateDirectDestWriteBorrows (Memory.pushBaseStack calleeBody [] mem) locals dst =
      Memory.pushBaseStack calleeBody [] (invalidateDirectDestWriteBorrows mem locals dst) := by
  rcases mem with ⟨nA, gl, _ | ⟨bHd, bTl⟩, nT, cal, tr, cs, ac, ap, nP, cl, fp, ex⟩
  · rfl
  · unfold invalidateDirectDestWriteBorrows
    dsimp only [Memory.pushBaseStack]
    rcases dst with ⟨loc, _ | ⟨hd, tl⟩⟩
    · rfl
    · cases hd <;> rfl

private theorem invalidateDirectDestWriteBorrows_borrows_nil
    (m : Memory) (locals : List LocalSlot) (dst : Place) (h_bor : m.borrows = []) :
    invalidateDirectDestWriteBorrows m locals dst = m := by
  rcases m with ⟨_, _, bor, _, _, _, _, _, _, _, _, _, _⟩
  dsimp only at h_bor; subst h_bor
  unfold invalidateDirectDestWriteBorrows
  rcases dst with ⟨_, _ | ⟨hd, _⟩⟩
  · rfl
  · cases hd <;> rfl

theorem writeIntrinsicReturn_nonDeref_eq
    (s : MachineState) (locals' : List LocalSlot) (destination : Place)
    (targetBb : BasicBlockIdx) (retVal : Value)
    (h_nd : ∀ restProj, destination.projection ≠ .deref :: restProj) :
    writeIntrinsicReturn s locals' destination targetBb retVal =
      match writePlaceValue locals' s.memory.borrows destination retVal (callStack := s.memory.callStack) with
      | .ok updatedLocals =>
        MirStepNode.step {
          frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := updatedLocals }
          memory := invalidateDirectDestWriteBorrows s.memory locals' destination
        }
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported := by
  unfold writeIntrinsicReturn
  rcases destination with ⟨loc, _ | ⟨hd, rp⟩⟩
  · rfl
  · cases hd <;> first | exact False.elim (h_nd rp rfl) | rfl

theorem writeIntrinsicReturn_pushBaseStack_of_noCallWP
    (calleeBody : CapturedMir) (baseStack : List SavedCallerFrame)
    (ms : MachineState) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) (retVal : Value)
    {Q : MirExecState → Prop} {P : Value → Memory → Prop}
    (h_st :
      evalNodeNoCallWP Q (mirNormalPost P)
        (writeIntrinsicReturn ms locals' destination targetBb retVal))
    (h_bor : baseStack = [] ∨ ms.memory.borrows = []) :
    ∃ nextSt : MachineState,
      writeIntrinsicReturn ms locals' destination targetBb retVal =
        MirStepNode.step nextSt ∧
      writeIntrinsicReturn (MachineState.pushBaseStack calleeBody baseStack ms)
        locals' destination targetBb retVal =
        MirStepNode.step (MachineState.pushBaseStack calleeBody baseStack nextSt) := by
  by_cases h_is_deref : ∃ restProj, destination.projection = .deref :: restProj
  · rcases h_is_deref with ⟨restProj, h_dp⟩
    rcases destination with ⟨loc, dProj⟩
    dsimp only at h_dp; subst h_dp
    unfold writeIntrinsicReturn at h_st ⊢
    rcases h_bor with rfl | h_nil_bor
    · dsimp only [MachineState.pushBaseStack] at h_st ⊢
      rw [Memory.pushBaseStack_borrows, Memory.pushBaseStack_nil_callStack,
          Memory.pushBaseStack_activeProtectors, Memory.pushBaseStack_callerLocals]
      cases h_ep : evalPlaceWrite locals' ms.memory.borrows ⟨loc, .deref :: restProj⟩ retVal
          ms.memory.activeProtectors [] emptyLayoutTable ms.memory.callStack with
      | unsupported => rw [h_ep] at h_st; exact False.elim h_st
      | ok updL =>
        rw [h_ep] at h_st; dsimp only at h_st ⊢
        cases h_tb : derefWriteTreeUB locals' ms.memory.borrows ⟨loc, .deref :: restProj⟩ with
        | true => rw [h_tb] at h_st; exact False.elim h_st
        | false =>
          exact ⟨{ frame := { ms.frame with blockIdx := targetBb, stmtIdx := 0, locals := updL }
                   memory := { ms.memory with
                               borrows :=
                                 invalidateDerefWriteBorrows locals' ms.memory.borrows
                                   ⟨loc, .deref :: restProj⟩ restProj
                                   ms.memory.callerLocals ms.memory.callStack } }, rfl, rfl⟩
      | ub =>
        rw [h_ep] at h_st; dsimp only at h_st ⊢
        rw [foreignFrameDerefWrite_pushBaseStack]
        cases h_ff : foreignFrameDerefWrite locals' ms.memory ⟨loc, .deref :: restProj⟩ restProj retVal with
        | ub => rw [h_ff] at h_st; exact False.elim h_st
        | unsupported => rw [h_ff] at h_st; exact False.elim h_st
        | ok updL mem' =>
          exact ⟨{ frame := { ms.frame with blockIdx := targetBb, stmtIdx := 0, locals := updL }
                   memory := mem' }, rfl, rfl⟩
    · dsimp only at h_st
      rw [h_nil_bor, evalPlaceWrite_deref_nil_borrows] at h_st
      dsimp only at h_st
      rw [foreignFrameDerefWrite_nil_borrows locals' ms.memory ⟨loc, .deref :: restProj⟩ restProj retVal h_nil_bor] at h_st
      exact False.elim h_st
  · have h_nd : ∀ restProj, destination.projection ≠ .deref :: restProj :=
      fun rp h_eq => h_is_deref ⟨rp, h_eq⟩
    rw [writeIntrinsicReturn_nonDeref_eq _ _ _ _ _ h_nd] at h_st ⊢
    rw [writeIntrinsicReturn_nonDeref_eq _ _ _ _ _ h_nd]
    rcases h_bor with rfl | h_nil_bor
    · dsimp only [MachineState.pushBaseStack]
      rw [Memory.pushBaseStack_borrows, Memory.pushBaseStack_nil_callStack]
      cases h_wr : writePlaceValue locals' ms.memory.borrows destination retVal
          (callStack := ms.memory.callStack) with
      | ok updL =>
        exact ⟨{ frame := { ms.frame with blockIdx := targetBb, stmtIdx := 0, locals := updL }
                 memory := invalidateDirectDestWriteBorrows ms.memory locals' destination },
          rfl,
          by dsimp only; rw [invalidateDirectDestWriteBorrows_pushBaseStack_nil]⟩
      | unsupported => rw [h_wr] at h_st; exact False.elim h_st
      | ub => rw [h_wr] at h_st; exact False.elim h_st
    · dsimp only [MachineState.pushBaseStack]
      rw [Memory.pushBaseStack_borrows]
      rw [h_nil_bor] at h_st ⊢
      rw [writePlaceValue_nil_borrows_callStack locals' destination retVal [] emptyLayoutTable ms.memory.callStack] at h_st ⊢
      rw [writePlaceValue_nil_borrows_callStack locals' destination retVal [] emptyLayoutTable
            (Memory.pushBaseStack calleeBody baseStack ms.memory).callStack]
      cases h_wr : writePlaceValue locals' [] destination retVal with
      | ok updL =>
        exact ⟨{ frame := { ms.frame with blockIdx := targetBb, stmtIdx := 0, locals := updL }
                 memory := ms.memory },
          by dsimp only; rw [invalidateDirectDestWriteBorrows_borrows_nil ms.memory locals' destination h_nil_bor],
          by dsimp only; rw [invalidateDirectDestWriteBorrows_borrows_nil _ locals' destination
               (by rw [Memory.pushBaseStack_borrows, h_nil_bor])]⟩
      | unsupported => simp only [h_wr] at h_st; exact False.elim h_st
      | ub => simp only [h_wr] at h_st; exact False.elim h_st

end Anneal.PureMirExec
end MovedPureMirExecPrefix
