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
`mem.activeProtectors = []`), while leaving heap allocations (`globals`,
`nextAllocId`), tag/protector counters (`nextTag`, `nextProtector`), caller
locals (`callerLocals`), and linked callee tables (`callees`) completely
unconstrained.
-/
def RootActiveMemory (mem : Memory) : Prop :=
  mem.borrows = [] ∧
  mem.callStack = [] ∧
  mem.activeCallee = none ∧
  mem.activeProtectors = []

@[simp]
theorem rootActiveMemory_initMachineState
    (body : CapturedMir) (args : List Value) :
    RootActiveMemory (initMachineState body args).memory :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp]
theorem rootActiveMemory_initMachineStateWithCallees
    (body : CapturedMir) (args : List Value) (callees : List CapturedMir) :
    RootActiveMemory (initMachineStateWithCallees body args callees).memory :=
  ⟨rfl, rfl, rfl, rfl⟩

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

Unlike `verifyMirSafeSym`, the existential step count inside `MirWpConverges`
may vary arbitrarily with `args`.
-/
theorem verifyMirSafe_of_wpConverges
    (c : Claim)
    (h_wp :
      ∀ args : List Value,
        c.pre args →
        MirWpConverges c.body (initMachineState c.body args)
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
        MirWpConverges c.body (initMachineState c.body args)
          (mirNormalPost (fun retVal _ => c.post args retVal))) :
    VerificationResult c :=
  verifyMirSafe_of_wpConverges c (fun args h_pre =>
    MirWpConverges.mono (fun _ => mirNormalPost_imp_mirSafePost) (h_wp args h_pre))

/--
Discharge a stateful `StatefulVerificationResult c` from fuel-free
`MirWpConverges` (`mirSafePost`).

The existential step count inside `MirWpConverges` may vary arbitrarily with
`(args, mem)`.
-/
theorem verifyStatefulMirSafe_of_wpConverges
    (c : StatefulClaim)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirWpConverges c.body (initMachineStateWithMemory c.body args mem)
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
        MirWpConverges c.body (initMachineStateWithMemory c.body args mem)
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
        MirWpConverges c.body (initMachineStateWithMemory c.body args mem)
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
          (initMachineStateWithMemory c.implBody args mem)
          (fun out =>
            out = .normal (model args mem) ∧
            c.post args mem (model args mem).1 (model args mem).2))
    (h_spec :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirNoCallWpConverges c.specBody
          (initMachineStateWithMemory c.specBody args mem)
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

/-- Partial-correctness (`DWLP mirUbWaivedWP`) soundness of `MirUbWaivedWpConverges`. -/
theorem dwlp_of_mirUbWaivedWpConverges
    {body : CapturedMir} {s : MachineState} {post : MirOutcome → Prop}
    (h : MirUbWaivedWpConverges body s post) :
    DWLP mirUbWaivedWP (mirTree body s) (fun out _ => post out) PUnit.unit := by
  rcases h with ⟨fuel, h_wp⟩
  rw [wpMirUbWaivedSym_eq_wpMirUbWaivedBounded] at h_wp
  exact dwlp_cofix_of_wpCoalBounded h_wp

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
          (initMachineStateWithMemory c.body args mem)
          (mirSafePost (c.post args mem)))
    (h_waived :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirUbWaivedWpConverges c.body
          (initMachineStateWithMemory c.body args mem)
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
Partial-correctness (`DWLP (mirModularWP contract.toCallContract)`) soundness of
`MirModularWpConverges`.
-/
theorem dwlp_of_mirModularWpConverges
    {contract : MirCallContract} {body : CapturedMir} {s : MachineState}
    {post : MirOutcome → Prop}
    (h : MirModularWpConverges contract body s post) :
    DWLP (mirModularWP contract.toCallContract) (mirTree body s)
      (fun out _ => post out) PUnit.unit := by
  rcases h with ⟨fuel, h_wp⟩
  rw [wpMirModularSym, wpMirExecModularSym_eq_wpCoalBounded] at h_wp
  exact dwlp_cofix_of_wpCoalBounded h_wp

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

/--
Fuel-free trace-aware weakest precondition over `MachineState`.
-/
def MirTraceWpConverges
    (body : CapturedMir) (s : MachineState)
    (post : List (Event MirEffect) → MirOutcome → Prop) : Prop :=
  ∃ fuel : Nat, wpMirTraceBounded fuel body s post

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

/-- Partial-correctness (`DWLP mirTraceWP`) soundness of `MirTraceWpConverges`. -/
theorem dwlp_of_mirTraceWpConverges
    {body : CapturedMir} {s : MachineState}
    {post : List (Event MirEffect) → MirOutcome → Prop}
    (h : MirTraceWpConverges body s post) :
    DWLP mirTraceWP (mirTree body s) (fun out tr => post tr out) [] := by
  rcases h with ⟨fuel, h_wp⟩
  exact dwlp_cofix_of_wpCoalBounded h_wp

/--
Fuel-free discharge of `TraceVerificationResult c` from `MirTraceWpConverges`.
-/
theorem verifyTraceMir_of_wpConverges
    (c : TraceClaim)
    (h_wp :
      ∀ (args : List Value) (mem : Memory),
        c.pre args mem →
        MirTraceWpConverges c.body
          (initMachineStateWithMemory c.body args mem)
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
      MirWpConverges c.body (initMachineState c.body expectedArgs)
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
        (initMachineStateWithMemory c.body expectedArgs expectedMem)
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
          (initMachineState c.body [.scalar { bits := b, sizeBytes := width }])
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
          (initMachineState c.body [.scalar { bits := b, sizeBytes := width }])
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
          (initMachineState c.body
            [ .scalar { bits := b1, sizeBytes := w1 }
            , .scalar { bits := b2, sizeBytes := w2 } ])
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
          (initMachineState c.body
            [ .scalar { bits := b1, sizeBytes := w1 }
            , .scalar { bits := b2, sizeBytes := w2 } ])
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
  rcases h_root with ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨3, ?_⟩
  dsimp [initMachineState, initMachineStateWithMemory, initLocals, initLocalsAux,
    List.length, multiBlockMidState, advanceStmt, Trusted.Sequence.set?,
    multiBlockPipelineBody, Trusted.Sequence.get?]
  dsimp [wpMirStepsSym, wpMirExecStepsSym]
  simp [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval,
    evalNodeNoCallWP_eq, stepMirState, stepMirFn, Trusted.Sequence.get?,
    evalStmt, evalRvalue, evalOperand, evalTerminator, readProjectedValue,
    writePlaceValue, invalidateConflictingBorrows, get?, List.length,
    Trusted.Sequence.length, BEq.beq, advanceStmt, Trusted.Sequence.set?,
    evalNodeNoCallWP, MirStepNode.step]

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
  rcases h_root with ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨3, ?_⟩
  dsimp [initMachineState, initMachineStateWithMemory, initLocals, initLocalsAux,
    List.length, multiBlockMidState, advanceStmt, Trusted.Sequence.set?,
    multiBlockPipelineBody, Trusted.Sequence.get?]
  dsimp [wpMirSym, wpMirExecSym]
  simp [evalSymNodeTree_eq, stepMirExecSymTree_eval,
    evalNodeWP_eq, stepMirState, stepMirFn, Trusted.Sequence.get?, evalStmt,
    evalRvalue, evalOperand, evalTerminator, writePlaceValue,
    invalidateConflictingBorrows, get?, List.length,
    Trusted.Sequence.length, BEq.beq, advanceStmt, Trusted.Sequence.set?,
    evalNodeWP, MirStepNode.step, MirStepNode.retNormal, mirNormalPost]

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
              [.scalar { bits := b, sizeBytes := 4 }] callees).memory)) :=
  multiBlockPipeline_wpConverges b
    (initMachineStateWithCallees multiBlockPipelineBody
      [.scalar { bits := b, sizeBytes := 4 }] callees).memory
    ⟨rfl, rfl, rfl, rfl⟩

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
    (multiBlockPipeline_wpConverges b _ ⟨rfl, rfl, rfl, rfl⟩)

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
    ⟨⟨42, by decide, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

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
    ⟨⟨42, by decide, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

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
  rcases h_root with ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨3, ?_⟩
  dsimp [initMachineState, initMachineStateWithMemory, initLocals, initLocalsAux,
    List.length, multiBlockMidState, advanceStmt, Trusted.Sequence.set?,
    multiBlockPipelineBody, Trusted.Sequence.get?]
  dsimp [wpMirNoCallSym, wpMirExecNoCallSym]
  simp [evalSymNodeTreeNoCall_eq, stepMirExecSymTree_eval,
    evalNodeNoCallWP_eq, stepMirState, stepMirFn, Trusted.Sequence.get?, evalStmt,
    evalRvalue, evalOperand, evalTerminator, writePlaceValue,
    invalidateConflictingBorrows, get?, List.length,
    Trusted.Sequence.length, BEq.beq, advanceStmt, Trusted.Sequence.set?,
    evalNodeNoCallWP, MirStepNode.step, MirStepNode.retNormal, mirNormalPost]

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


/-- UbException-aware `UbExceptionClaim` for `multiBlockPipelineBody`. -/
def multiBlockPipelineUbExceptionClaim : UbExceptionClaim where
  body := multiBlockPipelineBody
  pre args mem := WellTypedScalarArg1 4 args ∧ RootActiveMemory mem
  strictSafetyPre _ _ := True
  post args mem retVal mem' := args = [retVal] ∧ mem' = mem

/-- Non-vacuity witness for `multiBlockPipelineUbExceptionClaim.pre`. -/
theorem multiBlockPipelineUbExceptionClaim_nonVacuous :
    ∃ args mem, multiBlockPipelineUbExceptionClaim.pre args mem :=
  multiBlockPipelineStatefulClaim_nonVacuous

/-- Fuel-free discharge of `UbExceptionVerificationResult`. -/
theorem verify_multiBlockPipelineUbExceptionClaim :
    UbExceptionVerificationResult multiBlockPipelineUbExceptionClaim := by
  refine verifyUbExceptionMir_of_wpConverges
    multiBlockPipelineUbExceptionClaim
    (fun args mem h_pre _ => ?_)
    (fun args mem h_pre => ?_)
  · rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
    have h_conv := multiBlockPipeline_noCallWpConverges b mem h_root
    have h_wp := MirWpConverges.of_noCall h_conv
    refine MirWpConverges.mono ?_ h_wp
    intro out ho
    cases out with
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases ho with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | panic => exact False.elim ho
    | abort => exact False.elim ho
  · rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
    have h_conv := multiBlockPipeline_noCallWpConverges b mem h_root
    have h_wp := MirWpConverges.of_noCall h_conv
    have h_ub := MirUbWaivedWpConverges.of_mirWpConverges h_wp
    refine MirUbWaivedWpConverges.mono ?_ h_ub
    intro out ho
    cases out with
    | normal rv =>
      rcases rv with ⟨retVal, mem'⟩
      rcases ho with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | panic => exact False.elim ho
    | abort => exact False.elim ho

/-- Dummy call contract that allows anything. -/
def dummyContract : MirCallContract where
  pre _ := True
  post _ _ := True

/-- ModularClaim using dummyContract. -/
def multiBlockPipelineModularClaim : ModularClaim :=
  { body := multiBlockPipelineBody
    envAssumed := dummyContract.holdsOn
    pre := multiBlockPipelineEquivClaim.pre
    post := multiBlockPipelineEquivClaim.post }

/-- Non-vacuity witness for `multiBlockPipelineModularClaim.pre`. -/
theorem multiBlockPipelineModularClaim_nonVacuous :
    ∃ args mem, multiBlockPipelineModularClaim.pre args mem :=
  multiBlockPipelineStatefulClaim_nonVacuous

/-- Fuel-free discharge of a modular verification result. -/
theorem verify_multiBlockPipelineModularClaim :
    ModularVerificationResult multiBlockPipelineModularClaim := by
  exact verifyModularContractMir_of_wpConverges
    dummyContract multiBlockPipelineBody
    multiBlockPipelineModularClaim.pre multiBlockPipelineModularClaim.post
    (fun args mem h_pre => by
      rcases h_pre with ⟨⟨b, _, rfl⟩, h_root⟩
      have h_conv := multiBlockPipeline_noCallWpConverges b mem h_root
      have h_mod_wp := MirModularWpConverges.of_noCall (contract := dummyContract) h_conv
      refine MirModularWpConverges.mono ?_ h_mod_wp
      intro out ho
      cases out with
      | normal rv =>
        rcases rv with ⟨retVal, mem'⟩
        rcases ho with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      | panic => exact False.elim ho
      | abort => exact False.elim ho)

end ConcreteWitnesses

end Anneal.MirFuelFree
