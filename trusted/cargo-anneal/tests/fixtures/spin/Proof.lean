-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Captured
import Spec
import Anneal.Mvp.Execution

namespace Proof

open Trusted.Mvp Anneal.Mvp

def body : Body := Captured.program.bodies[0]

def s0 : State := ⟨0, 0, [.uninit, .dead, .uninit]⟩
def s1 : State := ⟨0, 1, [.uninit, .uninit, .uninit]⟩
def s2 : State := ⟨1, 0, [.uninit, .uninit, .uninit]⟩
def s3 : State := ⟨1, 1, [.uninit, .uninit, .value 0]⟩
def s4 : State := ⟨1, 0, [.uninit, .uninit, .value 0]⟩

theorem step0 : step body s0 = .next s1 := rfl
theorem step1 : step body s1 = .next s2 := rfl
theorem step2 : step body s2 = .next s3 := rfl
theorem step3 : step body s3 = .next s4 := rfl
theorem step4 : step body s4 = .next s3 := rfl

def invariant (state : State) : Prop :=
  state = s0 ∨ state = s1 ∨ state = s2 ∨ state = s3 ∨ state = s4

theorem closed (before after : State) (inv : invariant before)
    (transition : step body before = .next after) : invariant after := by
  cases inv with
  | inl same =>
      subst before
      have equal := StepResult.next.inj (step0.symm.trans transition)
      subst after
      exact .inr (.inl rfl)
  | inr inv => cases inv with
    | inl same =>
        subst before
        have equal := StepResult.next.inj (step1.symm.trans transition)
        subst after
        exact .inr (.inr (.inl rfl))
    | inr inv => cases inv with
      | inl same =>
          subst before
          have equal := StepResult.next.inj (step2.symm.trans transition)
          subst after
          exact .inr (.inr (.inr (.inl rfl)))
      | inr inv => cases inv with
        | inl same =>
            subst before
            have equal := StepResult.next.inj (step3.symm.trans transition)
            subst after
            exact .inr (.inr (.inr (.inr rfl)))
        | inr same =>
            subst before
            have equal := StepResult.next.inj (step4.symm.trans transition)
            subst after
            exact .inr (.inr (.inr (.inl rfl)))

theorem noFault (state : State) (inv : invariant state) (reason : Fault) :
    step body state ≠ .fault reason := by
  cases inv with
  | inl same => subst state; simp [step0]
  | inr inv => cases inv with
    | inl same => subst state; simp [step1]
    | inr inv => cases inv with
      | inl same => subst state; simp [step2]
      | inr inv => cases inv with
        | inl same => subst state; simp [step3]
        | inr same => subst state; simp [step4]

theorem safe (args : List Word) : Safe body args :=
  safeFrom_invariant invariant (show invariant (initial body args) from .inl rfl)
    closed noFault

theorem noReturnStep (state : State) (inv : invariant state) (value : Word) :
    step body state ≠ .ret value := by
  cases inv with
  | inl same => subst state; simp [step0]
  | inr inv => cases inv with
    | inl same => subst state; simp [step1]
    | inr inv => cases inv with
      | inl same => subst state; simp [step2]
      | inr inv => cases inv with
        | inl same => subst state; simp [step3]
        | inr same => subst state; simp [step4]

theorem noReturn (args : List Word) (value : Word) : ¬Returns body args value := by
  intro returned
  cases returned with
  | intro finish reached =>
      have preserved := invariant_reachable invariant
        (show invariant (initial body args) from .inl rfl) closed reached.1
      exact noReturnStep finish preserved value reached.2

theorem verify : CrateTheorem Captured.program Spec.specs := by
  constructor
  · rfl
  · constructor
    · intro id selected found
      cases id with
      | zero =>
          have same : body = selected := Option.some.inj found
          subst selected
          exact ⟨rfl, fun args _ _ => safe args⟩
      | succ id => simp [Captured.program] at found
    · intro selected found args value
      have same : body = selected := Option.some.inj found
      subst selected
      exact noReturn args value

end Proof
