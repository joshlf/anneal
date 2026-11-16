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
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

def body : Body := Captured.program.bodies[0]

def s0 : State := mkState 0 0 [.live none, .dead, .live (some .unit)]
def s1 : State := mkState 0 1 [.live none, .live none, .live (some .unit)]
def s2 : State := mkState 1 0 [.live none, .live none, .live (some .unit)]
def s3 : State := mkState 1 1 [.live none, .live none, .live (some .unit)]
def s4 : State := mkState 1 0 [.live none, .live none, .live (some .unit)]

theorem step0 : step body s0 = .step s1 := rfl
theorem step1 : step body s1 = .step s2 := rfl
theorem step2 : step body s2 = .step s3 := rfl
theorem step3 : step body s3 = .step s4 := rfl
theorem step4 : step body s4 = .step s3 := rfl

def invariant (state : State) : Prop :=
  state = s0 ∨ state = s1 ∨ state = s2 ∨ state = s3 ∨ state = s4

theorem closed (before after : State) (inv : invariant before)
    (transition : step body before = .step after) : invariant after := by
  cases inv with
  | inl same =>
      subst before
      have equal := StepResult.step.inj (step0.symm.trans transition)
      subst after
      exact .inr (.inl rfl)
  | inr inv => cases inv with
    | inl same =>
        subst before
        have equal := StepResult.step.inj (step1.symm.trans transition)
        subst after
        exact .inr (.inr (.inl rfl))
    | inr inv => cases inv with
      | inl same =>
          subst before
          have equal := StepResult.step.inj (step2.symm.trans transition)
          subst after
          exact .inr (.inr (.inr (.inl rfl)))
      | inr inv => cases inv with
        | inl same =>
            subst before
            have equal := StepResult.step.inj (step3.symm.trans transition)
            subst after
            exact .inr (.inr (.inr (.inr rfl)))
        | inr same =>
            subst before
            have equal := StepResult.step.inj (step4.symm.trans transition)
            subst after
            exact .inr (.inr (.inr (.inl rfl)))

theorem noFault (state : State) (inv : invariant state) (reason : FaultKind) :
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

theorem safe : Safe body [] :=
  safeFrom_of_reach
    (show Reach body (initial body []) s2 from
      .next (.next .refl step0) step1)
    (safeFrom_invariant invariant
      (show invariant s2 from .inr (.inr (.inl rfl))) closed noFault)

theorem noDoneStep (state : State) (inv : invariant state) (out : TerminalOut) :
    step body state ≠ .done out := by
  cases inv with
  | inl same => subst state; simp [step0]
  | inr inv => cases inv with
    | inl same => subst state; simp [step1]
    | inr inv => cases inv with
      | inl same => subst state; simp [step2]
      | inr inv => cases inv with
        | inl same => subst state; simp [step3]
        | inr same => subst state; simp [step4]

theorem verify : CrateTheorem ⟨Captured.program, Spec.specs⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
        have same : body = selected := Option.some.inj found
        subst selected
        refine bodyVerified_of_safe found rfl (fun args valid _ => ?_)
        cases args with
        | nil => exact safe
        | cons _ _ => cases valid
    | succ id => cases found
  · intro args out
    exact not_behavior_of_no_done (body := body) rfl (fun finish reached =>
      noDoneStep finish
        (invariant_reachable invariant
          (show invariant (initial body args) from .inl rfl) closed reached)
        out)

end Proof
