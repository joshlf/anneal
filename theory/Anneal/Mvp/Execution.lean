-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp.Semantics
import Init.Data.BitVec.Lemmas
import Init.Data.Option.Lemmas

/-!
These rules connect finite symbolic execution to the source claim. The proof
library adds no primitive semantics: successful evaluation implies safety of
every reachable prefix, and a source return with the computed result. Separate
invariant rules admit safe infinite execution without requiring evaluation to
finish.
-/

namespace Anneal.Mvp

open Trusted.Mvp

/--
Fuel bounds proof search, not the source execution or the safety claim. `none`
can mean exhaustion or a fault and proves neither divergence nor unsafety. Only
`some value` supplies the certificate consumed by the soundness rules below.
-/
def run (body : Body) (fuel : Nat) (state : State) : Option Word :=
  Nat.rec (motive := fun _ => State → Option Word) (fun _ => none)
    (fun _ iterate current =>
      match step body current with
      | .next next => iterate next
      | .ret value => some value
      | .fault _ => none) fuel state

theorem reach_prepend {body : Body} {start next finish : State}
    (first : step body start = .next next) (rest : Reach body next finish) :
    Reach body start finish := by
  induction rest with
  | refl => exact .next .refl first
  | next reached transition ih => exact .next ih transition

theorem reach_cases {body : Body} {start next finish : State}
    (first : step body start = .next next) (reached : Reach body start finish) :
    finish = start ∨ Reach body next finish := by
  induction reached with
  | refl => exact .inl rfl
  | @next before after reached transition ih =>
      cases ih with
      | inl equal =>
          subst before
          have same : StepResult.next next = .next after := first.symm.trans transition
          cases same
          exact .inr .refl
      | inr rest => exact .inr (.next rest transition)

-- Reach extends only through `next`. A return or fault therefore has no proper
-- continuation in this relation. These terminal cases let a finite certificate
-- account for every reachable prefix of the deterministic source step.
theorem reachable_after_return {body : Body} {start finish : State} {value : Word}
    (returned : step body start = .ret value) (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before after reached transition ih =>
      subst before
      simp [returned] at transition

theorem reachable_after_fault {body : Body} {start finish : State} {reason : Fault}
    (faulted : step body start = .fault reason) (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before after reached transition ih =>
      subst before
      simp [faulted] at transition

theorem safeFrom_return {body : Body} {start : State} {value : Word}
    (returned : step body start = .ret value) : SafeFrom body start := by
  intro finish reached reason
  have same := reachable_after_return returned reached
  subst finish
  simp [returned]

theorem safeFrom_next {body : Body} {start next : State}
    (first : step body start = .next next) (rest : SafeFrom body next) :
    SafeFrom body start := by
  intro finish reached reason
  cases reach_cases first reached with
  | inl equal =>
      subst finish
      simp [first]
  | inr tail => exact rest finish tail reason

/--
Transport safety across a finite source segment, including into a divergent
continuation. Reachability alone supplies no safety at the endpoint; the suffix
still owes that obligation. This rule uses the deterministic source step.
-/
theorem safeFrom_of_reach {body : Body} {start checkpoint : State}
    (segment : Reach body start checkpoint)
    (suffix : SafeFrom body checkpoint) : SafeFrom body start := by
  induction segment with
  | refl => exact suffix
  | next reached transition ih => exact ih (safeFrom_next transition suffix)

/--
A finite execution certificate names the exact source result. Each constructor
requires a checked source-step equality, and the inductive chain ends at an
actual return. A desired postcondition or exhausted evaluation fuel supplies no
replacement for that return witness.
-/
inductive Executes (body : Body) : State → Word → Prop where
  | ret {start : State} {value : Word} :
      step body start = .ret value → Executes body start value
  | next {start next : State} {value : Word} :
      step body start = .next next → Executes body next value →
      Executes body start value

/--
Compose a checked source segment with a finite returning continuation. The
suffix still supplies the actual source return, even for a reflexive segment.
-/
theorem executes_prepend {body : Body} {start checkpoint : State} {value : Word}
    (segment : Reach body start checkpoint)
    (suffix : Executes body checkpoint value) : Executes body start value := by
  induction segment with
  | refl => exact suffix
  | next reached transition ih => exact ih (.next transition suffix)

/--
One finite certificate covers every reachable prefix because `step` has a
single result for a given state. A nondeterministic extension needs a bridge
covering every relevant branch; one returning path alone would not suffice.
-/
theorem executes_safe {body : Body} {start : State} {value : Word}
    (execution : Executes body start value) : SafeFrom body start := by
  induction execution with
  | ret returned => exact safeFrom_return returned
  | next transition rest ih => exact safeFrom_next transition ih

theorem executes_returns {body : Body} {start : State} {value : Word}
    (execution : Executes body start value) : ReturnsFrom body start value := by
  induction execution with
  | ret returned => exact ⟨_, .refl, returned⟩
  | next transition rest ih =>
      cases ih with
      | intro finish reached =>
          exact ⟨finish, reach_prepend transition reached.1, reached.2⟩

theorem run_executes {body : Body} {fuel : Nat} {start : State} {value : Word}
    (success : run body fuel start = some value) : Executes body start value := by
  induction fuel generalizing start with
  | zero => simp [run] at success
  | succ fuel ih =>
      cases transition : step body start with
      | next next =>
          simp [run, transition] at success
          exact .next transition (ih success)
      | ret result =>
          have same : result = value := by
            simp [run, transition] at success
            exact success
          subst result
          exact .ret transition
      | fault reason => simp [run, transition] at success

theorem run_success {body : Body} {fuel : Nat} {start : State} {value : Word}
    (success : run body fuel start = some value) :
    SafeFrom body start ∧ ReturnsFrom body start value :=
  ⟨executes_safe (run_executes success), executes_returns (run_executes success)⟩

theorem run_initial_success {body : Body} {fuel : Nat} {args : List Word}
    {value : Word} (success : run body fuel (initial body args) = some value) :
    Safe body args ∧ Returns body args value :=
  run_success success

theorem executes_unique {body : Body} {start : State} {left right : Word}
    (execution : Executes body start left) (returned : ReturnsFrom body start right) :
    left = right := by
  induction execution with
  | ret first =>
      cases returned with
      | intro finish reached =>
          have same := reachable_after_return first reached.1
          subst finish
          have equal := first.symm.trans reached.2
          cases equal
          rfl
  | next first rest ih =>
      cases returned with
      | intro finish reached =>
          cases reach_cases first reached.1 with
          | inl same =>
              subst finish
              simp [first] at reached
          | inr tail => exact ih ⟨finish, tail, reached.2⟩

theorem run_result_unique {body : Body} {fuel : Nat} {start : State}
    {left right : Word} (success : run body fuel start = some left)
    (returned : ReturnsFrom body start right) : left = right :=
  executes_unique (run_executes success) returned

theorem invariant_reachable {body : Body} {start finish : State}
    (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before → step body before = .next after →
      invariant after)
    (reached : Reach body start finish) : invariant finish := by
  induction reached with
  | refl => exact entry
  | next reached transition ih => exact closed _ _ ih transition

/--
An invariant can prove prefix safety for a loop with no normal return.
Preservation and fault exclusion are independent obligations: a predicate can
be closed under all next steps while still admitting a faulting state with no
next step. Neither obligation requires eventually reaching a return.
-/
theorem safeFrom_invariant {body : Body} {start : State} (invariant : State → Prop)
    (entry : invariant start)
    (closed : ∀ before after, invariant before → step body before = .next after →
      invariant after)
    (noFault : ∀ state, invariant state → ∀ reason, step body state ≠ .fault reason) :
    SafeFrom body start := by
  intro finish reached
  have preserved := invariant_reachable invariant entry closed reached
  exact noFault finish preserved

theorem reachable_selfLoop {body : Body} {start finish : State}
    (loop : step body start = .next start) (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before after reached transition ih =>
      subst before
      have equal := loop.symm.trans transition
      cases equal
      rfl

theorem safeFrom_selfLoop {body : Body} {start : State}
    (loop : step body start = .next start) : SafeFrom body start := by
  apply safeFrom_invariant (fun state => state = start) rfl
  · intro before after same transition
    subst before
    have equal := loop.symm.trans transition
    cases equal
    rfl
  · intro state same reason
    subst state
    simp [loop]

/--
A finite proof may be built statement by statement with an arbitrary post.
The inductive return rule requires both an actual source return and its
postcondition. Thus this WP proves completion as well as safety; it cannot
verify a nonreturning loop merely because the postcondition never gets tested.
The invariant rules provide a separate route for safety without completion.
-/
inductive WP (body : Body) (post : Word → Prop) : State → Prop where
  | ret {start : State} {value : Word} :
      step body start = .ret value → post value → WP body post start
  | next {start next : State} :
      step body start = .next next → WP body post next → WP body post start

theorem wp_sound {body : Body} {post : Word → Prop} {start : State}
    (proof : WP body post start) :
    SafeFrom body start ∧ ∃ value, ReturnsFrom body start value ∧ post value := by
  induction proof with
  | ret returned property =>
      exact ⟨safeFrom_return returned, _, ⟨_, .refl, returned⟩, property⟩
  | next transition rest ih =>
      cases ih.2 with
      | intro value returned =>
          cases returned.1 with
          | intro finish reached =>
              exact ⟨safeFrom_next transition ih.1, value,
                ⟨finish, reach_prepend transition reached.1, reached.2⟩, returned.2⟩

end Anneal.Mvp
