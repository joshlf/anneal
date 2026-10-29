-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.Refinement

/-!
# Layer 1B: Small-Step Transition Outcomes and Prefix-Indexed Partial Behaviors

This module instantiates the Layer 1A refinement framework
(`Trusted.Refinement`) for operational semantics defined by small-step
transition trees.

We separate the *input query* of a finite execution prefix (`ExecQuery State`,
pairing an initial state `init` with a step budget `steps : Nat`) from its
*observable output* (`ExecOut Obs Val`, pairing the emitted observation trace
`trace : List Obs` with the resulting `PrefixOutcome Val`). Every small-step
machine `M : SmallStepMachine Prog State Obs Val` induces a partial behavior
`BehaviorOf M p : ExecQuery State → Partial (ExecOut Obs Val → Prop)` and
packages directly as a Layer 1A `Language` via `SmallStepMachine.toLanguage`.

## How Prefix Safety and Prefix Preservation Fall Out

Because `ExecQuery State` includes both `init : State` and `steps : Nat`:

1. **All-prefix safety without termination (`(M.toLanguage).WellFormed`):**
   At query `q = ⟨init, steps⟩`, `(BehaviorOf M p q).defined` asserts that if
   `M.initState p init` holds, then every prefix of length `steps` reachable
   from `init` has a safe outcome (`out.isSafe`: neither `.failed` nor
   `.stuck`). Consequently, `(M.toLanguage).sem p ≤ (M.toLanguage).WellFormed`
   requires safety at *every* finite step budget `steps : Nat` across both
   terminating and diverging executions, ruling out programs that trigger UB
   before entering an infinite loop.
2. **Preserving well-defined prefixes before non-time-traveling UB:**
   Suppose a program `s` emits an observable event at step `1` and triggers UB
   at step `2`. Because definedness is indexed by `q = ⟨init, steps⟩`:
   - At `q₁ = ⟨init, 1⟩`, `(BehaviorOf M s q₁).defined` holds (`True`), so any
     compiled target `t` satisfying `Compiles` (`t ≤ s`) must also be defined at
     `steps = 1` and preserve `s`'s 1-step observation trace.
   - At `q₂ = ⟨init, 2⟩`, `(BehaviorOf M s q₂).defined` is `False`, so `t ≤ s`
     leaves `t` unconstrained from step `2` onward.

This module belongs to `trusted/lean/` and contains only definitions,
structures, and inductives (zero theorems). Meta-theorems (`TotalStep`,
`InhabitedDemonic`, `non_vacuity_at_every_depth`, `behaviorOf_le_pure`) live in
`theory/Anneal/StepResult.lean`.
-/

namespace Trusted

/-- Quantifier polarity for nondeterministic choices in a small-step semantics.

    - `demonic`: runtime, allocator, or scheduler nondeterminism; a
      specification must hold across all branches.
    - `angelic`: existential witness choice. -/
@[candidate step_result]
inductive ChoiceKind where
  | demonic
  | angelic

/-- Distinguishes normal return from panic/unwind completion. -/
@[candidate step_result]
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Distinguishes language-level Undefined Behavior (`ub`) from explicit
    specification or assertion violations (`contractViolation`). -/
@[candidate step_result]
inductive FailureKind where
  | ub
  | contractViolation

/-- Outcome of a single transition step in a small-step interaction tree. -/
@[candidate step_result]
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Outcome recorded at the end of a finite execution prefix. -/
@[candidate step_result]
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

/-- A prefix outcome is safe when it neither triggers a failure (`ub` or
    `contractViolation`) nor gets stuck in an unstepped state. -/
@[candidate step_result]
def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

/-- Input query to a finite-prefix small-step execution (`Query` in
    `Language`): the initial machine state `init` and the step budget
    `steps`. -/
@[candidate step_result]
structure ExecQuery (State : Type) where
  init : State
  steps : Nat

/-- Observable output of a finite-prefix small-step execution (`Out` in
    `Language`): the accumulated observation trace `trace` and the terminal or
    intermediate `PrefixOutcome` `outcome`. -/
@[candidate step_result]
structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

/-- Small-step operational semantics parameterized by programs `Prog`, machine
    states `State`, step observations `Obs`, and return values `Val`. -/
@[candidate step_result]
structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of a finite execution prefix from current state `s`
    given initial state `init` and remaining step budget `fuel`.

    - At `fuel = 0`, the prefix finishes immediately in `.running`.
    - If `M.step p s` has no outgoing transition (`¬ ∃ r, M.step p s r`) or a
      choice node has no enabled branch (`¬ ∃ s', branches s'`), the machine
      records `.stuck` so unmodeled states or empty choices cannot silently
      vanish into an empty prefix set. -/
@[candidate step_result]
inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State) (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

/-- Induced query-indexed partial behavior of program `p` in machine `M`:
    - `defined`: if `q.init` is a valid initial state (`M.initState p q.init`),
      then every prefix of length `q.steps` reachable from `q.init` has a safe
      outcome (`out.isSafe`).
    - `val`: the predicate of all `ExecOut Obs Val` reachable from `q.init` in
      `q.steps` steps. -/
@[candidate step_result]
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a Layer 1A `Language` with
    `Query := ExecQuery State`, `Out := ExecOut Obs Val`, and
    `sem := BehaviorOf M`. -/
@[candidate step_result]
def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

end Trusted
