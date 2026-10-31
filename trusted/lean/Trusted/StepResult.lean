-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted.Attributes
import Trusted.Refinement

/-!
# Small-Step Transition Outcomes and Prefix-Indexed Partial Behaviors

This module instantiates the refinement framework (`Trusted.Refinement`) for
operational semantics defined by small-step transition trees.

We separate the *input query* of a finite execution prefix (`ExecQuery State`,
pairing an initial state `init` with a step budget `steps : Nat`) from its
*observable output* (`ExecOut Obs Val`, pairing the emitted observation trace
`trace : List Obs` with the resulting `PrefixOutcome Val`). Every small-step
machine `M : SmallStepMachine Prog State Obs Val` induces a partial behavior
`BehaviorOf M p : ExecQuery State → Partial (ExecOut Obs Val → Prop)` and
packages directly as a `Language` via `SmallStepMachine.toLanguage`.

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

/-- Distinguishes normal return from panic/unwind completion. -/
@[candidate step_result]
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Outcome of a single transition step in a small-step interaction tree:
    - `step obs next`: emits observation `obs` and advances to `next`.
    - `choice branches`: branches demonically over states satisfying
      `branches : State → Prop` without emitting an external observation.
    - `terminated term`: finishes execution normally or by unwinding.
    - `failed`: halts immediately due to Undefined Behavior. -/
@[candidate step_result]
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Outcome recorded at the end of a finite execution prefix:
    - `running`: the step budget was exhausted before reaching a terminal or
      failing step.
    - `terminated term`: execution reached a terminal state within the budget.
    - `failed`: execution encountered Undefined Behavior within the budget.
    - `stuck`: execution reached a state with no outgoing transitions or an
      empty nondeterministic choice set. -/
@[candidate step_result]
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

/-- A prefix outcome is safe when it neither triggers a failure (`.failed`) nor
    gets stuck in an unstepped state (`.stuck`).

    Notice that `.running` is safe: a prefix whose step budget `steps` expires
    before termination has not exhibited UB within those `steps` steps. -/
@[candidate step_result]
def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed => False
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
    states `State`, step observations `Obs`, and return values `Val`.
    - `initState p s` holds when `s` is a valid initial machine state for
      program `p`.
    - `step p s r` holds when state `s` of program `p` can take a single
      transition with outcome `r`. -/
@[candidate step_result]
structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of a finite execution prefix from state `s` given
    remaining step budget `fuel` under transition relation `step`.

    - At `fuel = 0`, the prefix finishes immediately in `.running`.
    - If `step p s` has no outgoing transition (`¬ ∃ r, step p s r`) or a
      choice node has no enabled branch (`¬ ∃ s', branches s'`), the machine
      records `.stuck` so unmodeled states or empty choices cannot silently
      vanish into an empty prefix set. -/
@[candidate step_result]
inductive ReachesPrefix
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      step p s (.choice branches) →
      branches s' →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix step p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      step p s (.terminated term) →
      ReachesPrefix step p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      step p s .failed →
      ReachesPrefix step p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, step p s r) →
      ReachesPrefix step p (n + 1) s [] .stuck

/-- Induced query-indexed partial behavior of program `p` in machine `M`:
    - `defined`: if `q.init` is a valid initial state (`M.initState p q.init`),
      then every prefix of length `q.steps` reachable from `q.init` has a safe
      outcome (`out.isSafe`). When `q.init` is not a valid initial state of `p`,
      `defined` holds vacuously and `val` is empty (`False`).
    - `val`: the predicate of all `ExecOut Obs Val` reachable from `q.init` in
      `q.steps` steps. -/
@[candidate step_result]
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M.step p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M.step p q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a `Language` with
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
