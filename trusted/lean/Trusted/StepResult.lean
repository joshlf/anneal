-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Core
import Trusted.Attributes
import Trusted.Refinement

/-!
# Small-Step Operational Machines and Stutter-Elastic Eventual Behaviors

This module (`Trusted/StepResult.lean`) instantiates `Trusted.Language` for
small-step operational transition systems (`SmallStepMachine`) without
coinduction or `Classical.choice`:

1. `StepResult` with 4 inductive constructors (`step`, `choice`, `terminated`,
   `failed`) plus smart constructors `StepResult.silent` (deterministic
   `τ`-step) and `StepResult.externalCall` (open-world callback boundary
   guard),
2. `ReachesPrefix` enforcing all-prefix safety (`.failed` and `.stuck` are
   unsafe at every finite step depth `n : Nat`), and
3. `EventualBehaviorOf` with 3-phase `EventualOut` (`.terminated`, `.diverges`,
   `.reacts`), providing `1 → 0`, `1 → k`, and `k → 1` silent-step
   elasticity, bidirectional termination preservation (`Term ↔ Term`,
   `Div ↔ Div`), and reactive infinite-trace refinement without the
   Prefix-Union Trap or finite-trace `.reacts` pollution.

Non-operational languages (denotational, big-step, algebraic, relational, or
certificate checkers) import only `Trusted.Refinement` and pay zero tax for this
module. Operational machines that do not emit external observation traces leave
`Obs : Type := Empty` at its default value, making `.reacts` uninhabited and
keeping every trace judgmentally `[]`.
-/

namespace Trusted

/-- Distinguishes normal return from panic/unwind completion. -/
@[candidate step_result]
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Single-step transition outcome in a small-step operational machine:
    - `step obs next`: emits external observation `obs` and advances to `next`.
    - `choice branches`: transitions silently (`τ`) to any state satisfying
      `branches : State → Prop` without emitting an external observation.
    - `terminated term`: finishes execution normally or by unwinding.
    - `failed`: halts immediately due to Undefined Behavior or contract
      violation. -/
@[candidate step_result]
inductive StepResult (State : Type) (Obs : Type := Empty) (Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Deterministic silent (`τ`) internal step to `next` (emits no `Obs`).

    Defining `.silent next` as `.choice (· = next)` avoids adding a redundant
    inductive constructor to `StepResult` and two redundant constructors to
    `ReachesPrefix` while preserving determinism and constructivity: the branch
    predicate `(· = next)` has the unique constructive witness `⟨next, rfl⟩`, so
    `ReachesPrefix.emptyChoice` (`¬ ∃ s', s' = next`) is provably `False`. -/
@[candidate step_result]
def StepResult.silent {State Obs Val : Type}
    (next : State) : StepResult State Obs Val :=
  .choice (· = next)

/-- Open-world external call / callback transition: checks `boundaryInv` (such
    as `AdtInv`, caller stack-frame isolation, and ABI alignment) at the call
    site before demonically havocing caller-saved state over `branches`. Adds
    zero inductive constructors to `StepResult` or `ReachesPrefix`.

    # Auditor Rationale
    1. **Why `boundaryInv` has type `Bool` rather than `Prop`:** `StepResult`
       lives in `Type`. Branching via `if boundaryInv then ... else ...` inside
       `Type` on an arbitrary `Prop` without a constructive `Decidable` instance
       would invoke `Classical.propDecidable` (`Classical.choice`), violating
       Anneal's zero-choice axiom policy.
    2. **Fail-closed on empty `branches`:** When `boundaryInv = true` and
       `branches` is uninhabited (`¬ ∃ s', branches s'`, e.g., an inconsistent
       external call summary), `ReachesPrefix.emptyChoice` transitions to
       `PrefixOutcome.stuck` (`isSafe = False`), making `defined` become `False`
       (`Partial.ub`) rather than succeeding vacuously. -/
@[candidate step_result]
def StepResult.externalCall {State Obs Val : Type}
    (boundaryInv : Bool) (branches : State → Prop) :
    StepResult State Obs Val :=
  if boundaryInv then .choice branches else .failed

/-- Outcome recorded at the end of an `n`-step execution prefix:
    - `running cur`: budget exhausted at active state `cur`. Carries `cur` so
      `EventualBehaviorOf` can express unbounded continuation from `cur` in
      `.diverges` and `.reacts`.
    - `terminated term`: reached a terminal state within the budget.
    - `failed`: encountered Undefined Behavior within the budget.
    - `stuck`: reached a state with no outgoing transition or an empty
      choice. -/
@[candidate step_result]
inductive PrefixOutcome (State Val : Type) where
  | running (cur : State)
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

/-- A prefix outcome is safe when it neither fails (`.failed`) nor gets stuck
    in an unmodeled state or empty choice (`.stuck`). -/
@[candidate step_result]
def PrefixOutcome.isSafe {State Val : Type} : PrefixOutcome State Val → Prop
  | .running _ => True
  | .terminated _ => True
  | .failed => False
  | .stuck => False

/-- Step-decoupled observable outcome of an operational execution:
    - `terminated trace term`: halts in `term` after emitting `trace`.
    - `diverges trace`: emits `trace` to reach a state from which it can take
      arbitrarily many silent (`τ`) steps without emitting further `Obs`.
    - `reacts trace`: emits non-empty observation prefix `trace` (`trace ≠ []`)
      along an unbounded ongoing execution. -/
@[candidate step_result]
inductive EventualOut (Obs : Type := Empty) (Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges   (trace : List Obs)
  | reacts     (trace : List Obs)

/-- Normal return with an empty observation trace (`trace := []`). -/
@[candidate step_result]
abbrev EventualOut.ret {Obs Val : Type} (v : Val) : EventualOut Obs Val :=
  .terminated [] (.normal v)

/-- Panic/unwind completion with an empty observation trace (`trace := []`). -/
@[candidate step_result]
abbrev EventualOut.unwind {Obs Val : Type} : EventualOut Obs Val :=
  .terminated [] .unwind

/-- Project the return value payload of `EventualOut` along `f : Val → SemVal`
    while preserving the observation trace and execution phase identically. -/
@[candidate step_result]
def EventualOut.map {Obs Val SemVal : Type} (f : Val → SemVal) :
    EventualOut Obs Val → EventualOut Obs SemVal
  | .terminated tr (.normal v) => .terminated tr (.normal (f v))
  | .terminated tr .unwind     => .terminated tr .unwind
  | .diverges tr               => .diverges tr
  | .reacts tr                 => .reacts tr

/-- Small-step operational machine parameterized by programs `Prog`, states
    `State`, external observations `Obs` (defaulting to `Empty`), and return
    values `Val`. -/
@[candidate step_result]
structure SmallStepMachine (Prog State : Type) (Obs : Type := Empty)
    (Val : Type) where
  initState : Prog → State → Prop
  step      : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of an `n`-step execution prefix from `s`.
    Observable steps (`step`) prepend `obs :: tr`; silent steps (`choice` and
    `silent`) preserve `tr` unchanged; unmodeled states (`noStep`) and empty
    choices (`emptyChoice`) record `.stuck`.

    # Auditor Note on Terminal Absorbency
    Recursive constructors (`step`, `choice`, `emptyChoice`, `terminated`,
    `failed`, `noStep`) only step from `.running s`; there is no constructor
    extending `.terminated`, `.failed`, or `.stuck` from step `k` to `k + 1`.
    Because `EventualBehaviorOf.defined` quantifies universally over all step
    budgets `∀ n tr out`, any path that reaches `.failed` or `.stuck` at step
    `k` immediately falsifies `defined` at `n = k`. -/
@[candidate step_result]
inductive ReachesPrefix
    {Prog State Obs Val : Type}
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome State Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] (.running s)
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome State Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome State Val) :
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

/-- Step-decoupled eventual behavior of program `p` in machine `M`:
    - `defined`: every finite step prefix `n : Nat` from `init` is safe
      (neither `.failed` nor `.stuck`).
    - `val`: reachable `.terminated`, `.diverges` (quiescent silent livelock
      after `tr`), and `.reacts` (non-empty observation prefix `tr` along an
      unbounded reactive execution) outcomes.

    # Auditor Rationale
    1. **Opposite Polarities of `M.initState p init`:** `M.initState p init` is
       an implication premise in `defined` (`M.initState p init → ...`) and a
       conjunct in `val` (`M.initState p init ∧ ...`). If `M.initState p init`
       is false on an input satisfying `pre init`, `val` is empty (`False`), so
       `Language.ProductiveOn pre p` (`∃ o, val h o`) fails closed.
    2. **Why `.reacts tr` Requires `tr ≠ []` AND Unbounded Continuation:**
       - `tr ≠ []` blocks the 0-step empty prefix (`ReachesPrefix.zero`) from
         polluting every program with `.reacts []` (the Prefix-Union Trap).
       - `∀ k, ∃ s' tr', ReachesPrefix M.step p k s tr' (.running s')` ensures
         that `.reacts tr` only fires on genuinely non-terminating reactive
         executions, preventing finite-trace terminating programs from polluting
         their singleton `.terminated tr (.normal v)` outcome set with
         `.reacts tr`. -/
@[candidate step_result]
def EventualBehaviorOf {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    State → Partial (EventualOut Obs Val → Prop) :=
  fun init => {
    defined :=
      M.initState p init →
        ∀ n tr out,
          ReachesPrefix M.step p n init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p init ∧
      match out with
      | .terminated tr term =>
          ∃ n, ReachesPrefix M.step p n init tr (.terminated term)
      | .diverges tr =>
          ∃ n s, ReachesPrefix M.step p n init tr (.running s) ∧
            ∀ k, ∃ s', ReachesPrefix M.step p k s [] (.running s')
      | .reacts tr =>
          tr ≠ [] ∧ ∃ n s, ReachesPrefix M.step p n init tr (.running s) ∧
            ∀ k, ∃ s' tr', ReachesPrefix M.step p k s tr' (.running s')
  }

/-- Package a `SmallStepMachine` as a `Trusted.Language` with observable return
    value projection `obsVal : Val → SemVal`. -/
@[candidate step_result]
abbrev SmallStepMachine.toLanguageWithObs {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val)
    {SemVal : Type} (obsVal : Val → SemVal) :
    Language (EventualOut Obs SemVal) where
  Prog  := Prog
  Query := State
  Out   := EventualOut Obs Val
  obs   := EventualOut.map obsVal
  sem   := EventualBehaviorOf M

/-- Package a `SmallStepMachine` as a `Trusted.Language` when `Val` has no
    unobserved slack (`obs := id`). -/
@[candidate step_result]
abbrev SmallStepMachine.toLanguage {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) :
    Language (EventualOut Obs Val) :=
  Language.mkSimple Prog State (EventualOut Obs Val) (EventualBehaviorOf M)

end Trusted
