-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:step_result
prelude
import Init.NotationExtra
import Init.Core
import Trusted.Refinement

/-!
# Small-Step Operational Machines & Eventual Behaviors (`Trusted/StepResult.lean`)

Instantiates `Trusted.Language` for small-step operational transition systems
(`SmallStepMachine`) without coinduction or `Classical.choice`:

1. `StepResult` (`step`, `choice`, `terminated`, `failed`) plus the smart
   constructor `StepResult.silent`.
2. `ReachesPrefix` enforcing all-prefix safety (`.failed` and `.stuck` are
   unsafe at every finite step budget `n : Nat`).
3. `EventualBehaviorOf` with 3-phase `EventualOut` (`.terminated`, `.diverges`,
   `.reacts`), using constructive infinite trajectory witnesses (`traj`) for
   both silent divergence (`.diverges`) and productive reactivity (`.reacts`),
   and static machine well-formedness `wf := M.wf`.
-/

namespace Trusted

/-- Distinguishes normal return from panic/unwind completion. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Single-step transition outcome in a small-step operational machine. -/
inductive StepResult (State : Type) (Obs : Type := Empty) (Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Deterministic silent (`τ`) internal step to `next` (emits no `Obs`). -/
def StepResult.silent {State Obs Val : Type}
    (next : State) : StepResult State Obs Val :=
  .choice (· = next)

/-- Outcome recorded at the end of an `n`-step execution prefix. -/
inductive PrefixOutcome (State Val : Type) where
  | running (cur : State)
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

/-- A prefix outcome is safe when it neither fails (`.failed`) nor gets stuck
in an unmodeled state or empty choice (`.stuck`). -/
def PrefixOutcome.isSafe {State Val : Type} : PrefixOutcome State Val → Prop
  | .running _ => True
  | .terminated _ => True
  | .failed => False
  | .stuck => False

/-- Step-decoupled observable outcome of an operational execution. -/
inductive EventualOut (Obs : Type := Empty) (Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges   (trace : List Obs)
  | reacts     (trace : List Obs)

/-- Small-step operational machine parameterized by programs `Prog`, states
`State`, external observations `Obs` (defaulting to `Empty`), and return values
`Val`. -/
structure SmallStepMachine (Prog State : Type) (Obs : Type := Empty)
    (Val : Type) where
  wf        : Prog → Prop := fun _ => True
  initState : Prog → State → Prop
  step      : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of an `n`-step execution prefix from `s`. -/
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

/-- Step-decoupled eventual behavior of program `p` in machine `M`, using
constructive infinite trajectory witnesses `traj : Nat → State` for both
`.diverges` and `.reacts`. -/
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
            ∃ traj : Nat → State, traj 0 = s ∧
              ∀ k, ∃ m, ReachesPrefix M.step p (m + 1) (traj k) []
                (.running (traj (k + 1)))
      | .reacts tr =>
          tr ≠ [] ∧ ∃ n s, ReachesPrefix M.step p n init tr (.running s) ∧
            ∃ (traj : Nat → State) (segTrace : Nat → List Obs),
              traj 0 = s ∧
              ∀ k, segTrace k ≠ [] ∧
                ∃ m, ReachesPrefix M.step p (m + 1) (traj k) (segTrace k)
                  (.running (traj (k + 1)))
  }

/-- Package a `SmallStepMachine` as a `Trusted.Language` with static program
well-formedness `wf := M.wf`. -/
abbrev SmallStepMachine.toLanguage {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog  := Prog
  Query := State
  Out   := EventualOut Obs Val
  wf    := M.wf
  sem   := EventualBehaviorOf M

end Trusted
