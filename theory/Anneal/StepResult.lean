-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted
import Anneal.Refinement

/-!
# Untrusted Small-Step Meta-Theorems and Structural Non-Vacuity

This module proves the structural non-vacuity theorems (`TotalStep`,
`InhabitedDemonic`, `non_vacuity_at_every_depth`) and `Partial` specification
bridge lemmas (`behaviorOf_le_wellFormed_iff`, `behaviorOf_le_specOn`,
`behaviorOf_le_spec`, `behaviorOf_le_pure`) over the Layer 1B small-step prefix
semantics (`Trusted.StepResult`).

Because `(BehaviorOf M p q).defined` and `(BehaviorOf M p q).val` quantify over
all prefixes reachable in `q.steps` steps from `q.init`, an operational
semantics with a silent stuck state or an empty demonic choice could otherwise
make `ReachesPrefix` empty and render `BehaviorOf M p ≤ spec` vacuously true.
`Trusted.ReachesPrefix` prevents silent vanishing by recording `.stuck`
whenever `noStep` or `emptyChoice` occurs, and `non_vacuity_at_every_depth`
proves constructively that any machine satisfying `TotalStep` and
`InhabitedDemonic` has at least one non-`.stuck` execution output at every
finite step budget `n : Nat`.
-/

namespace Anneal

open Trusted

/-- Every state of program `p` has at least one step outcome. -/
def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

/-- Every reachable choice node has at least one enabled branch, preventing an
    empty choice predicate from collapsing `ReachesPrefix`. -/
def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

/-- Constructive prefix existence at every step budget `n : Nat` from any
    starting state `s`. -/
theorem exists_reaches_prefix
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (init : State) (n : Nat) :
    ∀ (s : State),
      ∃ tr out, ReachesPrefix M p init n s tr out ∧ out ≠ .stuck := by
  induction n with
  | zero =>
    intro s
    exact ⟨[], .running, ReachesPrefix.zero s, by intro h; cases h⟩
  | succ k ih =>
    intro s
    cases h_tot p s with
    | intro r hstep =>
      cases r with
      | step obs s' =>
        cases ih s' with
        | intro tr hrest =>
          cases hrest with
          | intro out hpair =>
            exact ⟨obs :: tr, out,
              ReachesPrefix.step k s s' obs tr out hstep hpair.1,
              hpair.2⟩
      | choice kind branches =>
        cases h_dem p s kind branches hstep with
        | intro s' hbranch =>
          cases ih s' with
          | intro tr hrest =>
            cases hrest with
            | intro out hpair =>
              exact ⟨tr, out,
                ReachesPrefix.choice k kind s s' branches tr out hstep hbranch hpair.1,
                hpair.2⟩
      | terminated term =>
        exact ⟨[], .terminated term,
          ReachesPrefix.terminated k s term hstep,
          by intro h; cases h⟩
      | failed err =>
        exact ⟨[], .failed err,
          ReachesPrefix.failed k s err hstep,
          by intro h; cases h⟩

/-- Structural non-vacuity at every finite step depth `n : Nat`:
    given `TotalStep M`, `InhabitedDemonic M`, and an initial state `init` of
    `p`, there exists a reachable execution output `out : ExecOut Obs Val` at
    query `⟨init, n⟩` whose outcome is not `.stuck`. -/
theorem non_vacuity_at_every_depth
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (init : State)
    (h_init : M.initState p init)
    (n : Nat) :
    ∃ out : ExecOut Obs Val,
      M.initState p init ∧
      ReachesPrefix M p init n init out.trace out.outcome ∧
      out.outcome ≠ .stuck := by
  cases exists_reaches_prefix h_tot h_dem p init n init with
  | intro tr hrest =>
    cases hrest with
    | intro oc hpair =>
      refine ⟨{ trace := tr, outcome := oc }, ?_⟩
      exact ⟨h_init, hpair.1, hpair.2⟩

/-- Refining `(M.toLanguage).WellFormed` unfolds to `out.isSafe` across every
    initial state `init`, step budget `steps`, trace `tr`, and outcome `out`. -/
theorem behaviorOf_le_wellFormed_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} :
    BehaviorOf M p ≤ (M.toLanguage).WellFormed ↔
      ∀ init steps tr out,
        M.initState p init →
        ReachesPrefix M p init steps init tr out →
        out.isSafe := by
  constructor
  · intro h init steps tr out hinit hreach
    have hdef := (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mp h
      { init := init, steps := steps }
    exact hdef hinit tr out hreach
  · intro h
    refine (le_wellFormed_iff (L := M.toLanguage) (BehaviorOf M p)).mpr ?_
    intro q hinit tr out hreach
    exact h q.init q.steps tr out hinit hreach

/-- Bridge lemma for establishing `BehaviorOf M p ≤ (M.toLanguage).SpecOn pre
    Post`:
    it suffices to show that at every query `q` satisfying `pre q`, every
    reachable prefix `(q, out)` has a safe outcome (`out.outcome.isSafe`) and
    satisfies the functional postcondition `Post q out`. -/
theorem behaviorOf_le_specOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

/-- Bridge lemma for establishing `BehaviorOf M p ≤ (M.toLanguage).Spec Post`:
    it suffices to show that every reachable prefix `(q, out)` has a safe
    outcome (`out.outcome.isSafe`) and satisfies the functional postcondition
    `Post q out`. -/
theorem behaviorOf_le_spec
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).Spec Post :=
  behaviorOf_le_specOn (fun q out _ hpfx => h q out hpfx)

/-- Bridge lemma for establishing `BehaviorOf M p ≤ (fun q => Partial.pure (Post
    q))`:
    specialization of `behaviorOf_le_spec` (since `M.toLanguage.Spec Post` is
    definitionally `fun q => Partial.pure (Post q)`). -/
theorem behaviorOf_le_pure
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (fun q => Partial.pure (Post q)) :=
  behaviorOf_le_spec h

end Anneal
