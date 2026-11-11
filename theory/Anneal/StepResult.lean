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
# Small-Step Meta-Theorems and Constructive Reactive Separation (`Anneal.StepResult`)

Proves structural non-vacuity theorems (`TotalStep`, `InhabitedDemonic`,
`exists_reaches_prefix`), prefix concatenation (`reachesPrefix_cut_trans`),
`Partial` specification bridge lemmas (`eventualBehaviorOf_le_wellFormedOn_iff`,
`eventualBehaviorOf_le_wellFormed_iff`, `eventualBehaviorOf_le_normalSpecOn`,
`eventualBehaviorOf_le_normalSpec`), and constructive reactive trace separation
over `Trusted.StepResult` (`Law II`).
-/

namespace Anneal

open Trusted

/-- Any `StepResult.choice` produced by `RawStep.toStepResult` is inhabited. -/
theorem RawStep.toStepResult_choice_inhabited {State Obs Val : Type}
    {r : RawStep State Val} {branches : State → Prop}
    (h : StepResult.choice (Obs := Obs) (Val := Val) branches =
      r.toStepResult) :
    ∃ s', branches s' := by
  cases r with
  | silent s' =>
    injection h with hbr
    subst hbr
    exact ⟨s', rfl⟩
  | terminated _ => nomatch h
  | failed => nomatch h

/-- Dominator-cut prefix concatenation: reaching `.running s_cut` in `n₁`
silent steps and then reaching `out` with trace `tr` in `n₂` steps from `s_cut`
yields a `(n₁ + n₂)`-step prefix execution from `s₀`. -/
theorem reachesPrefix_cut_trans
    {Prog State Obs Val : Type}
    {step : Prog → State → StepResult State Obs Val → Prop}
    {p : Prog} :
    ∀ {n₁ n₂ : Nat} {s₀ s_cut : State} {tr : List Obs}
      {out : PrefixOutcome State Val},
      ReachesPrefix step p n₁ s₀ [] (.running s_cut) →
      ReachesPrefix step p n₂ s_cut tr out →
      ReachesPrefix step p (n₁ + n₂) s₀ tr out
  | 0, n₂, _, _, _, _, .zero _, h₂ =>
      Eq.mpr
        (congrArg (fun k => ReachesPrefix step p k _ _ _) (Nat.zero_add n₂))
        h₂
  | n₁ + 1, n₂, s₀, _, tr, out,
      .choice _ _ s_mid branches _ _ hstep hbr h₁, h₂ =>
      have h_ih : ReachesPrefix step p (n₁ + n₂ + 1) s₀ tr out :=
        .choice (n₁ + n₂) s₀ s_mid branches tr out hstep hbr
          (reachesPrefix_cut_trans h₁ h₂)
      Eq.mpr
        (congrArg (fun k => ReachesPrefix step p k s₀ tr out)
          (Nat.succ_add n₁ n₂))
        h_ih

/-- Every state of program `p` has at least one step outcome. -/
def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

/-- Every reachable choice node has at least one enabled branch. -/
def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (branches : State → Prop),
    M.step p s (.choice branches) → ∃ s', branches s'

/-- Constructive prefix existence at every step budget `n : Nat` from any
starting state `s`. -/
theorem exists_reaches_prefix
    {M : SmallStepMachine Prog State Obs Val}
    (h_tot : TotalStep M)
    (h_dem : InhabitedDemonic M)
    (p : Prog) (n : Nat) :
    ∀ (s : State),
      ∃ tr out, ReachesPrefix M.step p n s tr out ∧ out ≠ .stuck := by
  induction n with
  | zero =>
    intro s
    exact ⟨[], .running s, ReachesPrefix.zero s, by intro h; cases h⟩
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
      | choice branches =>
        cases h_dem p s branches hstep with
        | intro s' hbranch =>
          cases ih s' with
          | intro tr hrest =>
            cases hrest with
            | intro out hpair =>
              exact ⟨tr, out,
                ReachesPrefix.choice
                  k s s' branches tr out hstep hbranch hpair.1,
                hpair.2⟩
      | terminated term =>
        exact ⟨[], .terminated term,
          ReachesPrefix.terminated k s term hstep,
          by intro h; cases h⟩
      | failed =>
        exact ⟨[], .failed,
          ReachesPrefix.failed k s hstep,
          by intro h; cases h⟩

/-- Refining `wellFormedOn M.toLanguage pre` unfolds to `out.isSafe` across
every initial state `init` satisfying `pre init`, step budget `n`, trace `tr`,
and prefix outcome `out`. -/
theorem eventualBehaviorOf_le_wellFormedOn_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : State → Prop} :
    EventualBehaviorOf M p ≤ wellFormedOn M.toLanguage pre ↔
      ∀ init n tr out,
        pre init →
        M.initState p init →
        ReachesPrefix M.step p n init tr out →
        out.isSafe := by
  constructor
  · intro h init n tr out hpre hinit hreach
    exact
      (le_wellFormedOn_iff (L := M.toLanguage) (EventualBehaviorOf M p) pre).mp
        h init hpre hinit n tr out hreach
  · intro h
    refine
      (le_wellFormedOn_iff (L := M.toLanguage) (EventualBehaviorOf M p) pre).mpr
        ?_
    intro init hpre hinit n tr out hreach
    exact h init n tr out hpre hinit hreach

/-- Refining `wellFormed M.toLanguage` unfolds to `out.isSafe` across every
initial state `init`, step budget `n`, trace `tr`, and outcome `out`. -/
theorem eventualBehaviorOf_le_wellFormed_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} :
    EventualBehaviorOf M p ≤ wellFormed M.toLanguage ↔
      ∀ init n tr out,
        M.initState p init →
        ReachesPrefix M.step p n init tr out →
        out.isSafe := by
  constructor
  · intro h init n tr out hinit hreach
    exact
      (le_wellFormed_iff (L := M.toLanguage) (EventualBehaviorOf M p)).mp
        h init hinit n tr out hreach
  · intro h
    refine
      (le_wellFormed_iff (L := M.toLanguage) (EventualBehaviorOf M p)).mpr ?_
    intro init hinit n tr out hreach
    exact h init n tr out hinit hreach

/-- Bridge lemma for establishing normal-return partial-correctness
specifications on `EventualBehaviorOf M p`. -/
theorem eventualBehaviorOf_le_normalSpecOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : State → Prop}
    {P : State → Val → Prop}
    (h : ∀ (s : State) (n : Nat) (tr : List Obs) (oc : PrefixOutcome State Val),
      pre s →
      M.initState p s ∧
      ReachesPrefix M.step p n s tr oc →
      oc.isSafe ∧ ∀ ret, oc = .terminated (.normal ret) → P s ret) :
    EventualBehaviorOf M p ≤
      (M.toLanguage).SpecOn pre (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) := by
  intro s hpre
  refine ⟨fun hinit n tr oc hreach => (h s n tr oc hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval tr ret hout
  subst hout
  cases hval.2 with
  | intro n hreach =>
    exact (h s n tr (.terminated (.normal ret)) hpre ⟨hval.1, hreach⟩).2 ret rfl

/-- Unconditional specialization of `eventualBehaviorOf_le_normalSpecOn`. -/
theorem eventualBehaviorOf_le_normalSpec
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {P : State → Val → Prop}
    (h : ∀ (s : State) (n : Nat) (tr : List Obs) (oc : PrefixOutcome State Val),
      M.initState p s ∧
      ReachesPrefix M.step p n s tr oc →
      oc.isSafe ∧ ∀ ret, oc = .terminated (.normal ret) → P s ret) :
    EventualBehaviorOf M p ≤
      (M.toLanguage).Spec (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) :=
  eventualBehaviorOf_le_normalSpecOn (fun s n tr oc _ hpfx => h s n tr oc hpfx)

/-!
## Constructive Reactive Trajectory Separation (`Law II`)
-/

/-- A one-shot machine (`State := Bool`) that emits `()` once from `true` to
`false`, and then silently loops forever at `false`. This finite-emission
silent loop cannot inhabit `.reacts tr` because stage 1 of any trajectory
starting at `false` can never emit a non-empty trace segment. -/
def oneShotSilentMachine : SmallStepMachine Unit Bool Unit Empty where
  initState _ s := s = true
  step _ s r    :=
    if s then r = .step () false else r = .silent false

theorem oneShotSilent_false_only_empty_trace :
    ∀ n s' tr out,
      s' = false →
      ReachesPrefix oneShotSilentMachine.step () n s' tr out →
      tr = [] ∧ out = .running false
  | 0, _, _, _, rfl, .zero _ => ⟨rfl, rfl⟩
  | _ + 1, _, _, _, rfl, .step _ _ _ _ _ _ hstep _ => by cases hstep
  | n + 1, _, _, _, rfl, .choice _ _ s_next _ _ _ hstep hbr hrest => by
    dsimp [oneShotSilentMachine] at hstep
    injection hstep with hbr_eq
    subst hbr_eq
    exact oneShotSilent_false_only_empty_trace n s_next _ _ hbr hrest
  | _ + 1, _, _, _, rfl, .emptyChoice _ _ _ hstep hemp => by
    dsimp [oneShotSilentMachine] at hstep
    injection hstep with hbr_eq
    subst hbr_eq
    exact False.elim (hemp ⟨false, rfl⟩)
  | _ + 1, _, _, _, rfl, .terminated _ _ _ hstep => by cases hstep
  | _ + 1, _, _, _, rfl, .failed _ _ hstep => by cases hstep
  | _ + 1, _, _, _, rfl, .noStep _ _ hnostep =>
    False.elim (hnostep ⟨.silent false, rfl⟩)

theorem oneShotSilent_step_ends_at_false :
    ∀ m s₀ seg out,
      seg ≠ [] →
      ReachesPrefix oneShotSilentMachine.step () (m + 1) s₀ seg out →
      out = .running false
  | m, true, _, out, _, .step _ _ _ _ tr' _ hstep hrest => by
    dsimp [oneShotSilentMachine] at hstep
    injection hstep with _ hs'
    exact
      (oneShotSilent_false_only_empty_trace m _ tr' out hs' hrest).2
  | _, true, _, _, _, .choice _ _ _ _ _ _ hstep _ _ => by cases hstep
  | _, true, _, _, _, .emptyChoice _ _ _ hstep _ => by cases hstep
  | _, true, _, _, _, .terminated _ _ _ hstep => by cases hstep
  | _, true, _, _, _, .failed _ _ hstep => by cases hstep
  | _, true, _, _, _, .noStep _ _ hnostep =>
    False.elim (hnostep ⟨.step () false, rfl⟩)
  | m, false, seg, out, hne, hreach =>
    False.elim
      (hne
        (oneShotSilent_false_only_empty_trace (m + 1) false seg out rfl hreach).1)

/-- Canary theorem (`Law II`): a machine that emits only finitely many events
before entering a silent loop cannot inhabit `.reacts tr`. -/
theorem oneShotSilent_cannot_react
    (hdef : (EventualBehaviorOf oneShotSilentMachine () true).defined)
    (tr : List Unit) :
    ¬ (EventualBehaviorOf oneShotSilentMachine () true).val hdef (.reacts tr)
  | ⟨_, _, _, _, _, traj, segTrace, _, hstages⟩ =>
    let ⟨hne0, m0, hreach0⟩ := hstages 0
    have hout0 : PrefixOutcome.running (traj 1) = .running false :=
      oneShotSilent_step_ends_at_false m0 (traj 0) (segTrace 0)
        (.running (traj 1)) hne0 hreach0
    have htraj1 : traj 1 = false := PrefixOutcome.running.inj hout0
    let ⟨hne1, m1, hreach1⟩ := hstages 1
    let ⟨hempty1, _⟩ :=
      oneShotSilent_false_only_empty_trace (m1 + 1) (traj 1) (segTrace 1)
        (.running (traj 2)) htraj1 hreach1
    hne1 hempty1

/-!
## 2. Reactive Trace Separation (`BB-4`)
-/

namespace BB4

/-- A simple reactive server (`Prog := Bool`) where `true` is the productive
server that emits `()` at every step (`step () ()`), and `false` is a silent
loop (`silent ()`). -/
def reactiveVsSilentMachine : SmallStepMachine Bool Unit Unit Empty where
  initState _ _ := True
  step p _ r    :=
    if p then
      r = .step () ()
    else
      r = .silent ()

abbrev ReactiveLang : Language :=
  reactiveVsSilentMachine.toLanguage

theorem silentLoop_reaches_empty_prefix :
    ∀ k, ∃ s',
      ReachesPrefix reactiveVsSilentMachine.step false k () [] (.running s')
  | 0 => ⟨(), .zero ()⟩
  | k + 1 => by
    cases silentLoop_reaches_empty_prefix k with
    | intro s' hk =>
      exact ⟨s', .choice k () () (· = ()) [] (.running s') rfl rfl hk⟩

theorem reactiveServer_no_empty_step {k : Nat} {s s' : Unit}
    (h : ReachesPrefix reactiveVsSilentMachine.step true (k + 1) s []
      (.running s')) :
    False := by
  cases h with
  | choice _ _ _ _ _ _ hstep _ _ =>
    dsimp [reactiveVsSilentMachine] at hstep
    cases hstep

theorem reactiveServer_always_safe :
    ∀ n s tr out,
      ReachesPrefix reactiveVsSilentMachine.step true n s tr out →
      out.isSafe
  | 0, _, _, _, .zero _ => trivial
  | n + 1, _, _, _, .step _ _ s' _ tr out _ hrest =>
      reactiveServer_always_safe n s' tr out hrest
  | _ + 1, _, _, _, .choice _ _ _ _ _ _ hstep _ _ => by
      dsimp [reactiveVsSilentMachine] at hstep; cases hstep
  | _ + 1, _, _, _, .emptyChoice _ _ _ hstep _ => by
      dsimp [reactiveVsSilentMachine] at hstep; cases hstep
  | _ + 1, _, _, _, .terminated _ _ _ hstep => by
      dsimp [reactiveVsSilentMachine] at hstep; cases hstep
  | _ + 1, _, _, _, .failed _ _ hstep => by
      dsimp [reactiveVsSilentMachine] at hstep; cases hstep
  | _ + 1, _, _, _, .noStep _ _ hno =>
      False.elim (hno ⟨.step () (), rfl⟩)

/-- A silent loop (`false`) produces `.diverges []`, whereas the productive
reactive server (`true`) never silently diverges; hence `silentLoop` does not
compile `reactiveServer`. -/
theorem silentLoop_does_not_compile_reactiveServer :
    ¬ Compiles ReactiveLang ReactiveLang (BehaviorCodec.id ReactiveLang)
        true false := by
  intro hcomp
  have hdef_true : (ReactiveLang.sem true ()).defined :=
    fun _ n tr out hreach => reactiveServer_always_safe n () tr out hreach
  cases hcomp () hdef_true with
  | intro hdef_false hle =>
    have hdiv_false :
        (ReactiveLang.sem false ()).val hdef_false (.diverges []) :=
      ⟨trivial, 0, (), .zero (), fun _ => (), rfl, fun _ =>
        ⟨0, .choice 0 () () (· = ()) [] (.running ()) rfl rfl (.zero ())⟩⟩
    cases hle (.diverges []) hdiv_false with
    | intro o₁ h₁ =>
      cases h₁ with
      | intro hdec ho₁ =>
        injection hdec with heq
        subst heq
        cases ho₁.2 with
        | intro n hn =>
          cases hn with
          | intro s hs =>
            cases hs.2 with
            | intro traj htraj =>
              cases htraj.2 0 with
              | intro m hm =>
                exact reactiveServer_no_empty_step hm

end BB4

namespace StepCanaries

/-- A machine whose program fails static well-formedness (`wf := False`). -/
def IllFormedMachine : SmallStepMachine Unit Unit Empty Unit where
  wf        _   := False
  initState _ _ := False
  step _ s r    := r = .terminated (.normal s)

/-- Canary: a program that fails static machine well-formedness (`¬ M.wf p`) is
rejected even against a vacuous precondition (`fun _ => False`). -/
theorem s2_4_ill_formed_rejected :
    ¬ IllFormedMachine.toLanguage.Verified
      (fun _ => False) (fun _ _ => False) () :=
  verified_rejects_ill_formed (L := IllFormedMachine.toLanguage) () _ _
    (fun h => h)

/-- A 2-state silent livelock after emitting `obs₁` satisfies `.diverges [()]`
under stutter-elastic `EventualBehaviorOf` and refutes `.reacts [()]`. -/
inductive TwoLivelockState where
  | init
  | s1
  | s2

def TwoStateLivelockMachine :
    SmallStepMachine Unit TwoLivelockState Unit Unit where
  initState _ s := s = .init
  step _ s r :=
    match s with
    | .init => r = .step () .s1
    | .s1   => r = .silent .s2
    | .s2   => r = .silent .s1

def twoStateTraj : Nat → TwoLivelockState
  | 0     => .s1
  | k + 1 =>
    match twoStateTraj k with
    | .init => .s1
    | .s1   => .s2
    | .s2   => .s1

theorem twoStateTraj_step :
    ∀ k, ∃ m,
      ReachesPrefix TwoStateLivelockMachine.step () (m + 1) (twoStateTraj k) []
        (.running (twoStateTraj (k + 1))) := by
  have h_inv : ∀ k, twoStateTraj k = .s1 ∨ twoStateTraj k = .s2 := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      dsimp [twoStateTraj]
      cases ih with
      | inl h1 =>
        rw [h1]
        exact Or.inr rfl
      | inr h2 =>
        rw [h2]
        exact Or.inl rfl
  intro k
  cases h_inv k with
  | inl h1 =>
    refine ⟨0, ?_⟩
    dsimp [twoStateTraj]
    rw [h1]
    exact .choice 0 TwoLivelockState.s1 TwoLivelockState.s2
      (· = TwoLivelockState.s2) [] (.running TwoLivelockState.s2)
      rfl rfl (.zero TwoLivelockState.s2)
  | inr h2 =>
    refine ⟨0, ?_⟩
    dsimp [twoStateTraj]
    rw [h2]
    exact .choice 0 TwoLivelockState.s2 TwoLivelockState.s1
      (· = TwoLivelockState.s1) [] (.running TwoLivelockState.s1)
      rfl rfl (.zero TwoLivelockState.s1)

theorem twoState_silent_only {n : Nat} {s : TwoLivelockState} {tr : List Unit}
    {out : PrefixOutcome TwoLivelockState Unit}
    (hs : s = .s1 ∨ s = .s2)
    (hr : ReachesPrefix TwoStateLivelockMachine.step () n s tr out) :
    tr = [] ∧ (out = .running .s1 ∨ out = .running .s2) := by
  induction hr with
  | zero s =>
    exact ⟨rfl,
      hs.elim (fun h => Or.inl (by rw [h])) (fun h => Or.inr (by rw [h]))⟩
  | step _ _ _ _ _ _ hstep _ _ =>
    cases hs with
    | inl h => subst h; nomatch hstep
    | inr h => subst h; nomatch hstep
  | choice _ _ s' _ _ _ hstep hbr _ ih =>
    cases hs with
    | inl h =>
      subst h
      injection hstep with hb
      rw [hb] at hbr
      subst hbr
      exact ih (Or.inr rfl)
    | inr h =>
      subst h
      injection hstep with hb
      rw [hb] at hbr
      subst hbr
      exact ih (Or.inl rfl)
  | emptyChoice _ _ _ hstep hno =>
    cases hs with
    | inl h =>
      subst h
      injection hstep with hb
      rw [hb] at hno
      exact False.elim (hno ⟨.s2, rfl⟩)
    | inr h =>
      subst h
      injection hstep with hb
      rw [hb] at hno
      exact False.elim (hno ⟨.s1, rfl⟩)
  | terminated _ _ _ hstep =>
    cases hs with
    | inl h => subst h; nomatch hstep
    | inr h => subst h; nomatch hstep
  | failed _ _ hstep =>
    cases hs with
    | inl h => subst h; nomatch hstep
    | inr h => subst h; nomatch hstep
  | noStep _ _ hno =>
    cases hs with
    | inl h =>
      subst h
      exact False.elim (hno ⟨.silent .s2, rfl⟩)
    | inr h =>
      subst h
      exact False.elim (hno ⟨.silent .s1, rfl⟩)

theorem holdout_A3_part2_livelock_diverges_and_not_reacts
    (hdef : (EventualBehaviorOf TwoStateLivelockMachine () .init).defined) :
    (EventualBehaviorOf TwoStateLivelockMachine () .init).val hdef
      (.diverges [()]) ∧
    ¬ (EventualBehaviorOf TwoStateLivelockMachine () .init).val hdef
      (.reacts [()]) := by
  refine ⟨?_, ?_⟩
  · refine ⟨rfl, 1, TwoLivelockState.s1,
      .step 0 TwoLivelockState.init TwoLivelockState.s1 () []
        (.running TwoLivelockState.s1) rfl (.zero TwoLivelockState.s1),
      twoStateTraj, rfl, twoStateTraj_step⟩
  · -- After the single emission, the machine alternates silently between
    -- `s1` and `s2`, so the first trajectory segment of any `.reacts`
    -- witness would need a non-empty trace from a silent state.
    intro ⟨_, _, n, s, hpre, traj, segTrace, htraj0, hstages⟩
    cases hpre with
    | step n1 _ s' _ tr1 _ hstep hr1 =>
      injection hstep with _ hs'
      subst hs'
      have hs := (twoState_silent_only (Or.inl rfl) hr1).2
      have htrajS : traj 0 = .s1 ∨ traj 0 = .s2 := by
        rw [htraj0]
        cases hs with
        | inl h => injection h with h; exact Or.inl h
        | inr h => injection h with h; exact Or.inr h
      cases hstages 0 with
      | intro hne hex =>
        cases hex with
        | intro m hm =>
          exact hne (twoState_silent_only htrajS hm).1
    | choice _ _ _ _ _ _ hstep _ _ => nomatch hstep

/-- A finite countdown machine does not satisfy stutter-elastic `.diverges []`
(`∀ k, ∃ m, ReachesPrefix ... (m + 1) ...`), while
`.terminated [] (.normal 42)` holds. -/
inductive CountdownState where
  | init
  | count (n : Nat)

def CountdownMachine : SmallStepMachine Unit CountdownState Empty Nat where
  initState _ s := s = .init
  step _ s r :=
    match s with
    | .init          => r = .choice (fun s' => ∃ m : Nat, s' = .count m)
    | .count (m + 1) => r = .silent (.count m)
    | .count 0       => r = .terminated (.normal 42)

theorem countdown_reaches_le :
    ∀ {steps : Nat} {c : Nat} {tr : List Empty}
      {out : PrefixOutcome CountdownState Nat} {s' : CountdownState},
      ReachesPrefix CountdownMachine.step () steps (.count c) tr out →
      out = .running s' →
      ∃ c', s' = .count c' ∧ c' ≤ c := by
  intro steps
  induction steps with
  | zero =>
    intro c tr out s' hr hout
    cases hr with
    | zero =>
      injection hout with hs'
      exact ⟨c, hs'.symm, Nat.le_refl c⟩
  | succ steps ih =>
    intro c tr out s' hr hout
    cases c with
    | zero =>
      cases hr with
      | step _ _ _ obs _ _ _ _ => nomatch obs
      | choice _ _ _ _ _ _ hstep _ _ => nomatch hstep
      | emptyChoice _ _ _ _ _ => nomatch hout
      | terminated _ _ _ _ => nomatch hout
      | failed _ _ _ => nomatch hout
      | noStep _ _ _ => nomatch hout
    | succ c₀ =>
      cases hr with
      | step _ _ _ obs _ _ _ _ => nomatch obs
      | choice _ _ sMid _ _ _ hstep hbr hr' =>
        injection hstep with hb
        rw [hb] at hbr
        subst hbr
        cases ih hr' hout with
        | intro c' hc' =>
          exact ⟨c', hc'.1, Nat.le_succ_of_le hc'.2⟩
      | emptyChoice _ _ _ _ _ => nomatch hout
      | terminated _ _ _ _ => nomatch hout
      | failed _ _ _ => nomatch hout
      | noStep _ _ _ => nomatch hout

theorem countdown_step_plus_from_count :
    ∀ {m : Nat} {c : Nat} {tr : List Empty} {s' : CountdownState},
      ReachesPrefix CountdownMachine.step () (m + 1) (.count c) tr
        (.running s') →
      ∃ c₀ c', c = c₀ + 1 ∧ s' = .count c' ∧ c' ≤ c₀ := by
  intro m c tr s' hr
  cases c with
  | zero =>
    cases hr with
    | step _ _ _ obs _ _ _ _ => nomatch obs
    | choice _ _ _ _ _ _ hstep _ _ => nomatch hstep
  | succ c₀ =>
    cases hr with
    | step _ _ _ obs _ _ _ _ => nomatch obs
    | choice _ _ sMid _ _ _ hstep hbr hr' =>
      injection hstep with hb
      rw [hb] at hbr
      subst hbr
      cases countdown_reaches_le hr' rfl with
      | intro c' hc' =>
        exact ⟨c₀, c', rfl, hc'.1, hc'.2⟩

theorem countdown_reaches_from_init :
    ∀ {steps : Nat} {tr : List Empty} {s' : CountdownState},
      ReachesPrefix CountdownMachine.step () (steps + 1) .init tr
        (.running s') →
      ∃ c', s' = .count c' := by
  intro steps tr s' hr
  cases hr with
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ sMid _ _ _ hstep hbr hr' =>
    injection hstep with hb
    rw [hb] at hbr
    cases hbr with
    | intro m hm =>
      subst hm
      cases countdown_reaches_le hr' rfl with
      | intro c' hc' =>
        exact ⟨c', hc'.1⟩

theorem countdown_no_traj :
    ∀ (B : Nat) (traj : Nat → CountdownState),
      (∀ k, ∃ m,
        ReachesPrefix CountdownMachine.step () (m + 1) (traj k) []
          (.running (traj (k + 1)))) →
      ∀ idx c, c ≤ B → traj idx = .count c → False := by
  intro B
  induction B with
  | zero =>
    intro traj hstep idx c hle hidx
    cases hstep idx with
    | intro m hr =>
      rw [hidx] at hr
      cases countdown_step_plus_from_count hr with
      | intro c₀ hc₀ =>
        cases hc₀ with
        | intro c' hc' =>
          have hcz := hc'.1
          rw [hcz] at hle
          nomatch hle
  | succ B ih =>
    intro traj hstep idx c hle hidx
    cases hstep idx with
    | intro m hr =>
      rw [hidx] at hr
      cases countdown_step_plus_from_count hr with
      | intro c₀ hc₀ =>
        cases hc₀ with
        | intro c' hc' =>
          have hcz := hc'.1
          rw [hcz] at hle
          have hc₀_le : c₀ ≤ B := Nat.le_of_succ_le_succ hle
          have hc'_le : c' ≤ B := Nat.le_trans hc'.2.2 hc₀_le
          exact ih traj hstep (idx + 1) c' hc'_le hc'.2.1

theorem holdout_A3_part2_countdown_not_diverges_and_terminates
    (hdef : (EventualBehaviorOf CountdownMachine () .init).defined) :
    ¬ (EventualBehaviorOf CountdownMachine () .init).val hdef (.diverges []) ∧
    (EventualBehaviorOf CountdownMachine () .init).val hdef
      (.terminated [] (.normal 42)) := by
  refine ⟨?_, ?_⟩
  · intro hval
    cases hval.2 with
    | intro n hn =>
      cases hn with
      | intro s hs =>
        cases hs.2 with
        | intro traj htraj =>
          have hstep := htraj.2
          cases hs0 : traj 0 with
          | count c =>
            exact countdown_no_traj c traj hstep 0 c (Nat.le_refl c) hs0
          | init =>
            cases hstep 0 with
            | intro m0 hr0 =>
              rw [hs0] at hr0
              cases countdown_reaches_from_init hr0 with
              | intro c' hs1 =>
                exact countdown_no_traj c' traj hstep 1 c' (Nat.le_refl c') hs1
  · refine ⟨rfl, 2, ?_⟩
    exact .choice 1 CountdownState.init (CountdownState.count 0)
      (fun s' => ∃ m, s' = CountdownState.count m) []
      (.terminated (.normal 42)) rfl ⟨0, rfl⟩
      (.terminated 0 (CountdownState.count 0) (.normal 42) rfl)

end StepCanaries

end Anneal
