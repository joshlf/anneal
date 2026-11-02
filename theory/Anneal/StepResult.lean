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
# Small-Step Meta-Theorems, Stutter Elasticity, and Operational Combinators

This module (`theory/Anneal/StepResult.lean`) proves the structural
non-vacuity theorems (`TotalStep`, `InhabitedDemonic`,
`exists_reaches_prefix`), prefix concatenation (`reachesPrefix_cut_trans`),
`Partial` specification bridge lemmas (`eventualBehaviorOf_le_wellFormedOn_iff`,
`eventualBehaviorOf_le_wellFormed_iff`, `eventualBehaviorOf_le_normalSpecOn`,
`eventualBehaviorOf_le_normalSpec`, `eventualBehaviorOf_le_normalPure`),
reactive trace separation (`silentLoop_does_not_compile_reactiveServer`), and
deterministic/callback combinators (`DetMachine`, `ExternalCallContract`) over
`Trusted.StepResult`.
-/

namespace Anneal

open Trusted

/-!
## 1. Structural Totality, Prefix Concatenation, and Specification Bridges
-/

/-- Identity `EventualOut.map` reduces to `o`. -/
@[simp]
theorem EventualOut.map_id {Obs Val : Type} (o : EventualOut Obs Val) :
    EventualOut.map (fun v => v) o = o := by
  cases o with
  | terminated _ term =>
    cases term <;> rfl
  | diverges _ => rfl
  | reacts _   => rfl

/-- Dominator-cut prefix concatenation: reaching `.running s_cut` in `n₁`
    silent steps and then reaching `out` with trace `tr` in `n₂` steps from
    `s_cut` yields a `(n₁ + n₂)`-step prefix execution from `s₀`. -/
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

/-- Three-stage dominator-cut prefix concatenation (`s₀ → s₁ → s₂ → out`),
    showing linear proof-term composition across sequential basic-block or loop
    cuts via `reachesPrefix_cut_trans`. -/
theorem reachesPrefix_cut_trans3
    {Prog State Obs Val : Type}
    {step : Prog → State → StepResult State Obs Val → Prop}
    {p : Prog}
    {n₁ n₂ n₃ : Nat} {s₀ s₁ s₂ : State} {tr : List Obs}
    {out : PrefixOutcome State Val}
    (h₁ : ReachesPrefix step p n₁ s₀ [] (.running s₁))
    (h₂ : ReachesPrefix step p n₂ s₁ [] (.running s₂))
    (h₃ : ReachesPrefix step p n₃ s₂ tr out) :
    ReachesPrefix step p (n₁ + (n₂ + n₃)) s₀ tr out :=
  reachesPrefix_cut_trans h₁ (reachesPrefix_cut_trans h₂ h₃)

/-- Every state of program `p` has at least one step outcome. -/
def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

/-- Every reachable choice node has at least one enabled branch, preventing an
    empty choice predicate from collapsing `ReachesPrefix`. -/
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

/-- Refining `(M.toLanguage).WellFormedOn pre` unfolds to `out.isSafe` across
    every initial state `init` satisfying `pre init`, step budget `n`, trace
    `tr`, and prefix outcome `out`. -/
theorem eventualBehaviorOf_le_wellFormedOn_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : State → Prop} :
    EventualBehaviorOf M p ≤ (M.toLanguage).WellFormedOn pre ↔
      ∀ init n tr out,
        pre init →
        M.initState p init →
        ReachesPrefix M.step p n init tr out →
        out.isSafe := by
  constructor
  · intro h init n tr out hpre hinit hreach
    have hdef :=
      (le_wellFormedOn_iff (L := M.toLanguage) (EventualBehaviorOf M p) pre).mp
        h init hpre
    exact hdef hinit n tr out hreach
  · intro h
    refine
      (le_wellFormedOn_iff (L := M.toLanguage) (EventualBehaviorOf M p) pre).mpr
        ?_
    intro init hpre hinit n tr out hreach
    exact h init n tr out hpre hinit hreach

/-- Refining `(M.toLanguage).WellFormed` unfolds to `out.isSafe` across every
    initial state `init`, step budget `n`, trace `tr`, and outcome `out`. -/
theorem eventualBehaviorOf_le_wellFormed_iff
    {M : SmallStepMachine Prog State Obs Val} {p : Prog} :
    EventualBehaviorOf M p ≤ (M.toLanguage).WellFormed ↔
      ∀ init n tr out,
        M.initState p init →
        ReachesPrefix M.step p n init tr out →
        out.isSafe := by
  constructor
  · intro h init n tr out hinit hreach
    have hdef :=
      (le_wellFormed_iff (L := M.toLanguage) (EventualBehaviorOf M p)).mp h init
    exact hdef hinit n tr out hreach
  · intro h
    refine
      (le_wellFormed_iff (L := M.toLanguage) (EventualBehaviorOf M p)).mpr ?_
    intro init hinit n tr out hreach
    exact h init n tr out hinit hreach

/-- Bridge lemma for establishing normal-return partial-correctness
    specifications on `EventualBehaviorOf M p`: it suffices to show that at
    every initial state `s` satisfying `pre s`, every reachable prefix `(n, tr,
    oc)` is safe (`oc.isSafe`) and satisfies `P s ret` whenever
    `oc = .terminated (.normal ret)`. -/
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

/-- Unconditional specialization of `eventualBehaviorOf_le_normalSpecOn`
    (`pre := fun _ => True`). -/
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
## 2. Reactive Trace Separation (`BB-4`)
-/

namespace BB4

/-- A simple reactive server (`Prog := Bool`) where `true` is the productive
    server that emits `()` at every step (`step () ()`), and `false` is a
    silent loop (`silent ()`). -/
def reactiveVsSilentMachine : SmallStepMachine Bool Unit Unit Empty where
  initState _ _ := True
  step p _ r    :=
    if p then
      r = .step () ()
    else
      r = .silent ()

abbrev ReactiveLang : Language (EventualOut Unit Empty) :=
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
    reactive server (`true`) never silently diverges; hence `silentLoop` does
    not compile `reactiveServer`. -/
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

/-!
## 3. Zero-Tax Deterministic Machines (`BB-5`) and Open-World Callbacks (`BB-6`)
-/

namespace BB5

/-- Deterministic transition step with zero `.choice` or `Obs` constructors. -/
inductive DetStep (State Val : Type) where
  | silent (next : State)
  | terminated (term : TerminationKind Val)
  | failed

/-- Deterministic trace-free operational machine: `step` is a total function. -/
structure DetMachine (Prog State Val : Type) where
  initState : Prog → State → Prop
  step      : Prog → State → DetStep State Val

/-- Lift any `DetMachine` to a `Trusted.SmallStepMachine` (`Obs := Empty`). -/
def DetMachine.toSmallStep {Prog State Val : Type}
    (M : DetMachine Prog State Val) :
    SmallStepMachine Prog State Empty Val where
  initState := M.initState
  step p s r :=
    match M.step p s with
    | .silent s'       => r = .silent s'
    | .terminated term => r = .terminated term
    | .failed          => r = .failed

abbrev DetMachine.toLanguage {Prog State Val : Type}
    (M : DetMachine Prog State Val) :
    Language (EventualOut Empty Val) :=
  M.toSmallStep.toLanguage

/-- Bounded fuel evaluator for `DetMachine` (defined via `Nat.rec` so Lean's
    code generator does not emit `._unsafe_rec`). -/
def DetMachine.runSteps {Prog State Val : Type}
    (M : DetMachine Prog State Val) (p : Prog) (n : Nat) :
    State → PrefixOutcome State Val :=
  Nat.rec
    (motive := fun _ => State → PrefixOutcome State Val)
    (fun s => .running s)
    (fun _ run s =>
      match M.step p s with
      | .silent s'       => run s'
      | .terminated term => .terminated term
      | .failed          => .failed)
    n

/-- Dominator-cut composition for `DetMachine.runSteps`: reaching
    `.running s_cut` in `k₁` steps and then reaching `out` in `k₂` steps from
    `s_cut` equals a `(k₁ + k₂)`-step run from `s₀`. -/
theorem DetMachine.loopCut_runSteps {Prog State Val : Type}
    (M : DetMachine Prog State Val) (p : Prog) :
    ∀ (k₁ k₂ : Nat) (s₀ s_cut : State),
      M.runSteps p k₁ s₀ = .running s_cut →
      M.runSteps p (k₁ + k₂) s₀ = M.runSteps p k₂ s_cut
  | 0, k₂, _, _, h₁ => by
    dsimp [DetMachine.runSteps] at h₁
    injection h₁ with h_eq
    subst h_eq
    have h_zero : 0 + k₂ = k₂ := Nat.zero_add k₂
    rw [h_zero]
  | n + 1, k₂, s₀, s_cut, h₁ => by
    have h_succ : n + 1 + k₂ = (n + k₂) + 1 := Nat.succ_add n k₂
    rw [h_succ]
    dsimp [DetMachine.runSteps] at h₁ ⊢
    revert h₁
    cases M.step p s₀ with
    | silent s' =>
      intro h₁
      exact DetMachine.loopCut_runSteps M p n k₂ s' s_cut h₁
    | terminated _ =>
      intro h₁; cases h₁
    | failed =>
      intro h₁; cases h₁

/-- Every `DetMachine` automatically satisfies step totality with zero
    per-machine proof work. -/
theorem DetMachine.totalStep {Prog State Val : Type}
    (M : DetMachine Prog State Val) (p : Prog) (s : State) :
    ∃ r, M.toSmallStep.step p s r := by
  dsimp [DetMachine.toSmallStep]
  cases M.step p s with
  | silent s'       => exact ⟨.silent s', rfl⟩
  | terminated term => exact ⟨.terminated term, rfl⟩
  | failed          => exact ⟨.failed, rfl⟩

/-- Every `DetMachine` automatically satisfies demonic branch inhabitation with
    zero per-machine proof work. -/
theorem DetMachine.inhabitedDemonic {Prog State Val : Type}
    (M : DetMachine Prog State Val) (p : Prog) (s : State)
    (branches : State → Prop)
    (h : M.toSmallStep.step p s (.choice branches)) :
    ∃ s', branches s' := by
  dsimp [DetMachine.toSmallStep] at h
  revert h
  cases M.step p s with
  | silent s' =>
    dsimp [StepResult.silent]
    intro h
    injection h with h_eq
    rw [h_eq]
    exact ⟨s', rfl⟩
  | terminated _ =>
    intro h; cases h
  | failed =>
    intro h; cases h

end BB5

namespace BB6

/-- Open-world external call contract wrapping
    `Trusted.StepResult.externalCall`: checks `boundaryInv` at the call site and
    branches demonically over `frameRel s s' ∧ callPost s callId args s'`. -/
structure ExternalCallContract (State CallId Args : Type) where
  boundaryInv    : State → CallId → Args → Bool
  frameRel       : State → State → Prop
  callPost       : State → CallId → Args → State → Prop
  post_inhabited : ∀ s callId args,
    boundaryInv s callId args = true →
    ∃ s', frameRel s s' ∧ callPost s callId args s'

/-- Execute an open-world external call step via `StepResult.externalCall`. -/
def ExternalCallContract.evalStep {State CallId Args Obs Val : Type}
    (ext : ExternalCallContract State CallId Args)
    (s : State) (callId : CallId) (args : Args) :
    StepResult State Obs Val :=
  StepResult.externalCall (ext.boundaryInv s callId args)
    (fun s' => ext.frameRel s s' ∧ ext.callPost s callId args s')

/-- When `boundaryInv s callId args = true`, `evalStep` transitions to `.choice`
    over `frameRel ∧ callPost`. -/
@[simp]
theorem externalCall_ok_steps_to_choice
    {State CallId Args Obs Val : Type}
    (ext : ExternalCallContract State CallId Args)
    (s : State) (callId : CallId) (args : Args)
    (h_ok : ext.boundaryInv s callId args = true) :
    ext.evalStep (Obs := Obs) (Val := Val) s callId args =
      .choice
        (fun s' => ext.frameRel s s' ∧ ext.callPost s callId args s') := by
  dsimp [ExternalCallContract.evalStep, StepResult.externalCall]
  rw [h_ok]
  rfl

/-- When `boundaryInv s callId args = false`, `evalStep` transitions immediately
    to `.failed` at step 1. -/
@[simp]
theorem externalCall_violated_steps_to_failed
    {State CallId Args Obs Val : Type}
    (ext : ExternalCallContract State CallId Args)
    (s : State) (callId : CallId) (args : Args)
    (h_violated : ext.boundaryInv s callId args = false) :
    ext.evalStep (Obs := Obs) (Val := Val) s callId args = .failed := by
  dsimp [ExternalCallContract.evalStep, StepResult.externalCall]
  rw [h_violated]
  rfl

end BB6

/-!
## 4. Intrinsic Domain and Trajectory Divergence
-/

namespace StepCanaries

/-- Uninhabited `initState` machine and uninhabited `L.dom` constructively
    satisfy `Verified (fun _ => False) post` via `NonVacuousOn`'s `Or.inr`
    branch. -/
def EmptyInitMachine : SmallStepMachine Unit Unit Empty Unit where
  initState _ _ := False
  step _ s r    := r = .terminated (.normal s)

theorem s2_4_empty_init_verified_admitted :
    EmptyInitMachine.toLanguage.Verified
      (fun _ => False) (fun _ _ => False) () := by
  refine ⟨Or.inr (fun _ hdom => ?_), ?_, ?_⟩
  · cases hdom with
    | intro _ h => exact h
  · intro _ hfalse
    exact False.elim hfalse
  · intro _ hfalse
    exact False.elim hfalse

def InfallibleLang : Language Unit where
  Prog  := Unit
  Query := Unit
  Out   := Unit
  obs   := id
  sem   := fun _ _ => Partial.bot
  dom   := fun _ => False

theorem holdout_A4_part3_infallible_verified :
    InfallibleLang.Verified (fun _ => False) (fun _ _ => False) () := by
  refine ⟨Or.inr (fun _ h => h), ?_, ?_⟩
  · intro _ hfalse
    exact False.elim hfalse
  · intro _ hfalse
    exact False.elim hfalse

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

def twoStateTraj (k : Nat) : TwoLivelockState :=
  Nat.rec
    (motive := fun _ => TwoLivelockState)
    .s1
    (fun _ cur =>
      match cur with
      | .init => .s1
      | .s1   => .s2
      | .s2   => .s1)
    k

theorem twoStateTraj_succ (k : Nat) :
    twoStateTraj (k + 1) =
      match twoStateTraj k with
      | .init => .s1
      | .s1   => .s2
      | .s2   => .s1 := rfl

theorem twoStateTraj_step :
    ∀ k, ∃ m,
      ReachesPrefix TwoStateLivelockMachine.step () (m + 1) (twoStateTraj k) []
        (.running (twoStateTraj (k + 1))) := by
  have h_inv : ∀ k, twoStateTraj k = .s1 ∨ twoStateTraj k = .s2 := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [twoStateTraj_succ]
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
    rw [twoStateTraj_succ, h1]
    exact .choice 0 TwoLivelockState.s1 TwoLivelockState.s2
      (· = TwoLivelockState.s2) [] (.running TwoLivelockState.s2)
      rfl rfl (.zero TwoLivelockState.s2)
  | inr h2 =>
    refine ⟨0, ?_⟩
    rw [twoStateTraj_succ, h2]
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
  · intro hval
    cases hval.2.2 with
    | intro n hn =>
      cases hn with
      | intro s hs =>
        cases hs.1 with
        | step n1 _ s' _ tr1 _ hstep hr1 =>
          injection hstep with _ hs'
          subst hs'
          have hpair := twoState_silent_only (Or.inl rfl) hr1
          cases hs.2 1 with
          | intro k hk =>
            cases hk with
            | intro s'' hs'' =>
              cases hs'' with
              | intro tr' htr' =>
                cases hpair.2 with
                | inl h1 =>
                  injection h1 with hs1
                  subst hs1
                  have hpair' := twoState_silent_only (Or.inl rfl) htr'.2
                  have htr_nil := hpair'.1
                  have hlen := htr'.1
                  rw [htr_nil] at hlen
                  nomatch hlen
                | inr h2 =>
                  injection h2 with hs2
                  subst hs2
                  have hpair' := twoState_silent_only (Or.inr rfl) htr'.2
                  have htr_nil := hpair'.1
                  have hlen := htr'.1
                  rw [htr_nil] at hlen
                  nomatch hlen
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
    ∀ {m : Nat} {c : Nat} {tr : List Empty}
      {out : PrefixOutcome CountdownState Nat} {s' : CountdownState},
      ReachesPrefix CountdownMachine.step () (m + 1) (.count c) tr out →
      out = .running s' →
      ∃ c₀ c', c = c₀ + 1 ∧ s' = .count c' ∧ c' ≤ c₀ := by
  intro m c tr out s' hr hout
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
      cases countdown_reaches_le hr' hout with
      | intro c' hc' =>
        exact ⟨c₀, c', rfl, hc'.1, hc'.2⟩
    | emptyChoice _ _ _ _ _ => nomatch hout
    | terminated _ _ _ _ => nomatch hout
    | failed _ _ _ => nomatch hout
    | noStep _ _ _ => nomatch hout

theorem countdown_reaches_from_init :
    ∀ {steps : Nat} {tr : List Empty}
      {out : PrefixOutcome CountdownState Nat} {s' : CountdownState},
      ReachesPrefix CountdownMachine.step () (steps + 1) .init tr out →
      out = .running s' →
      ∃ c', s' = .count c' := by
  intro steps tr out s' hr hout
  cases hr with
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ sMid _ _ _ hstep hbr hr' =>
    injection hstep with hb
    rw [hb] at hbr
    cases hbr with
    | intro m hm =>
      subst hm
      cases countdown_reaches_le hr' hout with
      | intro c' hc' =>
        exact ⟨c', hc'.1⟩
  | emptyChoice _ _ _ _ _ => nomatch hout
  | terminated _ _ _ _ => nomatch hout
  | failed _ _ _ => nomatch hout
  | noStep _ _ _ => nomatch hout

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
      cases countdown_step_plus_from_count hr rfl with
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
      cases countdown_step_plus_from_count hr rfl with
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
              cases countdown_reaches_from_init hr0 rfl with
              | intro c' hs1 =>
                exact countdown_no_traj c' traj hstep 1 c' (Nat.le_refl c') hs1
  · refine ⟨rfl, 2, ?_⟩
    exact .choice 1 CountdownState.init (CountdownState.count 0)
      (fun s' => ∃ m, s' = CountdownState.count m) []
      (.terminated (.normal 42)) rfl ⟨0, rfl⟩
      (.terminated 0 (CountdownState.count 0) (.normal 42) rfl)

/-- Constructive silent loop (`MLoop`) and infinite ticker (`MTick`) verified
    with zero `Classical.choice`. -/
def MLoop : SmallStepMachine Unit Nat Empty Unit where
  initState _ n := n = 0
  step _ n r    := r = .silent (n + 1)

theorem mLoop_reaches_safe :
    ∀ {k n : Nat} {tr : List Empty} {out : PrefixOutcome Nat Unit},
      ReachesPrefix MLoop.step () k n tr out → out.isSafe := by
  intro k
  induction k with
  | zero =>
    intro n tr out hr
    cases hr with
    | zero => trivial
  | succ k ih =>
    intro n tr out hr
    cases hr with
    | step _ _ _ obs _ _ _ _ => nomatch obs
    | choice _ _ s' _ _ _ hstep hbr hr' =>
      injection hstep with hb
      rw [hb] at hbr
      subst hbr
      exact ih hr'
    | emptyChoice _ _ _ hstep hno =>
      injection hstep with hb
      rw [hb] at hno
      exact False.elim (hno ⟨n + 1, rfl⟩)
    | terminated _ _ _ hstep => nomatch hstep
    | failed _ _ hstep => nomatch hstep
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.silent (n + 1), rfl⟩)

theorem holdout_A4_part1_constructive_loop :
    MLoop.toLanguage.ProductiveOn (· = 0) () := by
  intro q hq
  subst hq
  have hdef : (MLoop.toLanguage.sem () 0).defined :=
    fun _ _ _ _ hr => mLoop_reaches_safe hr
  refine ⟨hdef, .diverges [], rfl, 0, 0, .zero 0, id, rfl, ?_⟩
  intro k
  exact ⟨0, .choice 0 k (k + 1) (· = k + 1) [] (.running (k + 1))
    rfl rfl (.zero (k + 1))⟩

def MTick : SmallStepMachine Unit Nat Unit Unit where
  initState _ n := n = 0
  step _ n r    := r = .step () (n + 1)

theorem mTick_reaches_n (m : Nat) :
    ∀ s,
      ReachesPrefix MTick.step () m s (List.replicate m ()) (.running (s + m)) := by
  induction m with
  | zero =>
    intro s
    simp only [Nat.add_zero, List.replicate]
    exact .zero s
  | succ m ih =>
    intro s
    have h_ih := ih (s + 1)
    have heq : s + 1 + m = s + (m + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 m, ← Nat.add_assoc]
    rw [heq] at h_ih
    exact .step m s (s + 1) () (List.replicate m ()) (.running (s + (m + 1)))
      rfl h_ih

theorem holdout_A4_part2_constructive_ticker
    (hdef : (MTick.toLanguage.sem () 0).defined) :
    (MTick.toLanguage.sem () 0).val hdef (.reacts [(), ()]) := by
  refine ⟨rfl, by decide, 2, 2,
    .step 1 0 1 () [()] (.running 2) rfl
      (.step 0 1 2 () [] (.running 2) rfl (.zero 2)), ?_⟩
  intro m
  refine ⟨m, 2 + m, List.replicate m (), ?_, mTick_reaches_n m 2⟩
  simp [List.length_replicate]

end StepCanaries

end Anneal
